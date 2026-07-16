#!/usr/bin/env python3
"""Trim doc-gen4 output to just this project's library, linking dependencies out to
the officially hosted Mathlib docs instead of shipping ~1.3 GB of them.

doc-gen4 has no native "document only my library" mode: the `:docs` facet renders
the entire import closure (all of Mathlib, Std, Init, Lean, Batteries, ...). For a
single-project repo that is 99.6% bloat. This post-build step keeps only the named
library's pages + the doc-gen4 chrome, deletes the dependency module trees,
and rewrites every cross-reference into a dependency so it points at
https://leanprover-community.github.io/mathlib4_docs/ (whose paths match doc-gen4's
exactly). Result: a few MB instead of ~1.3 GB, with upstream links that still work.

Caveat: the hosted docs track *current* mathlib, while ours are pinned. Module-level
paths are very stable, so the common Init/Mathlib links resolve; an occasional decl
that has since moved upstream may 404. That is the accepted cost of linking out
rather than self-hosting the whole closure.

Usage:  trim-docs.py <doc_dir> <LibName>
Stdlib only (runs in CI on a bare runner; no pip installs).
"""
import sys
import os
import re
import json
import shutil

HOSTED = "https://leanprover-community.github.io/mathlib4_docs/"
# Top-level output dirs that are doc-gen4 chrome, not dependency module trees.
ASSET_DIRS = {"declarations", "find", "src"}


def build_link_rewriter(dep_mods):
    """Rewrite href/src/data-path values of the form `(../)*Dep/...` or `(../)*Dep.html`
    into absolute hosted URLs, for Dep in the dependency set. Relative links to the
    kept library are left untouched (it is not in dep_mods)."""
    if not dep_mods:
        return lambda html: html
    # Longest names first so e.g. `LeanSearchClient` wins over a `Lean` prefix; the
    # trailing (/|.html) boundary already prevents `Lean` matching a kept lib that
    # merely starts with it.
    alt = "|".join(re.escape(m) for m in sorted(dep_mods, key=len, reverse=True))
    pat = re.compile(
        r'((?:href|src|data-path)=")((?:\.\.?/)*)(?=(?:%s)(?:/|\.html))' % alt
    )
    return lambda html: pat.sub(lambda m: m.group(1) + HOSTED, html)


def trim_navbar(s, lib):
    """Keep only the kept library's `<details>` block in the left-sidebar module list;
    drop every dependency library's block. General-doc chrome links are preserved."""
    marker = '<div class="module_list">'
    i = s.find(marker)
    if i < 0:
        return s
    start = i + len(marker)
    prefix, rest = s[:start], s[start:]

    # Segment the depth-0 <details> blocks (the per-library entries).
    depth = 0
    bstart = None
    blocks = []
    last_end = 0
    for m in re.finditer(r"<details\b|</details>", rest):
        if m.group().startswith("<details"):
            if depth == 0:
                bstart = m.start()
            depth += 1
        else:
            depth -= 1
            if depth == 0:
                blocks.append((bstart, m.end()))
                last_end = m.end()
    if not blocks:
        return s

    keep_path = "./%s.html" % lib
    kept = []
    for a, b in blocks:
        block = rest[a:b]
        mp = re.match(r'<details\b[^>]*\bdata-path="([^"]*)"', block)
        if mp and mp.group(1) == keep_path:
            kept.append(block)
    pre_gap = rest[: blocks[0][0]]   # text between module_list open and first block
    tail = rest[last_end:]           # module_list close + color picker + closing tags
    return prefix + pre_gap + "".join(kept) + tail


def trim_decl_data(path, lib):
    """Shrink the search/hover index (declaration-data.bmp) to the kept library only."""
    with open(path, encoding="utf-8") as f:
        d = json.load(f)

    def is_lib(name):
        return name == lib or name.startswith(lib + ".")

    decls = {k: v for k, v in d.get("declarations", {}).items() if is_lib(k)}
    kept = set(decls)
    modules = {k: v for k, v in d.get("modules", {}).items() if is_lib(k)}
    for v in modules.values():
        if isinstance(v, dict) and isinstance(v.get("importedBy"), list):
            v["importedBy"] = [m for m in v["importedBy"] if is_lib(m)]

    def filt(dd):
        out = {}
        for k, v in dd.items():
            if isinstance(v, list):
                vv = [x for x in v if x in kept]
                if vv:
                    out[k] = vv
        return out

    out = {
        "declarations": decls,
        "instances": filt(d.get("instances", {})),
        "instancesFor": filt(d.get("instancesFor", {})),
        "modules": modules,
    }
    with open(path, "w", encoding="utf-8") as f:
        json.dump(out, f, separators=(",", ":"))
    return len(d.get("declarations", {})), len(decls)


def main():
    if len(sys.argv) != 3:
        sys.exit("usage: trim-docs.py <doc_dir> <LibName>")
    doc_dir, lib = sys.argv[1], sys.argv[2]
    if not os.path.isdir(os.path.join(doc_dir, lib)):
        sys.exit("error: %s/%s not found - is the library name right?" % (doc_dir, lib))

    top_dirs = [e for e in os.listdir(doc_dir) if os.path.isdir(os.path.join(doc_dir, e))]
    # Anything that isn't the kept library, doc-gen4 chrome, or a dotdir (e.g. a
    # stray .git when run over a checked-out gh-pages tree) is a dependency module.
    dep_mods = sorted(
        d for d in top_dirs
        if d != lib and d not in ASSET_DIRS and not d.startswith(".")
    )
    print("Keeping library:   ", lib)
    print("Dropping deps:     ", ", ".join(dep_mods))

    # 1) Delete dependency module trees + their sibling <Dep>.html index pages.
    for d in dep_mods:
        shutil.rmtree(os.path.join(doc_dir, d), ignore_errors=True)
        h = os.path.join(doc_dir, d + ".html")
        if os.path.exists(h):
            os.remove(h)

    # 2) Structurally trim the sidebar.
    nav = os.path.join(doc_dir, "navbar.html")
    if os.path.exists(nav):
        with open(nav, encoding="utf-8") as f:
            s = f.read()
        with open(nav, "w", encoding="utf-8") as f:
            f.write(trim_navbar(s, lib))

    # 3) Rewrite dependency cross-references to the hosted docs in every kept page.
    rewrite = build_link_rewriter(dep_mods)
    n_files = 0
    for root, _, files in os.walk(doc_dir):
        for fn in files:
            if fn.endswith(".html"):
                p = os.path.join(root, fn)
                with open(p, encoding="utf-8") as f:
                    s = f.read()
                ns = rewrite(s)
                if ns != s:
                    n_files += 1
                    with open(p, "w", encoding="utf-8") as f:
                        f.write(ns)
    print("Rewrote dep links in %d html files" % n_files)

    # 4) Shrink the search/hover index.
    bmp = os.path.join(doc_dir, "declarations", "declaration-data.bmp")
    if os.path.exists(bmp):
        before, after = trim_decl_data(bmp, lib)
        print("Trimmed search index: %d -> %d declarations" % (before, after))

    print("Trim complete.")


if __name__ == "__main__":
    main()
