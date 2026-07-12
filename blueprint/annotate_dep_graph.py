#!/usr/bin/env python3
"""Surface per-node campaign estimates (laps + risk) on the dependency graph.

Post-processes web/dep_graph_document.html after `leanblueprint web`:
  * node fill tint by risk  — pale red (high) / amber (medium) / green (low);
    applied ONLY to nodes with no status fill of their own, so leanblueprint's
    proof-status backgrounds (blue = ready, green = proved) always win — a node
    that has progressed past "unstarted" keeps its status color and shows the
    estimate via label + tooltip only;
  * second label line       — the estimated treadmill-lap range;
  * hover tooltip           — laps + risk word + confidence;
  * legend entries for the three tints.

Single source of truth: the \\lapsrisk{laps}{risk}{conf} annotations in
src/content.tex (which mirror BLUEPRINT.md §2's ledger). Rerun after every
`leanblueprint web` — use ./build.sh, which chains the two. Idempotent.
"""
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
TEX = HERE / "src/content.tex"
HTML = HERE / "web/dep_graph_document.html"

TINT = {"high": "#F5B8B0", "medium": "#F2DD9E", "low": "#BFE3C4"}

ENV_RE = re.compile(
    r"\\begin\{(definition|lemma|theorem|proposition|corollary)\}"
    r".*?\\label\{([A-Z]\d+)\}(.*?)\\end\{",
    re.DOTALL,
)
LAPSRISK_RE = re.compile(r"\\lapsrisk\{([^}]*)\}\{([^}]*)\}\{([^}]*)\}")
NODE_RE = re.compile(r"(?P<pre>[;{]\s*)(?P<id>[A-Z]\d+)\s*\[(?P<attrs>[^\]]*)\]")

# The DOT lives inside a JS TEMPLATE LITERAL: a backslash there is a JS escape
# (`\v` in "$\varepsilon$" became a vertical-tab control char that killed the wasm
# renderer mid-parse — the 2026-07-10 five-node regression), a backtick would end
# the literal, `${` would interpolate. Whitelist hard: anything fancy (the ledger
# notes' LaTeX) belongs in the node modal, which renders content.tex properly.
SAFE_RE = re.compile(r"[^A-Za-z0-9 %·–.-]")


def sanitize(s: str) -> str:
    return SAFE_RE.sub("", s).strip()


def read_estimates() -> dict[str, tuple[str, str, str, str]]:
    """label -> (laps '8–15', risk word, conf '90%', env type), from content.tex."""
    out = {}
    for m in ENV_RE.finditer(TEX.read_text()):
        env, label, body = m.group(1), m.group(2), m.group(3)
        lr = LAPSRISK_RE.search(body)
        if not lr:
            continue
        laps = sanitize(lr.group(1).replace("--", "–"))
        risk_word = sanitize(lr.group(2).split()[0])  # "high --- risk kernel 1" -> "high"
        # Clip the confidence to its leading "NN%" — the ledger's dated notes are
        # for the modal, not a hover tooltip (and their LaTeX is what broke the JS).
        conf_m = re.match(r"\s*(\d+\s*\\?%)", lr.group(3))
        conf = conf_m.group(1).replace("\\", "") if conf_m else sanitize(lr.group(3))[:24]
        out[label] = (laps, risk_word, conf, env)
    return out


def patch_node(m: re.Match, est: dict) -> str:
    node_id, attrs = m.group("id"), m.group("attrs")
    if "class=" in attrs:  # already processed (idempotency)
        return m.group(0)
    if node_id in est and "tooltip=" not in attrs:
        laps, risk, conf, env = est[node_id]
        # Definition nodes carry no proof obligation, so leanblueprint fills them
        # green (dark green once the ancestor cone is green) as soon as their bound
        # defs compile — while the badge tracks the node's still-open SUPPORT work
        # (sorried helper lemmas in its files). Say so on the node itself, or a
        # green box with a lap count reads as a contradiction.
        line = f"support {laps}" if env == "definition" else laps
        tip = (
            f"{laps} support-lemma laps still open · risk {risk} · {conf} confidence "
            "(green fill only means the bound defs compile - definitions have no "
            "proof obligation in leanblueprint)"
            if env == "definition"
            else f"{laps} laps · risk {risk} · {conf} confidence"
        )
        # Two-line label: id + lap range. The file holds \\n so the JS template
        # literal collapses it to \n, which graphviz renders as a line break.
        attrs = re.sub(rf"label={node_id}\b", f'label="{node_id}\\\\n{line}"', attrs)
        attrs += f',\t\ttooltip="{tip}"'
        if "fillcolor" not in attrs:  # never override a leanblueprint status fill
            attrs += f',\t\tstyle=filled,\t\tfillcolor="{TINT[risk]}"'
    # EVERY filled node — our risk tints AND leanblueprint's own status fills
    # (proved green #9CEC8B, ready blue, ...) — is a light pastel, so the dark
    # theme's light label text is unreadable on it (X3 went invisible the moment
    # it earned its status fill). class= flows through graphviz into the SVG,
    # letting the injected CSS force dark text in BOTH themes.
    if "fillcolor" in attrs:
        attrs += ',\t\tclass="lightfill"'
    return f"{m.group('pre')}{node_id}\t[{attrs}]"


LEGEND_ANCHOR = "<dt>Dark green border</dt><dd>this is in Mathlib</dd>"
LEGEND_EXTRA = (
    "\n      \n      <dt>Pale red background</dt><dd>campaign risk: <em>high</em> "
    "(the node's PROOF is still open — the tint tracks remaining proof risk and drops "
    "only on completion; the border independently tracks statement status; label's "
    "second line = estimated treadmill laps)</dd>"
    "\n      \n      <dt>Pale amber background</dt><dd>campaign risk: <em>medium</em></dd>"
    "\n      \n      <dt>Pale green background</dt><dd>campaign risk: <em>low</em></dd>"
    "\n      \n      <dt>Green box, “support N–M” label</dt><dd>a "
    "<em>definition</em> node: its bound defs compile (that is all the green fill "
    "certifies — definitions have no proof obligation), while N–M laps of "
    "support-lemma work inside its files are still open; the lap line drops when "
    "that work is done</dd>"
)

# Filled nodes always carry a light pastel (risk tint or leanblueprint status
# fill), so force near-black label text on them regardless of the page theme (the
# dark theme's light link-text was unreadable on the tints, then again on X3's
# proved-green). Scoped to the class the DOT sets, so unfilled nodes keep their
# theme styling.
CSS_MARKER = "/* lightfill */"
CSS_EXTRA = (
    f"\n<style>{CSS_MARKER} #graph .lightfill text, "
    "#graph .lightfill a, #graph .lightfill a text "
    "{ fill: #1b1b1b !important; color: #1b1b1b !important; }</style>\n"
)


def main() -> int:
    est = read_estimates()
    if not est:
        sys.exit("no \\lapsrisk annotations found in content.tex")
    html = HTML.read_text()
    patched, n = NODE_RE.subn(lambda m: patch_node(m, est), html)
    if LEGEND_ANCHOR in patched and "campaign risk" not in patched:
        patched = patched.replace(LEGEND_ANCHOR, LEGEND_ANCHOR + LEGEND_EXTRA, 1)
    if CSS_MARKER not in patched and "</head>" in patched:
        patched = patched.replace("</head>", CSS_EXTRA + "</head>", 1)
    HTML.write_text(patched)
    annotated = sum(1 for i in est if f'tooltip="{est[i][0]}' in patched)
    print(f"dep graph: {len(est)} estimates in tex, {n} node attrs scanned, "
          f"{annotated} nodes annotated")
    return 0


if __name__ == "__main__":
    sys.exit(main())
