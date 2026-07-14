#!/usr/bin/env -S uv run --quiet python3
"""Character-diff PINNED Lean statements across a commit (judge ratification check).

A statement = the text from `theorem NAME` up to and including the first `:= by` / `:=`
at the end of the signature. Any change REVOKES that statement's ratification.
Proof-body churn is fine and expected on a D4 numeral change.
"""
import re
import subprocess
import sys

REPO = "/Users/gotrevor/src/tao-collatz"

# Usage: tao_stmt_diff.py [REV_OLD [REV_NEW]]   (default: the D4 numeral commit)
REV_OLD = sys.argv[1] if len(sys.argv) > 1 else "7803117^"
REV_NEW = sys.argv[2] if len(sys.argv) > 2 else "7803117"

# Every ratified pin. A statement edit to ANY of these revokes its ratification.
#
# Pass 26 lesson: this list WAS the erosion check's blind spot. `encounter_apex_proximity`
# (X10a, ratified pass 19) had its hypothesis rewritten by `61f8e80` and the differ said
# nothing, because the name was simply absent here. `triangle_encounter_le` was caught only
# because it happened to be listed. A pin that is not in this dict is NOT being watched.
# When the judge ratifies a statement, ADD IT HERE IN THE SAME PASS.
#
# Names are searched across ALL files listed below (pins get relocated — `fpDist_white_exit`
# and `Q_black_edge_case2` moved BlackEdge -> BlackEdgeQ in pass 26), so a move is reported
# as a move, not as a deletion.
PINNED_NAMES = [
    # Setup / geometry
    "black", "epsBW", "black_structure", "white_gap_above_run_top",
    # X9 — Lemma 7.9 (COMPLETE, pass 25)
    "fpDist_white_exit_deep", "fpDist_any_triangle_le", "fpDist_out_of_strip_le",
    "fpDist_any_triangle_le_of_localization_box", "many_triangles_white",
    # X10 — Lemma 7.10 (p.51: hypothesis is `s > m/log^2 m`) + X10a (p.53)
    "triangle_encounter_le", "encounter_apex_proximity",
    # X8 / Case-2 (COMPLETE, pass 26) — relocated to BlackEdgeQ.lean
    "fpDist_edgeWeight_le", "fpDist_white_exit", "Q_black_edge_case2",
    # X11 / Case-3 + the §7 spine above it (frozen)
    "Q_black_edge_case3", "Q_black_edge", "prop_7_8",
    # The trusted base — the two headline theorems
    "tao_collatz", "tao_collatz_quantitative",
]

SEARCH_FILES = [
    "TaoCollatz/Sec7/Setup.lean",
    "TaoCollatz/Sec7/Triangles.lean",
    "TaoCollatz/Sec7/White.lean",
    "TaoCollatz/Sec7/ManyTriangles.lean",
    "TaoCollatz/Sec7/BlackEdge.lean",
    "TaoCollatz/Sec7/BlackEdgeQ.lean",
    "TaoCollatz/Sec7/Case3.lean",
    "TaoCollatz/Statement.lean",
]


def show(rev: str, path: str) -> str:
    r = subprocess.run(["git", "show", f"{rev}:{path}"], cwd=REPO,
                       capture_output=True, text=True)
    return r.stdout


def statement(src: str, name: str) -> str | None:
    """Text from `theorem/lemma/def NAME` through the end of its signature."""
    m = re.search(rf"^(?:theorem|lemma|def|noncomputable def)\s+{re.escape(name)}\b",
                  src, re.M)
    if not m:
        return None
    tail = src[m.start():]
    # end of signature = first ':= by' or ':=' at depth 0-ish; take the first occurrence
    e = re.search(r":=\s*by\b|:=", tail)
    if not e:
        return None
    return tail[: e.end()]


def locate(rev: str, name: str):
    """Find a pinned statement anywhere in SEARCH_FILES (pins get relocated)."""
    for path in SEARCH_FILES:
        s = statement(show(rev, path), name)
        if s is not None:
            return path, s
    return None, None


bad, moved, missing, ok = [], [], [], []
for n in PINNED_NAMES:
    pa, a = locate(REV_OLD, n)
    pb, b = locate(REV_NEW, n)
    if a is None or b is None:
        missing.append(f"{n}  old={pa or '✗'}  new={pb or '✗'}")
    elif a != b:
        bad.append((n, pa, pb, a, b))
    else:
        ok.append(n)
        if pa != pb:
            moved.append(f"{n}: {pa} -> {pb}")

print(f"✅ character-identical ({len(ok)}/{len(PINNED_NAMES)}): {', '.join(ok)}")
if moved:
    print(f"\n↔  relocated but character-identical ({len(moved)}) — ratification SURVIVES:")
    for m in moved:
        print(f"   {m}")
if missing:
    print(f"\n⚠️  NOT FOUND ({len(missing)}) — a pin vanished; investigate:")
    for m in missing:
        print(f"   {m}")
if bad:
    print(f"\n🚨 STATEMENT CHANGED — RATIFICATION REVOKED ({len(bad)}):")
    for n, pa, pb, a, b in bad:
        print(f"\n--- {n}   ({pa} -> {pb})")
        print("OLD:", a[:700])
        print("NEW:", b[:700])
    sys.exit(1)
if missing:
    sys.exit(1)
print("\nNo pinned statement changed. All ratifications survive this range.")
