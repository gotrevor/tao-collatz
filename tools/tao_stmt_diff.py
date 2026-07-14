#!/usr/bin/env -S uv run --quiet python3
"""Character-diff PINNED Lean statements across a commit (judge ratification check).

A statement = the text from `theorem NAME` up to and including the first `:= by` / `:=`
at the end of the signature. Any change REVOKES that statement's ratification.
Proof-body churn is fine and expected on a D4 numeral change.
"""
import re
import subprocess
import sys

REV_OLD, REV_NEW = "7803117^", "7803117"
REPO = "/Users/gotrevor/src/tao-collatz"

PINNED = {
    "TaoCollatz/Sec7/Triangles.lean": ["black_structure", "white_gap_above_run_top"],
    "TaoCollatz/Sec7/ManyTriangles.lean": [
        "fpDist_white_exit_deep", "fpDist_any_triangle_le", "fpDist_out_of_strip_le",
        "fpDist_any_triangle_le_of_localization_box", "triangle_encounter_le",
    ],
    "TaoCollatz/Sec7/BlackEdge.lean": [
        "fpDist_edgeWeight_le", "fpDist_white_exit", "Q_black_edge_case2",
    ],
    "TaoCollatz/Sec7/White.lean": [],
    "TaoCollatz/Sec7/Setup.lean": ["black", "epsBW"],
}


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


bad, missing, ok = [], [], []
for path, names in PINNED.items():
    old_src, new_src = show(REV_OLD, path), show(REV_NEW, path)
    for n in names:
        a, b = statement(old_src, n), statement(new_src, n)
        if a is None or b is None:
            missing.append(f"{n} ({path}) old={'✓' if a else '✗'} new={'✓' if b else '✗'}")
        elif a != b:
            bad.append((n, path, a, b))
        else:
            ok.append(n)

print(f"✅ character-identical ({len(ok)}): {', '.join(ok)}")
if missing:
    print(f"\n⚠️  not found ({len(missing)}):")
    for m in missing:
        print(f"   {m}")
if bad:
    print(f"\n🚨 STATEMENT CHANGED — RATIFICATION REVOKED ({len(bad)}):")
    for n, path, a, b in bad:
        print(f"\n--- {n}  ({path})")
        print("OLD:", a[:600])
        print("NEW:", b[:600])
    sys.exit(1)
print("\nNo pinned statement changed. Ratifications survive the D4 numeral change.")
