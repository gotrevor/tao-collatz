#!/usr/bin/env -S uv run --quiet python3
"""Character-diff PINNED Lean statements across a commit (judge ratification check).

A statement = the text from `theorem NAME` up to and including the first `:= by` / `:=`
at the end of the signature. Any change REVOKES that statement's ratification.
Proof-body churn is fine and expected on a D4 numeral change.
"""
import re
import subprocess
import sys

REPO = str(__import__("pathlib").Path(__file__).resolve().parent.parent)

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
# Pass 27 lesson (the sequel): the list above was §7-shaped, but the FRONTIER MOVED to §5/§6.
# A guard aimed only at the finished part of the proof is blind to the part being worked on.
# The two OPEN crux statements — `fine_scale_mixing` (C10) and `stabilization` (C9) — are the
# statements a lap is under the most pressure to quietly make provable, and neither was watched
# (their files weren't even searched). WATCHED != RATIFIED: a name here means the differ reports
# any change to it. Ratification is the judge's separate reading against the PDF. Watching an
# un-ratified statement is strictly good — it is how we SEE the frontier move.
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
    # X11 / Case-3 leaves — (7.56) + (7.54), PROVED + ratified pass 27.
    # `few_white_mass_le` carries the paper-faithful deep hypothesis `m/log^2 m < s`;
    # it is where the `Cthr` largeness bridge to depth `m+1` lives. Guard it.
    "few_white_mass_le", "col_tail_mass_le",
    # §7 exports feeding §6 — Prop 7.1 + Prop 1.17. `charFn_decay` is C10's analytic INPUT,
    # so it is now upstream of live work: a lap that finds C10 hard could "adjust" it.
    "key_fourier_decay", "charFn_decay",
    # C10 (Prop 1.14, §6) — 🏆 COMPLETE + axiom-clean (verified 2026-07-14, HEAD 49b32c7).
    # C9 (Prop 1.11, §5) — still open. Both stay watched: a finished pin is exactly what a
    # later lap is tempted to "adjust" when something downstream will not close.
    "fine_scale_mixing", "stabilization",
    # 🔴 THE LIVE FRONTIER — §5. Watched the moment they were pinned (ratify ⟹ watch; and when
    # the frontier moves, MOVE THE GUARD WITH IT — pass 27's lesson, which the judge promptly
    # re-broke by pinning C7 and not adding it here for four hours).
    #   C7 (1.19), judge-pinned + ratified vs p.20. Stated character-identically to the FIRST
    #     CONJUNCT of `stabilization` — so if either drifts, the differ must catch it.
    #   C8 (Prop 5.2 / (5.8)), worker-pinned. WATCHED, *not* ratified — the judge still owes it
    #     a reading against pp.22–25. Watching an un-ratified statement is how we see it move.
    "first_passage_nonescape", "first_passage_approx",
    # The reduction floor — paper (1.2) Collatz->Syracuse + the Lemma 1.12/(1.21)/(1.22)
    # Syracuse-RV identities (all PROVED pass 27). The whole reduction rests on these.
    "colMin_eq_syrMin_oddPart",
    "syracZ_recursion", "syracZ_eq_rev_fnat", "syracZ_map_cast",
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
    "TaoCollatz/Sec7/Decay.lean",
    "TaoCollatz/Sec7/Reduction.lean",
    # the live frontier (pass 27) — §6/§5 + the reduction floor
    "TaoCollatz/Sec6/MixingFromDecay.lean",
    "TaoCollatz/Sec5/FirstPassage.lean",
    "TaoCollatz/Sec5/ApproxFormula.lean",
    "TaoCollatz/Sec5/Stabilization.lean",
    "TaoCollatz/Basic/Collatz.lean",
    "TaoCollatz/Syracuse/SyracRV.lean",
    "TaoCollatz/Statement.lean",
]


def show(rev: str, path: str) -> str:
    r = subprocess.run(["git", "show", f"{rev}:{path}"], cwd=REPO,
                       capture_output=True, text=True)
    return r.stdout


def statement(src: str, name: str) -> str | None:
    """Text from `theorem/lemma/def NAME` through the end of its signature.

    The trailing proof delimiter is NORMALIZED away: a proof that switches from tactic
    mode (`:= by`) to term mode (`:=`) leaves the *statement* character-identical, and
    the differ must not report it.

    This is not a nicety. On 2026-07-14 (judge pass 28→29 boundary) `fine_scale_mixing`
    — the C10 crux, a WATCHED statement — went `:= by` -> `:=` when its proof became a
    term, and the differ screamed "RATIFICATION REVOKED" at a statement whose every
    mathematical character was unchanged. **An over-sensitive guard is a guard that gets
    muted**, and a muted guard is how a real deviation walks through. Cry wolf never.
    """
    m = re.search(rf"^(?:theorem|lemma|def|noncomputable def)\s+{re.escape(name)}\b",
                  src, re.M)
    if not m:
        return None
    tail = src[m.start():]
    # end of signature = the first `:= by` or `:=`
    e = re.search(r":=\s*by\b|:=", tail)
    if not e:
        return None
    body = tail[: e.start()]                 # the signature, WITHOUT the delimiter
    return body.rstrip() + " :="             # normalized terminator: mode-agnostic


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
