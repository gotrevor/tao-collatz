#!/usr/bin/env python3
"""Frontier guard for the assembled explicit big-C campaign (BIG_C_EXPLICIT_BOUND_PLAN.md, step 0).

Normal mode:
  - validates the completed prefix of the ordered manifest below,
  - prints the FIRST MISSING entry (the next lap's mandatory target),
  - exits 0 when the prefix is clean, nonzero on a regression inside it
    (an entry present *after* a missing one, a manifest declaration that
    disappeared, or a completed `_atCX` proof that calls its existential
    `_atC` sibling — which would smuggle the existential back in).

--complete mode (the campaign's done-gate; red until the last commit):
  - requires every manifest entry plus the final theorem, and
  - runs the DEFINITIONAL-CLOSURE explicitness walk (tools/ExplicitnessClosure.lean,
    `lake env lean --run`). Per the judge amendment in DIRECTION.md this is a
    closure walk seeded at `TaoCollatz.C_tao_assembled`, NEVER a file grep
    (`Nat.sInf` legitimately appears in `syrMin`/`passTime` — statement objects,
    not the constant's spine). The walk prints the closure size it visited and
    FAILS if that size is 0 or the seed is unknown.
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

# Ordered manifest. Each entry: (file, [required declarations], atcx_pair)
# atcx_pair = (atcx_name, atc_name) when a universal-cutoff sibling must NOT
# call its existential `_atC` original (the delegate goes the other way).
FP = "TaoCollatz/Sec5/FirstPassage.lean"
AF = "TaoCollatz/Sec5/ApproxFormula.lean"
ST = "TaoCollatz/Sec5/Stabilization.lean"
RD = "TaoCollatz/Sec3/Reduction.lean"
BC = "TaoCollatz/ExplicitBigC.lean"


def atcx(file: str, base: str, extra_defs: list[str] | None = None):
    return (file, (extra_defs or []) + [base + "_atCX"], (base + "_atCX", base + "_atC"))


MANIFEST: list[tuple[str, list[str], tuple[str, str] | None]] = [
    # ---- Phase 1: Sec5/FirstPassage.lean ----
    (FP, ["X_rpowEps", "rpow_le_eps_mul_of_lt_one_atX"], None),
    (FP, ["X_descentPow", "descent_pow_bounds_atX"], None),
    (FP, ["X_descentPasses", "descent_passes_atX"], None),
    atcx(FP, "first_passage_nonescape", ["X_firstPassNonescape"]),
    # ---- Phase 2: Sec5/ApproxFormula.lean (C8 cutoff spine, bottom-up) ----
    atcx(AF, "goodTuple_prefix_dev_sum"),
    atcx(AF, "approx_good_tuple_whp"),
    atcx(AF, "passtime_edge_mass"),
    atcx(AF, "passtime_window_inner"),
    atcx(AF, "approx_passtime_window"),
    atcx(AF, "first_passage_window_reduce"),
    atcx(AF, "reverse_early_return_whp"),
    atcx(AF, "steppedMid_le_firstPassMid_add"),
    atcx(AF, "first_passage_stepback_reduce"),
    atcx(AF, "truncation_error_bound"),
    atcx(AF, "first_passage_truncation_reindex"),
    atcx(AF, "first_passage_affine_reindex"),
    atcx(AF, "first_passage_approx"),
    # ---- Phase 3: Sec5/Stabilization.lean (C9 cutoff spine) ----
    atcx(ST, "perNTerm_harmonic_approx"),
    atcx(ST, "good_tuple_whp_iid"),
    atcx(ST, "syracZ_sub_perNGoodMass_bound"),
    atcx(ST, "perNHarmonic_eq_harmZfine_approx"),
    atcx(ST, "harmonic_to_Z"),
    atcx(ST, "mainZ_bound"),
    atcx(ST, "perNTerm_eval"),
    atcx(ST, "Iy_count_ratio"),
    atcx(ST, "approxMainTerm_to_Z"),
    atcx(ST, "approxMainTerm_window_stable"),
    atcx(ST, "stabilization", ["X_stab"]),
    # ---- Phase 4: Sec3/Reduction.lean ----
    atcx(RD, "descentProb_step", ["X_descStep"]),
    atcx(RD, "descentProb_base", ["X_descBase"]),
    atcx(RD, "descentProb_ladder", ["X_descLadder"]),
    atcx(RD, "descent_whp", ["X_descWhp"]),
    atcx(RD, "window_bad_sum", ["X_windowBad"]),
    atcx(RD, "tao_syracuse_quantitative_sum", ["X_syrSum"]),
    atcx(RD, "tao_collatz_quantitative_spine"),
    # ---- Phase 5: TaoCollatz/ExplicitBigC.lean ----
    (BC, ["X_spine", "tao_collatz_quantitative_spine_atCX_of_le"], None),
    (BC, ["C_tao_assembled", "C_tao_assembled_pos"], None),
    (BC, ["tao_collatz_quantitative_assembled"], None),
]

DECL_RE = r"^(?:noncomputable\s+)?(?:theorem|def|abbrev|lemma)\s+{name}\b"
# A top-level declaration header (used to slice a proof body out of a file).
HEADER_RE = re.compile(
    r"^(?:noncomputable\s+)?(?:private\s+)?(?:theorem|def|abbrev|lemma|instance|structure|inductive|end|section|namespace)\b"
)


def decl_present(text: str, name: str) -> bool:
    return re.search(DECL_RE.format(name=re.escape(name)), text, re.M) is not None


def decl_body(text: str, name: str) -> str | None:
    """The source slice from `name`'s header to the next top-level declaration."""
    lines = text.splitlines()
    start = None
    for i, ln in enumerate(lines):
        if re.match(DECL_RE.format(name=re.escape(name)), ln):
            start = i
            break
    if start is None:
        return None
    end = len(lines)
    for j in range(start + 1, len(lines)):
        if HEADER_RE.match(lines[j]):
            end = j
            break
    return "\n".join(lines[start:end])


def load(file: str) -> str:
    p = ROOT / file
    return p.read_text() if p.exists() else ""


def run_closure_walk() -> bool:
    print("[audit] running definitional-closure explicitness walk (lake env lean --run) ...")
    proc = subprocess.run(
        ["lake", "env", "lean", "--run", "tools/ExplicitnessClosure.lean"],
        cwd=ROOT, capture_output=True, text=True,
    )
    sys.stdout.write(proc.stdout)
    sys.stderr.write(proc.stderr)
    if proc.returncode != 0:
        print("[audit] FAIL: explicitness closure walk failed (see output above)")
        return False
    m = re.search(r"CLOSURE_SIZE=(\d+)", proc.stdout)
    if not m or int(m.group(1)) == 0:
        print("[audit] FAIL: closure walk reported no walked closure (size 0 or missing) — "
              "a walk that visits nothing passes vacuously; refusing.")
        return False
    return True


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--complete", action="store_true",
                    help="done-gate: require the full manifest + explicitness closure")
    args = ap.parse_args()

    texts = {f: load(f) for f in {e[0] for e in MANIFEST}}
    status: list[tuple[bool, str, list[str]]] = []
    for file, decls, _ in MANIFEST:
        missing = [d for d in decls if not decl_present(texts[file], d)]
        status.append((not missing, file, missing if missing else decls))

    ok = True
    first_missing_idx = next((i for i, s in enumerate(status) if not s[0]), None)

    # Regression check: nothing after the frontier may be present out of order,
    # and everything before it must stay present (both are caught by the same scan).
    if first_missing_idx is not None:
        for i in range(first_missing_idx + 1, len(MANIFEST)):
            if status[i][0]:
                print(f"[audit] FAIL: manifest entry {i} ({', '.join(MANIFEST[i][1])}) is present "
                      f"but earlier entry {first_missing_idx} "
                      f"({', '.join(status[first_missing_idx][2])}) is missing — out-of-order/regression.")
                ok = False

    # Delegation-direction check on every completed _atCX.
    for i, (file, _decls, pair) in enumerate(MANIFEST):
        if pair is None or not status[i][0]:
            continue
        atcx_name, atc_name = pair
        body = decl_body(texts[file], atcx_name)
        if body is None:
            continue
        # Occurrences of the _atC name NOT as a prefix of _atCX.
        if re.search(rf"\b{re.escape(atc_name)}\b(?!X)", body.split("\n", 1)[1] if "\n" in body else ""):
            print(f"[audit] FAIL: {atcx_name} ({file}) references its existential sibling "
                  f"{atc_name} — the delegate must run _atC := ⟨X_*, _atCX⟩, never the reverse.")
            ok = False

    done = sum(1 for s in status if s[0])
    print(f"[audit] manifest: {done}/{len(MANIFEST)} entries complete")
    if first_missing_idx is not None:
        file, decls, _ = MANIFEST[first_missing_idx]
        print(f"[audit] NEXT TARGET (entry {first_missing_idx}, {file}): "
              f"{', '.join(status[first_missing_idx][2])}")
    else:
        print("[audit] manifest complete — run with --complete for the done-gate")

    if args.complete:
        if first_missing_idx is not None:
            print("[audit] FAIL (--complete): manifest incomplete")
            ok = False
        elif not run_closure_walk():
            ok = False
        else:
            print("[audit] --complete: manifest full + explicitness closure clean ✅")

    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
