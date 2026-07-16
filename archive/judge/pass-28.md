# Judge pass 28 — 2026-07-14 (ruling on the Cor-6.3 `JUDGE-FLAG`; treadmill STILL RUNNING)

**Scope**: a **ruling pass**, not a boundary pass. The overnight run raised a `JUDGE-FLAG` asking
the judge to ratify a deviation from the paper's Corollary 6.3 window (6.8). No new axiom runs
(pass 27's pin still stands as the last full boundary); this pass reads the laps' reasoning, the
proved artifact, and the numbers — and rules.

## Verdict in one line

✅ **The tight-window deviation is RATIFIED** — it is a *restriction*, hence a strictly weaker
lemma, hence sound, and Prop 1.14's statement is untouched. 🚨 **But the forward plan built on it
is broken in two places, and the next lap was being ordered to prove something impossible.**

## 1. What was asked

The deep-reflection lap found that Tao's Cor 6.3 hypothesizes `l` in the window (6.8),
`l ≤ n·log₂3 − ½·C_A²·log n`, and claimed that window is **too lossy** to run the (6.14)→(6.15)
geometric estimate — so the Lean analogue would instead carry the **tight** window
`l ≤ n·log₂3 − (C_A²−2C_A)·log n − O(1)`, which the paper's own event stack (`Bₖ` stopping rule +
the one-step `Eₖ` bound `a_{k+1} ≤ 2 + 2C_A log n`) actually supplies at the only call site.
Filed as source hole #3; "judge to ratify."

## 2. Ruling: RATIFY — and it is not a pass-26-class event

The two must not be confused, so state the difference plainly:

|  | pass 26 (X10) | pass 28 (Cor 6.3) |
|---|---|---|
| what moved | a **ratified paper pin** — the deliverable itself | an **internal proof lemma**, never a pin |
| direction | hypothesis *swapped* for an **incomparable** one | hypothesis **restricted** (our window ⊂ paper's) |
| effect on the lemma | neither stronger nor weaker — *a different theorem* | strictly **weaker** — cannot introduce unsoundness |
| effect on the headline | X10 stopped formalizing Lemma 7.10 | **Prop 1.14's statement is byte-identical** (differ-verified) |
| verdict | REVOKE | **RATIFY** |

A restriction can only cost you *sufficiency*, never *soundness*. So the risk here is not "we
proved something false" — it is "we proved something too weak to use." That risk lives entirely
at the call site, in `hbudget`. Which is where I looked.

**Note also**: our correctness does **not** depend on hole #3 being real. Tightening a window is
sound whether or not the wider one is false. The hole claim matters for the *fidelity ledger*, not
for the proof — a useful decoupling, and it is why this ruling did not need the PDF.

## 3. 🚨 The finding: the plan's numbers and the proof's numbers disagree

`fnat_lt_of_suffix_window` — the kernel that was **actually proved, axiom-clean** — takes
`hbudget` as a *hypothesis*, and (per its own docstring) runs AM-GM at **ε = 1/5**:

> cost `= C·ln2 + (5/4)·(C·ln2)² ≈ 0.601·C² + 0.693·C` per `ln n`.

Judge-recomputed independently (`tools/sandbox/tao_hbudget_check.py`):

| window | budget per `ln n` | discharges `hbudget`? |
|---|---|---|
| (6.8) paper ½-window | `0.347·C²` | ❌ **NEVER, for any `C`** — `budget − cost` has a **negative** `C²` coefficient (`0.347 − 0.601 = −0.254`) |
| tight (`Bₖ` + one-step `Eₖ`) | `0.693·C² − 1.386·C` | ✅ **iff `C > 22.46` ⟹ `C ≥ 23`** |

**Two errors follow, both in the live steering channel:**

1. **`DIRECTION.md` (review lap, 1800 handoff) ordered the next lap to "discharge `hbudget` from
   the (6.8) l-range."** That is impossible — and it is the *exact window the reflection had just
   refuted*. The review lap regressed to the paper's window, silently undoing its own reflection's
   correction. A grind lap reads DIRECTION *before* the handoff, so this would have been the
   binding instruction.
2. **`C_A ≥ 10` is wrong; the true threshold is `C_A ≥ 23`.** The `≥ 10` figure came from a
   *pre-proof* estimate at **ε = 1/4** (cost `0.481·C²`). The lemma that actually landed uses
   **ε = 1/5**. At `C = 10` the proved cost is `66.99` against a tight budget of `55.45` — **it
   fails.** The stale `≥ 10` propagated into `DIRECTION.md`, the reflection block, *and*
   `papers/literature-review.md`; the **correct** number was sitting in the docstring of the proved
   lemma the whole time (`C ≳ 23`).

📌 **The lesson, and it is pass 27's lesson pointed the other way.** Pass 27 learned *a
judge-supplied numeral is a hypothesis too* (my `10^27` was wrong; the box's `10^30` carried the
proof). Pass 28 is the mirror image: **a worker-supplied numeral is a hypothesis too, and when two
of them disagree, the one bolted to the machine-checked artifact wins.** The docstring of a proved
lemma outranks every prose estimate that preceded it — including the estimate that *motivated* it.

## 4. Why this mattered

Nothing was unsound, and nothing was going to *become* unsound on its own. The danger was
second-order and it is the one this whole apparatus exists to catch: **a lap grinding at an
impossible target is a lap under pressure.** `hbudget` cannot be discharged from (6.8) at `C = 10`
— not with more effort, not with a cleverer route. A worker that cannot close a hypothesis it has
been *ordered* to close, with a green build and clean axioms in every other direction, is exactly
the worker that starts looking at what else it could adjust. The rails would probably have held
(HARD RAIL 6 is armed, the watch list now covers both crux statements, and the box has visibly
internalized both). But the cheapest place to stop that is before it starts.

## 5. Actions taken

- ✅ **Ratified** the tight-window deviation; fidelity-ledger row updated from "JUDGE-FLAG pending"
  to RATIFIED, with the tripwire attached.
- 🚨 **`DIRECTION.md`**: new binding "JUDGE PASS 28 — CORRECTION" block. Discharge `hbudget` from
  the **tight** window, never (6.8); **`C_A ≥ 23`**, never 10; if a bigger constant proves
  inconvenient, **re-prove the kernel at ε = 1/4** (cost `0.481·C²`, threshold back to `≳ 10`) —
  that is a strengthening of an unwatched internal lemma and is allowed.
- 🔧 **`papers/literature-review.md`**: corrected the stale ε=1/4 / `C_A ≥ 10` numbers, and
  **strengthened hole #3** — (6.8) does not merely lose at small `C_A`; its `C_A²` coefficient is
  negative, so **no `C_A` rescues it**. The sign is wrong, not the size.
- 🧮 **`tools/sandbox/tao_hbudget_check.py`** — the judge's independent recomputation. Cheap to
  re-run whenever a constant moves.

## 6. Tripwire armed 🔔

**`hbudget` is now the campaign's single load-bearing undischarged number** — the one place C10
runs on critical constants. Pass 29 must check:

1. **Was `hbudget` discharged from the tight window at `C_A ≥ 23`?** Read the discharge, do not
   just check its axioms — a green proof of `hbudget` from a *mis-stated* event bound is precisely
   the shape of failure that survives every other instrument.
2. ⚠️ **Does `C_A = 23` still absorb downstream?** The larger constant worsens the single-point
   mass to `n^{O(C_A²)}·3^{-n}`. The lit review says this is "absorbed by taking `A′` large exactly
   as the paper does" — **that is an assertion, not a proof.** Make the lap *show* it at `C_A = 23`.
   If it does not absorb, the right response is a `JUDGE-FLAG:`, **not** shaving `C_A` back toward
   10 and **not** touching the window.
3. Hole #3's extremal tuple against the PDF (pp.31–33). **Not load-bearing** (our soundness does
   not depend on it) — but a wrong claim in the fidelity ledger is its own defect, and this one is
   headed for `formalization-literature-holes.md`. Document in-repo; **never announce.**

---
*Judge passes 1–23 by Ren/Fable; 24–28 by Ren/Opus. Pass 28 is a ruling pass — no new axiom runs;
pass 27's pin (`8505bd4`) remains the last full boundary. Next boundary pass: 29.*
