import TaoCollatz.Basic.Collatz
import TaoCollatz.Basic.LogDensity

/-!
# Non-vacuity anchors (comparator witnesses)

Small, fully-proved facts pinning the *semantics* of the trusted-base definitions
(`col`, `colMin`, `logProb`, `AlmostAllPos`) against exact finite
instances — the Lean-side companions of the D8 numeric statement traps in
`tools/check_blueprint.py`. They exist so the comparator challenge
(`Comparator/TaoCollatz/Challenge.lean`) can certify statements that are proved
*today*: CI machine-checks that the Mathlib-only rendering of every definition in
the headline statements is byte-identical to the development's, without waiting
for the headline theorems themselves.

Why these particular anchors:

* `colMin_twentyseven` — the famous 27 orbit really reaches 1 (111 Collatz steps,
  peak 9232) and `colMin` really is the orbit minimum. Kernel reduction only
  (`decide`), never `native_decide`.
* `colMin_zero` — `colMin` is not constantly 1.
* `almostAllPos_true` / `not_almostAllPos_false` — the density machinery can
  *distinguish*: the trivial property has log density 1, the empty one does not.
  A degenerate rendering (e.g. an error term fixed to 0) fails exactly this pair.
* `logProb_odd_window_two` — pins the `1/N` *weights*: on the window `{1, 2}` the
  odd numbers carry mass `2/3`. A natural-density impostor would say `1/2`, so
  this separates logarithmic from natural density — the distinction Theorem 1.3
  lives on (Tao 2019 proves log density; natural density is explicitly open, p.3).
-/

namespace TaoCollatz

open Filter Topology

/-- The orbit of `0` is `{0}`, so `colMin 0 = 0` — `colMin` is not constantly `1`. -/
theorem colMin_zero : colMin 0 = 0 :=
  Nat.le_antisymm (Nat.sInf_le ⟨0, rfl⟩) (Nat.zero_le _)

/-- The famous orbit: `27` reaches `1` (in 111 Collatz steps, peaking at 9232), and
`1` really is the minimum of its orbit. Discharged by kernel reduction. -/
theorem colMin_twentyseven : colMin 27 = 1 := by
  -- `decide +kernel`: the 111-step evaluation exceeds the elaborator's recursion
  -- depth, but the kernel reduces it directly (and adds no axioms).
  have hmem : (1 : ℕ) ∈ Set.range fun k => col^[k] 27 := ⟨111, by decide +kernel⟩
  refine Nat.le_antisymm (Nat.sInf_le hmem) ?_
  obtain ⟨k, hk⟩ := Nat.sInf_mem (⟨1, hmem⟩ : (Set.range fun k => col^[k] 27).Nonempty)
  exact (col_iterate_pos (by norm_num) k).trans_eq hk

/-- Any window containing `1` has positive total log-mass. -/
theorem logSum_univ_pos {x : ℕ} (hx : 1 ≤ x) : 0 < logSum Set.univ (Finset.Icc 1 x) := by
  unfold logSum
  refine Finset.sum_pos' (fun i _ => by positivity) ⟨1, ?_, by norm_num⟩
  simp only [Finset.mem_filter, Set.mem_univ, and_true, Finset.mem_Icc]
  omega

/-- The trivial property holds for almost all `N`: the log-density machinery is not
vacuously strict. -/
theorem almostAllPos_true : AlmostAllPos fun _ => True := by
  unfold AlmostAllPos HasLogDensity
  have h : ∀ x : ℕ, 1 ≤ x → logProb {N : ℕ | True} (Finset.Icc 1 x) = 1 := by
    intro x hx
    unfold logProb
    rw [Set.setOf_true, div_self (logSum_univ_pos hx).ne']
  exact Tendsto.congr' (eventually_atTop.mpr ⟨1, fun x hx => (h x hx).symm⟩) tendsto_const_nhds

/-- The empty property does *not* hold almost everywhere: log density distinguishes.
Together with `almostAllPos_true` this rules out a degenerate reading of
`AlmostAllPos` (one that every property, or none, would satisfy). -/
theorem not_almostAllPos_false : ¬ AlmostAllPos fun _ => False := by
  intro h
  unfold AlmostAllPos HasLogDensity at h
  have h0 : ∀ x : ℕ, logProb {N : ℕ | False} (Finset.Icc 1 x) = 0 := by
    intro x
    unfold logProb logSum
    rw [Finset.sum_filter]
    simp
  rw [tendsto_congr h0] at h
  exact zero_ne_one (tendsto_nhds_unique tendsto_const_nhds h)

/-- The `1/N` weights, pinned on an exact instance: on the window `{1, 2}` the odd
numbers carry log-mass `(1/1) / (1/1 + 1/2) = 2/3`. A natural-density impostor
would give `1/2`, so this anchor separates logarithmic from natural density. -/
theorem logProb_odd_window_two : logProb {N : ℕ | N % 2 = 1} (Finset.Icc 1 2) = 2 / 3 := by
  have hwin : Finset.Icc 1 2 = ({1, 2} : Finset ℕ) := by decide
  unfold logProb logSum
  rw [hwin, Finset.sum_filter, Finset.sum_filter,
    Finset.sum_insert (by decide : (1 : ℕ) ∉ ({2} : Finset ℕ)), Finset.sum_singleton,
    Finset.sum_insert (by decide : (1 : ℕ) ∉ ({2} : Finset ℕ)), Finset.sum_singleton]
  norm_num [Set.mem_setOf_eq]

end TaoCollatz
