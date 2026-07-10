import TaoCollatz.Syracuse.SyracRV
import Mathlib.Algebra.Order.Round
import Mathlib.Data.ZMod.Basic

/-!
# §7.1 setup: character phase `θ`, black/white points (nodes X1–X2)

Paper anchors: Tao 2019 §7.1, (7.7), (7.8), (7.9), (7.13), (7.14).

* `sfrac` — signed fractional part into `(-1/2, 1/2]`.
* `u2 n` — the unit `2 ∈ (ZMod (3ⁿ))ˣ`.
* `θq` — the phase `θ(j,l)` (7.8).
* `θq_succ_j`, `θq_pred_l` — the recursions (7.13)/(7.14), **proved** from ZMod arithmetic.
* `black`/`white` — the (7.9) dichotomy with `ε := 1/10⁴`.

-- RATIFY-4: `j : ℕ` with paper `j = j_lean + 1`, so the paper exponent `2j-2` becomes
-- `2*j` (a genuine ℕ exponent; `3` need not be a unit). `l : ℤ` carried by the unit `u2`.
-/

namespace TaoCollatz

/-- Signed fractional part `q - round q`, valued in `[-1/2, 1/2)` (mathlib `round` is
half-UP). The paper's `{·}` lands in `(-1/2, 1/2]` instead; the two conventions differ
only at exact half-integers, which the phases here never attain (their denominators are
odd powers of 3, so `θ ≡ 1/2 (mod 1)` is impossible) — ratified, 2026-07-09 judge pass. -/
def sfrac (q : ℚ) : ℚ := q - round q

/-- The unit `2 ∈ (ZMod (3ⁿ))ˣ` (2 is coprime to `3ⁿ`). -/
noncomputable def u2 (n : ℕ) : (ZMod (3 ^ n))ˣ :=
  ZMod.unitOfCoprime 2 (Nat.Coprime.pow_right n (by decide))

/-- The phase `θ(j,l)` (paper (7.8)), signed fractional part of
`ξ · (3^{2j} · 2^{1-l}) / 3ⁿ` reduced mod `3ⁿ`. -/
noncomputable def θq (n ξ : ℕ) (j : ℕ) (l : ℤ) : ℚ :=
  sfrac ((ξ * ((3 : ZMod (3 ^ n)) ^ (2 * j)
      * (↑((u2 n) ^ (1 - l)) : ZMod (3 ^ n))).val : ℚ) / 3 ^ n)

/-- `round` is invariant under `sfrac` up to integer scaling: if `y = c·x + m`
(`m ∈ ℤ`) then `sfrac y = c · sfrac x + k` for an integer `k`. -/
theorem sfrac_scale_of (c : ℤ) (x y : ℚ) (m : ℤ) (h : y = c * x + m) :
    ∃ k : ℤ, sfrac y = c * sfrac x + k := by
  refine ⟨c * round x - round ((c : ℚ) * x), ?_⟩
  unfold sfrac
  rw [h, round_add_intCast]
  push_cast
  ring

/-- Bridge: if `W' = c · W` in `ZMod (3ⁿ)`, then the phase-arguments satisfy
`arg(W') = c · arg(W) + integer`. -/
theorem argRel (n ξ : ℕ) (c : ℤ) (W W' : ZMod (3 ^ n)) (hWW' : W' = (c : ZMod (3 ^ n)) * W) :
    ∃ m : ℤ, ((ξ * W'.val : ℚ) / 3 ^ n) = c * ((ξ * W.val : ℚ) / 3 ^ n) + m := by
  haveI : NeZero (3 ^ n) := ⟨pow_ne_zero n (by norm_num)⟩
  have hdvd : ((3 : ℤ) ^ n) ∣ (c * (W.val : ℤ) - (W'.val : ℤ)) := by
    have hz : (((c * (W.val : ℤ) - (W'.val : ℤ)) : ℤ) : ZMod (3 ^ n)) = 0 := by
      push_cast
      rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, hWW']
      ring
    have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd _ (3 ^ n)).mp hz
    exact_mod_cast hd
  obtain ⟨t, ht⟩ := hdvd
  refine ⟨-(ξ * t), ?_⟩
  have h3 : (3 : ℚ) ^ n ≠ 0 := by positivity
  have hval : (W'.val : ℚ) = c * (W.val : ℚ) - 3 ^ n * t := by
    have hz2 : (W'.val : ℤ) = c * (W.val : ℤ) - 3 ^ n * t := by linarith [ht]
    exact_mod_cast hz2
  rw [hval]; field_simp; push_cast; ring

/-- Paper (7.13): the phase satisfies `θ(j+1,l) = 9·θ(j,l) + integer`. -/
theorem θq_succ_j (n ξ : ℕ) (j : ℕ) (l : ℤ) :
    ∃ k : ℤ, θq n ξ (j + 1) l = 9 * θq n ξ j l + k := by
  obtain ⟨m, hm⟩ := argRel n ξ 9
    ((3 : ZMod (3 ^ n)) ^ (2 * j) * (↑((u2 n) ^ (1 - l)) : ZMod (3 ^ n)))
    ((3 : ZMod (3 ^ n)) ^ (2 * (j + 1)) * (↑((u2 n) ^ (1 - l)) : ZMod (3 ^ n)))
    (by rw [show 2 * (j + 1) = 2 * j + 2 from by ring, pow_add]; push_cast; ring)
  obtain ⟨k, hk⟩ := sfrac_scale_of 9 _ _ m hm
  exact ⟨k, by simpa only [θq, Int.cast_ofNat] using hk⟩

/-- Paper (7.14): the phase satisfies `θ(j,l-1) = 2·θ(j,l) + integer`. -/
theorem θq_pred_l (n ξ : ℕ) (j : ℕ) (l : ℤ) :
    ∃ k : ℤ, θq n ξ j (l - 1) = 2 * θq n ξ j l + k := by
  have hu2 : (↑(u2 n) : ZMod (3 ^ n)) = 2 := by
    rw [u2, ZMod.coe_unitOfCoprime]; norm_num
  obtain ⟨m, hm⟩ := argRel n ξ 2
    ((3 : ZMod (3 ^ n)) ^ (2 * j) * (↑((u2 n) ^ (1 - l)) : ZMod (3 ^ n)))
    ((3 : ZMod (3 ^ n)) ^ (2 * j) * (↑((u2 n) ^ (1 - (l - 1))) : ZMod (3 ^ n)))
    (by
      rw [show (1 : ℤ) - (l - 1) = (1 - l) + 1 from by ring, zpow_add_one, Units.val_mul, hu2]
      push_cast; ring)
  obtain ⟨k, hk⟩ := sfrac_scale_of 2 _ _ m hm
  exact ⟨k, by simpa only [θq, Int.cast_ofNat] using hk⟩

/-- The §7 small constant `ε = 1/10⁴` (D4 candidate). -/
def epsBW : ℚ := 1 / 10 ^ 4

/-- A point `(j,l)` is *black* (7.9) if its phase is within `ε` of an integer. -/
def black (n ξ : ℕ) (j : ℕ) (l : ℤ) : Prop := |θq n ξ j l| ≤ epsBW

/-- A point `(j,l)` is *white* (7.9) if it is not black. -/
def white (n ξ : ℕ) (j : ℕ) (l : ℤ) : Prop := ¬ black n ξ j l

end TaoCollatz
