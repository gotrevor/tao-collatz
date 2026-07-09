# Skeleton spec — exact Lean statements for the Phase-A skeleton

Companion to `BLUEPRINT.md` (read that first, esp. §0 design decisions D1–D8).
This file fixes the **ratified statement shapes**. Implementer: create the files, make
`lake build` green (sorries allowed, NO axioms/native_decide), commit. Where this spec
gives a statement, keep its mathematical content **verbatim**; renaming/namespacing OK.
Paper anchors refer to arXiv:1909.03562v5 (`papers/` PDF).

Conventions: 0-indexed tuples `a : Fin n → ℕ` (paper index i = Lean index i-1).
`pre a m := ∑ i ∈ Finset.range m, if h : i < n then a ⟨i,h⟩ else 0` (prefix sum, paper `a_{[1,m]}`).
All probabilities: `PMF`, expectations via `tsum` (D1). Numbers: probabilities/expectations in `ℝ`
(`(p a).toReal`), characters in `ℂ`, θ in `ℚ`, triangle geometry in `ℝ`.

## 1. `TaoCollatz/Basic/Collatz.lean` (node C1)

```lean
def col (N : ℕ) : ℕ := if N % 2 = 1 then 3 * N + 1 else N / 2
noncomputable def colMin (N : ℕ) : ℕ := sInf (Set.range fun k => col^[k] N)
def oddPart (N : ℕ) : ℕ := N / 2 ^ (padicValNat 2 N)
def syr (N : ℕ) : ℕ := oddPart (3 * N + 1)
noncomputable def syrMin (N : ℕ) : ℕ := sInf (Set.range fun k => syr^[k] N)
```
Prove now (cheap): `syr_odd : N % 2 = 1 → syr N % 2 = 1`; `oddPart_odd`, `oddPart_pos`,
`syr_pos : 0 < N → 0 < syr N`, `2 ^ padicValNat 2 (3*N+1) * syr N = 3*N+1` for odd N.
State w/ sorry: `colMin_eq_syrMin_oddPart : 0 < N → colMin N = syrMin (oddPart N)` (paper (1.2)).

## 2. `TaoCollatz/Basic/LogDensity.lean` (node C3)

Port from `~/src/collatz-cryptid/lean/Collatz/LogDensity.lean` (v4.29→v4.31, expect ~0 fixes):
`logSum`, `logProb`, `posInterval`, `HasLogDensity`, `AlmostAllPos` — keep names/shapes.
Add the odd-window forms (paper §1.2, "almost all N ∈ 2ℕ+1"):
```lean
noncomputable def oddInterval (x : ℕ) : Finset ℕ := (Finset.range (x+1)).filter (fun N => N % 2 = 1)
def AlmostAllOdd (P : ℕ → Prop) : Prop :=
  Filter.Tendsto (fun x => logProb {N | P N} (oddInterval x)) Filter.atTop (nhds 1)
```

## 3. `TaoCollatz/Basic/Valuation.lean` (node C2)

```lean
def valVec (N n : ℕ) : Fin n → ℕ := fun i => padicValNat 2 (3 * syr^[(i:ℕ)] N + 1)  -- (1.8)
def fnat (n : ℕ) (a : Fin n → ℕ) : ℕ := ∑ m ∈ Finset.range n, 3 ^ (n - 1 - m) * 2 ^ pre a m  -- D2
```
**Prove now (load-bearing, node C2's heart, paper (1.7) × 2^|a|):**
```lean
theorem syr_iterate_key (N n : ℕ) (hN : N % 2 = 1) :
    2 ^ pre (valVec N n) n * syr^[n] N = 3 ^ n * N + fnat n (valVec N n)
```
(Induction on n; the step is `2^{a_{n+1}} * syr (syr^[n] N) = 3 * syr^[n] N + 1` from Collatz.lean.
Numerically validated: `tools/check_blueprint.py` check 1.)
Also state w/ sorry, Lemma 2.1 (uniqueness): if `2 ^ pre a n * M = 3 ^ n * N + fnat n a` with
`M` odd and every prefix-step odd condition — formalize as: valVec is the UNIQUE `a : Fin n → ℕ`
with all `a i ≥ 1` such that `3 ^ n * N + fnat n a ≡ 0 [MOD 2 ^ pre a n]` and quotient odd.
(Take care; if the clean uniqueness shape fights you, state the paper's version: for odd N,
`(Aff_a(N) ∈ 2ℕ+1) ↔ a = valVec N n`, where `Aff_a(N) := (3^n*N + fnat n a) / 2^(pre a n)`
guarded by the divisibility. Mark `-- RATIFY-2` for judge review.)

## 4. `TaoCollatz/Prob/Basic.lean` (node S1)

```lean
noncomputable def PMF.dTV {α : Type*} (p q : PMF α) : ℝ := ∑' a, |(p a).toReal - (q a).toReal|
noncomputable def PMF.expect {α : Type*} (p : PMF α) (f : α → ℝ) : ℝ := ∑' a, (p a).toReal * f a
noncomputable def PMF.cexpect {α : Type*} (p : PMF α) (f : α → ℂ) : ℂ := ∑' a, (p a).toReal * f a
noncomputable def PMF.iid {α : Type*} (p : PMF α) : (n : ℕ) → PMF (Fin n → α)
  | 0 => PMF.pure (fun i => i.elim0)
  | n + 1 => p.bind fun a => (PMF.iid p n).map (Fin.cons a)
```
Prove now (cheap): `PMF.dTV_comm`, `dTV_nonneg`; `iid` support/apply lemmas as needed later.
State w/ sorry (paper (1.10)): for any `E : Set α`,
`|p.toOuterMeasure E - q.toOuterMeasure E| ≤ ...` — OR the cleaner event form via indicator
expectations: `|p.expect (Set.indicator E 1) - q.expect (Set.indicator E 1)| ≤ p.dTV q`.
Use the expect-of-indicator form everywhere (avoids OuterMeasure friction).

## 5. `TaoCollatz/Prob/Geometric.lean` (node S2)

```lean
noncomputable def geomHalf : PMF ℕ := ⟨fun a => if a = 0 then 0 else 2⁻¹ ^ a, _⟩   -- P(a)=2^{-a}, a ≥ 1  ("Geom(2)")
noncomputable def geomQuarter : PMF ℕ := ⟨fun a => if a = 0 then 0 else 4⁻¹ * (3 * 4⁻¹) ^ (a - 1), _⟩  -- "Geom(4)"
noncomputable def pascal : PMF ℕ := ⟨fun b => if b < 2 then 0 else (b - 1) * 2⁻¹ ^ b, _⟩  -- a₁+a₂, b ≥ 2
noncomputable def pascalNe3 : PMF ℕ := ⟨fun b => if b < 2 ∨ b = 3 then 0 else (4/3) * ((b - 1) * 2⁻¹ ^ b), _⟩
```
(ENNReal literals; the `_` are `HasSum`/tsum=1 proofs — prove via `ENNReal.tsum_geometric` +
shift lemmas; these four normalization proofs are real work but standard. If one stalls,
sorry it and move on.)
State w/ sorry: `pascal = geomHalf.iid 2 |>.map (fun v => v 0 + v 1)` (definitional bridge);
negative binomial `((geomHalf.iid n).map fun v => ∑ i, v i) L = (L-1).choose (n-1) * 2⁻¹^L` for `L n ≥ 1`.

## 6. `TaoCollatz/Syracuse/SyracRV.lean` (node C4)

```lean
noncomputable def syracZ (n : ℕ) : PMF (ZMod (3 ^ n)) :=
  (geomHalf.iid n).map fun a => ∑ j ∈ Finset.range n, (3 : ZMod (3 ^ n)) ^ j * (2 : ZMod (3 ^ n))⁻¹ ^ pre a (j + 1)
```
This is the paper's (1.26) REVERSED form — deliberately (footnote 6); numerically validated
(harness check 3, both forms agree in law). State w/ sorry:
- `syracZ_map_cast (k ≤ n) : (syracZ n).map (ZMod.castHom (pow_dvd_pow 3 hkn) _) = syracZ k`  -- (1.22)
- Lemma 1.12 recursion (finite sum over `a ∈ Finset.Icc 1 (2*3^n)` with the `(1 - 2^{-2·3^n})⁻¹`
  normalization; validated harness check 5).
- The (1.21) bridge: `syracZ n = (geomHalf.iid n).map (fun a => (fnat n a : ZMod (3^n)) * (2 : ZMod (3^n))⁻¹ ^ pre a n)`.

## 7. `TaoCollatz/Syracuse/ValuationDist.lean` (node C5) — statements only

```lean
noncomputable def unifOddMod (n' : ℕ) : PMF (ZMod (2 ^ n')) :=
  PMF.uniformOfFinset (Finset.univ.filter fun z : ZMod (2 ^ n') => z.val % 2 = 1) (by ...)
theorem valuation_dist (c₀ K : ℝ) (hc₀ : 0 < c₀) (hK : 0 < K) :
    ∃ c₁ C : ℝ, 0 < c₁ ∧ 0 < C ∧ ∀ (n n' : ℕ) (X : PMF ℕ),
      (2 + c₀) * n ≤ (n' : ℝ) →
      (∀ N ∈ X.support, N % 2 = 1) →
      PMF.dTV (X.map fun N => (N : ZMod (2 ^ n'))) (unifOddMod n') ≤ K * 2 ^ (-(n' : ℝ)) →
      PMF.dTV (X.map fun N => valVec N n) (geomHalf.iid n) ≤ C * 2 ^ (-c₁ * n) := sorry  -- Prop 1.9
```
Plus Lemma 4.1 tail-bound statement (same hypotheses):
`(X.map fun N => pre (valVec N n) n).expect (indicator {L | n' ≤ L} 1) ≤ C * 2 ^ (-c * n)`.

## 8. `TaoCollatz/Sec5/FirstPassage.lean` (nodes C7/C8 defs)

```lean
def passes (x N : ℕ) : Prop := ∃ n, syr^[n] N ≤ x     -- T_x(N) < ∞
noncomputable def passTime (x N : ℕ) : ℕ := sInf {n | syr^[n] N ≤ x}
noncomputable def passLoc (x N : ℕ) : ℕ := if passes x N then syr^[passTime x N] N else 1  -- Pass_x, Syr^∞ := 1 convention
noncomputable def logWindow (lo hi : ℝ) : Finset ℕ :=
  (Finset.range (Nat.ceil hi + 1)).filter fun N => N % 2 = 1 ∧ lo ≤ (N : ℝ) ∧ (N : ℝ) ≤ hi
noncomputable def logUnifOdd (lo hi : ℝ) : PMF ℕ := ... -- log-uniform on logWindow: mass ∝ 1/N; guard nonempty via junk/pure 1
def alpha : ℝ := 1.001   -- (1.18)
theorem stabilization :   -- Prop 1.11; the SPINE's key input
    ∃ c C x₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : ℝ, x₀ ≤ x →
      (∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ),
        (logUnifOdd y (y ^ alpha)).expect (Set.indicator {N | ¬ passes ⌊x⌋₊ N} 1) ≤ C * x ^ (-c)) ∧
      PMF.dTV ((logUnifOdd (x ^ alpha) (x ^ alpha ^ alpha)).map (passLoc ⌊x⌋₊))
              ((logUnifOdd (x ^ alpha ^ 2) (x ^ (alpha ^ 2) ^ alpha)).map (passLoc ⌊x⌋₊))
        ≤ C * (Real.log x) ^ (-c) := sorry
```
⚠️ Window endpoints: `N_y ≡ Log(2ℕ+1 ∩ [y, y^α])` with y = x^α resp. x^{α²}; so windows are
`[x^α, x^{α²}]` and `[x^{α²}, x^{α³}]`. Write them as such (`x ^ alpha, x ^ (alpha^2)` etc.) —
the nested-pow spelling above is error-prone; mark `-- RATIFY-3` for judge pass.

## 9. `TaoCollatz/Fourier/ZMod3.lean` + statements of Props 1.14/1.17 (`Sec6/`, `Sec7/Decay.lean`)

```lean
noncomputable def eC (q : ℚ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * (q : ℂ))   -- e(θ)
noncomputable def osc (m n : ℕ) (c : ZMod (3 ^ n) → ℝ) : ℝ :=   -- (1.24)
  ∑ Y : ZMod (3 ^ n), |c Y - (3 : ℝ) ^ (((m : ℤ)) - n) *
      ∑ Y' ∈ Finset.univ.filter (fun Y' : ZMod (3 ^ n) =>
        ZMod.castHom (pow_dvd_pow 3 hmn) (ZMod (3 ^ m)) Y' = ZMod.castHom _ _ Y), c Y'|
theorem fine_scale_mixing (A : ℝ) (hA : 0 < A) :   -- Prop 1.14
    ∃ C > 0, ∀ n m : ℕ, 1 ≤ m → m ≤ n →
      osc m n (fun Y => ((syracZ n) Y).toReal) ≤ C * (m : ℝ) ^ (-A) := sorry
theorem charFn_decay (A : ℝ) (hA : 0 < A) :   -- Prop 1.17 — THE CRUX STATEMENT
    ∃ C > 0, ∀ n : ℕ, 1 ≤ n → ∀ ξ : ZMod (3 ^ n), ¬ (3 ∣ ξ.val) →
      ‖(syracZ n).cexpect fun Y => eC (-(ξ.val * Y.val : ℚ) / 3 ^ n)‖ ≤ C * (n : ℝ) ^ (-A) := sorry
```
(`osc` needs `hmn : m ≤ n` as hypothesis-argument or `min`-guard; implementer's choice, mark RATIFY.)

## 10. `TaoCollatz/Sec7/Setup.lean`, `White.lean`, `Triangles.lean` (nodes X1–X3)

```lean
-- θ (7.7)/(7.8), paper-indexed j ≥ 1, l ∈ ℤ. u2 n : (ZMod (3^n))ˣ := 2.
def sfrac (q : ℚ) : ℚ := q - round q          -- signed frac; paper wants (-1/2,1/2]; for our θ
                                              -- denominators are odd ⇒ |sfrac| < 1/2 strictly; note & move on
noncomputable def θq (n ξ : ℕ) (j l : ℤ) : ℚ :=
  sfrac ((ξ * ((3 : ZMod (3 ^ n)) ^ (2 * j - 2) * ((u2 n) ^ (1 - l) : (ZMod (3 ^ n))ˣ)).val : ℚ) / 3 ^ n)
```
⚠️ `(3 : ZMod (3^n)) ^ (2*j - 2)` with j : ℤ — 3 is NOT a unit; but 2j-2 ≥ 0 in all uses (j ≥ 1).
Make j : ℕ with paper j = Lean j + 1 (so exponent 2*j : ℕ), l : ℤ via the unit u2. RATIFY-4.
**Prove now (de-risk, from ZMod arithmetic):** the identities (7.13)/(7.14) as
```lean
theorem θq_succ_j : ∃ k : ℤ, θq n ξ (j+1) l = 9 * θq n ξ j l + k
theorem θq_pred_l : ∃ k : ℤ, θq n ξ j (l-1) = 2 * θq n ξ j l + k
```
Black/white (7.9), ε := (1/10^4 : ℚ) (D4 candidate — keep as a named constant `epsBW`):
`def black (n ξ : ℕ) (j : ℕ) (l : ℤ) : Prop := |θq n ξ j l| ≤ epsBW` ; white := ¬black; plus strip guard j+1 ∈ [1, ⌊n/2⌋] (paper j ∈ [n/2]).
Triangle (7.11) over ℝ; Lemma 7.4 statement w/ sorry:
```lean
def triangle (j₀ : ℕ) (l₀ : ℤ) (s : ℝ) : Set (ℕ × ℤ) :=
  {p | j₀ ≤ p.1 ∧ p.2 ≤ l₀ ∧ ((p.1 : ℝ) - j₀) * Real.log 9 + ((l₀ : ℝ) - p.2) * Real.log 2 ≤ s}
theorem black_structure (n ξ : ℕ) (hξ : ¬ 3 ∣ ξ) (hn : 1 ≤ n) :   -- Lemma 7.4
    ∃ T : Set (ℕ × ℤ × ℝ), (∀ t ∈ T, 0 ≤ t.2.2) ∧
      {p : ℕ × ℤ | p.1 + 1 ≤ n / 2 ∧ black n ξ p.1 p.2} = ⋃ t ∈ T, triangle t.1 t.2.1 t.2.2 ∧
      (pairwise Euclidean separation ≥ (1/10) * Real.log (1/epsBW)) ∧
      (∀ t ∈ T, ∀ p ∈ triangle ..., (p.1:ℝ) + 1 ≤ n/2 - (1/10) * Real.log (1/epsBW))
    := sorry
```
(Exact conjunct spelling is implementer's; content must match Lemma 7.4's three claims:
partition into triangles, strip confinement, ≥(1/10)log(1/ε) separation. RATIFY-5.)
White cancellation Lemma 7.2 (prove the algebraic half now; the `cos ≤ exp(-ε³)` half may sorry):
`f(x,3) = χ(5x)(1+χ(2x))/2` and `|f| = |cos(π θ)|` at the specialization — statement per paper p.35.

## 11. `TaoCollatz/Sec7/Holding.lean` (node X4 — D6 finitization; the design-validation file)

```lean
noncomputable def hold : PMF (ℕ × ℤ) :=   -- §7.3 Hold; first coord ≥ 1 always
  geomQuarter.bind fun k => ((pascalNe3.iid (k - 1)).map fun v => (k, (3 + ∑ i, v i : ℤ)))
noncomputable def Qaux (W : Set (ℕ × ℤ)) (ε : ℝ) : ℕ → ℤ → ℝ
  | 0, l => Real.exp (-(ε^3) * (Set.indicator W 1 (0, l) : ℝ))   -- careful: see (†) below
  | (m+1), l => ...
```
**(†) Design note — implement carefully, this file EXISTS to validate D6:** define
`Q (half : ℕ) (W) (ε) : ℤ × ℤ → ℝ` on paper coordinates (j,l) with
`Q (j,l) = 1` for `j > half`, and for `j ≤ half`
`Q (j,l) = exp(-ε³·1_W(j,l)) * ∑' d : ℕ × ℤ, (hold d).toReal * Q (j + d.1, l + d.2)`,
via strong recursion on `half - j` (hold's support has `d.1 ≥ 1` — prove `hold_support_fst_pos`
first; the recursive call is at strictly smaller `half - j`). Deliverable lemmas:
```lean
theorem Q_boundary (hj : half < j) : Q half W ε (j, l) = 1
theorem Q_rec (hj : j ≤ half) : Q half W ε (j, l)
    = Real.exp (-(ε^3) * (Set.indicator W 1 (j, l))) * ∑' d, (hold d).toReal * Q half W ε (j + d.1, l + d.2)  -- (7.35)
theorem Q_nonneg / Q_le_one : 0 ≤ Q ... ≤ 1
```
If the ℤ-vs-ℕ j-coordinate fights the recursion, use `j : ℕ` (the walk only moves right). RATIFY-6.
Then Prop 7.3 (finitized) + the reduction chain statements, all sorry:
```lean
theorem renewal_white_encounters (A) (hA : 0 < A) : ∃ C > 0, ∀ n ξ (hξ) (hn : 1 ≤ n),
    (pascal.iid (n/2)).expect (fun b => Real.exp (-(epsR^3) * #{j | b_j = 3 ∧ white at (j, pre b (j+1))})) ≤ C * n ^ (-A)  -- Prop 7.3, finite-vector form
theorem key_fourier_decay ... -- Prop 7.1 = Prop 1.17 restated through (1.26); reduction lemma statements per (7.4)/(7.5)
```

## 12. `TaoCollatz/Statement.lean` — TRUSTED BASE

Imports ONLY `Basic.Collatz` + `Basic.LogDensity`. Contents exactly:
```lean
theorem tao_collatz (f : ℕ → ℝ) (hf : Filter.Tendsto f Filter.atTop Filter.atTop) :
    AlmostAllPos fun N => (colMin N : ℝ) < f N := sorry     -- Theorem 1.3
theorem tao_collatz_quantitative :                          -- Theorem 3.1, Colmin form
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ N₀ x : ℕ, 2 ≤ N₀ → 2 ≤ x →
      1 - C / (Real.log N₀) ^ c ≤ logProb {N | colMin N ≤ N₀} (posInterval x) := sorry
```

## 13. Root module + build hygiene

`TaoCollatz.lean` imports everything. `lake build` must be green (sorry warnings OK).
Check `lean-sorry` runs clean structurally. NO `axiom`, NO `native_decide`, no `maxHeartbeats`
bumps without a `-- HEARTBEAT:` comment. Commit message: `skeleton: Phase-A defs + ratified statement chain`.

## RATIFY markers

`RATIFY-n` comments flag statement-shape choices needing a judge pass against the paper
before grind laps start. Keep them greppable.
