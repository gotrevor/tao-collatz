# PENDING WORK (kept current per lap; newest on top)

## Lap fruit-10 (2026-07-14, brick b step 3): **`cond_char_factor` PROVED — the conditional char factorization**

Build green 3285, `#print axioms cond_char_factor = norm_stdAddChar = [propext, Classical.choice,
Quot.sound]`. Landed in `Sec6/MixingFromDecay.lean` (commit `595b408`). This is the assembly the
previous lap set up: it fuses `char_offset_split` (pointwise additive→multiplicative split) with
`cexpect_iid_append` (iid block independence) into the head×tail expectation split, for a fixed cut
`n=j+p` and fixed tail-valuation level `l`:
```
E_a[ stdAddChar(-(X(a)·ξ)) · 1_{pre(tail a)=l} ]
  = E_vh[ stdAddChar(-((3^p·(Fnat_j(vh)·2⁻ᵖʳᵉ⁽ᵛʰ,ʲ⁾)·2⁻ˡ)·ξ)) ]           -- pure HEAD block
  · E_vt[ stdAddChar(-((Fnat_p(vt)·2⁻ᵖʳᵉ⁽ᵛᵗ,ᵖ⁾)·ξ)) · 1_{pre(vt)=l} ]     -- pure TAIL block (w/ indicator)
```
Proof: `set` the two block observables `f`(head-only), `g`(tail-only, carries indicator); norm
bounds via new helper `norm_stdAddChar` (`stdAddChar_apply`+`Circle.norm_coe`, needs `[NeZero N]`);
`rw [← PMF.cexpect_iid_append]`; then `congrArg (cexpect _)` + `funext a` reduces to the pointwise
identity, split on `pre(tail a)=l`: on the event `char_offset_split` + `pre_castAdd a (le_refl j)`
(head val `pre a j`↔`pre vh j`) + `h` (freeze `2⁻ᵖʳᵉ⁽ᵗᵃⁱˡ⁾`→`2⁻ˡ`) + `ring`; off the event both
sides vanish via the indicator (`simp [if_neg]`). Gotcha banked: don't `set N := 3^(j+p)` — it
rewrites `ZMod (3^(j+p))` to `ZMod N` and then `rw [char_offset_split]` (stated with `3^(j+p)`)
fails to match syntactically; keep `3^(j+p)` explicit in `f`/`g`.

**→ NEXT (brick b, remaining) — the tail factor ⟹ `charFn_decay`, then the §6 conditioning assembly**:
1. **Tail factor = level-`p` Syracuse char sum.** The pure-tail expectation
   `E_vt[stdAddChar(-((Fnat_p(vt)·2⁻ᵖʳᵉ⁽ᵛᵗ,ᵖ⁾)·ξ))·1_{pre(vt)=l}]` — drop/bound the indicator (`≤1`)
   or handle it in the union over `l` — is, via `syracZ_eq_rev_fnat` (which is exactly the pushforward
   of `iid geomHalf p` under `vt ↦ Fnat_p(vt)·2⁻ᵖʳᵉ⁽ᵛᵗ,ᵖ⁾`), a level-`p` Syracuse character sum. But
   `Fnat_p(vt)` here lives in `ZMod (3^(j+p))`, whereas `syracZ p : PMF (ZMod (3^p))`; need a
   `syracZ_map_cast`-style reindex tying the char at level `3^(j+p)` (for high `ξ = 3^j·2^l·ξ'`,
   `3∤ξ'`) to the level-`p` char at `ξ'`. Then `charFn_decay` (Prop 1.17, PROVED) bounds it `≤ Cₐ·p⁻ᴬ`.
   The head factor has norm `≤1` (`cexpect_norm_le` + `norm_stdAddChar`).
2. **Bridge `𝓕(densC g_l) ξ ↔ cexpect`.** Show the conditioned density's DFT equals (a scalar times)
   this `E_a[stdAddChar(-(X·ξ))·1_{pre(tail)=l}]` — finite-∑-over-`ZMod` ↔ tsum-over-`a` swap with
   `g_l(Y)=E_a[1_{X=Y ∧ pre(tail)=l}]`. Then `osc_le_sqrt_highfreq` (general `c`, PROVED) on `g_l`.
3. **Conditioning events + reassembly** (stopping time `k`, events E/Eₖ/Bₖ/Cₖ,ₗ, union over `k,l`,
   triangle ineq; paper (6.2)–(6.10)). Decompose into named `sorry`s in `Sec6/MixingFromDecay.lean`.
   Full 7-step plan: fruit-8.

## Lap fruit-9 (2026-07-14, review + brick d): **§7 confirmed CLOSED; C10 bridge GENERALIZED to arbitrary `c`**

**Review-lap finding**: `#print axioms` confirms the entire §7 crux is axiom-clean — `prop_7_8`,
`Q_black_edge`, `Q_polynomial_decay`, `charFn_decay` (Prop 1.17), `key_fourier_decay` (Prop 7.1)
all `[propext, Classical.choice, Quot.sound]`. Only 4 live sorries remain (2 frozen headlines +
C10 `fine_scale_mixing` + C9 `stabilization`). DIRECTION.md CURRENT DIRECTIVE + STATUS.md were
stale (§7-era); both rewritten to point at C10. No trigger fired; route = CONTINUE.

**Brick (d) DONE** (build green 3285, axiom-clean): generalized the whole CS/Parseval bridge in
`Sec6/MixingFromDecay.lean` from the raw `syracZ` density to an **arbitrary real
`c : ZMod (3^n) → ℝ`**. `densC n` → `densC n c := fun Y => (c Y : ℂ)`; threaded `c` through
`condAvgC`, `devC`, `osc_eq_sum_norm_devC`, `densC_inversion`, `condAvgC_eq_lowSum`,
`devC_eq_highfreq_invDFT`, `sum_norm_sq_devC_eq`, `osc_le_sqrt_highfreq`. The character lemmas
(`coset_char_sum`, `fiber_char_reindex`, `geom_sum_root_of_pow_eq_one`, `fiber/high/lowFreq`) were
already density-independent — untouched. `#print axioms osc_le_sqrt_highfreq = [propext, choice,
Quot.sound]`. So the bridge `osc m n hmn c ≤ √(∑_{highFreq} ‖𝓕(densC n c)ξ‖²)` now holds for ANY
real density — ready to apply to the conditioned `g`.

**Brick (a) ALGEBRAIC CORE DONE** (build green 3285, axiom-clean): `fnat_split` in
`Basic/Valuation.lean` — the route-decisive identity, Tao's (1.26) integerified:
```
fnat (j+p) a = 3^p · fnat j (fun i => a (Fin.castAdd p i))         -- first j coords
             + 2^{pre a j} · fnat p (fun i => a (Fin.natAdd j i))  -- last p coords
```
Purely algebraic (no probability): split `∑_{m∈range(j+p)}` via `Finset.sum_range_add`; first block
factors `3^p` (exponent `j+p-1-m = p+(j-1-m)`) with `pre_castAdd` (prefix of first `j` = prefix of
whole for `m≤j`); second block factors `2^{pre a j}` with `pre_natAdd_split`
(`pre a (j+m) = pre a j + pre(tail) m`). Both helper lemmas also proved + clean. This CONFIRMS the
F-split route is viable at the algebra level — the char-sum factorization now has its foundation.

**Brick (a) FINISHED at the ZMod level** (build green, axiom-clean): `syracZ_offset_split` in
`Syracuse/SyracRV.lean` — `fnat_split` reduced mod `3ⁿ` into the exact offset form the character sum
uses (the map of `syracZ_eq_rev_fnat`). For `a : Fin (j+p) → ℕ`, in `ZMod (3^(j+p))`:
```
(fnat (j+p) a) · 2⁻ᵖʳᵉ⁽ᵃ,ʲ⁺ᵖ⁾
  = 3^p · (fnat j head · 2⁻ᵖʳᵉ⁽ᵃ,ʲ⁾) · 2⁻ᵖʳᵉ⁽ᵗᵃⁱˡ,ᵖ⁾   -- head-offset, scaled by 3^p and tail-val
  + (fnat p tail · 2⁻ᵖʳᵉ⁽ᵗᵃⁱˡ,ᵖ⁾)                       -- tail-offset (a level-p Syracuse offset)
```
Proof: `pre_natAdd_split` (split `pre a (j+p)`) + `fnat_split` (cast to ZMod) + `2·2⁻¹=1` unit
cancellation via `linear_combination`. **The `3^p` on the head term is the structural crux**: mod
`3ⁿ` it annihilates the low `j` ternary digits, so the head only feeds LOW frequencies and the tail
carries the HIGH frequencies. The residual head↔tail coupling is exactly `2⁻ᵖʳᵉ⁽ᵗᵃⁱˡ,ᵖ⁾`, which
conditioning on the cut-valuation `pre a j = l` removes.

**Brick (b) step 1 DONE** (build green, axiom-clean): `char_offset_split` in
`Sec6/MixingFromDecay.lean` — the pointwise additive→multiplicative character factorization,
`stdAddChar(-(X·ξ)) = stdAddChar(-(head·ξ))·stdAddChar(-(tail·ξ))` via `AddChar.map_add_eq_mul`,
where `head = 3^p·(Fnat_j·2⁻ᴸ)·2⁻ᴹ`, `tail = Fnat_p(last p)·2⁻ᴹ` (L=pre a j, M=pre tail p).

### 🔑 KEY ROUTE FINDING (this lap — sharpens the crux; the decisive step-2 recipe)
Coordinate-dependence of the two split terms (`X = Term1 + Term2`, `L=pre a j` head-val,
`M=pre(tail) p` tail-val):
- **Term1** (head term) `= 3^p·(Fnat_j(head)·2⁻ᴸ)·2⁻ᴹ` — depends on head (via `Fnat_j`,`L`) **and tail
  (via `2⁻ᴹ`)**.
- **Term2** (tail term) `= Fnat_p(tail)·2⁻ᴹ` — depends on **tail only**.

So the `char_offset_split` factors are NOT (pure-head)·(pure-tail): the head factor carries `2⁻ᴹ`, a
tail quantity. Hence `E_a[stdAddChar(-(X·ξ))]` does **NOT** factor into head×tail directly.
**RESOLUTION (decisive)**: condition on `M = pre(tail) p` (the *tail* valuation). On `{M = l}`:
`2⁻ᴹ → 2⁻ˡ` is a constant, so Term1 becomes head-only (`3^p·Fnat_j(head)·2⁻ᴸ·2⁻ˡ`) and Term2 stays
tail-only. Then the two `stdAddChar` factors depend on DISJOINT iid coordinate blocks and the
conditional expectation FACTORS. (Note: this is the mirror of Tao's orientation — Tao's `2^{-l}` sits
on his 2nd term with `l` the head valuation; `syracZ`'s `a∘rev` convention swaps the roles, so *we*
condition on the tail valuation `M`. Math identical, just which block is "head".) **This is why
conditioning is mandatory, not bookkeeping — and it says exactly WHICH valuation to condition on.**

**Brick (b) step 2 (the ENGINE) DONE** (build green, axiom-clean): `cexpect_iid_append` in
`Prob/Basic.lean` — the D1 product-form block-independence lemma:
```
(iid (j+q)).cexpect (fun v => f(v∘castAdd) · g(v∘natAdd)) = (iid j).cexpect f · (iid q).cexpect g
```
for bounded `f,g` (`‖·‖≤1`). Proof: `iid_apply_eq_prod` + `Fin.prod_univ_add` give the mass
factorization `iid(j+q)(append vh vt) = iid_j(vh)·iid_q(vt)`; reindex the tsum via `Fin.appendEquiv`;
factor via `tsum_mul_tsum_of_summable_norm` (summability from the new `summable_iid_norm_le_one`).
**This IS the head×tail separation** — with `g` carrying a `1_{pre(tail)=l}` indicator it delivers the
conditional factorization. The reusable engine of the §6 char-sum factorization.

**→ NEXT (brick b — assemble the conditional character factorization)**:
1. **Combine `char_offset_split` + `cexpect_iid_append`**: write `𝓕(densC g_l) ξ =
   E_a[stdAddChar(-(X·ξ))·1_{pre(tail)=l}]`, factor pointwise via `char_offset_split`, then apply
   `cexpect_iid_append` with `f`=head char (`stdAddChar(-(3^p·Fnat_j(head)·2⁻ᴸ·2⁻ˡ·ξ))`, head-only on
   `{M=l}`) and `g`=tail char × `1_{pre(tail)=l}`. Both char factors have norm 1, indicator ≤1 — the
   `‖·‖≤1` hyps hold. Sum over `l` reassembles the full char sum.
2. **Tail factor = level-`p` Syracuse char sum** ⟹ `charFn_decay` (Prop 1.17, PROVED) via a
   `syracZ_map_cast`-style reindex at level `3^p` (`syracZ_eq_rev_fnat` connects `Fnat_p·2⁻ᵖʳᵉ` to
   `syracZ p`; then `charFn_decay` bounds `(syracZ p).cexpect(eC …)`).
3. **Conditioning events + reassembly** (stopping time k, E/Eₖ/Bₖ/Cₖ,ₗ, union over k,l, triangle
   ineq; paper (6.2)–(6.10)). Bridge `𝓕(densC g) ↔ cexpect` (finite-∑ over ZMod ↔ tsum-over-`a` swap:
   `g(Y)=E_a[1_{X=Y∧ev}]`). Decompose into named `sorry`s in `Sec6/MixingFromDecay.lean` as built.
   Full 7-step plan: fruit-8.

## Lap fruit-8 (2026-07-15): **C10 Cauchy–Schwarz bridge `osc_le_sqrt_highfreq` FULLY PROVED, axiom-clean**

The entire Plancherel/Cauchy–Schwarz half of C10 (`fine_scale_mixing`) is now sorry-free and
`#print axioms osc_le_sqrt_highfreq = [propext, Classical.choice, Quot.sound]`. Everything landed
this lap in `Sec6/MixingFromDecay.lean` (7 green commits). New machinery (all reusable):

- `osc_eq_sum_norm_devC` — `osc = ∑_Y ‖devC Y‖` (cast of the real deviation to ℂ-norm).
- `sum_norm_sq_devC_eq` — Parseval `L²`: `∑‖devC‖² = N⁻¹∑_{highFreq}‖𝓕(densC)ξ‖²`, via `devC = 𝓕⁻ g`
  (`g` = high-freq restriction of `𝓕(densC)`) + `ZMod.dft_parseval` (`LinearEquiv.apply_symm_apply`).
- `densC_inversion` — `densC Y = N⁻¹∑_ξ 𝓕(densC)ξ·e(ξ·Y)` (`LinearEquiv.symm_apply_apply` + `invDFT_apply`).
- `devC_eq_highfreq_invDFT` — deviation = high-freq inverse DFT (inversion − low projection; filter split).
- `condAvgC_eq_lowSum` — the `3ᵐ`-conditional average IS the low-freq projection (inversion into fiber
  average → sum swap → `coset_char_sum` → `3^{m-n}·3^{n-m}=1`).
- `coset_char_sum` (the number-theoretic heart) — `∑_{fiber} e(ξY') = [ξ∈low]·3^{n-m}·e(ξY)`, via
  `fiber_char_reindex` + character split `e(ξ(Y+t·3ᵐ))=e(ξY)·rᵗ` + `geom_sum_root_of_pow_eq_one`
  (`r^{3^{n-m}}=1`) + low criterion `r=1 ⟺ 3^{n-m}∣ξ.val`.
- `fiber_char_reindex` (pure combinatorics) — fiber `= image (t↦Y+t·3ᵐ) (range 3^{n-m})`, injective
  (`Nat.ModEq.mul_right_cancel'`) + surjective (`t=(Y'-Y).val/3ᵐ`, `castHom(Y'-Y)=0 ⟹ 3ᵐ∣val`).
- `geom_sum_root_of_pow_eq_one` — `r^K=1 ⟹ ∑_{j<K} rʲ = if r=1 then K else 0` (reusable brick).

**Gotchas banked**: (1) rewriting `3^n` when it's ALSO a `ZMod (3^n)` modulus → "motive not type
correct"; extract a pure-ℕ helper `∀ v, 3^n∣v*3^m ↔ 3^{n-m}∣v` so `3^n` isn't tied to a type.
(2) `ZMod.castHom_apply` takes ONLY the element (`castHom h R i = cast i`), not `h`/`R` explicitly.
(3) `Complex.norm_real` (not `Complex.norm_ofReal`) + `Real.norm_eq_abs`. (4) `Finset.sum_ite_mem_eq`
(additive of `prod_ite_mem_eq`) for `∑ if i∈s then f else 0 = ∑_{i∈s} f`.

### 🚨 ROUTE FINDING (refuted sub-approach — this is the lap's main result on the crux)

`highfreq_l2_le` (∑_{highFreq}‖𝓕(densC n)ξ‖² ≤ C·m^{-A} for raw syracZ) is **FALSE** — DELETED.
Proof it's false: by Parseval (`sum_norm_sq_devC_eq`), `∑_{highFreq m n}‖ĉ_n(ξ)‖² = Q(n)−Q(m)` where
`Q(ℓ):=3^ℓ·∑_Y syracZ(ℓ,Y)² = 3^ℓ·P(X=X' at level ℓ)`. An **exact DP computation** of syracZ
(`scripts/syracZ_highfreq_l2.py`, no deps) gives, for m=1: n=2→0.476, n=3→0.938, n=4→1.402,
n=5→1.867 — i.e. `∑_high‖ĉ‖²` GROWS ≈ 0.46·(n−m), NOT ≤ C·m^{-A}. (The `=Q(n)−Q(m)` identity
matches to full precision, so the Parseval reformulation is confirmed.)

**Consequence**: `osc_le_sqrt_highfreq` (PROVED, axiom-clean, and CORRECT) is hopelessly lossy on the
RAW density: `osc ≤ √(0.46·n)` → ∞. The Cauchy–Schwarz-on-raw-syracZ route CANNOT prove Prop 1.14.
`fine_scale_mixing` reverted to a documented `sorry` (was resting on the false lemma).

**The real route (Tao §6, paper lines 1920–2200, pdf pp.28–31)**: apply Cauchy–Schwarz to the
CONDITIONED density `g_{n,k,l}(Y) = P((Xₙ=Y) ∧ Eₖ ∧ Bₖ ∧ Cₖ,ₗ)`, NOT raw syracZ. Steps:
1. Reduce to `0.9n ≤ m ≤ n` (telescoping + triangle for general m; (6.1)).
2. Condition on event `E` = the sub-Gaussian bounds (6.2) on all partial sums `a_{[i,j]}` (Lemma 2.2
   + union bound ⟹ `P(Ē) ≪ n^{-A-1}`); triangle-inequality it off.
3. Stopping time `k` (unique with `a_{[1,k]} ≤ n·log3/log2 − Cₐ²log n < a_{[1,k+1]}`), then the level
   `l = a_{[1,k+1]}`; union-bound over `k` (≈ n·log3/(2log2)) and `l` (a `Cₐ²log n`-window).
4. **Independent split** (1.5)/(1.26): on `Cₖ,ₗ`, `Xₙ = F_{k+1}(a_{k+1},…,a₁) + 3^{k+1}2^{-l}F_{n-k-1}(aₙ,…,a_{k+2}) mod 3ⁿ`,
   2nd summand independent of `a₁..a_{k+1},Eₖ,Bₖ,Cₖ,ₗ` ⟹ char sum FACTORS:
   `∑_Y g(Y)e(-ξY/3ⁿ) = [E e(-ξ F_{k+1})1_{Eₖ∧Bₖ∧Cₖ,ₗ}] · [E e(-ξ2^{-l}F_{n-k-1}/3^{n-k-1})]`.
5. For high `ξ = 3ʲ2ˡξ'` (`0≤j<n-m`, `3∤ξ'`), the 2nd factor is a level-`n-k-1` Syracuse char sum at
   `ξ'` ⟹ `charFn_decay` (Prop 1.17, PROVED axiom-clean) bounds it `≤ Cₐ(n-k-1)^{-A}`. 1st factor `≤1`.
6. `osc_le_sqrt_highfreq` (GENERALIZE to arbitrary real `c` first — proof never used syracZ-ness) on `g`,
   then Plancherel/geometric sum over high `ξ` ⟹ `∑_high‖ĝ‖² ≪ (n-k-1)^{-2A}·(count)` — now SMALL
   because the 1st-factor ℓ² mass is bounded (F_{k+1} lives in k+1 coords: Renyi-2-entropy point).
7. Reassemble by triangle inequality over `k,l` and the event differences.

**Prerequisite bricks to build (next laps, hardest-first)**: (a) the `Fₖ`/`F`-splitting as a Lean
identity on `Xₙ` conditioned on `Cₖ,ₗ` (needs `pre`/`fnat` (1.5),(1.26) — some in `Basic/`, `Syracuse/`);
(b) independence of the two summands ⟹ char-sum factorization (D1 PMF product form, `cexpect_mul` of
independent factors); (c) the event `E` sub-Gaussian bound from Lemma 2.2 (already have `Gj`/`Geom`
machinery in §2); (d) generalize `osc_le_sqrt_highfreq` to arbitrary `c`. **Start with (d)** (mechanical,
unblocks applying the bridge to `g`) then (a).

Then C10 is done and only C9 (`stabilization`, §5) + headlines remain.

## Lap fruit-7 (2026-07-14): **Parseval on `ZMod N` PROVED (S4 brick) + full C10 route mapped**

With §7 done and all of SyracRV closed, the two remaining spine sorries are the HEROIC
analytic nodes. Dependency order (BLUEPRINT critical path `… → C10 → C9 → C6`) makes
**C10 = `fine_scale_mixing` (§6, Prop 1.14) the upstream target** (C9/`stabilization` §5
consumes it). This lap NARROWED C10:

**Landed (axiom-clean, build green):** `TaoCollatz/Fourier/Parseval.lean` (node S4) —
`ZMod.dft_parseval_complex` (`∑ₖ 𝓕Φ(k)·conj = N·∑ⱼ Φ(j)·conj`) and `ZMod.dft_parseval`
(real: `∑ₖ ‖𝓕Φ(k)‖² = N·∑ⱼ ‖Φ(j)‖²`), derived from `stdAddChar` orthogonality
(`AddChar.sum_eq_zero_of_ne_one` + `isPrimitive_stdAddChar`) via the double-sum swap. Mathlib
has `ZMod.dft` + inversion `dft_dft` but NOT Parseval; now we do.

**Full C10 route (`fine_scale_mixing`), derived & ready to execute next lap:**
Let `c_n(Y) := (syracZ n Y).toReal` (the density; ∑=1). The 3ᵐ-conditional average in `osc`
= projection onto **low frequencies** `{ξ : 3^{n-m} ∣ ξ.val}` (those ξ constant on 3ᵐ-cosets:
`e(ξ·3ᵐt/3ⁿ)=1 ⟺ 3^{n-m}∣ξ`). So the deviation `c_n − avg = 3⁻ⁿ ∑_{high ξ} ĉ_n(ξ) e(ξ·/3ⁿ)`
where `high = {ξ : ¬ 3^{n-m}∣ξ.val}`, `ĉ_n(ξ) = ∑_Y c_n(Y) e(-ξY/3ⁿ)` (= `𝓕 (c_n)` up to sign;
note `ĉ_n(ξ) = (syracZ n).cexpect (Y ↦ eC(-(ξ.val·Y.val)/3ⁿ))`, EXACTLY charFn_decay's expr).
1. **Cauchy–Schwarz** (`osc = ∑_Y |dev|`): `osc ≤ √(3ⁿ)·√(∑_Y |dev|²)`, and by **`dft_parseval`**
   `∑_Y|dev|² = 3⁻ⁿ ∑_{high ξ}|ĉ_n(ξ)|²` ⟹ `osc ≤ √(∑_{high ξ}|ĉ_n(ξ)|²)`.  ← new sub-lemma.
2. **Per-frequency decay**: for `ξ = 3ʲ·η`, `η` not div by 3, `j = v₃(ξ) < n-m`, the projection
   compat `syracZ_map_cast` gives `ĉ_n(3ʲη) = ĉ_{n-j}(η)`; **Prop 1.17 `charFn_decay`** (PROVED,
   axiom-clean) bounds `|ĉ_{n-j}(η)| ≤ C·(n-j)^{-A} ≤ C·m^{-A}` (since n-j ≥ m+1).  ← new sub-lemma.
3. **Sum the frequencies**: split `high` by `j = v₃(ξ)`; at each `j`, `∑_{η not÷3, lvl n-j}|ĉ_{n-j}(η)|²
   ≤ ∑_all |ĉ_{n-j}|² = 3^{n-j}∑_Y c_{n-j}(Y)²` (Parseval at lvl n-j). Balance the count vs the
   Prop-1.17 decay to get `∑_{high}|ĉ_n|² ≤ C'·m^{-A'}`; combine with step 1 ⟹ `osc ≤ C·m^{-A}`.
   (Constant chase: choose the Prop-1.17 exponent `A` large enough to beat the ≤ n frequency
   scales; each scale contributes `≲ m^{-2A}`, ∑ over j<n-m scales is `≲ n·m^{-2A} ≤ m^{1-2A}`.)

**DONE this lap (build green, decomposition landed)**: `Sec6/MixingFromDecay.lean` now proves
`fine_scale_mixing` from two named sub-lemmas (`highfreq_l2_le` applied at exponent `2A`, so the
`√` restores `m^{-A}`); added `densC` (ℂ density) and `highFreq m n` (the `¬3^{n-m}∣ξ.val` modes):
- `osc_le_sqrt_highfreq` [sorry] — step 1: `osc ≤ √(∑_{highFreq} ‖𝓕(densC n) ξ‖²)` (CS + Parseval).
- `highfreq_l2_le` [sorry] — steps 2–3: `∑_{highFreq} ‖𝓕(densC n) ξ‖² ≤ C·m^{-A}` (∀A), from
  `charFn_decay` via `syracZ_map_cast` projection + per-level Parseval count.

**NEXT lap**: discharge the two Sec6 sub-lemmas. `osc_le_sqrt_highfreq` needs (a) the identity
"3ᵐ-conditional-average = low-freq inverse-DFT" (relate `osc`'s castHom-fiber average to
`∑_{low ξ} 𝓕(densC)(ξ)e(ξ·/3ⁿ)`), then (b) `∑_Y|dev| ≤ √(3ⁿ)·√(∑_Y|dev|²)` (Finset Cauchy–Schwarz,
`Finset.inner_mul_le_norm_mul_norm` or `Finset.sum_div_pow_mul_...`), then (c) `ZMod.dft_parseval`.
`highfreq_l2_le` needs the cexpect↔dft bridge (`𝓕(densC n) ξ` vs `(syracZ n).cexpect (eC …)`; sign),
the `syracZ_map_cast` reduction of `ĉ_n(3ʲη)=ĉ_{n-j}(η)`, then `charFn_decay` + a geometric sum.

## Lap fruit-6 (2026-07-14): **Lemma 1.12 `syracZ_recursion` PROVED — ALL of SyracRV closed**

The last SyracRV stub is done; `Syracuse/SyracRV.lean` is now **sorry-free & axiom-clean**
(`#print axioms syracZ_recursion = [propext, Classical.choice, Quot.sound]`, full build 3282).
The genuine ZMod number-theory crux (the fiber lemma) fell. New machinery, all reusable:

1. **`cast_Ghat`** — truncation `castHom_{3ⁿ⁺¹→3ⁿ}(Ĝ w) = Gₙ w` (the `k=n` case of the
   `syracZ_map_cast` truncation, with `w` used directly — no `castLE`, no vanishing tail).
2. **`three_mul_eq_iff`** — `3·A = 3·B ↔ (A mod 3ⁿ) = (B mod 3ⁿ)` in `ZMod 3ⁿ⁺¹`. The
   `3·ZMod 3ⁿ⁺¹ ≅ ZMod 3ⁿ` iso, proved via `∀C, 3·C=0 ↔ castHom C = 0` (both sides ⟺
   `3ⁿ ∣ C.val`, using `natCast_eq_zero_iff` + `Nat.mul_dvd_mul_iff_left`; `sub` to lift to A,B).
3. **`syracZ_fiber`** (the crux, ~90 lines) — for fixed head `a₀` and target `x`,
   `∑' w, (iid n) w · [Gₙ₊₁(cons a₀ w)=x] = if (2^{a₀}x.val)%3=1 then syracZ n arg else 0`.
   Route: `syracZ_offset_peel` head-peel ⟹ cond ⟺ `(m:ZMod 3ⁿ⁺¹)=1+3Ĝ(w)` (m=2^{a₀}x.val,
   via unit `2^{a₀}`); reduce mod 3 (castHom to `ZMod 3`) ⟹ guard `m%3=1`; then `m=3q+1`,
   cancel the `1`, `three_mul_eq_iff` + `cast_Ghat` ⟹ `arg = Gₙ(w)`; `PMF.map_apply` on both.
4. **Assembly** — `PMF.map_apply` → product form → `PMF.tsum_iid_succ_mul` peels `a₀` →
   `syracZ_fiber` collapses the tail → `geom_fold_geomHalf` folds the `a₀`-sum. Periodicity
   `f(a+P)=f(a)`, P=2·3ⁿ: guard via `2^P≡1 (mod 3)` (`Nat.ModEq`); value via `two_pow_period`
   (`2^{2·3ⁿ}=1 mod 3ⁿ⁺¹`) ⟹ `(m_{a+P}:ZMod 3ⁿ⁺¹)=(m_a:_)` ⟹ same arg by `three_mul_eq_iff`.

### Remaining non-headline sorries (whole repo):
- `Sec5/FirstPassage.lean:81` `stabilization` (Prop 1.11) — HEROIC analytic (multi-lap; narrow only).
- `Sec6/MixingFromDecay.lean:19` `fine_scale_mixing` — HEROIC analytic §6 (multi-lap; narrow only).
- `Statement.lean:22,28` — the two headlines (discharge only when the whole chain lands; DO NOT TOUCH).

**NEXT**: with §7 done and all of SyracRV closed, the remaining spine work is the two HEROIC
analytic §5/§6 stubs (`stabilization`, `fine_scale_mixing`) — narrow only — plus any objective-3
fruit the judge lists (ManyTriangles split, Pin C8). Attack `stabilization` (Prop 1.11) next:
decompose the first-passage stabilization into named sub-lemmas before attempting the analytic core.

## Lap fruit-5 (2026-07-14): **Lemma 1.12 — FIVE cores PROVED, one hard fiber lemma left**

Sustained narrowing of `syracZ_recursion` (`Syracuse/SyracRV.lean`, the last SyracRV stub).
All the analytic / number-theoretic scaffolding is now machine-checked & axiom-clean (build 3282):
1. `pre_succ_tail` — `pre a (m+1) = a 0 + pre (tail a) m`.
2. `syracZ_offset_peel` — `Gₙ₊₁(a) = 2⁻ᵃ⁰·(1 + 3·Ĝ(tail a))` (head-peel of the offset).
3. `geom_fold` — `∑'_a 2⁻ᵃ·g(a) = (1−2⁻ᴾ)⁻¹·∑_{r<P} 2⁻ʳ·g(r)` for P-periodic g.
4. `two_pow_period` — `2^{2·3ⁿ} ≡ 1 (mod 3ⁿ⁺¹)` (ℤ-dvd induction, no LTE needed).
5. `geom_fold_geomHalf` — the Geom(2)-weighted, Icc-form fold the theorem literally consumes.

**ONLY remaining piece = the ZMod fiber lemma** (the genuinely hard core). Precise target:
```
∀ a0 x, ∑' w:Fin n→ℕ, (geomHalf.iid n) w * (if x = Gₙ₊₁(Fin.cons a0 w) then 1 else 0)
      = if (2^a0·x.val)%3 = 1 then syracZ n (((2^a0·x.val−1)/3 : ℕ) : ZMod 3ⁿ) else 0
```
Route: (a) `syracZ_offset_peel` ⟹ condition `x = Gₙ₊₁(cons a0 w)` ⟺ `2^{a0}·x = 1 + 3·Ĝ(w)`
(mult by the unit `2^{a0}`); (b) split on the guard `2^{a0}x ≡ 1 (mod 3)`; (c) when it holds,
`1+3·Ĝ(w)=2^{a0}x` ⟺ `Ĝ(w) ≡ arg (mod 3ⁿ)` via the `3·ZMod 3ⁿ⁺¹ ≅ ZMod 3ⁿ` iso, and
`Ĝ(w) mod 3ⁿ = Gₙ(w)` (the castHom truncation from `syracZ_map_cast`), so the w-sum = `syracZ n arg`
by `map_apply`. This is the ZMod number-theory crux (~100+ lines). Then the FINAL assembly:
`map_apply` + `tsum_iid_succ_mul` (peel a0) + fiber lemma + guard/arg periodicity (from
`two_pow_period`) + `geom_fold_geomHalf`. All five cores above plug straight in.

## Lap fruit-4 (2026-07-14): **§5 `logUnifOdd` normalization PROVED** + **Lemma 1.12 decomposed**

Two advances, both objective-3 fruit, both axiom-clean & build green (3282):

**(a) `logUnifOdd` normalization** (`Sec5/FirstPassage.lean`) — closed the `PMF.ofFinset`
normalization sorry (a real on-path spine stub). Refactored the outer `if → dite` so
window-nonemptiness is in scope, then `∑_{N∈W} N⁻¹/D = D/D = 1` with `D = ∑_{M∈W} M⁻¹` finite
(odd ⇒ `M≠0`, `ENNReal.sum_ne_top`) and nonzero (`Finset.sum_eq_zero_iff` + nonempty).
FirstPassage now carries ONLY the heroic `stabilization` (Prop 1.11) sorry.

**(b) `syracZ_recursion` (Lemma 1.12) DECOMPOSED** (`Syracuse/SyracRV.lean`) — proved the
algebraic core as reusable sub-lemmas: `pre_succ_tail` (`pre a (m+1) = a 0 + pre (tail a) m`)
and `syracZ_offset_peel` (`Gₙ₊₁(a) = 2⁻ᵃ⁰·(1 + 3·Ĝ(tail a))` in `ZMod 3ⁿ⁺¹`). Full remaining
probabilistic route written into the sorry (peel a₀ → mod-3 guard + divide-by-3 → castHom
truncation → geometric fold via `orderOf(2 : ZMod 3ⁿ⁺¹) = 2·3ⁿ`). See its route comment.

### Remaining non-headline sorries (post-lap inventory):
- `Syracuse/SyracRV.lean` `syracZ_recursion` — DOABLE, core proved; next: step (1) tsum-peel of
  the fiber mass + step (4) `orderOf(2 : ZMod 3ⁿ⁺¹) = 2·3ⁿ` (number theory) + geometric resum.
- `Sec5/FirstPassage.lean` `stabilization` (Prop 1.11) — HEROIC analytic (multi-lap, narrow only).
- `Sec6/MixingFromDecay.lean` `fine_scale_mixing` — HEROIC analytic §6 (multi-lap, narrow only).
- `Statement.lean` — the two headlines (discharge only when the whole chain lands; DO NOT TOUCH).

## Lap fruit-3 (2026-07-14): **Syracuse (1.22) `syracZ_map_cast` PROVED (axiom-clean)** — SyracRV stub 2/3

Objective-3 fruit, SyracRV stub 2 of 3. Closed `syracZ_map_cast` (`Syracuse/SyracRV.lean`): the
paper-(1.22) projection compatibility — reducing `Syrac(ℤ/3ⁿℤ)` mod `3ᵏ` yields `Syrac(ℤ/3ᵏℤ)`.

**Proof = truncation ∘ marginalization:**
- **`iid_map_castLE`** (general, reusable, private): the prefix-`k` marginal of an iid vector is iid
  — `(p.iid n).map (·∘Fin.castLE h) = p.iid k`. Induction on `k`, front-peel: `iid (m+1) =
  bind a0, cons a0 (iid m)`; the restriction commutes with `Fin.cons` (`hcons`, via `Fin.cons_zero`
  /`Fin.cons_succ` + castLE val-preservation); `PMF.map_bind` + `PMF.map_comp` + IH. Base `k=0` via
  `PMF.map_const` (target `Fin 0 → α` is a subsingleton).
- **truncation** `htrunc`: `castHom` (a ring hom) pushes through `F_n`'s sum; terms `j ≥ k` vanish
  (`3^k = 0` in `ZMod 3ᵏ` via `ZMod.natCast_self`); `φ(3)=3`, `φ(2)=2` (`map_ofNat`), and
  `φ(2⁻¹)=2⁻¹` by right-inverse uniqueness for the unit 2; prefix sums unchanged on first `k`
  coords (`hpre`). So `φ∘F_n = F_k∘restrict`, then compose with the marginal.
- `#print axioms syracZ_map_cast = [propext, Classical.choice, Quot.sound]`; full build green (3282).

**NEXT — the last SyracRV stub, `syracZ_recursion` (Lemma 1.12):** the HARDEST of the three. It
computes the pointwise mass of `syracZ (n+1) x` as a `(1-2^{-2·3ⁿ})⁻¹`-normalized sum over
`a ∈ Icc 1 (2·3ⁿ)` with the divide-by-3 guard `(2^a·x.val)%3=1`. Needs: peel the first geometric
coordinate `a0~Geom(2)` off `iid (n+1)` (`tsum_iid_succ_mul`), reduce the top digit of the offset
`∑_j 3^j 2^{-pre}` mod `3^{n+1}`, isolate the `x`-fiber (the `2^{a0}·(rest) ≡ 3·(inner) + ...`
congruence), and resum the geometric tail `a0 > 2·3ⁿ` giving the normalization. Route sketch above;
expect multi-lap. The `iid_apply_eq_prod`/`iid_map_castLE`/`syracZ_eq_rev_fnat` machinery is reusable.

## Lap fruit-2 (2026-07-14): **Syracuse (1.21) `syracZ_eq_rev_fnat` PROVED (axiom-clean)** — SyracRV stub 1/3

Objective-3 fruit, SyracRV stub 1 of 3. Closed `syracZ_eq_rev_fnat` (`Syracuse/SyracRV.lean`):
the paper-(1.21) bridge showing the (1.26)-**reversed** offset law `Syrac(ℤ/3ⁿℤ)` agrees in law
with the `fnat`-based forward-offset form. NOT a pointwise identity (checked n=2 — the two
functions differ); it is genuinely **distributional**, and the reversal is essential.

**Proof shape (exchangeability):**
- **Pointwise** `hkey : ∀ b, g b = f (b ∘ Fin.rev)` where `f` = reversed summand, `g` = fnat summand.
  Pure `ZMod (3ⁿ)` algebra: reflect the `fnat` sum (`Finset.sum_range_reflect`), then per term the
  exponent identity `2^P·(2⁻¹)^(Q+P) = (2⁻¹)^Q` using `2·2⁻¹=1` (2 is a unit mod 3ⁿ via
  `ZMod.isUnit_iff_coprime` + `Nat.Coprime.pow_right`).
- **Prefix-split lemma** `pre_comp_rev : pre (a∘Fin.rev) m + pre a (n-m) = pre a n` (ℕ backbone of
  exchangeability): reflect + `sum_Ico_eq_sum_range` + `sum_Ico_consecutive`.
- **Law invariance** `iid_map_rev : (p.iid n).map (·∘Fin.rev) = p.iid n` via `iid_apply_eq_prod`
  (product form) + `Fintype.prod_equiv Fin.revPerm`. Then `iid.map g = iid.map (f∘rev)
  = (iid.map rev).map f = iid.map f = syracZ n` (`PMF.map_comp`).
- Refactor: moved `iid_apply_eq_prod` up to `Prob/Basic.lean` (namespace `PMF`) so SyracRV can use
  it without importing ValuationDist (import cycle); ValuationDist re-exports it. Full build green
  (3282), `#print axioms syracZ_eq_rev_fnat = [propext, Classical.choice, Quot.sound]`.

**NEXT in SyracRV:** `syracZ_map_cast` (1.22 projection compat) and `syracZ_recursion` (Lemma 1.12).
The recursion is the meatier one (divide-by-3 guard, geometric normalization `(1-2^{-2·3ⁿ})⁻¹`).

## Lap fruit-1 (2026-07-14): **Collatz (1.2) `colMin_eq_syrMin_oddPart` PROVED (axiom-clean)** — spine stub C1 closed

With §7 done, pivoted to objective 3 (fruit). Closed the paper-(1.2) spine stub
`colMin_eq_syrMin_oddPart : colMin N = syrMin (oddPart N)` (`Basic/Collatz.lean`, axiom-clean,
`lake build` green 3282). This is a foundational on-path node (the Collatz→Syracuse reformulation
the whole reduction rests on).

**Proof (two structural facts + `sInf` monotonicity):**
- **Fact A** `col_reaches_syr`: every Syracuse iterate of `oddPart N` is a Collatz iterate of `N`
  (induction on `j`; each step `col` does `3M+1` then halves `padicValNat 2 (3M+1)` times down to
  `oddPart(3M+1)=syr M` via `col_iterate_oddPart`).
- **Invariant B** `oddPart_col_iterate`: the odd part of every Collatz iterate is a Syracuse
  iterate (induction on `k`; `oddPart` invariant under halving, and on odds `col x=3x+1` gives
  `oddPart=syr x`).
- Then: `colMin ≤ syrMin` since `{syr iterates} ⊆ {col iterates}` (Fact A, `Nat.sInf_mem`+`Nat.sInf_le`);
  `syrMin ≤ colMin` since `colMin` is attained and its odd part `≤` it is a `syr` iterate (Invariant B).
- New helpers (all axiom-clean, `Basic/Collatz.lean`): `padicValNat_two_of_odd`, `oddPart_of_odd`,
  `padicValNat_two_two_mul`, `oddPart_two_mul`, `col_pos`, `col_iterate_pos`, `syr_iterate_pos`,
  `col_iterate_oddPart`.

### NEXT — remaining spine stubs / fruit (objective 3):
- `Syracuse/SyracRV.lean` (3 sorries: `syracZ_map_cast`, `syracZ_recursion`, `syracZ_eq_rev_fnat`) —
  foundational Syracuse-random-variable identities. Likely tractable next.
- `Sec6/MixingFromDecay.lean` `fine_scale_mixing`, `Sec5/FirstPassage.lean` `stabilization` (Prop 1.11)
  + `logUnifOdd` normalization — the two big ones are HEROIC analytic (multi-lap); `logUnifOdd`
  normalization needs a `dite` refactor to bring the nonempty hyp into scope.
- `Sec7/White.lean`, `Sec7/Reduction.lean`, `Sec7/BlackEdgeQ.lean`, `Prob/Basic.lean` each carry a
  sorry — inventory the on-path ones.
- **The `ManyTriangles.lean` split** (5,519 lines, zero-risk hygiene) — DIRECTION obj-3 item 1.
- **Pin C8** (§5 first-passage) — mark `RATIFY-C8`, never `\leanok`.

## Lap X11d-DONE (2026-07-14): **🏆🏆 §7 MONOTONICITY COMPLETE — `prop_7_8` AXIOM-CLEAN, Case3.lean SORRY-FREE**

The sole remaining §7 leaf `col_tail_mass_le` (7.54 bad-column Gaussian tail) is PROVED and
axiom-clean. **`Case3.lean` is now SORRY-FREE.** The whole §7 spine goes axiom-clean
(`[propext, Classical.choice, Quot.sound]`, judge-to-verify):
`col_tail_mass_le → few_white_mass_le → Q_black_edge_case3 → prop_7_8`. `lake build` green (3282).
Commit `b0ea748`. **This is the campaign's spine — the §7 crux (X8/X10/X11, "the paper's pinnacle",
the 65–75% risk concentration) is DONE.**

### col_tail proof (standard super-exponential tail, `Case3.lean`)
- Walk→fpDistPlus marginal via `fpDist_walk_eq_fpDistPlus` at `p=P`.
- Containment `{0.9m ≤ x.1} ⊆ {2D ≤ |x.1−s/4|}` with `D=m/40`, using budget `s < 3.2(m+2)`
  (from `s·log2 ≤ (m+2)log9` [=hs2] and `log9 < 3.2·log2` via `9^5 < 2^16`).
- `fpDistPlus_col_tail` gives `C(exp(−cD²/(1+s))+exp(−cD))`; both `≤ exp(−(c/16960)m)` since
  `1+s ≤ 10.6m`; closed by NEW helper `exp_neg_mul_le_rpow_neg` (poly beaten by super-exp,
  extracted from `hold_fst_tail_le`'s `hclose`) → `≤ m^{−A}/2`.

### NEXT — §7 is done, so PIVOT TO OBJECTIVE 3 (DIRECTION.md): burn down the fruit
Now that the campaign's hardest crux is closed, DIRECTION objective 3 is the order:
1. **The `ManyTriangles.lean` split** (5,519 lines; queued 6+ laps). Pure moves, verbatim names,
   thin re-export shim. Zero mathematical risk.
2. **The spine stubs** (downstream, cheap): `Syracuse/SyracRV.lean` (sorries), `Sec5/FirstPassage.lean`,
   `Sec6/MixingFromDecay.lean`, `Basic/Collatz.lean`. Also `Sec7/White.lean`, `Sec7/Reduction.lean`,
   `Sec7/BlackEdgeQ.lean`, `Prob/Basic.lean` each carry a sorry — inventory and attack the on-path ones.
3. **Pin C8** (§5 first-passage, the last un-pinned node) — mark `RATIFY-C8`, never `\leanok`.
The remaining `sorry` census (src): Statement.lean(2 headlines, GATED), SyracRV, FirstPassage,
MixingFromDecay, Collatz, White, Reduction, BlackEdgeQ, Prob/Basic. Check the critical path
`S3 → X6 → {X8,X10} → X11 → C10 → C9 → C6 → Statement` — which downstream nodes now unblock.

## Lap X11d-assembly (2026-07-14): **🏆 (7.56) CRUX `few_white_mass_le` ASSEMBLED — §7 crux now hinges on ONE leaf**

The deepest leaf `few_white_mass_le` (7.56) is now **kernel-checked assembly** from its three proved
component terms + the pointwise split. `lake build` green (3282 jobs). Case3 sorries **2 → 1**
(only `col_tail_mass_le` remains). `#print axioms few_white_mass_le` = `[propext, sorryAx,
Classical.choice, Quot.sound]` — the `sorryAx` is SOLELY via `col_tail_mass_le` (no new sorry
introduced by the assembly).

### What landed
- **Moved `col_tail_mass_le` above `few_white_mass_le`** (it doesn't depend on few_white) so the
  assembly can consume its bad-column term.
- **Assembly recipe executed** exactly as decomp-6 §NEXT: `A' = 2A+A₀` (from estar), `K = ⌈(A+3)log10/ε³⌉`
  (the goal threshold), `R = ⌈((K+1)+(A+5)log10+2)/ε₀⌉`, `P = encWindowIter A' (K+1) R`,
  `Cthr = max(Cthr_e, Cthr_c, 10g, ⌈B^2.5⌉, ⌈10·500^{1/A}⌉)` where `B := 4^{A'}(1+P)³`.
- **Pointwise split** `few_white_pointwise_split` applied inside `Σe fpDist Σv hold·` with per-v support
  casing (v∉support ⟹ hold.iid=0), then tsum-linearity → three terms: reach (`few_white_reach_mass_le`,
  ≤10^{−A−3}), E∗ (`few_white_estar_mass_le`, ≤10^{−A−3}), bad-column (`col_tail_mass_le` ≤ m^{−A}/2,
  bridged to ≤10^{−A−3} via the numeric `m^{−A}/2 ≤ 10^{−A−3}` for m ≥ ⌈10·500^{1/A}⌉). Sum
  `3·10^{−A−3} ≤ 10^{−A−2}`. ✓
- **Cthr threading**: the deep bridge lives inside `few_white_estar_mass_le` (bakes Cthr=10^30);
  the `hreg` discharge (⌊4^{A'}(1+p)³⌋ ≤ (m+1)^0.4) closes via `Cthr ≥ ⌈B^2.5⌉` (B = 4^{A'}(1+P)³ a
  fixed constant, (m+1)^0.4 ≥ B^{2.5·0.4}=B); `hg: g ≤ 0.1m` via `Cthr ≥ 10g`.

### NEXT — the SOLE remaining §7 leaf: `col_tail_mass_le` (Case3.lean:~2093), the (7.54) bad-column tail
`Σe fpDist Σv hold·1_{0.9m ≤ e.1+(pathSum v P).1} ≤ m^{−A}/2` for m ≥ Cthr. Standard Gaussian tail:
bridge walk→marginal via `fpDist_walk_eq_fpDistPlus`, then `fpDistPlus_col_tail` (deviation D≍m via
`budget_le_of_mem_triangle`: s·log2≤(m+2)log9, so s=O(m) and advancing past 0.9m is a large deviation),
then `exp(−cm) ≤ m^{−A}/2` via `exp_neg_mul_le_of_large`/`log_le_eps_mul_of_large` (both `BlackEdge.lean`).
⚠ The col event is `0.9m ≤ e.1+(pathSum v P).1` (walk displacement); under the marginal law this is
`fpDistPlus s P`'s first coord — align with `fpDistPlus_col_tail`'s deviation form. When it lands,
`few_white_mass_le → damping_expectation_le → … → Q_black_edge_case3 → prop_7_8` all go axiom-clean and
**§7 monotonicity is DONE**.

## Lap X11d-repair (2026-07-14): **JUDGE PASS 26 REPAIR DONE — `_rpow` engines split out, Lemma 7.10/X10a pins RESTORED byte-identical (`4f51542`, green 3282 jobs)**

Executed the judge-mandated repair of `61f8e80` (which had edited four ratified pins). Now HARD RAIL 6
compliant: ratified pins are immutable. All seven touched decls `#print axioms` clean (believed clean,
judge to verify), both pin statements verified **byte-identical to `e08871e`** (re-ratifies X10/X10a).

- **Engine layer** (deep hyp `(depth)^0.8 < s`, proofs unchanged, just renamed): `triangle_encounter_le_rpow`,
  `encounter_apex_proximity_rpow` (ManyTriangles), `bigTriangle_walk_le_rpow`, `estar_union_le_rpow` (Case3).
  The Case-3 chain (`bigTriangle→estar→few_white_estar_mass_le`) consumes these `_rpow` forms.
- **Pin layer** (deep hyp `m/log²m < s`, e08871e statements): `encounter_apex_proximity` = e08871e proof
  VERBATIM (its deep-hyp use derives `m^0.4 ≤ 12s` directly for all m — a `_rpow` corollary would fail on
  small m where `m^0.8 > m/log²m`). `triangle_encounter_le` = thin corollary of `_rpow` (LHS is a
  sub-probability): m ≥ 10^27 bridges via `log_sq_le_rpow`; m < 10^27 gives `LHS ≤ 1 ≤ maxC/s'` with
  `maxC := max C_eng 10^11 > m^0.4 ≥ s'`.
- These pins are STANDALONE (nothing consumes them) — they formalize the paper's Lemma 7.10 / (7.63)–(7.65).

### NEXT (unchanged crux) — `few_white_mass_le` (7.56) ASSEMBLY (all 3 terms + split exist, `_rpow` chain wired)
See the decomp-6 assembly recipe below. Cthr must include `10^27` so the depth-`m+1` bridge
`(m+1)^0.8 ≤ 2m^0.8 ≤ m/log²m < s` closes (judge pass 26 step 3, still unproved, lives in the two Case3
sorries `few_white_mass_le`@2111, `col_tail_mass_le`@2258). `few_white_estar_mass_le` already bakes
Cthr=10^30 for its own bridge; thread ≥10^27 through the outer assembly + col_tail.

## Lap X11d-decomp-6 (2026-07-14): **E∗ TERM `few_white_estar_mass_le` FULLY PROVED (axiom-clean) + route-decisive deep-hyp generalization**

Two advances on the (7.56) crux `few_white_mass_le`, both axiom-clean, `lake build` green (3267 jobs):

### 🔑 ROUTE-DECISIVE FINDING (corrects a prior-lap error): the deep-hyp reconciliation
`m/log²m < s ⟹ (m+1)/log²(m+1) < s` is **FALSE**, NOT a "small gap bridgeable via Cthr" as
decomp-5's handoff claimed. Counterexample: `x/log²x` is increasing, so for `s` = least nat `>
m/log²m` and `m` chosen so `frac(m/log²m)` is within `1/log²m` of 1, `(m+1)/log²(m+1) ≥ s`. The
E∗ term needs `estar_union_le` at depth `n/2−j = m+1` (triangle at `n/2−m−1`, phase `−1` shift),
which the frozen regime `m/log²m < s` cannot supply in the strong `/log²` form.
**FIX (legitimate generalization, NOT a weakening):** both consumers of the X10 deep hyp use only
a WEAK power bound — `triangle_encounter_le` via `m^0.8 < s` (its `hsdeep`), `encounter_apex_proximity`
via `m^0.4 ≤ 12s`. Generalized the deep hyp of `encounter_apex_proximity`, `triangle_encounter_le`
(both `ManyTriangles.lean`), `bigTriangle_walk_le`, `estar_union_le` (both `Case3.lean`) from
`(depth)/log²(depth) < s` to `(depth)^0.8 < s`. This IS bridgeable: `(m+1)^0.8 ≤ 2m^0.8 ≤ m/log²m < s`
for `m ≥ Cthr` (proved inside few_white_estar via `log m ≤ 20m^0.05`, Cthr = 10^30). Commit `61f8e80`.

### E∗ term `few_white_estar_mass_le` (`Case3.lean`, axiom-clean) — the middle term of the split
`Σe fpDist Σv hold·(Σ_{p<P+1} indicator bigTri(⌊4^A'(1+p)³⌋)(n/2−m−1+…)) ≤ 10^{−A−3}`, with A' EXPOSED.
- **Algebra** (`fbda427`): tsum↔finite-sum swap (`Summable.tsum_finsetSum`) turns inner `Σ_p` into the
  outer union `estar_union_le` bounds at `j=n/2−m−1`, `T=P`, `A=A'`; `ENNReal.toReal_sum` bridge;
  deep-hyp bridge above; `ENNReal.le_ofReal_iff_toReal_le`.
- **Numeric** `estar_scaled_numeric` (`8edbdaa`): `C'·A'²·4^{−A'}+C'·exp(−c·A'²) ≤ 10^{−A−3}` ∀A>0 at
  A'=2A+A₀. Two poly·geom domination helpers (`sq_mul_exp_neg_le`: `x²e^{−bx}≤4/b²`;
  `sq_mul_exp_neg_le_inv`: `≤27/(b³x)`). term1: base-16-beats-10 (`4^{−A'}=4^{−A₀}·16^{−A}`, 16>10),
  cleared-denominator linear-in-A₀ thresholds. term2: complete-the-square `(8cA−log10)²≥0` + `A₀≥√X2`.
  A₀ = max(A₀e, 1, Kthr, √X2), all symbolic in C',c,log4,log10 (no numeral log bounds). HEARTBEAT bump
  (justified, large single-shot chase).

### NEXT — `few_white_mass_le` (7.56) ASSEMBLY, now that all three terms exist:
- **reach term** `few_white_reach_mass_le` ✓ (≤10^{−A−3}), **E∗ term** `few_white_estar_mass_le` ✓
  (≤10^{−A−3}, exposes A'), **bad-column** `col_tail_mass_le` (PROVED ≤m^{−A}/2; + numeric m^{−A}/2 ≤
  10^{−A−3} for m≥Cthr). Pointwise split `few_white_pointwise_split` ✓.
- Assembly: pick `A' = 2A+A₀` (from estar_scaled_numeric via few_white_estar_mass_le's exposed A'),
  `K=⌈(A+3)log10/epsBW³⌉`, `R=⌈((K+1)+(A+5)log10+2)/ε₀⌉`, `P=encWindowIter A' (K+1) R`, Cthr = max of
  the three terms' Cthrs + 10g (for `hg:(g:ℝ)≤0.1m`) + 10^30 (deep bridge). Apply
  `few_white_pointwise_split` inside `Σe fpDist Σv hold·` (per-v support casing: v∉support ⟹ hold.iid=0),
  tsum-linearity (model: `few_white_reach_mass_le`'s wrapping) → reach+E∗+bad, sum `3·10^{−(A+3)} ≤
  10^{−(A+2)}`. ⚠ few_white_estar's `hreg` (∀p≤P, ⌊4^A'(1+p)³⌋ ≤ (m+1)^0.4) discharged since P=O(1) and
  floors bounded by 4^A'(1+P)³ ≤ (m+1)^0.4 for m≥Cthr. ⚠ col_tail is AFTER few_white in the file —
  reorder or forward-ref. Its integrand matches the split's 3rd term exactly.

## Lap X11d-decomp-5 (2026-07-14): **INDEX-SHIFT RECONCILIATION PROVED — `few_white_pointwise_dichotomy` (axiom-clean)**

The "fiddly kernel" the crux `few_white_mass_le` rests on is now a proved, axiom-clean lemma
`few_white_pointwise_dichotomy` (`Case3.lean`, right above the crux). It discharges reconciliations
(a)+(b) from decomp-4's note in one clean combinatorial statement:
- **(a) whiteStrip vs whiteSet∩strip**: NON-issue — `whiteSet n ξ ∩ {q.1≤n/2}` IS `whiteStrip n ξ`
  by definition (`whiteStrip := {p | p.1≤n/2 ∧ p∈whiteSet}`), so the crux's `Set.indicator
  (whiteSet∩{q.1≤n/2})` and the fold's `whiteStrip` membership are the same set (just prove set-eq
  when wiring the tsum).
- **(b) cumWhite = Nw index shift**: SETTLED. With walk dimension `T=P` (forced so the `Fin P→ℕ×ℤ`
  vector types match `estar_union_le`/`reaches_fewWhite_mass_le_ten`), the crux's forward count
  `myNw = Σ_{p<P} 1_{q₀+pathSum v p∈WS}` (positions `pathSum 0..P−1`, includes start `q₀`) and the
  fold's `cumWhite = Σ_{p<P} 1_{q₀+pathSum v (p+1)∈WS}` (`encFold_cumWhite`, positions `1..P`)
  differ ONLY in boundary terms: `cumWhite + 1_{q₀∈WS} = myNw + 1_{q₀+pathSum P∈WS}` (two
  range-succ splits: `sum_range_succ'` + `sum_range_succ`), so **`cumWhite ≤ myNw + 1`**. Hence the
  clean route: feed `deterministic_encounter_or_bigTriangle` at **`K' := K+1`** — its few-white
  hypothesis `cumWhite ≤ K+1` follows from `myNw ≤ K`; `reaches_fewWhite_mass_le_ten` is likewise
  used at `K+1` (its R-bound `K'+(A+3)log10+2 ≤ εR` just needs `R` a bit bigger; the 10^{−(A+1)}
  bound is K-independent). encInit gives `.pos=q₀`, `.cumWhite=0` (`rfl`+`simp[encInit]`).

The lemma output: `myNw ≤ K ⟹ (R ≤ count ∧ cumWhite ≤ K+1) ∨ (∃p≤P, ∃t∈F.T, phase pt ∈ triangle t
∧ 4^A(1+p)³ ≤ t.2.2)`. **NOTE**: it takes the depth hyp `∀p≤P, (q₀+pathSum v p).1+g ≤ n/2` as a
PARAMETER (reconciliation (c) — sourcing it from the Case-3 regime deferred to the tsum assembly),
and takes `A` free (so instantiate at `A'=κA` for the E∗ base-scaling of decomp-3).

### 🔑 ROUTE-DECISIVE FINDING (decomp-5, from paper pp.48–50 read): `few_white_mass_le` is a
**THREE-way split, not two.** The dichotomy `few_white_pointwise_dichotomy` needs the depth hyp
`∀p≤P, (q₀+pathSum v p).1 + g ≤ n/2` (i.e. `e.1+(pathSum v p).1 + g ≤ m`), which **FAILS for
large-displacement (e,v)** — `few_white_mass_le` sums over ALL columns (it's the full damping
expectation; the (7.54) column split in `damping_column_mass_le` already factored out `10^A·m^{−A}`
over ALL e,v, so few_white is genuinely un-restricted). So the pointwise dichotomy is valid ONLY on
the **good column** `{adv := e.1+(pathSum v P).1 < 0.9m}`. There, by `pathSum_fst_le` (JUST ADDED:
`(pathSum v p).1 ≤ (pathSum v P).1` monotone, since hold steps have `.1 ≥ 1` via
`hold_support_fst_pos`), every intermediate `(q₀+pathSum v p).1 = n/2−m+e.1+(pathSum v p).1 ≤
n/2−m+adv < n/2−0.1m`, so `+g ≤ n/2` holds once `g ≤ 0.1m`, i.e. **`Cthr ≥ 10g`**. ✓ Paper matches:
(7.55)/(7.56) are the FULL expectation; the good/bad split only bounds the weight (10^A good vs
exp(−cm) bad mass). So:
`P(myNw≤K) ≤ P(myNw≤K ∧ adv<0.9m) + P(adv≥0.9m) ≤ [reach + E∗] + [bad-column]`, each ≤ 10^{−(A+3)},
sum `3·10^{−(A+3)} = 0.03·10^{−(A+1)} ≤ 10^{−(A+2)}`. ✓ The **bad-column term reuses `col_tail`'s
machinery** (`fpDist_walk_eq_fpDistPlus`→`fpDistPlus_col_tail`, mass of `{adv≥0.9m} ≤ exp(−cm) ≤
10^{−(A+3)}` for m≥Cthr).

### NEXT — the tsum assembly of `few_white_mass_le` (THREE-way, per finding above):
0. **`pathSum_fst_le` + `pathSum_depth_le` DONE** (both axiom-clean). `pathSum_depth_le` takes the
   clean endpoint hyp `q₀.1+(pathSum v T).1+g ≤ half` and gives `∀p≤T, (q₀+pathSum v p).1+g ≤ half`.
   In the assembly instantiate `half=n/2`, `q₀.1=n/2−m+e.1`, `T=P` ⟹ endpoint hyp is `adv+g ≤ m`
   (`adv := e.1+(pathSum v P).1`), which the good column `¬(0.9m ≤ adv)` gives once `g ≤ 0.1m`
   (`Cthr ≥ 10g`) — that last `adv+g≤m` derivation is trivial ℕ/ℝ arithmetic, do it INLINE in step 1.
1. **Pointwise split DONE** (`few_white_pointwise_split`, axiom-clean): `ofReal(1_{myNw≤K}) ≤
   ofReal(1_{reach R ∧ cumWhite≤K+1}) + Σ_{p∈range(P+1)} indicator(bigTriangleSet F ⌊4^{A'}(1+p)³⌋)
   (phase pt at j=n/2−m−1) + ofReal(1_{0.9m≤e.1+(pathSum v P).1})`. Takes `A'` (the scaled exponent),
   `hP : encWindowIter A' (K+1) R ≤ P`, `hg : (g:ℝ) ≤ 0.1·m` (⟸ Cthr≥10g). Also exposed the explicit
   horizon witness: `deterministic_encounter_claim_at` + `few_white_pointwise_dichotomy` now take
   explicit `P` with `encWindowIter A (K+1) R ≤ P` (needed for uniform-P before ∀ n ξ F).
2. **reach term DONE** (`few_white_reach_mass_le`, axiom-clean): `Σe fpDist Σv hold·ofReal(1_{reach∧
   cw≤K+1}) ≤ 10^{−A−3}`. Wraps `reaches_fewWhite_mass_le_ten`@(A+2),K'=K+1 per-e via bridge
   `PMF.toReal_tsum_mul_ofReal` + `Σfpdist=1`. EXPOSES shared `ε₀,g`; R-bound hyp `(K+1)+(A+5)log10+2
   ≤ ε₀R`. Assembly uses this `g` in the split.
3. **E∗ term** ≤ 10^{−(A+3)} (NEXT): `few_white_estar_mass_le` — `Σe fpDist Σv hold·(Σ_{p<P+1}
   indicator bigTri) ≤ 10^{−A−3}`. Swap finite Σ_p ↔ tsums, apply `estar_union_le` @exponent A',
   `j=n/2−m−1`, `T=P`. ✅ **SMALL-A RESOLVED (decomp-6): use `A' := 2A + A₀`** (A₀ ≥ 1 constant from
   estar's A₀ + numeric), NOT κA. Then `A' ≥ 1` ∀A>0 (dichotomy OK) AND `4^{−A'}·10^A =
   4^{−A₀}(10/16)^A` bounded (base 16>10), so `estar_bound(A') ≤ 10^{−A−3}` UNIFORMLY over all A>0 —
   no judge flag. Hard sub-part = the numeric `C'(2A+A₀)²4^{−(2A+A₀)}+C'exp(−c(2A+A₀)²) ≤ 10^{−A−3}`
   (poly·geom bounded ⟹ pick A₀; needs a `x²·r^x` domination lemma). ⚠ deep-hyp reconcile: estar
   wants `(n/2−j)/log(n/2−j)²<s` with n/2−j=m+1; my hyp m/log m²<s — Cthr (x/log x² incr, gap small).
4. **bad-column term** ≤ 10^{−(A+3)}: `col_tail_mass_le` (PROVED, gives ≤ m^{−A}/2) + numeric
   `m^{−A}/2 ≤ 10^{−A−3}` for m≥Cthr(A). Its integrand `ofReal(1_{0.9m≤e.1+(pathSum v P).1})` MATCHES
   the split's third term exactly. ⚠ col_tail is AFTER few_white in the file — must MOVE it before
   (it doesn't depend on few_white), or few_white forward-refs (reorder needed).
5. **Assembly** (`few_white_mass_le` proper): pick `A'=2A+A₀`, `K=⌈(A+3)log10/ε³⌉`, `R=⌈((K+1)+
   (A+5)log10+2)/ε₀⌉`, `P=encWindowIter A' (K+1) R`, `Cthr≥10g` + estar/col_tail Cthrs; apply
   `few_white_pointwise_split` inside `Σe fpDist Σv hold·`(with per-v support casing: v∉support ⟹
   hold.iid=0), tsum-linearity → reach+E∗+bad terms, sum `3·10^{−(A+3)} ≤ 10^{−(A+2)}`.

## Lap X11d-decomp-4 (2026-07-14): **(7.55) COUNT-SPLIT PROVED — crux down to `few_white_mass_le` (7.56) + `col_tail_mass_le`**

`damping_expectation_le` (7.55) is now **kernel-checked assembly** from `few_white_mass_le`
(7.56). Proved this lap (axiom-clean): the paper's count split
`exp(−ε³Nw) ≤ 1_{Nw≤K} + 10^{−(A+3)}` with **`K := ⌈(A+3)·log10/ε³⌉`** (chosen so the tail
`10^{−(A+3)}` fits for ALL A>0 — avoids the small-A failure of the paper's `e^{−10A}` tail),
`PMF`-averaging the constant tail (`Σfpdist=Σhold=1` via `tsum_coe`+`tsum_mul_right`), and the
numeric `10^{−(A+2)} + 10^{−(A+3)} ≤ 10^{−(A+1)}`.

**The §7 crux is now TWO sorries (both `Case3.lean`):**
1. **`few_white_mass_le`** (`:1427`) — **THE deepest leaf (7.56).** `P(Nw≤K) ≤ 10^{−(A+2)}` with
   `K=⌈(A+3)log10/ε³⌉`. Execution plan (all machinery proved & axiom-clean, route validated
   decomp-3): fix `e` (⟹ q₀=(n/2−m+e.1, l+e.2)); apply `deterministic_encounter_or_bigTriangle`
   at `A':=κ·A` (κ=10, base 4^10) and gate `g` from `reaches_fewWhite_mass_le_ten` ⟹ pointwise
   `{Nw≤K} ⊆ {reach R} ∪ {E∗}`; so `1_{Nw≤K} ≤ 1_{reach R ∧ Nw≤K} + 1_{E∗}`; average over e:
   `P(Nw≤K) ≤ P(reach R ∧ Nw≤K) + P(E∗)`. Bound: reach-R via `reaches_fewWhite_mass_le_ten` at
   `A+2` (⟹ 10^{−(A+3)}, needs `R=⌈(K+(A+5)log10+2)/ε⌉`); E∗ via `estar_union_le` at `A'=κA`
   ∘ `bigTriangle_of_encounter` (⟹ ≤ 10^{−(A+3)} for A≥A₀). Sum `2·10^{−(A+3)} ≤ 10^{−(A+2)}`. ✓
   **⚠ RECONCILIATIONS to nail (per decomp-2/3 notes):** (a) whiteStrip vs whiteSet∩strip and
   the p vs p+1 index shift between my `Nw` and the deterministic claim's few-white sum
   (`Σ_{p<T} 1_{q₀+pathSum(p+1)∈whiteStrip}`); (b) `cumWhite = Nw` via `encFold_cumWhite`; (c)
   depth hyp `(q₀+pathSum p).1 + g ≤ n/2` from the regime (needs Cthr, deep start j−1); (d) the
   fpDist-average of the per-e single-walk bounds (Σ_e fpDist·const ≤ const). ⚠ SMALL-A: the
   estar/reaches A₀ thresholds mean this likely needs A≥A₀ (via A'=κA≥A₀_estar); if the
   ∀A>0 statement can't be met for A<A₀ this route, FLAG for judge (don't weaken — Q_black_edge_case3
   is frozen). Probe: does A<A₀ follow trivially / by A-monotonicity? Decompose further if needed.
2. **`col_tail_mass_le`** (`:1577`) — standard Gaussian tail (7.54 bad column), unchanged from
   decomp-3: `fpDist_walk_eq_fpDistPlus` → `fpDistPlus_col_tail` → `exp_neg_mul_le_of_large`.

**NEXT: `few_white_mass_le`.** First move: decompose into the reach-R-mass + E∗-mass pieces
(each fed by the named proved lemma at the scaled A), proving the pointwise `{Nw≤K}⊆{reach R}∪{E∗}`
and the fpDist averaging; the index-shift/whiteStrip reconciliation is the fiddly kernel.

## Lap X11d-decomp-3 (2026-07-14): **(7.54) BRANCH SPLIT PROVED — crux down to the two paper atoms (7.55)/(7.54-tail)**

`damping_column_mass_le` is now **kernel-checked assembly** from TWO sub-lemmas, following
Tao (7.54) exactly. Proved this lap (the assembly, ~230 lines, axiom-clean): the pointwise
column-weight split
`exp(−ε³Nw)·max(n/2−j_end,1)^{−A} ≤ 1_{adv≥0.9m} + 10^A·m^{−A}·exp(−ε³Nw)`
(case `adv≥0.9m`: my ABSOLUTE weight ≤1, exp≤1; case `adv<0.9m`: `n/2−j_end = m−adv > 0.1m` so
weight ≤ (0.1m)^{−A} = 10^A·m^{−A} via `rpow_le_rpow_of_nonpos`), then `tsum_add` split +
factoring `ofReal(10^A m^{−A})` out of the damping sum, then the constant collapse
`10^A·m^{−A}·10^{−A−1} = m^{−A}/10` and final `m^{−A}/2 + m^{−A}/10 ≤ m^{−A}`.

**The §7 crux is now the TWO leaf obligations (both `Case3.lean`):**
1. **`damping_expectation_le`** (`:1423`) — **THE deep piece (7.55/7.56).** `P`-uniform,
   `m`-INDEPENDENT: `E[exp(−ε³Nw)] ≤ 10^{−A−1}` (a constant). This is where ALL the proved
   X11c machinery plugs in. Attack: `E[exp(−ε³Nw)] ≤ P(Nw≤K) + e^{−10A}` (K=⌈10A/ε³⌉; the
   `e^{−10A} ≤ 10^{−A−1}` slack holds for A≥1), then `P(Nw≤K) ≤ P(reach R)+P(E∗)` via
   `deterministic_encounter_or_bigTriangle` (cumWhite=Nw through `encFold_cumWhite`), bounded
   by `reaches_fewWhite_mass_le_ten` + `estar_union_le ∘ bigTriangle_of_encounter`.

   ### ⚠⚠ ROUTE FINDING (2026-07-14, lap decomp-3): **base-4 E∗ threshold is TOO SMALL —
   but the fix needs NO reproving, just A-SCALED instantiation.**
   The E∗ union bound `estar_union_le` gives `P(E∗) ≤ C'·A²·4^{−A} + C'·e^{−cA²}`, and
   `4^{−A} = 10^{−0.6A} ≫ 10^{−A−1}`, so **`A²·4^{−A} > 10^{−A−2}` for ALL A≥1** — the E∗ mass
   at base 4 cannot fit the `damping_expectation_le` budget (worse, its (7.54) contribution
   `10^A·A²4^{−A} = A²·2.5^A → ∞`). Base 4 must become a base `> 10` (column-weight base).
   **KEY: Lemma 7.10 (`bigTriangle_walk_le`) is base-FREE (`s'` is a free ∀-param), and in the
   geometry lemmas `A` enters ONLY through the threshold `4^A`** (`deterministic_encounter_claim`,
   `_or_bigTriangle`, `bigTriangle_of_encounter`, `estar_union_le` all take `A` as a free
   universal, used only in `4^A(1+p)³`). So instantiate them at **`A' := κ·A`** (integer κ, e.g.
   κ=10): since `4^{κA} = (4^κ)^A`, the effective base becomes `4^κ = 4^{10} ≈ 10^6`, giving
   `P(E∗) ≤ C'(κA)²·(4^κ)^{−A} + … = C'κ²A²·10^{−6A}·(…) ≤ 10^{−(A+3)}` for A≥A₀ — NO reproving.
   (Need `A' = κA ≥ A₀_estar/claim`; absorb into `Cthr`/A₀.)
   Likewise **`reaches_fewWhite_mass_le_ten` tunes to `10^{−(A+j)}`** by instantiating at `A+j−1`
   (its `A` is a free universal appearing only in the bound `10^{−(A+1)}` and hyp
   `K+(A+3)log10+2 ≤ εR`; at `A+2` → `10^{−(A+3)}` under `K+(A+5)log10+2 ≤ εR`, so
   `R := ⌈(K+(A+5)log10+2)/ε⌉`).
   **Net assembly closes**: `P(F∗) ≤ 10^{−(A+3)}` [reaches at A+2] `+ P(E∗) ≤ 10^{−(A+3)}` [estar
   at κA] `+ e^{−10A} ≤ 10^{−(A+3)}` [A≥A₀] `= 3·10^{−(A+3)} = 0.03·10^{−(A+1)} ≤ 10^{−(A+1)}`. ✓
   ⚠ shared gate `g`: obtain `g` from `reaches_fewWhite_mass_le_ten` (existential) and pass THAT
   same `g` into `deterministic_encounter_or_bigTriangle` (parameter) — that is why reaches
   provides `g` existentially. P = `_or_bigTriangle` P₀ at `A'=κA` (needs g,R,K,A').
2. **`col_tail_mass_le`** (`:1443`) — standard Gaussian tail (7.54 bad column). `P`-parametric:
   mass{adv ≥ 0.9m} ≤ m^{−A}/2 for m≥Cthr. Bridge walk→marginal via `fpDist_walk_eq_fpDistPlus`,
   then `fpDistPlus_col_tail` (dev D≍m, via `budget_le_of_mem_triangle`: s·log2≤(m+2)log9), then
   `exp(−cm) ≤ m^{−A}/2` via `exp_neg_mul_le_of_large`/`log_le_eps_mul_of_large` (both in
   `BlackEdge.lean`). NOTE the col event is `0.9m ≤ e.1+(pathSum v P).1` (walk displacement),
   which under the marginal law is `fpDistPlus`'s first coord — align with `fpDistPlus_col_tail`'s
   `|e.1 − s/4| ≥ 2D` deviation form (s = O(m) via (7.52), so 0.9m advance ⟹ large deviation).

**NEXT: `damping_expectation_le`** (hardest-first). First move: state the {Nw>K}/{Nw≤K} split
as a pointwise `exp(−ε³Nw) ≤ 1_{Nw≤K} + e^{−ε³K}` bound, reduce to `P(Nw≤K) ≤ 10^{−A−1}−e^{−10A}`,
then wire `deterministic_encounter_or_bigTriangle`. Decompose further if the constant chase bites.

## Lap X11d-decomp-2 (2026-07-14): **(7.54) COLUMN PEEL PROVED — crux narrowed to `damping_column_mass_le`**

`damped_iter_expectation_le` is now **kernel-checked assembly** from ONE deeper sub-lemma.
Proved this lap: the (7.54) end-value peel `Q(end) ≤ max(n/2−j_end,1)^{−A}·Q_{m−1}`
(`Q_le_Qm`, applied per-path with support casing: off-support `hold.iid=0`, on-support the
walk advances ≥ P ≥ 1 steps via `pathSum_fst_ge`+`PMF.iid_support_coord` so the
`n/2−(m−1) ≤ j_end` hyp holds) + factoring the constant `ofReal Q_{m−1}` out of the
double tsum (`ENNReal.tsum_mul_left` + `mul_left_comm`) + `ofReal_mul` bookkeeping.

**SOLE remaining §7 sorry is now `damping_column_mass_le`** (`Case3.lean:1433`): the pure
mass estimate
`Σ_e fpDist s e · Σ_v hold.iid P v · ofReal(exp(−ε³·Nw)·max(n/2−j_end,1)^{−A}) ≤ ofReal(m^{−A})`.
No `Q`, no `Qm` — just first-passage ⊗ Hold-walk masses. This is the (7.55)–(7.67) numerics.

### NEXT — attack `damping_column_mass_le` (all ingredients proved & axiom-clean):
1. **damping split by white count** `K=⌈10A/ε³⌉`: on `{Nw>K}` the exp factor ≤ `e^{−10A}`;
   the column weight `max(n/2−j_end,1)^{−A} ≤ (n/2−m)^{−A}·(…)`... actually weight ≤ 1 when
   j_end ≤ n/2−1 (max ≥1). Cleanest first probe: bound `max(..)^{−A} ≤ 1` (since max ≥ 1 and
   −A<0), reducing to `Σ_e fpDist Σ_v hold·ofReal(exp(−ε³Nw)) ≤ m^{−A}` — the **pure damping
   expectation** ≤ m^{−A}. THAT is the (7.55)–(7.56) heart; but note weight≤1 alone is too
   lossy (loses the m^{−A}); the m^{−A} MUST come from the column weight, not damping. So the
   real split keeps the column weight and uses `Nw` damping only to kill the E∗/reach-R mass.
2. **few-white geometry** `{Nw≤K} ⊆ {reach R} ∪ {E∗}`
   (`deterministic_encounter_or_bigTriangle`, `cumWhite=Nw` via `encFold_cumWhite`); masses
   `reaches_fewWhite_mass_le_ten` (≤10^{−(A+1)}) + `estar_union_le ∘ bigTriangle_of_encounter`
   (at `j−1` phase shift). `R=⌈(K+(A+3)log10+2)/ε⌉`.
3. **column tail**: bad column `j_end ≥ 0.9m` has mass `O(e^{−cm})` (`fpDistPlus_col_tail` at
   dev≍m via `budget_le_of_mem_triangle`: `s·log2 ≤ (m+2)log9`); on complement weight ≤ 10^A.
   The `m^{−A}` target = column weight `(0.1m)^{−A}·10^A`-ish tightened; reconcile constants.
**⚠ The m^{−A} bookkeeping is the subtle part** — study the paper's (7.54)–(7.56) exact
constant chase (pp.48–49) before coding; the current `damping_column_mass_le` statement bakes
in the column weight so the m^{−A} is available. `P` = `deterministic_encounter_or_bigTriangle`
`P₀`; `Cthr` for regime plumbing (⌊4^A(1+p)³⌋≤m^{0.4}; X10 deep hyp at j−1).

## Lap X11d-decomp-1 (2026-07-14): **X11d ENTRY REDUCTION (7.53) PROVED — crux isolated as `damped_iter_expectation_le`**

`Q_black_edge_case3` no longer has a raw `sorry`: it is now **kernel-checked assembly**
from ONE named sub-lemma. The (7.53) entry (`Q_le_damped_iter`) + `ENNReal.ofReal` strip
(`ofReal_le_ofReal_iff`, RHS-nonneg via `Real.rpow_nonneg`+`Qm_nonneg`) are proved. The
SOLE remaining §7 sorry is now **`damped_iter_expectation_le`** (`Case3.lean:1435`), the pure
first-passage⊗Hold-walk expectation estimate ≤ `m^{−A}·Q_{m−1}`, stated in `ofReal`/tsum
form that composes verbatim with `Q_le_damped_iter`'s RHS (half=n/2, W=whiteSet, ε=epsBW,
j=n/2−m). `#print axioms prop_7_8` still carries `sorryAx` solely via this one lemma.

### NEXT — decompose `damped_iter_expectation_le` into the three attack-path pieces:
1. **(7.54) column split**: end value `Q(end)` → weight `max(1−j_end/m,1/m)^{−A}·Q_{m−1}`;
   bad column `j_end ≥ 0.9m` has mass `O(e^{−cm})` (`fpDistPlus_col_tail`,
   `budget_le_of_mem_triangle`); on its complement weight ≤ 10^A.
2. **damping split by white count** `K=⌈10A/ε³⌉`: `{Nw>K}` integrand ≤ `e^{−10A} ≤ 10^{−(A+1)}`.
3. **few-white geometry** `{Nw≤K} ⊆ {reach R} ∪ {E∗}`
   (`deterministic_encounter_or_bigTriangle`, `cumWhite=Nw` via `encFold_cumWhite`); masses
   bounded by `reaches_fewWhite_mass_le_ten` and `estar_union_le ∘ bigTriangle_of_encounter`
   (latter at `j−1` phase shift). `R=⌈(K+(A+3)log10+2)/ε⌉`.
Horizon `P` = the `deterministic_encounter_or_bigTriangle` `P₀` (needs g,R,K,A); `Cthr`
large enough for regime plumbing (⌊4^A(1+p)³⌋ ≤ m^{0.4} for p≤P; X10 deep hyp at j−1).
**Study first**: `encFold_cumWhite`, `fpDistPlus_col_tail`, `budget_le_of_mem_triangle`,
and how `Q(end)`'s tsum indexes relate to `deterministic_encounter_or_bigTriangle`'s `v`.

## Lap review+X11a+X11c (2026-07-14): **X11a + ALL X11c sub-machinery PROVED (axiom-clean) — only the X11d body remains**

**This lap landed 10 axiom-clean lemmas.** ALL X11 sub-machinery is now in place; the
SOLE remaining piece is the X11d body assembling `Q_black_edge_case3`. **⚠ estar_union_le
was FLOOR-corrected** (was ceil — wrong threshold; ceil gives a set that does NOT contain
the geometry-join E∗). Now `bigTriangleSet ⌊4^A(1+p)³⌋` CONTAINS the E∗ event.

### X11 sub-machinery inventory (all axiom-clean, `Case3.lean`) — READY for X11d:
- **X11a `estar_union_le`** (FLOOR): `Σ_p (E∗ walk mass at ⌊4^A(1+p)³⌋).toReal
  ≤ 4C·A²·4^{−A} + 4C·exp(−cA²)`. Helpers `sum_inv_sq_le_two`, `sum_geom_pow_le`.
- **X11c Markov**: `reaches_fewWhite_mass_le_ten` — mass of {reach R ∧ ≤K whites}
  ≤ 10^{−(A+1)} when `εR ≥ K+(A+3)log10+2`. (Chain: `encVal_ge_of_reaches` →
  `reaches_fewWhite_mass_le` (via `fstar_markov`) → `fewWhite_num_closure`.)
- **X11c geometry**: `deterministic_encounter_or_bigTriangle` — pointwise
  {depth}∩{few white} ⟹ {reach R} ∨ {∃p≤T, phase point ((pos p).1−1,·) ∈ triangle t
  with real size ≥ 4^A(1+p)³}.
- **X11c bridge**: `bigTriangle_of_encounter` — that E∗ disjunct (real threshold) ⟹
  `phase point ∈ bigTriangleSet F ⌊4^A(1+p)³⌋` (`⌊x⌋≤x≤t.2.2`). Feeds `estar_union_le`.

### THE remaining piece: **X11d body** = `Q_black_edge_case3` (`Case3.lean` ~line 1290)
This is the full (7.53)–(7.67) assembly. Attack path:
1. **Entry**: `Q_le_damped_iter (n/2) (whiteSet n ξ) epsBW _ s P (n/2−m) l` gives
   `ofReal(Q …) ≤ Σ_e fpDist s e · Σ_v hold.iid P v · ofReal(exp(−ε³·Nw(e,v))·Q(end))`,
   where `Nw(e,v) = Σ_{p<P} 1_{whiteSet∩strip}(pos p)`, `pos p = (n/2−m)+e.1+pathSum.1, …`.
   Choose `P = encWindowIter epsBW K R`-ish (the deterministic-claim horizon `P₀`), and
   `K=⌈10A/epsBW³⌉`, `R=⌈(K+(A+3)log10+2)/epsBW⌉` (matches `fewWhite_num_closure` hyp).
2. **(7.54) end-value**: `Q(end) → m^{−A}·Q_{m−1}·max(1−j_end/m,1/m)^{−A}` via `Q_le_Qm`/(7.38);
   the event `j_end ≥ 0.9m` has mass `O(e^{−cm})` (`fpDistPlus_col_tail` at dev ≍ m, using
   `budget_le_of_mem_triangle`: `s·log2 ≤ (m+2)log9`); on its complement weight ≤ 10^A.
3. **Damping bound** (the heart): `E[exp(−ε³ Nw)] ≤ 10^{−(A+1)}·(1+…)`. Split by white count:
   - {Nw > K}: integrand < exp(−ε³K) ≤ exp(−10A) ≤ 10^{−(A+1)} (K=⌈10A/ε³⌉). Contributes ≤ that.
   - {Nw ≤ K} (few white, cumWhite=Nw via `encFold_cumWhite`): use
     `deterministic_encounter_or_bigTriangle` (needs depth — from the good column branch,
     `j_end<0.9m` ⟹ depth ≥ 0.1m ≥ g): {few white} ⊆ {reach R} ∪ {E∗}. Then
     {reach R ∧ few white} mass ≤ 10^{−(A+1)} (`reaches_fewWhite_mass_le_ten`); {E∗} mass ≤
     `estar_union_le` (via `bigTriangle_of_encounter`, applied at `j−1` for the phase point).
   Sum the three ≤ (const)·10^{−(A+1)} ≤ 10^{−A−1}, giving `Q ≤ m^{−A}·Q_{m−1}`.
4. **Regime plumbing**: `Cthr` large enough that `⌊4^A(1+p)³⌋ ≤ (n/2−(m+1))^{0.4}` for all p≤P
   (horizon P=O_{A,ε}(1), so O(1) ≤ m^{0.4}); `s>m/log²m` ⟹ X10 deep hyp at j−1 (m+1/log²(m+1)).

**Study first for X11d**: `Q_le_damped_iter` exact form (done — see above), `Q_le_Qm`/(7.38),
`fpDistPlus_col_tail`, `budget_le_of_mem_triangle`, `encFold_cumWhite` (cumWhite=Nw link),
and the `hold.support` depth facts. This is a LARGE integration — decompose into named
sub-`sorry`s in `Case3.lean` (raising the src count is PROGRESS) rather than one monolith.

**NEXT: X11d body.** First move: decompose `Q_black_edge_case3` into named sub-lemmas
(entry reduction, column split, damping split), each a `sorry`, then discharge the tractable ones.

**X11c Markov/F∗ side — COMPLETE (all axiom-clean, `Case3.lean`):**
- **`encVal_ge_of_reaches`**: `{R ≤ count ∧ cumWhite ≤ K} → encVal ε R ≥ e^{−K+εR}`
  (banked ≤ cumWhite via `encFold_banked_le`; `min(count,R)=R`). The F∗ containment.
- **`reaches_fewWhite_mass_le`**: joint-walk mass of {reach R ∧ few white}
  `≤ e^{2ε}/e^{−K+εR}` — `fstar_markov` at `lam=e^{−K+εR}` through the containment.
  (Summability idiom copied from `encExpect_le`: `ENNReal.summable_toReal` +
  `Summable.of_nonneg_of_le` + `Summable.tsum_le_tsum`.)
- **`fewWhite_num_closure`**: `e^{2ε}/e^{−K+εR} ≤ 10^{−(A+1)}` when `εR ≥ K+(A+3)log10+2`
  (i.e. `R:=⌈(K+(A+3)log10+2)/ε⌉`); `e^a/e^b=e^{a−b}`, `10^x=e^{x log10}`, slack `2ε−2≤0`.
- **`reaches_fewWhite_mass_le_ten`** (capstone): mass of {reach R ∧ few white} `≤ 10^{−(A+1)}`.

**REMAINING for X11 (two pieces):**
1. **X11c geometry join** (NEXT): use `deterministic_encounter_claim` (✓) contrapositive —
   on {depth (i)} ∩ {outside E∗ (ii)}, ¬reach R ⟹ ¬few-white (>K whites). So
   {depth}∩{outside E∗} ⊆ {reach R} ∪ {many white}. Combined with
   `reaches_fewWhite_mass_le_ten` (reach-R mass ≤ 10^{−(A+1)}) and `estar_union_le`
   (E∗ mass ≤ 2C·A²·4^{−A}+2C·exp(−cA²)), bound the damping expectation. **⚠ reconcile:**
   the deterministic claim's cond (ii) is the PHASE point `((pos p).1−1,…)` and strict
   `t.2.2 < 4^A(1+p)³`, while `estar_union_le` bounds the POSITION in `bigTriangleSet ⌈…⌉`
   (ceil). Bridge the −1 shift and ceil-vs-strict (`⌈x⌉ ≥ x`, and `t.2.2 < x ≤ ⌈x⌉`... note
   direction: need `¬(t.2.2 < 4^A(1+p)³)` ⟺ big triangle; align with `s'≤t.2.2` in `bigTriangleSet`).
2. **X11d body** = `Q_black_edge_case3`: `Q_le_damped_iter` (7.53) + (7.54) col split
   (`fpDistPlus_col_tail`, `budget_le_of_mem_triangle`) + few-white damping (weights ≤ m^A/10^A)
   + the X11c damping bound. **First move:** map the exact structure of `Q_black_edge_case3`'s
   goal onto the walk expectation; identify how the damping factor `exp(−ε³Σ1_W)` and the
   (7.54) `max(1−j/m,1/m)^{−A}` weight are consumed.

**NEXT: the X11c geometry join** — state the damping-expectation bound joining
`deterministic_encounter_claim` + `estar_union_le` + `reaches_fewWhite_mass_le_ten`,
handling the phase −1 shift and ceil-vs-strict reconciliation.

### (prior sub-note) Lap review+X11a: `estar_union_le` PROVED

Review lap confirmed direction sound (recent laps drove the X11 crux, not side-leaves;
`#print axioms` re-run confirms `prop_7_8` carries `sorryAx` solely via
`Q_black_edge_case3`). STATUS.md + DIRECTION.md refreshed. Then **landed X11a**:

**`estar_union_le`** (`Case3.lean`, axiom-clean): sums the per-`p` `bigTriangle_walk_le`
over `p ∈ range(T+1)` at `s' = ⌈4^A(1+p)³⌉₊`. Result:
`Σ_p (walk mass in bigTriangleSet).toReal ≤ 2C·A²·4^{-A} + 2C·exp(-c·A²)` (`C',c,A₀`
existential, `C'=2C` from X10's `bigTriangle_walk_le`, `A₀ = max A₀_X10 √(log2/c)`).
Two axiom-clean series helpers proved en route:
- **`sum_inv_sq_le_two`**: `Σ_{p<T+1} 1/(1+p)² ≤ 2` (telescoping induction `≤ 2−1/(T+1)`,
  step `1/(k+2)²+1/(k+2) ≤ 1/(k+1)` via `div_le_div_iff₀`+`nlinarith`).
- **`sum_geom_pow_le`**: `Σ_{p<T+1} r^{1+p} ≤ 2r` for `0≤r≤1/2` (partial ≤ geometric
  tsum `(1-r)⁻¹` via `Summable.sum_le_tsum`+`tsum_geometric_of_lt_one`, then `(1-r)⁻¹≤2`).
Assembly: per-`p` `hbig` from X10; `Finset.sum_add_distrib` split; poly branch bounds
`A²(1+p)/s' ≤ A²·4^{-A}·(1/(1+p)²)` termwise (`Nat.le_ceil`, `gcongr`, `Real.rpow_neg`);
exp branch rewrites `exp(-cA²(1+p)) = exp(-cA²)^(1+p)` (`Real.exp_nat_mul`) then geometric.
The `r=exp(-cA²)≤1/2` threshold uses `A ≥ √(log2/c)` ⟹ `c·A²≥log2`.

**X11 (`Q_black_edge_case3`, `Case3.lean`) — X11a NOW ✓; remaining X11c + X11d:**
- **X11c `few_whites_le`** (NEXT): the (7.56) join. `fstar_markov` (✓, gives F∗-mass
  `≤ e^{2ε}/lam` with fixed gate `g`) + `deterministic_encounter_claim` (✓, being OUTSIDE
  E∗ i.e. cond (ii) forces the fold to reach count R). Plan: `K=⌈10A/epsBW³⌉`,
  `R:=⌈(K+(A+3)log10+2)/ε⌉` so {fold reaches R} ⊆ {encVal ≥ lam=e^{-K+εR}} = F∗ via
  `encFold_banked_le` (`Case3.lean:132`) + `encVal` def (`ManyTriangles.lean:360`); then
  `fstar_markov` at that `lam` bounds the reaches-R mass; on the complement of E∗ ∪ {reaches R},
  the deterministic claim gives a contradiction ⟹ few whites (≤ K). **Study first:**
  `encVal`/`encInit` defs, `encFold_banked_le`/`encFold_cumWhite` (`Case3.lean:132,156`),
  how `deterministic_encounter_claim`'s conds (i)/(ii)/(iii) wire to the fold count.
- **X11d body** = `Q_black_edge_case3`: `Q_le_damped_iter` (7.53) + (7.54) col split
  (`fpDistPlus_col_tail`, `budget_le_of_mem_triangle`) + few-white damping (weights ≤ m^A/10^A)
  + X11a (✓) + X11c. **⚠ two reconciliations:** the E∗ event uses the PHASE point
  `((pos p).1−1,…)` (per claim cond (ii)) while `bigTriangle_walk_le`/`estar_union_le` bound the
  POSITION (−1 shift); and `bigTriangleSet ⌈4^A(1+p)³⌉` (ceil) vs the claim's strict
  `t.2.2 < 4^A(1+p)³`. X11d must bridge both.

**Proved X11 machinery (all axiom-clean):** `Q_le_walk_damped`, `Q_le_damped_iter`,
`iid_pathSum_law`, `fpDist_walk_eq_fpDistPlus`, `bigTriangle_walk_le`, **`estar_union_le`**
(new), `sum_inv_sq_le_two`+`sum_geom_pow_le` (new helpers), `fstar_markov`,
`deterministic_encounter_claim`, `triangle_encounter_le` (X10), `fpDistPlus_col_tail`,
`encFold_banked_le`, `encFold_cumWhite`, `many_triangles_white` (X9).

**NEXT: `few_whites_le` (X11c).** Study `encVal`/`encFold_banked_le`; state the few-white
event bound joining `fstar_markov` + `deterministic_encounter_claim` + `estar_union_le`.

## Lap D-box cont12 (2026-07-14): **`bigTriangle_walk_le` PROVED (axiom-clean)** — per-`p` big-triangle walk bound; X11a approach VALIDATED

Third grounded X11 sub-lemma (`Case3.lean`, axiom-clean). This is the ROUTE-DECISIVE probe: it
confirms `fpDist_walk_eq_fpDistPlus` (the 7.54 bridge) actually composes with
`triangle_encounter_le` (X10) to bound one E∗-union term. Statement: for `p ≤ T`, `1 ≤ s' ≤
(n/2−j)^{0.4}`, in the X10 deep regime,
`(∑_e fpDist s e · ∑_v (hold.iid T v)·1_{bigTriangleSet F s'}(j+e.1+(pathSum v p).1, …)).toReal
  ≤ C·A²(1+p)/s' + C·exp(−c·A²(1+p))`.
Proof: reassociate the position to Prod-add form (`ext <;> simp [add_assoc]`), apply the bridge
(walk → `fpDistPlus s p` marginal), push `ℝ≥0∞`→`ℝ` in one step by rewriting the indicator as
`ENNReal.ofReal` of the ℝ indicator + `PMF.toReal_tsum_mul_ofReal`, then `triangle_encounter_le`.
Reuses the same C, c, A₀ as X10. **The X11a assembly is now "just" summation over `p`.**

**X11 (`Q_black_edge_case3`, `Case3.lean`) — three proved bridges READY, remaining assembly:**
- **X11a `estar_union_le`** (p.54): sum `bigTriangle_walk_le` (NOW ✓) over `p ∈ range(T+1)` at
  `s'=⌈4^A(1+p)³⌉`. Needs: (a) the convergent series `Σ_p (1+p)^{-2} ≤ 2` (telescoping:
  `1/(k+1)² ≤ 1/k−1/(k+1)`) for the `1/s'` terms — since `s' ≥ 4^A(1+p)³` gives
  `A²(1+p)/s' ≤ A²·4^{-A}(1+p)^{-2}`; (b) the geometric `Σ_p exp(−c·A²(1+p))` ≤ `exp(−cA²)/(1−…)`,
  then the comparison `exp(−cA²) ≤ (const)·A²·4^{-A}` for `A ≥ A₀` (since `cA² ≥ A·ln4 − 2lnA`).
  Net E∗-mass `≤ C'·A²·4^{-A}`. Regime OK: horizon `T = encWindowIter A K R = O_{A,ε,R}(1)`, so
  `s'=⌈4^A(1+p)³⌉ = O(1) ≤ m^{0.4}` for `m ≥ C_{A,ε}`. **Next target.**
- **X11c `few_whites_le`** (7.56 join): `fstar_markov` (✓) + `deterministic_encounter_claim` (✓);
  `K=⌈10A/epsBW³⌉`, `R:=⌈(K+(A+3)log10+2)/ε⌉`, {reaches R} ⊆ F∗ via `encFold_banked_le`.
- **X11d body** = `Q_black_edge_case3`: `Q_le_damped_iter` + (7.54) col split (`fpDistPlus_col_tail`,
  `budget_le_of_mem_triangle`) + few-white damping (weights ≤ m^A/10^A) + X11a + X11c. NB the E∗
  event uses the PHASE point `((pos p).1−1, …)` (per `deterministic_encounter_claim` cond (ii))
  while `bigTriangle_walk_le` bounds the POSITION — X11d must bridge the −1 shift, and reconcile
  `bigTriangleSet ⌈4^A(1+p)³⌉` (ceil) vs the claim's strict `t.2.2 < 4^A(1+p)³`.

**Proved X11 machinery (all axiom-clean):** `Q_le_walk_damped`, `Q_le_damped_iter` (7.53),
`iid_pathSum_law`, **`fpDist_walk_eq_fpDistPlus`** (7.54 bridge), **`bigTriangle_walk_le`** (per-p
E∗ term), **`fstar_markov`** (7.56 Markov), `deterministic_encounter_claim` (7.67),
`triangle_encounter_le` (X10), `fpDistPlus_col_tail`, `encFold_banked_le`, `many_triangles_white`.

**NEXT: `estar_union_le` (X11a)** — prove `Σ_p (1+p)^{-2} ≤ 2` (telescoping) + the exp-geometric
comparison, sum `bigTriangle_walk_le` over `p ∈ range(T+1)`.

## Lap D-box cont11 (2026-07-14): **`fpDist_walk_eq_fpDistPlus` PROVED (axiom-clean)** — the (7.53)→(7.54) walk→fpDistPlus bridge for X11

Second grounded X11 sub-lemma landed (`Case3.lean`, axiom-clean). Building on `iid_pathSum_law`,
it converts the `Q_le_damped_iter` walk expectation into `fpDistPlus s p`-marginal form — the
exact law `triangle_encounter_le` (X10) bounds. Statement:
`∑_e fpDist s e · ∑_v (hold.iid T v)·g(e + pathSum v p) = ∑_x fpDistPlus s p x · g x` (p ≤ T).
Proof: `iid_pathSum_law` (prefix marginal = `iidSum hold p`) composed with the bind/map
unfolding of `fpDistPlus` (`PMF.tsum_bind_mul`, `PMF.tsum_map_mul`); `congr 1` + `simpa` handles
the beta-reduction. This is the conversion X11a (`estar_union_le`) and X11d both need to apply X10.

**X11 (`Q_black_edge_case3`, `Case3.lean`) remaining — two probabilistic inputs now READY:**
`fstar_markov` (7.56 Markov ✓) and `fpDist_walk_eq_fpDistPlus` (7.54 bridge ✓), plus X10
`triangle_encounter_le`, `deterministic_encounter_claim` (7.67), `Q_le_damped_iter` (7.53), all
proved. Decomposition to build next:
- **X11a `estar_union_le`** (p.54): the E∗ union bound. Via `fpDist_walk_eq_fpDistPlus` (NOW ✓)
  turn each per-`p` big-triangle event into `∑_x fpDistPlus s p x·1_{bigTriangleSet F s'}`, bound
  by `triangle_encounter_le` at `s'=⌈4^A(1+p)³⌉`; sum over `p` via `Σ(1+p)^{-2} ≤ 2` (the `1/s'`
  terms) + geometric (`exp` terms) ⟹ E∗-mass `≤ C·A²·4^{-A}`. No new analysis. **Next target.**
- **X11c `few_whites_le`** (7.56 join): `fstar_markov` (✓) + `deterministic_encounter_claim` (✓);
  `K=⌈10A/epsBW³⌉`, `R:=⌈(K+(A+3)log10+2)/ε⌉`, {reaches R} ⊆ F∗ via `encFold_banked_le`.
- **X11d body** = `Q_black_edge_case3`: `Q_le_damped_iter` + (7.54) col split (`fpDistPlus_col_tail`,
  `budget_le_of_mem_triangle`) + few-white damping (weights ≤ m^A/10^A) + X11a + X11c.

**NEXT: `estar_union_le` (X11a).** Read `bigTriangleSet` def + the paper (7.54)–(7.55) union
structure; state the E∗-mass bound over horizon `T`; prove via `fpDist_walk_eq_fpDistPlus` +
`triangle_encounter_le` + `Σ(1+p)^{-2}`.

## Lap D-box cont10 (2026-07-14): **`fstar_markov` PROVED (axiom-clean)** — X9-discharged (7.56) Markov bound; X11 crux now has its probabilistic input ready

X8 is fully complete; the sole remaining §7 assembly sorry is X11 `Q_black_edge_case3`
(`Case3.lean:955`), the (7.53)–(7.67) chain — a multi-lemma wall. This lap advanced it with
a grounded, self-contained sub-lemma: **`fstar_markov`** (`Case3.lean`, axiom-clean).

**What it does:** `fstar_markov_le` (proved) took Lemma 7.9's conclusion `encExpect ≤ e^{2ε}`
as an UNPROVED hypothesis `hbound`. `many_triangles_white` (X9, proved) supplies exactly
that. Composing them discharges the X9 dependency and FIXES the encoding gate `g` (from
`many_triangles_white`), yielding the hypothesis-free (7.56) input: `∀ ε≤ε₀, R≥1, T, q₀, lam>0,
∑_v (hold.iid T v)·1[lam ≤ encVal ε R (fold F R g q₀ v)] ≤ e^{2ε}/lam`.

**X11 (`Q_black_edge_case3`) remaining decomposition** (documented plan, sub-lemmas NOT yet
in `Case3.lean` — decompose next):
- **X11a `estar_union_le`** (p.54): `∑_{p≤T}` of X10 `triangle_encounter_le` (proved) through
  `iid_pathSum_law` (proved); the `1/s'` terms sum via `Σ(1+p)^{-2} ≤ 2`, exp terms geometric.
  "No new analysis" — pure assembly. Most tractable next target.
- **X11c `few_whites_le`** (7.56 join): `K = ⌈10A/epsBW³⌉` white cap; `R := ⌈(K+(A+3)log10+2)/ε⌉`
  makes {fold reaches R} ⊆ F∗ via `encFold_banked_le` (proved) + `encVal` ≥ lam=e^{-K+εR};
  then `fstar_markov` (NOW READY ✓) bounds F∗-mass; the deterministic (7.67) claim
  `deterministic_encounter_claim` (proved) forces reaches-R on the non-few-white/deep branch.
- **X11d assembly** = `Q_black_edge_case3` body: `Q_le_damped_iter` (proved) reduces `Q` to the
  fpDist×iid-walk expectation with white-damping; (7.54) col split (`fpDistPlus_col_tail` at
  D≈0.05m; `s/4 ≤ 0.79(m+2)` from (7.52) `budget_le_of_mem_triangle`); the few-white branch is
  killed by the damping (weights ≤ m^A/10^A), the many-encounter branch by X11a+X11c.

**Proved machinery ready for X11** (all axiom-clean): `Q_le_walk_damped`, `Q_le_damped_iter`,
`iid_pathSum_law`, `fstar_markov_le`, **`fstar_markov`** (new), `deterministic_encounter_claim`
(X11b), `triangle_encounter_le` (X10), `fpDistPlus_col_tail`, `encFold_banked_le`,
`encFold_cumWhite`, `budget_le_of_mem_triangle`, `many_triangles_white` (X9).

**NEXT: `estar_union_le` (X11a)** — state it (union-over-p of `bigTriangleSet` big-triangle
events, bounded via `iid_pathSum_law` + `triangle_encounter_le` + `Σ(1+p)^{-2}`), prove it
(no new analysis), then `few_whites_le` (X11c) using `fstar_markov`, then the X11d body.

## Lap D-box cont9 (2026-07-14): **`Q_black_edge_case2` PROVED (axiom-clean)** — X8 Case-2 (Prop 7.8 Case 2) is COMPLETE

The (7.46)–(7.51) Case-2 assembly is a machine-checked theorem
(`#print axioms = [propext, Classical.choice, Quot.sound]`, no `sorryAx`). **All of X8
Case-2 is now done**: both kernels (`fpDist_edgeWeight_le` ✓, `fpDist_white_exit` ✓) AND
the assembly. Full build green (3282 jobs).

**The proof (in `BlackEdgeQ.lean`):** entry `Q_le_fpDist_expect` (ℝ≥0∞ (7.45)) converted
to ℝ via `PMF.toReal_tsum_mul_ofReal` + `PMF.tsum_mul_ofReal_le_one` (RHS ≤ 1 finite) +
`ENNReal.toReal_mono`, giving `Q ≤ ∑ₑ fpDist·Q(endpoint)`. Per-endpoint `Q_fp_endpoint_le`:
`Q(endpt) ≤ (1 - c·1_W)·(edgeWeight·Q_{m-1})` with `c = 1-e^{-ε³} ∈ (0,1)`. Then the (7.47)
split `∑ fpDist·(1-c·1_W)·edgeWeight = ∑ fpDist·edgeWeight - c·∑ fpDist·1_W·edgeWeight`
(`Summable.tsum_sub`), bounded by `fpDist_edgeWeight_le` (`∑ fpDist·ew ≤ (1+δ)m^{-A}`,
δ=c·p₀/2) and, using the NEW pointwise `edgeWeight ≥ m^{-A}` (`rpow_neg_le_edgeWeight`)
+ white-exit (`∑ fpDist·1_W ≥ p₀`): `∑ fpDist·1_W·edgeWeight ≥ p₀·m^{-A}`. Net
`∑ fpDist·(1-c·1_W)·ew ≤ (1+δ-c·p₀)m^{-A} = (1-c·p₀/2)m^{-A} ≤ m^{-A}`, so
`Q ≤ Q_{m-1}·m^{-A}`. Two new helper lemmas added (`edgeWeight_le_one`,
`rpow_neg_le_edgeWeight`).

**X8 is COMPLETE. Remaining §7 assembly sorry: exactly ONE — `Q_black_edge_case3`
(`Case3.lean:941`, X11), the (7.53)–(7.67) Case-3 chain.** This is the DIRECTION step-2
target. X9 (`fpDist_white_exit_deep`/`many_triangles_white`) and X10 are both proved and
axiom-clean, so its two hardest inputs are ground truth. Once it lands, `Q_black_edge` →
`prop_7_8` → `Q_polynomial_decay` (all in Case3.lean, already assembled via DI) close, and
§7 monotonicity is done.

**NEXT: `Q_black_edge_case3` (`Case3.lean`).** First move: read its statement + the
(7.53)–(7.67) route in the paper (pp.48–49); it is the `s > m/log²m` (large-budget) twin of
Case 2. Entry is again `Q_le_fpDist_expect` at `P=0` per its docstring; the budget bound
`budget_le_of_mem_triangle` (`s·log2 ≤ (m+2)log9`, still in `BlackEdge.lean`) caps `s=O(m)`.

## Lap D-box cont8 (2026-07-14): **`fpDist_white_exit` PROVED (axiom-clean)** — the (7.50)/(7.51) Case-2 white-exit crux is DONE via kernel-merge

The DIRECTION-mandated next move is discharged. `fpDist_white_exit` is now a machine-checked
theorem (`#print axioms = [propext, Classical.choice, Quot.sound]`, no `sorryAx`).

**The structural finding (why "derive from deep" needed a relocation, not an in-place proof):**
`fpDist_white_exit_deep` (`ManyTriangles.lean`) is STRICTLY STRONGER than `fpDist_white_exit`
— identical tsum conclusion, *no* `s ≤ m/log²m` budget hypothesis, mass sharpened to
`51/100 ≤ p₀`. So Case-2 white-exit is a trivial weakening (drop the extra hyp, `p₀>0` from
`51/100≤p₀`). BUT `ManyTriangles` imports `BlackEdge`, so `BlackEdge` could NOT see the deep
kernel (circular). The geometry genuinely lives downstream.

**The fix (statements FROZEN verbatim, only relocation + the one `sorry`→proof):** created
`TaoCollatz/Sec7/BlackEdgeQ.lean` (imports `ManyTriangles`) and moved the Q-assembly tail of
`BlackEdge.lean` there — `fpDist_white_exit`, `Q_black_edge_case2`, `Q_black_edge_of_case3`,
`prop_7_8_of_black_edge`, `Q_polynomial_decay_of_prop_7_8`. This tail was consumed ONLY by
`Case3.lean` (which imports the new file now) and `ManyTriangles` does not depend on it, so the
move is cycle-free. `budget_le_of_mem_triangle` STAYED in `BlackEdge` (ManyTriangles uses it).
`fpDist_white_exit` proof = `obtain ⟨p₀,hp₀,Cthr,h⟩ := fpDist_white_exit_deep; exact ⟨p₀, by
linarith, Cthr, fun … _hbudget => h …⟩`. Full build green (3282 jobs).

**X8 Case-2 remaining: exactly ONE sorry — `Q_black_edge_case2` (`BlackEdgeQ.lean:64`).**
Both its kernels are now proved: `fpDist_edgeWeight_le` ✓ (7.48) + `fpDist_white_exit` ✓
(7.50/7.51). Per its docstring the assembly is "mechanical … `ℝ≥0∞`→`ℝ` bookkeeping across the
fpDist tsum": (7.45) entry `Q_le_fpDist_expect` + `Q_fp_endpoint_le` per endpoint, then the
(7.47) split `E[(1-(1-e^{-ε³})·1_W)·w] ≤ E[w] - (1-e^{-ε³})·m^{-A}·P(W)` (uses `w ≥ m^{-A}`
pointwise), bounded via `fpDist_edgeWeight_le` (δ := `(1-e^{-ε³})·p₀/2`) and `fpDist_white_exit`
(p₀), giving `Q ≤ ((1+δ)-(1-e^{-ε³})·p₀)·m^{-A}·Q_{m-1} ≤ m^{-A}·Q_{m-1}`.

**NEXT: `Q_black_edge_case2` (`BlackEdgeQ.lean`).** First move: read `Q_le_fpDist_expect`,
`Q_fp_endpoint_le`, `fpDist_edgeWeight_le`, `fpDist_white_exit` statements; the (7.47) split is
where the two kernels combine. Then X11 `Q_black_edge_case3` (`Case3.lean`, still sorry).

## Lap D-box cont7 (2026-07-14): **`fpDist_edgeWeight_le` PROVED (axiom-clean)** — the (7.48) Case-2 crux glue is DONE

The (7.48)/(7.49) weight degradation is a machine-checked theorem. Decomposed into:
- **`fpDist_edgeWeight_split`** (NEW, the mechanical Fubini heart, axiom-clean): sums
  `edgeWeight_summand_le` over `d` (hold) and `e` (fpDist), splits the joint tail via
  `1_{m<2(e₁+d₁)} ≤ 1_{m<4e₁}+1_{m<4d₁}`, factoring into `m^{−A}·Z_fp(θ)·Z_hold(θ) +
  T_fp + T_hold` (θ=2A/m). Takes the two MGF summabilities as hypotheses.
- **`fpDist_edgeWeight_le`** (main): supplies summabilities (`fpDist_fst_mgf_general.1`
  for fp; `tiltZ_hold_ne_top`→`ENNReal.summable_toReal` for hold), ε=min(δ/8,2), bounds
  Z_fp,Z_hold ≤ 1+ε (`fpDist_fst_mgf_le`, `hold_fst_mgf_le_real`), MGF ≤ m^{−A}(1+ε)² ≤
  (1+δ/2)m^{−A}, tails ≤ (δ/4)m^{−A} each; sum = (1+δ)m^{−A}. HEARTBEAT 1M.

**X8 Case-2 remaining: `fpDist_white_exit` (`BlackEdge.lean`, sorried) → `Q_black_edge_case2`.**

**NEXT: `fpDist_white_exit`.** DIRECTION.md: it is the Case-2 TWIN of the now-proved
deep kernel `fpDist_white_exit_deep` (`ManyTriangles.lean`) — "same geometry, budget
hypothesis `s ≤ m/log²m` added; DERIVE it from `fpDist_white_exit_deep` if you can."
First move: read both statements side by side, diff the hypotheses, and try to obtain
`fpDist_white_exit` as a specialization/weakening of the deep variant. Then
`Q_black_edge_case2` ((7.46)–(7.51) assembly, uses `fpDist_edgeWeight_le` ✓ +
`fpDist_white_exit`), then X11 `Q_black_edge_case3` (`Case3.lean`).

## Lap D-box cont6 (2026-07-14): **`hold_fst_tail_le` PROVED (axiom-clean)** — all 4 inputs of `fpDist_edgeWeight_le` now proved

The hold half of the (7.48) tail is done (axiom-clean). Route was far cleaner than the
fp tail: `hold`'s first marginal IS the geometric `geomQuarter` (`hold_map_fst`), so
`hold_tsum_fst` + `geomQuarter_tail` gives the closed form `∑_{k>m/4} geomQuarter(k) =
(3/4)^⌊m/4⌋`, then `(3/4)^⌊m/4⌋ ≤ exp(−(log(4/3)/8)m) ≤ δ·m^{−A}` via the same
`log_le_eps_mul_of_large`+`exp_neg_mul_le_of_large` closeout. No Fubini/MGF.

**STATUS of the (7.48) glue `fpDist_edgeWeight_le` — ALL FOUR inputs now PROVED:**
`fpDist_fst_mgf_le` ✓ · `hold_fst_mgf_le_real` ✓ · `fpDist_fst_tail_le` ✓ · `hold_fst_tail_le` ✓.

**NEXT (the crux is now pure assembly): `fpDist_edgeWeight_le`** (`BlackEdge.lean`, sorried).
Goal `∑_e fpDist·edgeWeight A m e ≤ (1+δ)m^{−A}` for `m≥Cthr`, `s≤m/log²m`. Route:
- Pointwise `edgeWeight_summand_le` (PROVED): `edgeWeight A m e = max(m−(e₁+d₁),1)^{−A}`?
  NB — CHECK the exact shape: `edgeWeight` is over `e` only; the `d` (hold) sum enters
  via the renewal? RE-READ `edgeWeight` def + `edgeWeight_summand_le` statement first —
  the summand bound is `max(m−J,1)^{−A} ≤ m^{−A}exp(2A·J/m) + 1_{m<2J}` with `J=e₁+d₁`,
  so the glue is a DOUBLE sum over `e` (fpDist) and `d` (hold). Confirm whether the
  `fpDist_edgeWeight_le` statement already folds the `d`-sum into `edgeWeight`, or if the
  hold sum is separate. If `edgeWeight` depends only on `e`, the `d`/hold machinery may
  belong to a different lemma — verify before assembling.
- MGF term: `m^{−A}·Z_fp(2A/m)·Z_hold(2A/m) ≤ (1+δ/2)m^{−A}` from `fpDist_fst_mgf_le`
  (needs `2A/m ≤ 1/100` too for `hold_fst_mgf_le_real`; add threshold) — factor
  `exp(2A·J/m)=exp(2A e₁/m)exp(2A d₁/m)`, Fubini over `e,d`.
- Tail term: `1_{m<2J} ≤ 1_{4e₁>m} + 1_{4d₁>m}` (since `2J>m ⟹ 4e₁>m ∨ 4d₁>m`), giving
  `≤ (δ/2)m^{−A}` from `fpDist_fst_tail_le` + `hold_fst_tail_le` (each with δ→δ/4-ish so
  the two tails sum to δ/2). Then `(1+δ/2)+(δ/2)=1+δ`.
- Then `fpDist_white_exit` (derive from `fpDist_white_exit_deep`, now a theorem), then
  `Q_black_edge_case2`, then `Q_black_edge_case3` (X11d, `Case3.lean`).

## Lap D-box cont5 (2026-07-14): **`fpDist_fst_tail_le` PROVED (axiom-clean)** — the fixed-tilt fp tail, the hardest X8 input

The genuinely-new large-deviation input of the (7.48) tail is now a machine-checked
theorem: `∑_e fpDist(s,e)·1_{m<4e₁} ≤ δ·m^{−A}` for `m ≥ Cthr`, `s ≤ m/log²m`.
`#print axioms = [propext, Classical.choice, Quot.sound]` (both it and the refactored
`fpDist_fst_mgf_le` verified clean). Full build green (3281 jobs).

**What landed (`BlackEdge.lean`, all axiom-clean):**
- **`fpDist_fst_mgf_general`** (NEW reusable engine): the Fubini + `gaussExp_col_tail`
  envelope core for ANY admissible tilt `0≤θ≤½min(c,c²/20)`, cutoff `K≥25`, budget
  `s·log2≤(K+2)log9`. Returns `Summable ∧ Z_fp(θ) ≤ exp(θK) + gaussExp_RHS`. Both the
  vanishing-tilt MGF and the fixed-tilt tail specialize it. `fpDist_fst_mgf_le` refactored
  onto it (was ~110-line spine → 4-line specialize; still clean).
- **`log_le_eps_mul_of_large`** (NEW helper): `∀ε>0 ∃N ∀m≥N, log m ≤ εm` (via `log m≤2√m`,
  `√m≥2/ε`). The polynomial-vs-exponential closeout: `exp(−ρm)·m^A → 0`.
- **`fpDist_fst_tail_le`** (the target): fixed `θ₀=½min(c,c²/20)`, cutoff `K=⌊m/log²m⌋+25`.
  Pointwise Chernoff `1_{m<4e₁} ≤ exp(θ₀(e₁−m/4))` ⟹ `T ≤ exp(−θ₀m/4)·Z_fp(θ₀)`;
  `fpDist_fst_mgf_general` ⟹ `Z_fp(θ₀) ≤ exp(θ₀K)+gaussExp_RHS ≤ B·exp(θ₀K)` (each
  gaussExp exp-term ≤1 since K+1−s/4≥0, `exp(θ₀s/4)≤exp(θ₀K)` since s/4≤K,
  `B=1+C'(1/d₂+1/d₁)`); `K≤m/8` (m≥400, log²m≥16) ⟹ `K−m/4≤−m/8`; close with
  `B·exp(−θ₀m/8) ≤ δ·m^{−A}` via `log_le_eps_mul_of_large`+`exp_neg_mul_le_of_large`.
  HEARTBEAT 2M (nested `Real.exp` atoms make isDefEq/nlinarith costly).

**NEXT — hardest-first, in order:**
1. **`hold_fst_tail_le`** (`BlackEdge.lean`, sorried): `∑_d hold·1_{m<4d₁} ≤ δ·m^{−A}`.
   The hold half of the (7.48) tail — should be a CLEANER twin of the fp tail: `hold` is
   a genuine PMF with a geometric first coordinate, so a fixed-tilt Chernoff
   `1_{m<4d₁} ≤ exp(θ(d₁−m/4))` gives `≤ exp(−θm/4)·Z_hold(θ)` with `Z_hold(θ)` a
   CONSTANT MGF (no s-dependence, no gaussExp) — use `tiltZ_hold_fst_le`/`hold_fst_mgf_le_real`
   at a FIXED θ≤1/100 (NB `hold_fst_mgf_le_real` gives `≤1+4θ+32θ²`, a constant), then
   `exp(−θm/4)·(1+4θ+32θ²) ≤ δm^{−A}` via the same `log_le_eps_mul`+`exp_neg_mul` closeout.
   Much shorter than the fp tail (no Fubini/envelope). Reuse the fp-tail closeout block verbatim.
2. **`fpDist_edgeWeight_le`** (the (7.48) glue): now ALL FOUR inputs proved
   (`fpDist_fst_mgf_le` ✓, `hold_fst_mgf_le_real` ✓, `fpDist_fst_tail_le` ✓, `hold_fst_tail_le` ←1).
   Double-`tsum` glue: `edgeWeight_summand_le` summed over d then e; MGF term
   `m^{−A}·Z_fp(2A/m)·Z_hold(2A/m) ≤ (1+δ/2)m^{−A}`; tail `1_{m<2(e₁+d₁)} ≤ 1_{4e₁>m}+1_{4d₁>m}`
   ⟹ `(δ/2)m^{−A}` from the two tail lemmas; pick δ-splits `(1+δ/2)+(δ/2)=1+δ`.
3. **`fpDist_white_exit`** (Case-2 twin of `fpDist_white_exit_deep`, now a theorem — derive from it).
4. **`Q_black_edge_case2`** (X8 Case-2 assembly), then `Q_black_edge_case3` (X11d, `Case3.lean`).

## Lap D-box cont4 (2026-07-14): **`fpDist_edgeWeight_le` decomposed + ℝ hold-MGF bridge PROVED** — corrected the tail route

Attacked the next X8 sorry `fpDist_edgeWeight_le` (the (7.48) weight degradation). Two
outcomes: (1) **`hold_fst_mgf_le_real` PROVED** (axiom-clean) — the ℝ-valued first-coord
`Hold` MGF `∑_d hold(d)·exp(θ d₁) ≤ 1+4θ+32θ²` for `|θ|≤1/100`, bridging the `ℝ≥0∞`
`tiltZ_hold_fst_le` via `ENNReal.tsum_toReal_eq`+`toReal_mono`. This is the `Z_hold`
factor of the MGF term. (2) **Route correction (the real finding).**

**⚠️ CORRECTION — the tail is NOT pure glue.** The prior handoffs claimed the (7.48)
tail `P(e₁+d₁>m/2) ≤ (δ/2)m^{−A}` is "a Chernoff of `fpDist_fst_mgf_le`". FALSE: a
Chernoff at the `2A/m` tilt gives `e^{−(2A/m)(m/4)} = e^{−A/2}`, a NON-DECAYING constant,
whereas we need decay `≪ m^{−A}` (since `m^{−A}→0`). The tail needs a **FIXED-tilt**
Chernoff (`θ₀ = Θ(1)`), which is genuine new analytic input — not glue. Recorded in the
lemma docstrings.

**Decomposition (all in `BlackEdge.lean`):** `fpDist_edgeWeight_le` now reduces to
- `fpDist_fst_mgf_le` (✓ PROVED last lap) — MGF factor `Z_fp(2A/m)`.
- `hold_fst_mgf_le_real` (✓ PROVED this lap) — MGF factor `Z_hold(2A/m)`.
- `fpDist_fst_tail_le` (OPEN, sorried, precise stmt): `∑_e fpDist·1_{m<4e₁} ≤ δ·m^{−A}`.
  **The hardest remaining piece.** Route: Fubini + `fpDist_col_le` + `gaussExp_col_tail`
  at cutoff `K'=Θ(s)` (budget `s·log2 ≤ (K'+2)log9`, ⌈s·log2/log9⌉) gives
  `Z_fp(θ₀) ≤ exp(θ₀K') + gaussExp_RHS = exp(O(m/log²m))`; then Chernoff
  `e^{−θ₀m/4}·Z_fp(θ₀) = exp(−θ₀m/4 + O(m/log²m)) ≪ m^{−A}` via `exp_neg_mul_le_of_large`.
  ~150 lines reusing the `fpDist_fst_mgf_le` machinery (θ₀ = ½min(c,c²/20) from col_le).
- `hold_fst_tail_le` (OPEN, sorried, precise stmt): `∑_d hold·1_{m<4d₁} ≤ δ·m^{−A}`.
  Chernoff via `holdSum_halfspace_le` at `n=1` — needs `iidSum hold 1 = hold` first
  (`iidSum_succ` + `iidSum_zero` + `pure_bind`/`map` cleanup).

**NEXT (hardest-first): prove `fpDist_fst_tail_le`** (the fixed-tilt fp tail). Then
`hold_fst_tail_le`, then the double-`tsum` glue for `fpDist_edgeWeight_le`:
`∑_e fpDist·edgeWeight ≤ m^{−A}·Z_fp·Z_hold + P_fp(e₁>m/4) + P_hold(d₁>m/4)`
(edgeWeight_summand_le summed over d, factor `exp(θ(e₁+d₁))=exp(θe₁)exp(θd₁)`, Fubini;
1_{m<2(e₁+d₁)} ≤ 1_{4e₁>m} + 1_{4d₁>m}). Pick `δ` splits so `(1+δ/2)+(δ/2)=1+δ`.

## Lap D-box cont3 (2026-07-14): **`fpDist_fst_mgf_le` FULLY PROVED (axiom-clean)** — X8 first-coord MGF closed

`fpDist_fst_mgf_numeric` (the analytic tail-threshold core) is now **PROVED**, so
`fpDist_fst_mgf_le` is `#print axioms = [propext, Classical.choice, Quot.sound]` — no
`sorryAx`. The genuinely-new analytic input of the (7.48) crux is a machine-checked
theorem. Full build green (3281 jobs).

**What landed (`BlackEdge.lean`, all axiom-clean):**
- **`log_sq_ge_of_large`**: `∀ b, ∃ N, ∀ m≥N, b ≤ log²m` — turns the `s ≤ m/log²m`
  budget into an explicit threshold (`N = ⌈exp√(max b 0)⌉`, via `Real.log_le_log` +
  `pow_le_pow_left₀`).
- **`exp_neg_mul_le_of_large`**: `∀ ρ>0 b>0, ∃ N, ∀ m≥N, exp(-ρm) ≤ b` — the
  super-exponential tail decay as an explicit threshold (`N = ⌈log b⁻¹/ρ⌉`).
- **`fpDist_fst_mgf_numeric`**: `Cthr = 25+N₁+N₃+N₈₅+N₄`, split `K = ⌊mL/(2A)⌋`
  (`L = log(1+δ/2)`). Five estimates: (E1) `θ=2A/m ≤ ½min(c,c²/20)` (m≥N₁); (E2) bulk
  `exp(θK) ≤ exp L = 1+δ/2` (floor); (E3) budget `s·log2 ≤ (K+2)log9` (log²m ≥
  `2A log2/(L log9)`); (E4) tail `≤ δ/2` — prefactor `exp(θs/4) ≤ exp(A/2)`, rates
  `a₂=c²/20-θ ≥ c²/40`, `a₁=c-θ ≥ c/2` bound denominators, `x₀=K+1-s/4 ≥ mL/(4A)`
  (log²m ≥ A/L), so tail `≤ Q·exp(-ρm) ≤ δ/2`. ~200 lines, `maxHeartbeats 4000000`.

**NEXT — glue `fpDist_edgeWeight_le`** (`BlackEdge.lean`, the (7.48)/(7.49) weight
degradation; still `sorry`). Now that BOTH inputs are proved (`edgeWeight_summand_le`
pointwise bound + `fpDist_fst_mgf_le` first-coord MGF), this is the double-`tsum`
glue: sum `edgeWeight_summand_le` over `d` (hold MGF `tiltZ_hold_fst_le` → 1) then
over `e` with `fpDist` (`fpDist_fst_mgf_le` for the `e.1` factor); tail
`P(e.1+d.1 > m/2) ≤ (δ/2)m^{-A}` via a Chernoff of `fpDist_fst_mgf_le` (`e.1 > m/4`)
+ hold Chernoff (`holdSum_halfspace_le`, `d.1 > m/4`). `Cthr = max` of region
thresholds; `(1+δ/2)+(δ/2) = 1+δ`. Then `fpDist_white_exit` / `Q_black_edge_case2`
(X8 Case-2), then `Q_black_edge_case3_assembled` (X11d, `Case3.lean`).

## Lap D-box cont2 (2026-07-14): **`fpDist_fst_mgf_le` mechanical spine PROVED** — crux reduced to one numeric obligation

The X8 crux sub-goal `fpDist_fst_mgf_le` (`BlackEdge.lean`) is now **proved off a single
clean interface** `fpDist_fst_mgf_numeric` (the only remaining `sorry`). `#print axioms
fpDist_fst_mgf_le = [propext, sorryAx, Classical.choice, Quot.sound]` — the `sorryAx`
traces *solely* to `fpDist_fst_mgf_numeric`. Full build green (3281 jobs).

**What landed (mechanical, template = `fpDist_out_of_strip_le`):** the entire
Fubini/split/mass spine of the first-coord `fpDist` MGF:
- **Exponent rewrite** `2A·e.1/m = θ·e.1` (`θ := 2A/m`), then `set f, M`.
- **Tonelli 2D-summability** via `summable_prod_of_nonneg`: column slices summable
  (`hfp2d.comp_injective`) + the column-marginal series `∑'_j (∑'_l f)` summable by
  domination `g(j) = M(j)·e^{θj} ≤ U(j)`.
- **The dominating envelope** `U(j) = [j≤K] e^{θK}·M(j) + [K<j] e^{θj}·(fpDist_col_le env)`.
  Bulk part finite-support-summable (`summable_of_ne_finset_zero`, `Finset.range (K+1)`);
  tail part = `gaussExp_col_tail`'s summand verbatim ⟹ `hsumT`.
- **`g ≤ U` pointwise** (two cases: `j≤K` uses `e^{θj} ≤ e^{θK}` + `M≥0`; `j>K` uses
  `fpDist_col_le` = `M j ≤ env j`).
- **Fubini** `Summable.tsum_prod'` collapses the 2D sum to `∑'_j g(j) ≤ ∑'_j U(j)`.
- **Bulk ≤ 1+δ/2**: factor `e^{θK}` (`tsum_mul_left`), `∑'_j [j≤K] M(j) ≤ ∑'_j M(j) = 1`
  (marginal mass via `summable_prod_of_nonneg` + `(fpDist s).tsum_coe`), cite `hbulk`.
- **Tail ≤ δ/2**: `hleT.trans htail` (gaussExp RHS ≤ δ/2). Sum `(1+δ/2)+(δ/2) = 1+δ`.

**NEXT — hardest-first: discharge `fpDist_fst_mgf_numeric`** (`BlackEdge.lean:~296`).
This is the analytic tail-threshold — pure constant-juggling, route sound. With `c,C'`
from `fpDist_col_le` (absolute), `θ = 2A/m`, `L := log(1+δ/2)`, `K := ⌊m·L/(2A)⌋`:
1. `θ ≤ ½min(c,c²/20)`: needs `m ≥ 2A/(½min(c,c²/20))` =: m₁.
2. bulk `e^{θK} ≤ 1+δ/2`: `θK = (2A/m)⌊m L/(2A)⌋ ≤ L`, so `e^{θK} ≤ e^L = 1+δ/2`. (floor)
3. gaussExp budget `s·log2 ≤ (K+2)·log9` + `25 ≤ K`: from `s ≤ m/log²m` (≪ K = Θ(m)) for
   `m ≥` some m₂ (needs `log²m ≥ A/L`-ish so `K ≫ s`).
4. tail RHS `≤ δ/2`: `x₀ = K+1-s/4 ≥ m·L/(4A)` for `m ≥ exp(√(A/L))` =: m₃ (since
   `s/4 ≤ m/(4log²m)`); prefactor `e^{θs/4} ≤ e^{A/(2log²m)} ≤ e^{A/2}`; rates
   `a₂ = c²/20-θ ≥ c²/40`, `a₁ = c-θ ≥ c/2` (denominators bounded below); so
   `RHS ≤ 2C'e^{A/2}·e^{-(c²/40)·mL/(4A)}/(1-e^{-c²/40}) → 0`, ≤ δ/2 for `m ≥ m₄`.
   `Cthr = max(25, m₁, m₂, m₃, m₄)`. The `log²m → ∞` steps are the fiddly part.
   TODO(alt): could weaken to `s ≤ m/log m` if `log²m` bookkeeping bites (still gives the
   asymptotics; but the (7.52) hyp is `log²m`, keep it).

## Lap D-box (2026-07-14): **X8 `edgeWeight_summand_le` PROVED** — the pointwise weight bound

With the X9 kernel closed (below), moved to the non-gated X8 crux `fpDist_edgeWeight_le`
(`BlackEdge.lean:407`, the (7.48) weight degradation). Landed the **uniform pointwise weight
bound** `edgeWeight_summand_le` (axiom-clean `[propext, Classical.choice, Quot.sound]`):

> `∀ A ≥ 0, m ≥ 2, e d`, with `J = e₁ + d₁`:
> `max(m − J, 1)^{−A} ≤ m^{−A}·exp(2A·J/m) + 1_{m < 2J}`.

**Why this is the right shape**: it dominates `edgeWeight` WITHOUT an inner `[J ≤ m/2]`
region split (no Fubini/summability barrier). Main region `J ≤ m/2` uses the concavity core
`one_sub_rpow_neg_le_exp` (`x = J/m ≤ 1/2`); tail `J > m/2` uses weight `≤ 1 ≤` indicator.
Summing over `d` with `hold`, then over `e` with `fpDist`, the MGF term factors cleanly:
`∑_e fpDist·edgeWeight ≤ m^{−A}·Z_{fp,fst}(2A/m)·Z_{hold,fst}(2A/m) + P(e₁+d₁ > m/2)`.

**⚙️ ARCHITECTURE BLOCKER RESOLVED** (2026-07-14): all three X8 `BlackEdge.lean` sorries
(`fpDist_edgeWeight_le`, `fpDist_white_exit`, `Q_black_edge_case2`) need the fp-concentration
machinery (X6 `fpDist_location_bound`, `fpDist_col_le`, the `Gweight` toolbox) — which lived
DOWNSTREAM in `FpLocation`/`ManyTriangles`, invisible to BlackEdge. Checked the Sec7 import DAG:
`FpLocation`'s transitive closure never reaches `BlackEdge` (it only pulls `HoldLocal`+`Mgf`+
`LocalInstances`), so **added `import TaoCollatz.Sec7.FpLocation` to `BlackEdge.lean`** — no
cycle, full build green (3281 jobs). X6 + `Gweight` + `sum_sqrt_exp_le`/`conv_Gweight_exp` are
now all available in BlackEdge. This unblocks the entire X8 Case-2 subtree without any lemma
relocation. (The same import gives `fpDist_col_le` etc. once ManyTriangles-level lemmas are
needed — though those are further downstream; X6 alone suffices for `fpDist_fst_mgf_le`.)

**Named src sub-goal added** (`BlackEdge.lean`, compiler-checked disclosed `sorry`):
`fpDist_fst_mgf_le` — the first-coordinate `fpDist` MGF `∑_e fpDist·exp(2A·e.1/m) ≤ 1+δ`
for `m ≥ C`. This is THE genuinely-new analytic input; both the main MGF factor AND the tail
of `fpDist_edgeWeight_le` reduce to it (the tail via a Chernoff of it on `e.1 > m/4` plus a
`hold` Chernoff on `d.1 > m/4`). Full route in its docstring. **ROUTE CORRECTED** (2026-07-14): the renewal-MGF plan is overkill;
the sharp `≤1+δ` follows from `∑_e fpDist·exp(θe.1) = 1 + ∑_e fpDist·(exp(θe.1)−1)` with the
**bulk** (`e.1 ≤ K=Θ(m/log)`) bounded by mass-1 alone (`exp(θK)−1 ≤ δ/2`) and the **tail**
(`e.1 > K`) by X6 `fpDist_location_bound` (available upstream in `FpLocation`), whose loss
constant is harmless because `j > K` sits super-exponentially deep in the `s/4`-centred Gaussian
(`θj − c²j²/(1+s) → −∞`). Reuses the `Gweight` toolbox (`sum_sqrt_exp_le`,
`sum_range_exp_neg_sq_le`, `conv_Gweight_exp`) + the `l`-geometric `∑_{l>s} e^{−c(l−s)}`.
**This is the crux's hardest-first target — attack it next.**

**✅ TAIL LEMMA PROVED** (commit `0a26b44`): `gaussExp_col_tail` (`FpLocation.lean`, axiom-clean)
— the Gaussian×growing-exp column tail `∑_{j>m} e^{θj}·C'·Gweight(1+s,c(j−s/4))/√(1+s) ≤
C'·e^{θs/4}·(shifted-geometric in γ₂−θ and c−θ)`, for `0≤θ≤½min(c,c²/20)`, `m≥25`, budget.
This is the analytic meat. Enablers `fpDist_col_le`, `hasSum_int_shift_exp`, `hasSum_nat_tail_exp`
all now upstream in `FpLocation`, visible to BlackEdge.

**REMAINING for `fpDist_fst_mgf_le` = pure ASSEMBLY** (no new analysis):
1. **Fubini 2D→1D**: `∑'_{(j,l)} fpDist·e^{θj} = ∑'_j e^{θj}·M(j)`, `M(j)=∑'_l fpDist(s,(j,l)).toReal
   ≤ fpDist_col_le`. Total `∑'_j M(j) ≤ 1`.
2. **Split at `K`** (`θ=2A/m`, `K` with `θK ≤ log(1+δ/2)`): finite bulk `∑_{j≤K} e^{θj}M(j) ≤
   e^{θK}·1 ≤ 1+δ/2`; tail `∑_{j>K} e^{θj}·(fpDist_col_le envelope) ≤ gaussExp_col_tail`'s RHS.
3. **Numerics**: pick `Cthr` (≥25, ≥ enough that `θ=2A/m ≤ ½min(c,c²/20)` and gaussExp RHS → ≤ δ/2).
   `e^{θs/4} ≤ e^{A/(2log²m)}` bounded; the shifted geometrics `e^{−(rate)·Θ(m)} → 0`.
   Then `1+δ/2 + δ/2 = 1+δ`. Also need the budget `s·log2 ≤ (m+2)·log9` — derive from
   `s ≤ m/log²m` (the (7.52) hypothesis) since `log²m ≥ ...` gives it with room.
Then glue `fpDist_edgeWeight_le` from `edgeWeight_summand_le` + `fpDist_fst_mgf_le` + hold MGF + tail.

**SHARP ASSEMBLY PLAN for `fpDist_fst_mgf_le`** (now that `fpDist_col_le` is upstream in
`FpLocation`, visible to BlackEdge — commit `21b0e0c`):
1. **Fubini 2D→1D**: `∑'_{(j,l)} fpDist(s,(j,l))·exp(θj) = ∑'_j exp(θj)·M(j)` where
   `M(j) := ∑'_l fpDist(s,(j,l)).toReal` (via `tsum_prod'` + `tsum_mul_left`, `exp(θj)`
   constant in `l`). Then `M(j) ≤ C'·Gweight(1+s,c(j−s/4))/√(1+s)` by `fpDist_col_le`.
   Note `∑'_j M(j) = ` total `fpDist` mass `≤ 1` (`fpDist_tsum_toReal`).
2. **Split at `K = ⌊m·log(1+δ/2)/(2A)⌋`** (so `θK = (2A/m)K ≤ log(1+δ/2)`, `θ=2A/m`):
   • **Bulk `j ≤ K`** is a FINITE range sum: `∑_{j≤K} exp(θj)·M(j) ≤ exp(θK)·∑_{j≤K} M(j)
     ≤ exp(θK)·1 ≤ 1+δ/2`. (Only needs mass ≤ 1 — no envelope, no infinite summability.)
   • **Tail `j > K`**: `∑'_{j>K} exp(θj)·C'·Gweight(1+s,c(j−s/4))/√(1+s) ≤ δ/2` — THE meat.
3. **Tail lemma = adapt `gaussian_col_tail`** (currently `ManyTriangles.lean:1827`, uses
   `hasSum_nat_tail_exp` at `:1804`) with the extra `exp(θj)` factor: fold it into each
   geometric — `exp(θj)·exp(−c(j−s/4)) = exp(−(c−θ)(j−a))` (`a=(cs/4)/(c−θ)`, needs `θ<c`
   i.e. `m>2A/c`); `exp(θj)·exp(−c²(j−s/4)²/(1+s))` dominated via `x²/t ≥ (x₀/t)x` with the
   tail start `x₀=c(K−s/4)` big enough that the effective rate `c²x₀/(1+s) − θ > 0` (since
   `1+s ≤ m`, `x₀=Θ(m)`, `θ=2A/m→0`). Both → geometric via `hasSum_nat_tail_exp`.
   **To place the tail lemma upstream** (BlackEdge/FpLocation), also move `hasSum_nat_tail_exp`
   up (mathlib-only proof) — same pure-move pattern as `fpDist_col_le`.
   NB the 2D summability of step 1 comes for free once the tail (step 2) is summable + bulk
   is finite; assemble summability as `finite ∪ tail`.

**NEXT for `fpDist_edgeWeight_le` (three remaining pieces, all now routed through the pointwise bound)**:
1. **MGF factor** `Z_{fp,fst}(2A/m)·Z_{hold,fst}(2A/m) ≤ 1 + δ/2` for `m ≥ C`. `Z_{hold,fst}(θ)`
   at `θ = 2A/m → 0` → 1 (reuse `tiltZ_hold_fst`/`tiltZ_hold_fst_le`, `K = 32` quadratic bound
   in `Prob/Mgf.lean:637`). `Z_{fp,fst}(θ) = ∑_e fpDist·exp(θ e₁) ≤ exp(θ·s/4 + …)`: need a
   first-coordinate fpDist MGF/Chernoff. `e₁` mean ≈ `s/4 ≤ m/(4log²m)`, so
   `Z_{fp,fst}(2A/m) ≤ exp(A·s/(2m)) ≤ exp(A/(2log²m)) → 1`. The fp first-coord MGF bound is
   the one genuinely-new analytic input (X6 `fpDist_col_le`/`fpDist_location_bound` centre it at
   `s/4`; or a direct Chernoff via the Gweight row engine).
2. **Tail** `∑_e fpDist·∑_d hold·1_{m < 2(e₁+d₁)} = P(e₁+d₁ > m/2) ≤ (δ/2)·m^{−A}` for `m ≥ C`.
   Large deviation: `e₁+d₁` concentrated at `s/4 + 4 ≪ m/2`; Chernoff at a fixed first-coord
   tilt (`holdSum_halfspace_le` at `(θ,0)` for the hold part; fp first-coord Chernoff for `e₁`).
3. **Glue**: sum `edgeWeight_summand_le` over `d` (inner tsum, `hold`-summability of the exp term
   from `tiltZ_hold_fst` finiteness + the indicator ≤ 1), then over `e` with `fpDist` (mass 1);
   the exp factor separates `exp(2A(e₁+d₁)/m) = exp(2A e₁/m)·exp(2A d₁/m)`; combine 1+2 with
   `Cthr = max` of the two regions' thresholds and `(1+δ/2) + (δ/2) = 1+δ`.


## Lap D-box (2026-07-14): **`fpDist_any_triangle_le` PROVED — X9 white-exit kernel CLOSED** — axiom-clean

Commit `94444b9`. The last route-decisive blocker on the X9 white-exit kernel is discharged.
`fpDist_any_triangle_le` and `fpDist_white_exit_deep` are both machine-verified
`[propext, Classical.choice, Quot.sound]` (no `sorryAx`). Full build green (3281 jobs).

**What landed** (wiring the sharp explicit constants `B = 64`, `Y = 150` into the box):
- `40000000` (old throwaway `B`) → `64` throughout the box lemmas
  (`phaseInFamily_support_imp_localization_bad`, `exists_fpDist_localization_box`,
  `fpDist_any_triangle_le_of_localization_box`). The constant is *symbolic* there — it
  cancels in the facewidth `nlinarith` step (`5Y+B ≤ 16X` and `16e₁−5e₂ < B` give
  `16(e₁−X) < 5s` independent of `B`), so no geometry changed.
- `fpDist_localization_le_eighth`: existential `∃ Y` → **numeral** `∀ s` at `Y = 150`,
  now assembled from the sharp leaves `fpDist_height_tail_le_sixteenth_sharp` +
  `fpDist_linear_tail_le_sixteenth_sharp` (both off X6). `exists_fpDist_localization_box`
  now returns the explicit `X = 51, Y = 150`.
- `sep_const_gt_two_hundred` (`Triangles.lean`): `sep = (1/10)·log(10^1000) = 100·log 10 > 200`
  via `log 10 > 3·log 2 > 2.07` (`2^30 < 10^10` + `Real.log_two_gt_d9`).
- `fpDist_any_triangle_le`: `refine ⟨0, …⟩`; feed `X = 51, Y = 150`,
  `hsepXY : 51²+150² = 25101 < 200² < sep²`, and the numeral `hloc` into
  `fpDist_any_triangle_le_of_localization_box`. **Moved the three box lemmas above their
  consumer** (they were defined ~600 lines below — forward-reference fix).

**MILESTONE**: `fpDist_white_exit_deep` (X9's only open external input) is now a THEOREM.
X9's kernel — the last route-decisive blocker on Prop 1.17's Case-3 chain — is CLOSED with
ground truth. Both throwaway constants explicit and both tails sharp; the arithmetic
obstruction the whole judge-pass-24 directive targeted is fully cleared and consumed.

**NEXT — the Case-2 twin `fpDist_white_exit` + `Q_black_edge_case2` (X8), and `Q_black_edge_case3_assembled` (X11d)**:
The remaining Sec7 sorries are in `BlackEdge.lean` and `Case3.lean`.
- ⚠️ **Architecture note**: `fpDist_white_exit` (BlackEdge, Case-2 twin) has the SAME
  whiteness conclusion as `fpDist_white_exit_deep` + the extra unused `s ≤ m/log²m` hyp,
  so morally it "follows by citing `fpDist_white_exit_deep`". BUT `BlackEdge.lean` is
  UPSTREAM of `ManyTriangles.lean` (ManyTriangles imports BlackEdge), so it cannot cite
  the now-proved kernel directly. Options: (a) relocate the shared white-exit
  decomposition (`fpDist_out_of_strip_le` + the box machinery + `fpDist_any_triangle_le`)
  into an upstream module both import, then derive both twins from it; (b) prove
  `fpDist_white_exit`/`Q_black_edge_case2` downstream (à la `Case3.lean`) and pin the
  BlackEdge statements. Decide next lap — this is a genuine module-layering call, not just
  a mechanical port.
- The non-architecture X8 leaf `fpDist_edgeWeight_le` (the (7.48) weight degradation) is
  genuinely off-X6 and non-gated; concavity core `one_sub_rpow_neg_le_exp` already landed
  (see Lap C part 2b below for the MGF + tail decomposition plan).
- `Q_black_edge_case3_assembled` (X11d, `Case3.lean`): mechanical ℝ≥0∞→ℝ bookkeeping
  (plan in the Lap 60 entry below).


## Lap D-eps (2026-07-14): **`epsBW` re-frozen `10⁻⁹⁰ → 10⁻¹⁰⁰⁰`** (judge pre-authorized) — DEDICATED lap

The judge's pre-authorized ε-ruling (DIRECTION.md) fires: proved constants `B = 64 ≤ 250`,
`Y = 150 ≤ 200` are inside the envelope, so `epsBW := 1/10^1000` is authorized.
`sep = (1/10)·log(1/ε) = 100·log 10 ≈ 230.3`, which dominates the box `√(51²+150²) ≈ 158.4`.
Executed as a **dedicated lap** (only the numeral + mechanical repairs, NO route work):

- `Setup.lean`: `epsBW := 1/10^1000`.
- Bulk `10^90 → 10^1000` (White, BlackEdge, ManyTriangles, Triangles).
- **X3 Lemma 7.4 window cascade** (the ε-sweep "armed items", monotone-good): the buffer
  radius grew `<26 → <301`, so the lattice window bumped `25 → 300` and the corner-scale
  factor `9^25·2^25 → 9^300·2^300` across `sep_const_lt_twenty_six`,
  `lattice_close_of_sq_dist_lt_sep`, `corner_scale_near_le`,
  `weaklyBlack_of_corner_scale_near`, `black_near_black_mem_corner`. Content survives
  (the far smaller ε overwhelms the larger window: `9^300·2^300·10^{-1000} ≈ 10^{-623} < 1/2`).
- **Gotcha**: `norm_num` refuses to evaluate `a^b` past `exponentiation.threshold 256`;
  added `set_option exponentiation.threshold 3000` to the four §7 files so `10^1000` and
  `9^300·2^300` magnitude checks evaluate.

All axiom-clean; full `lake build` green (3281 jobs). **JUDGE**: the ε-sweep
re-ratification (seven armed items; `#print axioms` on X2/X3/X10) is yours to run.

**NEXT — Lap D-box (route)**: now that `sep ≈ 230 > 158.4`, close `fpDist_any_triangle_le`
(`ManyTriangles.lean:2095`). Rewire the box from the throwaway `40000000` (old `B`) to the
sharp `64`, and from the existential `Y` to `150`: `exists_fpDist_localization_box`,
`fpDist_any_triangle_le_of_localization_box` (hyp `5Y+40000000 ≤ 16X` and the `40000000`
in the bad-event), `phaseInFamily_support_imp_localization_bad`, and
`fpDist_localization_le_eighth` (swap `fpDist_height_tail_le_sixteenth` →
`fpDist_height_tail_le_sixteenth_sharp`, `fpDist_linear_tail_le_sixteenth` → `_sharp`).
Then `X = ⌈814/16⌉ = 51`, and `hsepXY : 51² + 150² < ((1/10)·log(1/10^1000))²` closes
(`51²+150² = 25101 < 230.3² ≈ 53019`). That discharges `fpDist_any_triangle_le`, hence
`fpDist_white_exit_deep`, hence the X9 white-exit kernel. (Do the `ManyTriangles.lean`
BLUEPRINT §2 split first if iterating on that 5.2k-line file gets painful.)


## Lap C part 2b (2026-07-14): started X8 `fpDist_edgeWeight_le` — concavity core landed

With Lap C/D done/gated (below), moved to the non-gated X8 crux
`fpDist_edgeWeight_le` (`Sec7/BlackEdge.lean:216`, the (7.48) weight degradation —
off X6, NOT the gated separation fight). Landed the reusable **(7.42) concavity
core** `one_sub_rpow_neg_le_exp : 0≤A → 0≤x → x≤1/2 → (1-x)^{-A} ≤ exp(2Ax)`
(axiom-clean); this is the pointwise bound that turns the depth weight
`(m-J)^{-A} = m^{-A}(1-J/m)^{-A}` into `m^{-A}·exp(2A·J/m)`.

**Decomposition plan for `fpDist_edgeWeight_le`** (next lap; `J := e.1+d.1` = total
`j`-advance = first-passage `j` + one hold `j`):
1. **Main region** (`J ≤ m/2`): pointwise `one_sub_rpow_neg_le_exp` ⟹
   `∑_e fpDist·∑_d hold·[J≤m/2]·max(m-J,1)^{-A} ≤ m^{-A}·E[exp(2A·J/m)]`. The MGF
   `E[exp(2A(e.1+d.1)/m)] = Z_fp,fst(2A/m)·Z_hold,fst(2A/m)` (first-coord tilt).
   `e.1` has mean ≈ s/4 ≤ m/(4log²m), `d.1` mean 4 ⟹ MGF ≤ exp(2A/m·(s/4+4)+O(1/m²))
   ≤ exp(A·s/(2m)) ≤ exp(A/(2log²m)) → 1, so `≤ (1+δ/2)` for `m ≥ C`.
   Needs: a first-coordinate fpDist MGF/Chernoff bound (reuse `tiltZ_hold_fst`,
   `holdSum_halfspace_le`, and X6's `fpDist_col_le`/`fpDist_location_bound` for the
   `e.1` mean — the col marginal is centered at s/4).
2. **Tail** (`J > m/2`): weight ≤ 1 (max ≥1), so `≤ P(e.1+d.1 > m/2)`; large
   deviation (J concentrated at s/4 ≪ m/2) ⟹ `≤ exp(-c·m) ≤ (δ/2)·m^{-A}` for `m≥C`.
   Chernoff at a fixed first-coord tilt; reuse the same MGF machinery.
3. **Glue**: split the double-`∑` by `[J≤m/2]`, add the two (ℝ tsum summability from
   `edgeWeight`/`fpDist` finiteness). `Cthr = max` of the two regions' thresholds.
NB `fpDist_white_exit` and `Q_black_edge_case2` (the other listed X8 sorries) route
through the gated `fpDist_any_triangle_le` separation fight, so they stay blocked;
`fpDist_edgeWeight_le` is the genuinely non-gated on-path X8 leaf.

## Lap C part 2 (2026-07-14): **constant `Y` MADE EXPLICIT (existential → `Y = 150`)** — axiom-clean

Directive step 3 (judge pass 24) is **DONE**. `fpDist_height_tail_le_sixteenth_sharp`
(`Sec7/FpLocation.lean`) proves, at the **numeral** radius `Y₀ = 150`:
`∀ s, ∑_e [s+150 ≤ e.2] fpDist s e ≤ 1/16`, machine-verified
`[propext, Classical.choice, Quot.sound]`. This kills the last *existential* in the
localization box (the old `fpDist_height_tail_le_sixteenth` summed X6's `∃`-bound
envelope, so the box was not a number). The existential form is left in place;
Lap D rewires.

**What landed** (this commit), all axiom-clean, off X6 (renewal route, judge pass 24):
- `tiltZ_pascalNe3_le_num_snd` : `Z_ne3(1/20) ≤ 1252/1000` — large-tilt numeric MGF
  bound at the positive height tilt `μ = 1/20` (mirrors `tiltZ_pascalNe3_le_num` at
  `-5/16`; `e^{1/20} ≤ 1.05128`, `e^{3/20} ≥ 1.1618` via `Real.exp_bound`).
- `tiltZ_hold_snd_num` : `Z(0,1/20) ≤ 48/10` — via the exact closed form
  `tiltZ_hold_closed` (tilt outside the `|μ|≤1/50` box of `tiltZ_hold_snd`).
- `holdStep_height_tail (T:ℤ)` : single-step Chernoff `∑_d [T≤d.2] hold d ≤
  e^{-T/20}·(48/10)` (`holdSum_halfspace_le_of_mgf` at `n=1`, `iidSum hold 1 = hold`).
- `hasSum_int_level_geom` / `geom_level_sum_le` : the geometric sum
  `∑_{u≤s} e^{-(1/20)(s+150-u)} = e^{-7.5}/(1-e^{-1/20})` (reflection `u↦s-u` +
  `of_nat_of_neg_add_one`; ℝ→ℝ≥0∞ via `ENNReal.ofReal_tsum_of_nonneg`).
- `fpDist_height_tail_le_sixteenth_sharp` : the assembly.
  `fpDist_le_renewal_conv` → swap endpoint sum inward (tsum_comm) → single-step
  Chernoff on the `hold` tail → group by level `u=p.2` and apply
  `renewal_level_le_one` (mass ≤1/level) → geometric sum. Final numeric margin:
  `(48/10)·e^{-7.5}/(1-e^{-1/20}) ≈ 0.0545 ≤ 1/16` (`e^{7.5}=e^{3/4·10}≥(2.11)^{10}≥1667`).

**Constants now BOTH explicit**: `B = 64` (Lap B), `Y = 150`. Box
`= √(⌈(5·150+64)/16⌉² + 150²) = √(⌈814/16⌉² + 150²) = √(51² + 150²) ≈ 158.4`.
(Directive target was `Y≈139`→box≈147; `Y=150` is well within the "`Y≤~250` fine"
budget. Judge re-freezes `epsBW` regardless — needs `10⁻⁹⁰→~10⁻⁷⁰⁰`, sep≈161.)

**NEXT — Lap D (epsBW-gated — JUDGE's call, do NOT touch epsBW)**: wire `64` and
`150` into the `ManyTriangles.lean` localization box (numeral `40000000` at
~1618/2706/2728; existential `Y` at 2708). `fpDist_localization_le_eighth` currently
consumes the existential `fpDist_height_tail_le_sixteenth`; swap for
`fpDist_height_tail_le_sixteenth_sharp` (real-threshold form, drop-in) + the sharp
linear tail, then feed `exists_fpDist_localization_box` + the box inequality into
`fpDist_any_triangle_le_of_localization_box`. Report the real box `√(52²+150²)` to the
judge; the `epsBW` re-freeze lands after (box `√(51²+150²)≈158.4` needs sep≥159 ⟹
`(1/10)ln(1/epsBW)≥159` ⟹ `epsBW ≤ 10^{-690}` ish). Until then
`fpDist_any_triangle_le` stays sorried. (`ManyTriangles.lean` BLUEPRINT §2 split still
queued — do it before editing that 5.2k-line file.)

## Lap B (2026-07-13): **constant `B` DISCHARGED 4·10⁷ → 64** (X11 localization) — axiom-clean

Directive step 2 (judge pass 24 / HANDOFF-2026-07-13-e) is **DONE**. The throwaway
transverse-localization constant `B` in `fpDist_linear_tail` is now `64`, machine-
verified `[propext, Classical.choice, Quot.sound]` (real-analytic, **no**
`native_decide`).

**What landed** (commit `3625037`):
- `tiltZ_hold_closed` (`Prob/Mgf.lean`): the EXACT general `Hold` MGF closed form
  `Z(l₁,l₂) = (e^{l₁+3l₂}/4)·(1 − (3/4)e^{l₁}·Z_ne3(l₂))⁻¹` (generalizes the two
  coordinate forms `tiltZ_hold_fst`/`tiltZ_hold_snd`). Finite up to `θ ≈ 0.213`.
- `tiltZ_pascalNe3_le_num`, `tiltZ_hold_le_num`: numeric large-tilt bounds at
  `(l₁,l₂)=(1,−5/16)` (i.e. `θ=1/16` on `Z=16j−5l`), giving **`Z_hold ≤ 76/100 < 1`**.
  Uses `Real.exp_bound` (n=6/7) + `exp_one_lt_d9`; all rational bounds, big margin
  (ratio ≈0.640, ρ≈0.736; see `tools/… mgf_check.py` scratch).
- `holdSum_halfspace_le_of_mgf` (`Sec7/HoldLocal.lean`): Markov-under-tilt taking the
  MGF bound as a hypothesis, so the tilt can exit the `|λ|≤1/200` box that capped the
  old proof at `θ=1/20000` (the whole reason `B` was `4·10⁷`).
- `fpDist_linear_tail_sharp` + `fpDist_linear_tail_le_sixteenth_sharp`
  (`Sec7/FpLocation.lean`): threshold `64` ⟹ tail `≤ 1/16`.

**NOT yet wired** into the `ManyTriangles.lean` localization box — that is Lap D
(numeral `40000000` appears at `ManyTriangles.lean:1618,2706,2728,…`). Lap D is
`epsBW`-gated (judge's call). Leave `fpDist_any_triangle_le` sorried until then.

## Lap C part 1 (2026-07-13): **renewal mass per height level `≤ 1` PROVED** — the "trick"

Commit `2daf42f`, axiom-clean. `renewal_level_le_one : ∀ u, ∑_j renewalMass (j,u) ≤ 1`.
This is the decisive sub-lemma for making `Y` explicit (judge pass 24's route step 2).
Reduced to the 1-D height marginal `hold.map Prod.snd` (renewal process on ℤ, increments
`≥3`), proved via the renewal equation `U = δ₀ + F⋆U` (`renewalHeight_eq`) + strong
induction on the level (`renewalHeight_le_one`). New API in `FpLocation.lean`:
`holdSnd_support_ge`, `pmf_map_add_apply`, `iidSum_holdSnd_apply`, `renewalHeight`
(+`_zero_of_neg`/`_eq`/`_le_one`), `renewal_level_le_one`.

**REMAINING for Lap C** (assembly, next resume):
1. Single-step height Chernoff: `∀ T, ∑_d [d.2 ≥ T] hold d ≤ ofReal(e^{-μT})·tiltZ hold (expW2 0 μ)`
   — Markov in the 2nd coord; reuse `tiltZ_hold_snd` closed form + a numeric bound at μ≈0.06
   (analog of `tiltZ_hold_le_num`; `tiltZ_hold_snd_le` gives the ≤ shape but only on |μ|≤1/100 —
   need a fresh numeric bound at μ≈0.0575, or accept a larger Y from a smaller μ inside the box).
2. Assembly via `fpDist_le_renewal_conv`: `∑_e [s+Y≤e.2] fpDist s e ≤ ∑_p [p.2≤s] renewalMass p ·
   (∑_d[d.2≥s+Y-p.2] hold d)`; group by level `u=p.2≤s`, apply `renewal_level_le_one`, reindex
   `w=s-u≥0`, sum the geometric `∑_w e^{-μw}` ⟹ explicit `Y`. Target `Y≈139` (μ*≈0.0575); any
   `Y≤~250` is fine (box dominated by Y; judge re-freezes epsBW regardless).
3. New `fpDist_height_tail_le_sixteenth_sharp : ∀ s, ∑_e [s+Y₀≤e.2] fpDist s e ≤ 1/16` at explicit
   numeral `Y₀`. Leave `fpDist_height_tail_le_sixteenth` (existential) in place; Lap D rewires.

### NEXT (superseded framing) — Lap C: `Y = 139`, re-prove `fpDist_height_tail` OFF X6
`Sec7/ManyTriangles.lean:2522`. Its radius is existential today (sums X6's
`fpDist_location_bound`, `∃`-bound `(cL,CL)`), so the box is not a number — the real
blocker. Do **not** make X6's constants explicit. Route (judge pass 24):
1. `fpDist_le_renewal_conv` — endpoint = a pre-passage point below the budget line
   plus one `hold` step.
2. **Heights strictly increase**: `Δl = 3 + Σv ≥ 3 > 0`, so the walk visits each
   height level **at most once** ⟹ renewal mass per level `≤ 1` (no renewal theorem).
   This is the trick that makes `Y` explicit.
3. `Δl`'s exact MGF (ceiling `μ_c ≈ 0.064`); at `μ*≈0.0575`, tail `≤1/16` at `Y=139`.
   The `Δl` MGF closed form is now available via the same `pascalNe3`/`geomQuarter`
   toolbox used for `B` (`tiltZ_hold_snd`, `tiltZ_pascalNe3_le_num` pattern reusable).
Then **box = √(⌈(5·139+64)/16⌉² + 139²) = √(48² + 139²) ≈ 147** — report to judge; the
`epsBW` re-freeze (`10⁻⁹⁰ → 10⁻¹⁰⁰⁰`, sep≈230) is the judge's, and Lap D lands after.

The `ManyTriangles.lean` split (BLUEPRINT §2) is still queued; it was deferred this
lap because `B` lives in `FpLocation.lean` (split-independent) and the crux advance
outranked the refactor. Do the split immediately before Lap C (which edits the big
file) to get fast iteration.

## Lap 60 (cont): **X11b PROVED** — `deterministic_encounter_claim` axiom-clean

- The (7.67) crux is machine-checked (`#print axioms` = trust base): outside E∗,
  ≤K whites and g-deep positions force fold count ≥ R within
  `encWindowIter A K R` steps. Engine: `encFoldAt` stopped-state machinery;
  `encFoldAt_barrier_le` (barrier ≤ height + 2·4^A(1+p)³ via covering-triangle
  top, (7.11) extent `triangle_top_le`, `Real.log_two_gt_d9`);
  `encFoldAt_count_step` (window step: flat count freezes barrier
  (`encStep_barrier_of_count_eq`), heights (+3/step, `pathSum_snd_ge`) clear the
  envelope after ⌈4^A(1+p)³⌉+1 steps, pigeonhole vs hfew finds a black position
  (`black_of_notMem_whiteStrip`), encounter fires).
- **X11 remaining (in attack order)**: `estar_union_le` (X11a — assembly of
  proved `triangle_encounter_le` through `iid_pathSum_law`; the 1/s' terms sum
  via Σ(1+p)⁻² ≤ 2, exp terms geometric); `few_whites_le` (X11c join);
  `Q_black_edge_case3_assembled` (X11d bookkeeping).
- Gotchas: `rw [encStep] at h ⊢; split at h` leaves the goal's dite unreduced —
  `rename_i hq; rw [dif_neg hq]` for the else-branch; un-beta-reduced
  `(fun i => …) a` blocks omega — `simp only [] at h` or `show` first; a `set`
  doesn't fold NEW terms (coveringTriangle proofs) — bridge with
  `have h' : … := h` (proof irrelevance makes it defeq); triangle_top_le needs
  its implicit `q` given explicitly when the expected type mentions only `q.2`.


## Lap 60: **X11 DECOMPOSED** — `Sec7/Case3.lean` created; (7.53) master iterate PROVED

- **Architecture**: `Q_black_edge_case3`'s proof must consume X9/X10 (which live in
  ManyTriangles, importing BlackEdge), so the assembly lives in NEW `Sec7/Case3.lean`
  downstream; `Q_black_edge_case3_assembled` pins the identical statement. When it
  closes, relocate `Q_black_edge`/`prop_7_8` there and delete BlackEdge's sorry.
- PROVED axiom-clean (`#print axioms` = trust base):
  - `Q_le_walk_damped` / `Q_le_damped_iter` — the (7.53) iterate of (7.35) through
    the first passage + P Hold steps, RETAINING the accumulated white damping (the
    correct indicator is `whiteStrip` = W ∩ strip: the boundary emits no factor).
  - `iid_pathSum_law` — prefix marginal of `hold.iid T` at `p ≤ T` = `iidSum hold p`;
    composed with `fpDist s` gives `fpDistPlus s p`, the exact law X10 bounds.
  - `fstar_markov_le` — p.55 Markov over the encounter fold (consumes X9's
    conclusion as hypothesis `hbound`; `∑ iid·encVal = encExpect` is rfl).
  - `pathSum` API (`_cons`, `_head`, `_succ_of_lt`, `_of_ge`) + fold invariants
    (`encFold_pos`, `encFold_count_le`, `encFold_banked_le`, `encFold_cumWhite`).
- PINNED (4 sorries; **judge ratification requested**, paper anchors in docstrings):
  - `estar_union_le` (X11a, p.54 bottom): Σ_{p≤T} X10 at s'=⌈4^A(1+p)³⌉ ≤ C·A²·4^{−A};
    assembly of `triangle_encounter_le` through `iid_pathSum_law` + Σ(1+p)^{−2} ≤ 2 +
    geometric; no new analysis.
  - `deterministic_encounter_claim` (X11b, p.55 — **THE crux next lap**): outside E∗,
    ≤K whites and staying g-deep force the fold count ≥ R within P₀(A,ε,R,K) steps.
    Plan (docstring): induct on encounter times p_i; barrier after encounter i is the
    top of a `<4^A(1+p_i)³` triangle → cleared in ≤⌈2·4^A(1+p_i)³/3⌉ steps (heights
    ≥3/step, (7.11) extent ≤ s_Δ/log2); then a black point occurs within K+2 steps
    (white/black complementarity at phase point, deep-in-strip); encStep triggers at
    the first one. P₀ = R-fold iterate of p ↦ p+⌈2·4^A(1+p)³⌉+K+2.
  - `few_whites_le` (X11c, (7.56)): the join; K = ⌈10A/epsBW³⌉ whites among T+1
    positions + col<0.9m event; R := ⌈(K+(A+3)log10+2)/ε⌉ makes fold-reaches-R ⊆ F∗
    via `encFold_banked_le`; NB the fold counts whites at offsets p+1 while the
    master iterate counts p — off-by-one absorbed by K+1.
  - `Q_black_edge_case3_assembled` (X11d): mechanical ℝ≥0∞→ℝ bookkeeping;
    `Q_le_damped_iter` + `Q_le_Qm` + col tail (`fpDistPlus_col_tail` at D≈0.05m,
    s/4 ≤ 0.79(m+2) from (7.52)) + `few_whites_le` (weights ≤ m^A / 10^A).
- Gotchas: `open scoped Classical in` goes BEFORE the docstring; `rw [tsum_congr ...]`
  underdetermined — use term-level `(tsum_congr ...).trans`; rewriting a numeral `1`
  that also occurs as `Fin (T+1)` index breaks motives — prove a `pathSum_head`
  lemma without `Fin.cons` in the statement; `PMF.pure_apply` if-condition is
  `d = 0` (use `if_neg hd`, not `Ne.symm`).


## Lap 59: **X10b PROVED** — `encounter_separated_sum` axiom-clean (+ statement fix)

- **STATEMENT FIX (needs judge re-ratification)**: added regime hypothesis
  `(s')² ≤ 1+s` to X10b. Pinned form was FALSE for `s' ≫ √s` (nearest band
  alone carries ~W/√(1+s)). Paper regime from `s' ≤ m^0.4`, `s ≥ m/log²m`;
  consumer `triangle_encounter_le` carries exactly those hypotheses (glue must
  derive `s'² ≤ 1+s`, threshold `log²m ≤ m^0.2` absorbed into its S₀).
- Proved chain (all `#print axioms` = trust base):
  `tsum_int_Gweight_le` (ℤ-row engine) → `separated_Gweight_tsum_le`
  (D-separated set ≤ 4 + K√t/⌊D/2⌋; ≤2 near elements via side-of-μ Bool
  injection, far elements donate disjoint ⌊D/2⌋-blocks toward the centre) →
  `banded_Gweight_tsum_le` (band union ≤ (2W+1)(…); apex+offset injection) →
  `qualifying_apex_separated` (witness row l_Δ+⌊s'/2⌋ + apex_separation ⇒
  apex columns ≥ s'/10 apart; log2 ∈ (0.6931471803, 0.6931471808), log9 < 2.4)
  → `encounter_separated_sum` (fpDistPlus convolution glue, C₃ = 12C'+120C'K).
- **X10 remaining: ONLY the `triangle_encounter_le` glue** (plan in lap-58
  cont-2 entry): trivial branch s' < 100·A²(1+p) via
  fpDistPlus_indicator_sum_le_one; small-s branch s < S₀; main branch
  pointwise indicator split 1_{bigTriangleSet} ≤ 1_{heightEsc}+1_{colEsc}+
  1_{proximity} (X10a) with tails at H = 2A²(1+p), D = s^0.6, then X10b at
  W = 2A²(1+p) (must check 100W ≤ s' and s'² ≤ 1+s in context, plus
  fpDistPlus_support_snd_gt).
- Lean gotchas: `div_le_div_iff` → `div_le_div_iff₀`; ℝ≥0∞ `zero_le` now has
  implicit arg (no `zero_le _`); `le_or_lt` → `le_or_gt`;
  `Int.natCast_floor_eq_floor` bridges ⌊·⌋₊ and ⌊·⌋; after `rintro` on a
  subtype element insert `show` to avoid `↑⟨x,⋯⟩` blocking omega.

## Lap 58 (cont-3): **X10a PROVED** — `encounter_apex_proximity` axiom-clean

- The (7.63)→(7.65) confinement geometry is machine-checked (`#print axioms` =
  trust base): outside E′, a size-≥s' encounter pins the endpoint column to the
  triangle's apex within 2A²(1+p) and pins the (7.65) lower-tip window. The
  "well below" case builds `jst := min (j+e.1) (t'.1 + ⌊bud/log9⌋₊)` at row l_Δ
  in BOTH triangles, killed by `not_mem_two`; t' ≠ t₀ since the endpoint height
  exceeds l_Δ. Constants: C₂ = 2, S₀ = 10⁸; the A²(1+p) ≤ 3s/25 chain runs
  hbig → s' ≤ m^{0.4} → log²m ≤ m^{0.6}/0.09 (log_le_rpow_div) → m^{0.4} ≤ 12s.
- Lean gotchas hit: `linarith` chokes on `0.09`-style OfScientific literals
  (rewrite to fractions first); big-context `nlinarith` timeouts fixed with
  `linarith only [...]` + explicit `mul_le_mul` product hints; a trailing
  in-tactic `calc` greedily eats following dedented `have`s (use `exact`);
  `∑' (a b : X),` needs one paren group per binder.
- REMAINING for X10: **X10b `encounter_separated_sum`** (p.54 sum, plan in its
  docstring) + the `triangle_encounter_le` glue (branches + tails, plan in
  lap-58 cont-2 entry below).

## Lap 58 (cont-2): X10 assembly DECOMPOSED — X10a/X10b pinned

- `triangle_encounter_le` decomposed per pp.52–54 into two named src sorries
  (NEEDS JUDGE RATIFICATION next pass):
  - **`encounter_apex_proximity`** (X10a, p.53): outside E′, membership in a
    size-`≥s'` triangle t' forces (7.65) (|lower tip − l_Δ| ≤ C₂A²(1+p)) and
    apex proximity (0 ≤ j+e.1 − j_{t'} ≤ C₂A²(1+p)). Proof plan: the "well
    below" case builds an integer point (j', l_Δ) ∈ t' ∩ t₀ — (7.64) keeps
    j'−j ≈ s/4 inside t₀'s slope budget s_Δ ≥ s·log2 (¼log9 < log2, with an
    S₀-threshold in s absorbing O(s^{0.6})+O(A²(1+p)) slack; verified on paper:
    0.144s budget needs s^{0.6} ≤ s/40 i.e. s ≥ ~7.3e4) — contradicting
    not_mem_two (t' ≠ t₀ since endpoint height > l_Δ). Then (7.11) for t'
    confines the column.
  - **`encounter_separated_sum`** (X10b, p.54): P(endpoint column within W of a
    qualifying apex) ≤ C₃W/s'. Plan: p.54 interval argument at row
    l_* = l_Δ + ⌊s'/2⌋ feeds apex_separation (PROVED) → apexes ≫s'-separated;
    2W+1-bands at s'/10 spacing; fpDistPlus column marginal = fpDist_col_le ⋆
    Hold (row engine is centre-uniform so drift is free).
- **Glue TODO** (mechanical but long): trivial branch s' < 100A²(1+p) (RHS ≥ 1
  via C ≥ 100²); small-s branch s < S₀ (bounded s bounds m ≤ ~S₀log²S₀, s',
  A²(1+p) ≤ s'/100 → absorb into C·e^{−cA²(1+p)}); main branch pointwise
  indicator split 1_{bigTriangleSet} ≤ 1_{heightEsc} + 1_{colEsc} + 1_{proximity}
  (X10a supplies the third), tails at H = 2A²(1+p) (margin needs A ≥ 5) and
  D = s^{0.6} (margin 10(1+p) ≤ s^{0.6} from 1+p ≤ s'/(100·25) ≤ m^{0.4}/2500 and
  log^{1.2}m ≤ 6^{1.2}·m^{0.2} via Real.log_le_rpow_div); then
  e^{−c·s^{0.2}}-type terms ≤ CA²(1+p)/s' via e^{−y} ≤ 6/y³ + s' ≤ m^{0.4}.
  Also needs small support lemma fpDistPlus_support_snd_gt (hold heights ≥ 3).

## Lap 58 (cont): BOTH (7.61) tails PROVED — `fpDistPlus_col_tail` lands

- **`fpDistPlus_col_tail` PROVED axiom-clean** (2026-07-13): `fpDist_col_dev`
  (`P(|f.1−s/4| ≥ D) ≤ C(e^{−cD²/(1+s)} + e^{−cD})`, by exponent-halving on the
  Gweight tail — each piece donates a prefactor at `|x| ≥ cD`, leaving a
  rate-`c/2` Gweight the row engine sums) + `holdSum_col_tail` (Chernoff at
  tilt `(1/1000, 0)`, `e^{5p/1000 − y/1000}`) + the same ℝ≥0∞ convolution glue
  (split `1_{2D ≤ |f.1+w.1−s/4|} ≤ 1_{D ≤ |f.1−s/4|} + 1_{D ≤ w.1}`).
- X10's remaining work is now ONLY the `triangle_encounter_le` assembly:
  (a) the (7.60) trivial branch `s' < C·A²(1+p)` via
  `fpDistPlus_indicator_sum_le_one`; (b) outside the escape event `E′` (the two
  proved tails at `H = 2A²(1+p)`, `D = s^{0.6}`-ish), the endpoint is confined
  to a window meeting only (7.63)–(7.65)-separated triangles; (c) the
  Σ-separated Gaussian sum via `apex_separation` + the row engine. (b) is the
  next hard sub-step: the confinement/geometry argument (pp.53–54) relating the
  window to `bigTriangleSet` membership.

## Lap 58: `fpDistPlus_height_tail` PROVED (X10's (7.61) height tail, axiom-clean)

- The 4-step lap-57 plan executed in full, all axiom-clean (`#print axioms` =
  trust base, 2026-07-13): (i) **`sum_range_Gweight_le`** — Gweight row-sum
  engine `∑_{j<N} Gweight(t, c(j−μ)) ≤ K√t`, uniform in real centre μ and N
  (double-cover to `⌊μ⌋` + `sum_abs_int_le` + `sum_range_exp_neg_sq_le` +
  geometric); (ii) **`fpDist_height_tail`** — `P(f.2 ≥ s+y) ≤ Ce^{−cy}` in
  ℝ≥0∞ form (X6 envelope: `e^{−c(l−s)}` donates `e^{−(c/2)y}`, row engine
  cancels the `1/√(1+s)`); (iii) **`holdSum_height_tail`** — p-step Chernoff at
  tilt `(0, 1/1000)`, `≤ e^{17p/1000 − y/1000}`; (iv) **glue** — pointwise
  `1_{s+H≤f.2+w.2} ≤ 1_{s+H/2≤f.2} + 1_{H/2≤w.2}` after PMF.bind/map expansion,
  all in ℝ≥0∞ (no summability side conditions — this was the right call, zero
  Fubini pain), final constants `c = min(cB/2, 1/6250)`, `C = CB+1`.
- The statement moved from its lap-57 pin site (line ~274) to the end of the
  file (needs the engines); a pointer comment remains. Statement UNCHANGED —
  the lap-57 judge-ratification queue item still covers it.
- NEXT: **`fpDistPlus_col_tail`** — same skeleton, column direction: pointwise
  split `1_{2D≤|(f+w).1−s/4|} ≤ 1_{D≤|f.1−s/4|} + 1_{D≤w.1}`; the fp column
  piece from `fpDist_col_le` (Gweight ≤ e^{−cD²'ish} + e^{−cD} needs the
  Gweight-tail bound at distance D, giving BOTH terms of the pinned RHS) and
  the w-piece from `holdSum_halfspace_le` at `(1/1000, 0)` (col mean 4/step,
  margin `10(1+p) ≤ D` gives exponent `5p/1000 − D/1000 ≤ −D/2000`). Then the
  (7.65) Σ-separated sum (`apex_separation` + Gaussian-AP engine), then the
  `triangle_encounter_le` assembly.

## Lap 57: 51/100 pin LANDED · `gaussian_col_tail` PROVED · ROUTE ESCALATION on (7.50)

- Judge pass-16 demand discharged (`3c95898`): `fpDist_white_exit_deep` pin is
  now `51/100 ≤ p₀` (witness 3/4 unchanged); `many_triangles_white`'s ε₀-floor
  `≥ 1/100 ≥ 10⁻⁴` certified by arithmetic.
- `gaussian_col_tail` PROVED (`813c9e7`) via new `hasSum_nat_tail_exp` (ℕ-tail
  shifted geometric): Gaussian piece dominated at rate `c²/20` using
  `20·x₀ ≥ t` from the budget + `9⁵ ≤ 2¹⁶`; prefactor `e^{-γx₀}` pushed below
  `1/(8D)` by a `Nat.ceil` threshold. **`fpDist_out_of_strip_le` is axiom-clean**
  (`#print axioms` = trust base).
- **ROUTE ESCALATION** (`ROUTE-ESCALATION-2026-07-13.md`): `F.separated` is
  VACUOUS at `epsBW = 10⁻⁴` (sep² ≈ 0.848 < 1 = min lattice distance²; X3
  proves the clause BY this vacuity, `Triangles.lean:1211`). The (7.50)
  whiteness ring needs separation > overshoot-O(1), so
  **`fpDist_any_triangle_le` is unprovable from the interface** — and so is any
  positive white-mass pin (the fallback `c₀ > 0` dies too). White-exit kernel
  (X9's input, X8's twin) BLOCKED pending an altitude ruling. Remedies: (A)
  shrink ε + formalize real Lemma-7.4 separation; (B) vertical white-gap lemma
  from the fibre structure (~13 rows at current ε; PROBE FIRST, numerics via
  check-8 harness); (C) re-route Case 2. Recommendation: probe (B).
- Non-blocked crux queue: X10 assembly (`triangle_encounter_le`, apex route is
  disjointness-based, unaffected); row-tail lemma `P(overshoot ≥ H) ≤ Ce^{-cH}`
  (needed under every remedy).
- Lap-57 cont (X10 statement design, commits `854f0f5`+): `triangle_encounter_le`
  re-pinned `∃A₀ ≥ 1, ∀A ≥ A₀` (the ratified `∀A>0` was FALSE — height drift
  `16p` outside the `A²(1+p)` window at small `A`; needs judge re-ratification).
  Two (7.61) tails pinned: `fpDistPlus_height_tail` (margin `50(1+p) ≤ H` —
  NB height mean is 16/step, first-pinned `10(1+p)` was below drift, corrected),
  `fpDistPlus_col_tail` (margin `10(1+p) ≤ D`, col mean 4/step, fine).
- **Proof plan for `fpDistPlus_height_tail`** (next): (1) missing engine
  `tsum_Gweight_row_le`: `∃K, ∀t ≥ 1, ∀μ, ∑'_{j:ℕ} Gweight(t, c(j−μ)) ≤ K√t` —
  double-cover to integer offsets (tsum analogue of `sum_abs_int_le`, reduce
  real centre μ to `⌊μ⌋` at cost `f(max(m−1,0))`), then `sum_range_exp_neg_sq_le`
  (uniform in N ⟹ tsum bound `3+2√t/c`) + geometric. (2) fp row tail
  `P(f.2 ≥ s+y) ≤ Ce^{-cy}`: sum `fpDist_location_bound` — `l`-tail geometric
  (`hasSum_nat_tail_exp`-style ≥ s+y version), `j`-sum by the new engine. (3)
  `p`-step tail via `holdSum_halfspace_le` (`l1=0, l2=1/1000`, cond `y ≤ d.2`,
  `Classical.decPred`; exponent `17p/1000 − y/1000`). (4) glue: PMF.bind Fubini
  in ℝ≥0∞, pointwise `1_{s+H ≤ (f+w).2} ≤ 1_{f.2 ≥ s+H/2} + 1_{w.2 ≥ H/2}`.
  Same skeleton then gives `fpDistPlus_col_tail` (Gweight column deviation +
  `l1=1/1000` halfspace).

## Lap 56 (review + crux advance): white-exit kernel DECOMPOSED; reduction glue + overshoot exclusion PROVED

Review: X9 `many_triangles_white` verified CLOSED modulo exactly
`fpDist_white_exit_deep` (`#print axioms` = trust base + `sorryAx`;
`encExpect_entered_le` axiom-clean). Directive promoted the shared white-exit
kernel to THE active move; STATUS + DIRECTION refreshed (commit `2d9747c`).

**Crux advance** (`Sec7/ManyTriangles.lean`, commit pending): `fpDist_white_exit_deep`
is now **PROVED** from a clean (7.50)-geometry decomposition. The old monolithic
sorry → two named analytic sub-sorries + one proved helper + axiom-clean glue:

- **`endpoint_notMem_start_triangle`** (PROVED, axiom-clean): the (7.50) "clears
  the apex" step. `fpDist_support_snd_gt` gives `s < e.2`; with `s = l_Δ - l` the
  phase height `l+e.2 > l_Δ`, and `triangle` needs height `≤ l₀`, so the endpoint
  is outside the START triangle. This is why `phaseInFamily` = the FOREIGN mass.
- **`outStripSet` / `phaseInFamily`** (new defs): the two complement pieces of the
  white strip. Split via `white = ¬black` + `F.cover`: an endpoint is bad ⟺ its
  phase point overshoots `⌊n/2⌋` (out-of-strip) OR its phase point (`(q.1-1,q.2)`)
  lands in some family triangle (non-white). Cover needs `p.1+1 ≤ n/2`, supplied
  by ¬out + `1 ≤ n/2-m+e.1`.
- **Reduction glue** (PROVED, axiom-clean): pointwise `1_W(q) ≥ 1 - 1_out(q) -
  1_tri(q)`, then `∑ fpDist·(1-1_out-1_tri) = 1 - outMass - triMass` (via
  `Summable.tsum_sub` + `fpDist_tsum_toReal`) `≥ 1 - 1/8 - 1/8 = 3/4`, and
  `tsum_le_tsum` lifts the pointwise bound. `p₀ := 3/4 > 1/2` clears the chain cap
  comfortably (numeric white-exit mass ≈ 0.99, harness check 9).

**Lap 56 cont — shared prerequisite LANDED** (`Sec7/ManyTriangles.lean`, both
axiom-clean, `lake build` green):
- **`hasSum_int_shift_exp`** (PROVED): a support-shifted exponential over `ℤ`
  sums geometrically — `∑_{l>s} e^{-c(l-s)} = e^{-c}/(1-e^{-c})`. Route: ℤ→ℕ
  split (`HasSum.of_nat_of_neg_add_one`, neg part = 0), then ℕ-shift by `s+1`
  (`hasSum_nat_add_iff'`, front sum = 0), then `hasSum_geometric_of_lt_one`.
- **`fpDist_col_le`** (PROVED): the first-passage COLUMN MARGINAL —
  `∑'_l (fpDist s (j,l)).toReal ≤ C'·Gweight(1+s, c(j-s/4))/√(1+s)`. Collapses
  X6's `fpDist_location_bound` over the height `l` (support `l>s` kills the
  `e^{-c(l-s)}` factor geometrically via the helper above). This is the SHARED
  prerequisite both tails need: `fpDist_out_of_strip_le` sums it over `j>m`;
  `fpDist_any_triangle_le` reads column-wise Gaussian decay off it.

**Lap 56 cont-2 — `fpDist_out_of_strip_le` PROVED** (`Sec7/ManyTriangles.lean`,
build green): the whole probabilistic structure is now machine-checked, reducing
the tail to ONE isolated pure-analysis sorry:
- Fubini (`Summable.tsum_prod'` + fiber summability via `comp_injective`) factors
  the 2-D endpoint sum into column marginals; each column `≤ fpDist_col_le`;
  the indicator collapses to `if m < e.1`; the (7.52) budget is cast from
  `budget_le_of_mem_triangle`. `fpDist_out_of_strip_le` now depends only on
  **`gaussian_col_tail`** (`#print axioms` = trust base + `sorryAx` via it alone).
- **`gaussian_col_tail`** (the remaining sorry): pure real-analysis — for fixed
  `c>0, C'≥0`, `∑_{j>m} C'·Gweight(1+s, c(j-s/4))/√(1+s) ≤ 1/8` once `m ≥ Cthr`,
  under budget `s·log2 ≤ (m+2)·log9`. Split `Gweight = exp(-x²/t)+exp(-|x|)`:
  the `exp(-|x|)` part is geometric in `j` (reuse `hasSum_int_shift_exp`-style,
  now over ℕ); the `exp(-x²/t)` part needs the half-line Gaussian tail
  `exp(-x²/t) ≤ exp(-x₀·x/t)` (from `x² ≥ x₀·x` on the tail `x ≥ x₀ = m+1-s/4 > 0`),
  then geometric. Both `≤ 1/16` for `Cthr` large (the gap `x₀ ≥ ~0.2m → ∞`).
  `FpLocation` finite-range analogues: `sum_range_exp_neg_sq_le`, `sum_exp_geom_le`.

Gotcha (lap 56): `Summable.tsum_prod'` takes TWO args — `Summable f` AND
`∀ b, Summable (fun c => f (b,c))` (fiber summability); pass the latter via
`hgsum.comp_injective (fun c1 c2 h => by simpa using h)`. After the `rw`, the
goal carries `(b,c).1`; normalise with `show … (if m < a …)` (defeq) before the
final `exact`, else the `tsum` function comparison won't reduce the projection.

**Next attack — the two residual analytic sub-sorries** (both consume X6
`fpDist_location_bound` via `fpDist_col_le`; both are the SAME geometry shared with
X8's Case-2 twin):

1. **`fpDist_out_of_strip_le`** (`≤ 1/8`): Gaussian `j`-tail. From X6,
   `(fpDist s (j,l)).toReal ≤ (D·K)·exp(-cF·(l-s))/√(1+s)·Gweight(1+s, cF·(j-s/4))`.
   Sum over `j = ⌊n/2⌋-m+e.1 > ⌊n/2⌋` (i.e. `e.1 > m`) and all `l`. The budget
   `s·log2 ≤ (m+2)·log9` (derive via `budget_le_of_mem_triangle` at the phase
   point `(⌊n/2⌋-m-1, l)`, `hjm : ⌊n/2⌋ ≤ (⌊n/2⌋-m-1)+1+m`) gives `s/4 ≤ 0.8m`,
   so `e.1 > m` is a `≥ ~0.2m ≥ ~3s/4·(…)` right-deviation of a Gaussian centered
   at `s/4` with scale `√(1+s)` — tail `≤ 1/8` for `m ≥ Cthr`. PROBE FIRST: does
   X6's `Gweight` sum over a half-line give an explicit exp-small bound? (check
   `Gweight` def + any existing `∑ Gweight` lemma in `FpLocation`/`LocalBound`.)
2. **`fpDist_any_triangle_le`** (`≤ 1/8`): the separation fight. `phaseInFamily`
   mass = foreign mass (start excluded). Each foreign triangle t'' is
   `(1/10)log(1/ε) ≈ 0.92` from t (`F.separated`); the (7.11) slope band confines
   the endpoint to an `O(1)` slab about t's diagonal; sum the Gaussian envelope
   over the `≫`-separated foreign apexes (reuse the `apex_separation` +
   Gaussian-AP engine that X10 uses). This is the genuinely hard half.

**Derive X8's twin**: `fpDist_white_exit` (BlackEdge.lean) has the SAME conclusion
+ the extra `s ≤ m/log²m` hyp (unused for whiteness). Once the two sub-sorries
land, `fpDist_white_exit` follows by discarding that hyp and reusing the same
decomposition (or citing `fpDist_white_exit_deep` directly — `p₀ = 3/4 > 0`).

## Lap 55 (cont-2): **LEMMA 7.9 CLOSED (modulo its one kernel)** — `many_triangles_white` PROVED

Directive step 2 done in the same lap as the design. The (7.57) pin is now a
THEOREM; `#print axioms many_triangles_white` = trust base + `sorryAx` via
exactly `fpDist_white_exit_deep` (the pinned external input, directive step 3).
New machinery, all verified `[propext, Classical.choice, Quot.sound]`:

- `encExpect_block_le` GENERALIZED: the `s/3 + 1 ≤ T` horizon hypothesis is
  REPLACED by `∀ e, encVal ε R σ ≤ f e` — the bridge now holds at EVERY horizon
  (short-horizon leftovers keep `encVal` constant mid-block and `fpDist` has
  mass 1, so the pointwise domination absorbs them). This removed the entire
  small-`T` case split the lap-54 plan was stuck on.
- `encExpect_wander_le` hfresh RESTRICTED to the entered class (`∀ hcov`-form
  over `coveringTriangle` — proof-irrelevance makes the barrier field equation
  rewrite cleanly). This kills the divergent general-fresh Z-channel: wander
  encounters always normalize onto ENTERED states.
- **`encExpect_entered_le` (the Y-induction, AXIOM-CLEAN)**: entered states are
  ≤ `encChainX ε p₀`, by induction on the budget `R`; per block the bridge maps
  exits through `f = 1_W + e^εX·1_{¬W}`; instant re-encounters normalize via
  `encExpect_normalize_init` (white banks `e^{ε−1}X ≤ 1`), wander exits carry
  their credit into the wander lemma; the fixed point
  `e^εX − (e^εX−1)p₀ = X` (`encChainX_fixed`) closes the induction. The white
  mass `≥ p₀` enters as HYPOTHESIS `hwhite`, so this theorem is clean.
- `many_triangles_white`: init = credit-0 wander state; `ε₀ := min(1/100,
  (2p₁−1)/2)` with `p₁ := min p₀ 1`; smallness via `e^ε(1−ε) ≤ 1`; final bound
  `max 1 (e^ε·X) ≤ e^{2ε}` via `encChainX_le_exp`. Gate `g := Cthr` of the
  kernel — exactly what makes `hwhite` available at every gated encounter.
- `fpDist_tsum_toReal` helper.

**Note for the judge**: `encounter_two_mass_bound` / `encounter_vertex_bound`
ended up NOT consumed by the final gluing (the fixed-point computation is done
inline via `encChainX_fixed` in `encExpect_entered_le`); they remain as the
ledger's documentation/alternate route.

**Next (directive step 3)**: `fpDist_white_exit_deep` — X9's only remaining
input; prove GENERAL then derive X8's `fpDist_white_exit`. Route: X6
`fpDist_location_bound` concentration + `fpDist_support_snd_gt` top-clearing +
X3 separation excludes other triangles + in-strip via `s = O(m)` ((7.52)).
Then X10 (fpDistPlus location bound first).

## Lap 55 (cont): DEPTH-GATED FOLD LANDED — directive step 1 done, X9 gluing unblocked

`encStep`/`encExpect` now carry a gate `g : ℕ`: the encounter condition's strip
conjunct is `q₁ + g ≤ n/2` (so `g = 0` IS the previously-ratified encoding,
definitionally). All ten fold lemmas threaded and re-verified
`[propext, Classical.choice, Quot.sound]` (real runs): succ/le/of_count_ge/anti/
normalize(_init)/of_edge/wander_le/shift/block_le. `encExpect_of_edge` is now the
SHALLOW freeze (`n/2 < pos₁ + g ⟹ encExpect = encVal`) — exactly the near-edge
case of the Z-induction. `many_triangles_white` re-pinned with `∃ g : ℕ` and a
SECOND DEVIATION docstring (near-edge gate; paper anchors (7.59)/p.50/p.51 +
consumer verification vs (7.54)/p.55). **Judge: re-ratification requested** — the
encounter-fold encoding and the (7.57) pin both changed (pass-12 tripwire
anticipated this).

Gotcha: the block bridge's observable was named `g` (`∀ g : ℕ × ℤ → ℝ`) and
shadowed the gate — renamed to `f` inside `encExpect_block_le` only.

**Next (directive step 2)**: the Z-induction gluing of `many_triangles_white`,
per the lap-54 cont-4 plan, now with the near-edge branch discharged by
`encExpect_of_edge` (frozen, value = encVal ≤ e^{ε·count−banked}; entering states
have banked ≥ ... handle via the normalized fresh-state shape) and every gated
encounter deep enough for `fpDist_white_exit_deep`. Fresh states: `Z(ρ) := sup`
over `⟨q, b, 0, 0, 0⟩` of `E_ρ`; induction on ρ; per block `encExpect_block_le`
with the two-mass split (`encounter_two_mass_bound`, monotone in Z above the
fixed point); white mass from `fpDist_white_exit_deep` (still the open external
input — directive step 3).

## Reflection — 2026-07-12 (lap 55, deep reflection; strong-model altitude pass)

### Route verdict: **CONTINUE** — no registered trigger has fired

- **T1** (D6 finitization forces measure theory): tested and CLEARED in lap 52 —
  the encounter-fold encoding carried the head-peel recursion, block bridge,
  CLAIM-G coupling, all proved axiom-clean. No infinite-product measure anywhere.
- **T2** (ε = 10⁻⁴ separation too weak for the (7.65) Σ-sum): re-grounded against
  the actual pp.52–54 text this lap. The ≫s′ separation of Σ comes from Lemma
  7.4's *integer-disjointness* of apex intervals plus (7.60) `s′ ≥ CA²(1+p)` —
  NOT from the raw 0.92 constant — and that geometric core is already PROVED
  (`apex_gap`, `apex_separation`, `not_mem_two`). T2 is unlikely to fire; keep it
  registered until the Σ-sum closes in Lean.
- **False-summit check**: laps 50–54 closed X6, X1, X2, X5 as whole nodes, each
  re-verified clean this lap with real `#print axioms` runs. No recurring
  "almost-cracked" claim; the one confidence downgrade (X9 75→70) had a concrete
  cause (the confirmed paper gap). This is real motion, not circling.
- **Destination check**: no prior art (web-checked 2026-07-12; nothing beyond
  unrelated conditional/full-conjecture Collatz artifacts). Full discharge
  remains the realistic endpoint: every kernel attacked so far has fallen, and
  nothing on the remaining path looks generational.

### The load-bearing finding: X9's near-edge regime is a STATEMENT-truth risk

The lap-54 "NEEDS DESIGN" caveat is sharper than recorded. `fpDist_location_bound`
is unconditional in `s`, but the white-exit lower bound genuinely FAILS at depth
`m < Cthr` (the endpoint's `j`-advance `≈ s/4 = O(m)` can leave the strip: the
whiteStrip mass really does collapse near the edge — it is not merely
unprovable-with-current-tools). Since `many_triangles_white` quantifies over ALL
starts and ALL `TriangleFamily` instances, an adversarial family stacked along
the drift line in the edge strip can chain near-edge encounters whose `e^ε`
payments have no white-exit compensation. **The pinned `exp(2ε)` is plausibly
FALSE as stated.** The paper's own proof glosses exactly this: its (7.59) step
says "repeating the proof of (7.51)" — but (7.51)'s geometry needs the triangle
deep. This is a second literature hole adjacent to the judge-confirmed banking
gap (pass 9).

Two fixes, BOTH verified this lap against the actual consumer (pp.49 + 55 read
in full):

1. **Depth-gated fold (RECOMMENDED — keeps `exp(2ε)`)**: change `encStep` to
   count an encounter only when the covering triangle sits at depth
   `≥ Cthr` (equivalently `pos₁ ≤ n/2 − Cthr` at encounter time, `Cthr` = the
   white-exit threshold). Consumer-safe: in Case 3 the surviving branch of the
   (7.54) split has `j_{[1,k+P]} < 0.9m`, so the walk stays at depth `≥ 0.1m ≥
   Cthr` (Case 3 has `m ≥ C_{A,ε}`) throughout the (7.67) window — every
   encounter the deterministic claim produces IS deep, so `r ≥ R` still holds
   with the gated count. Cost: rework `encStep` + re-prove ~3 short lemmas
   (`encExpect_of_edge` → `encExpect_of_shallow`: below the gate the fold's
   count/banked freeze, so `encExpect = encVal`), and judge re-ratification of
   the encoding (pass-12 tripwire anticipated an edit here).
2. **∃C re-pin (FALLBACK)**: `encExpect ≤ C` for an absolute `C`. Provable with
   machinery on hand: `pos₁` strictly increases per step (Hold's first coord
   ≥ 1), so the walk spends ≤ `Cthr` steps below the gate line, hence ≤ `Cthr`
   uncompensated encounters, hence a pathwise factor `e^{ε·Cthr}`; total
   `C = e^{2ε + ε·Cthr}`, uniform in `n, ξ, F, R, T, start`. Consumer absorbs
   it: p.55 applies Markov at threshold `10^A`, giving `P(F_*) ≤ C·10^{−A−2}`,
   and Prop 7.3's `∀A` quantifier eats any absolute constant (the paper's
   (7.56) target is "say"-slack).

Either way the X9 assembly becomes downhill — all other ingredients
(`encExpect_block_le`, `encounter_vertex_bound`, `encExpect_normalize(_init)`,
`encExpect_wander_le`, two-mass bound, chain fixed point) are proved. The
two-mass ledger generalizes monotonically to any `Z ≥ encChainX` (the vertex
inequality `p₀ + (1−p₀)e^εZ ≤ Z` is monotone in `Z` above the fixed point), so
mixing the deep bound with a larger edge constant costs nothing.

### Second finding: the p₀ > 1/2 certification burden is softer than recorded

The paper only ever proves white-exit mass "`≫ 1`" at (7.59) — it never needs
1/2. Our corrected ledger needs `p₀ > 1/2` only for the *clean* `exp(2ε)`
constant: for any certified absolute `c₀ > ~ε` the chain value is
`exp(O(ε/c₀))` — absolute, hence consumable by the same p.55 argument. So if
certifying `p₀ > 1/2` through X6's (non-sharp) Gaussian constants fights,
`fpDist_white_exit_deep` may be weakened to `∃p₀ > 0` plus an explicit numeral
`c₀` (e.g. 1/100) without route damage. Judge pass-9's rider stands but is a
constant-quality question, not feasibility.

### X10 re-rated (up): volume, not novelty

Read pp.52–54 in full against the Lean state. The proof is: (7.60) triviality
reduction; escape event E′ = two tail bounds (Lemma 7.7 = X6 ✓ + Lemma 2.2 = S3
✓, applied to `fpDistPlus`); the (7.63)–(7.65) geometric implication (elementary,
apex core already proved); the Σ mass sum = per-point Gaussian location bound
summed over a ≫s′-separated set = `(1/s′)` × the existing Gaussian-AP engine
(`sum_range_exp_neg_sq_le` family). ONE genuinely new prerequisite: a
**fpDistPlus location bound** — Lemma 7.7's bound convolved with `p` extra iid
Hold steps ("(7.48) as before", then Lemma 2.2 for the `l`-tail of the added
steps). Name it, prove it first; the rest is assembly. Confidence 70% → ~78%.

### KEEP / STOP / bookkeeping

- **KEEP**: hardest-first inside §7; per-lemma `#print axioms` verification; the
  judge's statement-ratification loop (it caught the banking gap — it is
  earning its cost); committing every green build.
- **STOP**: carrying the stale "24/26 open sorries" number — ground truth is
  **20** (7 crux: BlackEdge ×4, ManyTriangles ×3; 13 spine stubs). Also stop
  listing X4/X7 as open in prose: `Holding/Monotone/Bridge.lean` are sorry-free;
  their blueprint rows deserve ✅ at the next judge pass.
- **Kernel merge (architecture)**: prove `fpDist_white_exit_deep` GENERAL and
  derive X8's `fpDist_white_exit` from it (its extra `s ≤ m/log²m` hypothesis is
  used only for edgeWeight degradation, per its own docstring) — collapses two
  open kernels into one obligation.

### Priority order (binding version in DIRECTION.md)

1. X9 near-edge design: implement the depth-gated fold (fallback: ∃C re-pin);
   flag the edited statement for judge re-ratification; then close
   `many_triangles_white`.
2. `fpDist_white_exit_deep` (then derive the X8 twin).
3. X10: fpDistPlus location bound → E′ → separated-Σ assembly.
4. X11 assembly (`Q_black_edge_case3` internals) + X8 assembly.
5. C8 pin (last RED) opportunistically; spine stubs stay frozen.


## Lap 54 (cont-4): X9 gluing pieces PROVED — wander claim, edge freeze, two-mass bound, fixed point

**Route simplification found while gluing (supersedes the four-mass LP shape):**
the LP collapses to TWO masses. White-credit branches are all ≤ 1 pathwise
(white re-encounter banks the credit: `e^{ε−1}X ≤ e^{2ε−1} ≤ 1`; never-encounter
ends at `encVal = 1`; out-of-strip exit freezes at `encVal = 1` since `pos₁` is
non-decreasing so `pos₁ > n/2` kills the encounter condition forever). Only the
in-strip-black instant-re-encounter mass `d` pays `e^ε·X`, and
`d ≤ 1 − P(whiteStrip exit) ≤ 1 − p₀`. Proved axiom-clean this pass:
- `encChainX_fixed`: `p₀ + (1−p₀)e^εX = X`.
- `encounter_two_mass_bound`: `(1−d) + d·e^εX ≤ X` for `d ≤ 1−p₀`.
- `encExpect_of_edge`: `pos₁ > n/2 ⟹ encExpect = encVal` (fold frozen).
- `encExpect_wander_le`: between-blocks wander with credit `w₀`:
  `E_{R'+1}(T, ⟨p,b,0,w,0⟩) ≤ max 1 (e^ε e^{−w₀} Z)` given fresh-state bound `Z`
  at budget `R'` (T-induction; encounter branch via `encExpect_normalize_init`
  handled ABSTRACTLY — set σ' := encStep …, prove count/banked/cumWhite field
  equations, never name the coveringTriangle barrier).

**Remaining for `many_triangles_white`** (the Z-induction on budget ρ):
`Z(ρ) := sup over fresh states E_ρ(T, ⟨pos,bar,0,0,0⟩) ≤ X` by induction on ρ:
base ρ=0 frozen (`encExpect_of_count_ge`, encVal=1 ≤ X); step: block bridge
`encExpect_block_le` (s := (bar − pos₂).toNat; for non-in-triangle fresh states
s=0 works) with `g e :=` case-split on the endpoint `pos+e`: (i) instant
encounter (encStep enters count 1) → normalize → `e^ε e^{−1_W} Z(ρ−1)`;
(ii) no encounter, in-strip → wander claim with w₀ = 1_W(endpoint);
(iii) `pos₁+e₁ > n/2` → edge freeze value 1. Uniform g-bound:
`g e ≤ if (pos+e) ∈ whiteStrip then 1 else e^ε·X` — the white instant-encounter
case needs `e^{ε−1}X ≤ 1` (`hXe` of the vertex lemma, holds for ε ≤ 1/4 say);
then `Σ' fpDist·g ≤ (1−d) + d e^εX ≤ X` via `encounter_two_mass_bound` with the
white mass from `fpDist_white_exit_deep`. CAVEAT to verify while gluing: the
fresh state entering the Z-claim comes from an encounter at q with (q₁−1, q₂) in
triangle t — matching `fpDist_white_exit_deep`'s start shape needs m := n/2 − q₁
≥ Cthr; for q₁ > n/2 − Cthr (near the edge) the white-exit bound is unavailable —
handle by a separate edge-strip argument (endpoints there leave the strip in
O(Cthr) blocks... or weaken: for those states use the trivial value ≤ e^εX and
argue they only occur ≤ once? NEEDS DESIGN — this is the open faithfulness risk
of the gluing, alongside the p₀-vs-strip-height bookkeeping inside
fpDist_white_exit_deep itself). Then `many_triangles_white` = init case:
s=0 block + `g ≤ e^εX` uniformly + `X ≤ e^ε` ⟹ `≤ e^{2ε}`.


## Lap 54 (cont-3): **CLAIM-G coupling PROVED** — `encExpect_normalize` + `_init` axiom-clean

The X9 state-normalization is done: `encExpect_normalize` (invariant induction —
both folds branch identically off shared pos/barrier; counts/whites advance in
lockstep; banking fires simultaneously since `σ.count < R'+c ⟺ τ.count < R'`;
`encVal` factors pathwise as `e^{εc}·max(e^{−k},e^{−w})·encVal_τ`) and its
consumer instance `encExpect_normalize_init`
(`E_R(T,σ) ≤ e^{ε·σ.count}·max(e^{−banked},e^{−cumWhite})·E_{R−count}(T, fresh σ.pos)`).

**X9 assembly inventory now**: PROVED = encExpect_succ, encExpect_anti,
encExpect_block_le, encExpect_of_count_ge (ρ=0 base), encounter_vertex_bound +
encChainX cap, encExpect_normalize(_init). OPEN = `fpDist_white_exit_deep`
(external, X8-geometry) + the final Y/Z gluing induction inside
`many_triangles_white` (induction on remaining budget ρ = R − count via
`encExpect_of_count_ge` base; per-block: `encExpect_block_le` with
`g e := ` the normalized continuation, vertex-split the fpDist endpoint mass by
(whiteStrip × re-encounter) into the `encounter_vertex_bound` LP; whiteness mass
≥ p₀ from `fpDist_white_exit_deep`). The gluing needs the event-mass bookkeeping:
express `Σ' fpDist·g` split into the four masses — next sub-step.

Gotcha: `refine ... (by dsimp only; omega)` dies with "No goals" when `dsimp`
closes a goal that unification already made rfl; `(by dsimp only <;> omega)` is
vacuous-safe.


## Lap 54 (cont-2): X9 assembly opened — chain arithmetic PROVED, white-exit input named

`ManyTriangles.lean` gains the lap-52 route's real-arithmetic core, all PROVED
axiom-clean: `encChainX` (the sharp instant-re-encounter chain value
`X = p₀/(1−(1−p₀)e^ε)`), `encChainX_den_pos`, `one_le_encChainX`,
`encChainX_le_exp` (the cap making exp(2ε) consumable), and
**`encounter_vertex_bound`** — the four-mass vertex analysis: the per-block
linear program is maximised at `(a,d) = (0, 1−p₀)` where the value is EXACTLY
`X` (the fixed-point identity `p₀ + (1−p₀)e^εX = X`). Plus ONE new named sorry:
**`fpDist_white_exit_deep`** ((7.59)-shaped, sibling of the Case-2 kernel with
the `s ≤ m/log²m` hypothesis removed and mass sharpened to `p₀ > 1/2`; route in
docstring — same geometry, budget O(m) via (7.52)). src sorry count 24→25 by
decomposition (progress, not regression).

**Remaining X9 gap** (`many_triangles_white` sorry): the Y/Z two-level induction
gluing `encExpect_block_le` (proved) + `encounter_vertex_bound` (proved) +
`fpDist_white_exit_deep` (open) + the CLAIM-G state-normalization coupling
(encExpect_anti-style fold induction, statement in lap-52 entry). That coupling
is the next X9 sub-step to formalize.


## Lap 54 (cont): **X2 CLOSED** — `white_cos_bound` (Lemma 7.2 sharp half) PROVED; Sec7/White.lean sorry-free

Chain (all mathlib-elementary): white ⟹ `ε < |θ| ≤ 1/2` (sfrac = `abs_sub_round`)
⟹ `cos(πθ) ≥ 0` ⟹ `|cos πθ| ≤ 1 − 2θ²` (`Real.cos_le_one_sub_mul_cos_sq`,
Jordan-type; `2/π²·(πθ)² = 2θ²` exactly) `≤ 1 − 2ε² ≤ 1 + (−ε³) ≤ exp(−ε³)`
(`Real.add_one_le_exp`), numerics at ε = 1/10⁴ by nlinarith.
**Prop 1.17's sorry surface is now EXACTLY the Prop 7.8 chain** (BlackEdge ×4,
ManyTriangles ×2). Next: X9 R-induction assembly (lap-52 route), X10 Σ-count
(lap-51 route), pin C8 (last RED statement).


## Lap 54 (2026-07-12): **X5 CLOSED (RED→GREEN in one lap)** — Lemma 7.6 (p.42, Hold basics) fully machine-checked

New `Sec7/HoldBasics.lean`, SORRY-FREE, axiom-clean. Clause map: exponential
tail + the "in particular" Lemma 2.2 conclusion were already S3's
`hold_tail_bound`/`hold_local_bound` (direct Chernoff route (7.29)-(7.30));
this lap added **mean (4,16)** (`hold_mean_fst`/`hold_mean_snd`, via generic
`tsum_iid_sum_mul` + `geomHalf_mean`=2, `pascal_mean`=4, `pascalNe3_mean`=13/3
(paper (7.29)), `geomQuarter_mean`=4, `geomQuarter_mean_sub_one`=3) and
**aperiodicity** (`hold_aperiodic`: supp Hold ⊆ x+H forces H=⊤; witnesses
(1,3),(2,5),(2,7),(2,8) → differences (1,2),(1,4),(1,5) generate ℤ²; converse
support lemma `iid_mem_support` added to go with `iid_support_coord`).

**Node status**: the ONLY remaining RED statement-less node is **C8** (§5 first
passage). Next per handoff-h: X2 `white_cos_bound` (cheapest Prop-1.17 shrink),
pin C8, then X9/X10 assemblies (routes in lap-51/52 entries).

Gotchas (corpus-worthy): writing `f (Fin.cons a w i)` in your own statement
fails elaboration (motive metavar) — ascribe `(Fin.cons a w : Fin (n+1) → α) i`;
`ENNReal.tsum_eq_add_tsum_ite` bakes in `Classical.propDecidable`, mismatching
your `instDecidableEqNat` ite — bridge via `by_cases <;> simp`; never backward-rw
an equation whose RHS numeral occurs inside inverses (`rw [← h] with h : a+b=4`
hits the `4` in `4⁻¹`) — use `.trans h.symm` + `ENNReal.add_right_inj`.


## Lap 53 (2026-07-12): **X1 CLOSED (RED→GREEN in one lap)** — (7.4)/(7.5) pairing PROVED; Prop 1.17 a theorem over {X2, Prop 7.8 chain}

**Final state**: `Sec7/Reduction.lean` is SORRY-FREE. `cexpect_pairing` (the (7.5)
crux) proved axiom-clean via: cexpect calculus (`cexpect_bind`/`cexpect_map`/
`cexpect_iid_succ`/`cexpect_norm_le`/`cexpect_const_mul`), `tsum_geom_pair`
(head-pair reindex through the injective zero-extension `(a₀,a₁)↦(a₀+a₁,a₁)` +
`Summable.tsum_prod'`), and `cexpect_pairing_gen` (strong induction, two-coordinate
peel; the ZMod (1.26)-sum split closed by `linear_combination` over the 2-unit
cancellation `inv2_cancel`). Prop 7.1 + Prop 1.17 now rest ONLY on
`white_cos_bound` (X2, elementary: white ⟹ |θ|>ε ⟹ |cos πθ| ≤ e^{-ε³}) and the
Prop 7.8 chain. **X2 is now the cheapest way to shrink Prop 1.17's sorry
surface** — a good small-lap target alongside the X9/X10 assemblies.

Gotchas this lap (for the corpus): `Function.Injective.tsum_eq` wants
`support ⊆ range` but `Function.Injective.summable_iff` wants the ∀-form;
`rw` of numeral-shape `1 = 0+1` under `Fin.cons` breaks motives (state `pre`
equations at syntactic `0+1`/`0+1+1` instead); `set`-bound local defs make
`rw [hsplit]` close goals by set-defeq (a following `simp only [hdef]` then
errors "no goals").

### (superseded lap-53 entry below)
## Lap 53 (2026-07-12): X1 = §7.1 reduction chain RED→YELLOW — Prop 1.17 now a theorem over the §7 sorries

New `Sec7/Reduction.lean` (statements ratifiable vs paper pp.33–35, (7.1)–(7.6)):
- PROVED axiom-clean: `eC_norm/eC_add/eC_intCast/eC_char_add` (additive character
  algebra on `ZMod 3^n`), `fCond_norm_le_one` (7.6), `norm_one_add_eC_neg`
  (half-angle), **`fCond_three_norm` = Lemma 7.2 exactly** (`|f(x,3)| = |cos πθ|`,
  via `χ(7x)=χ(5x)χ(2x)` and `2·xArg = 3^{2j}u2^{1-l}` unit algebra),
  `cexpect_map` (PMF pushforward seam, Fubini via `Summable.tsum_comm'`),
  `expect_mono_le`, `prod_fCond_le_damping` (product ≤ exp(−ε³·#white), consumes
  X2 `white_cos_bound`).
- PIN (the one new sorry): **`cexpect_pairing`** = paper (7.4)/(7.5): `‖S_χ(n)‖ ≤
  E_{b~Pascal^{n/2}} ∏_j ‖fCond(xArg(j, pre b (j+1)), b_j)‖`.
- `key_fourier_decay` (Prop 7.1) MOVED Holding→Reduction and PROVED from
  `cexpect_pairing` + damping + `renewal_white_encounters` (Prop 7.3, proved).
- `charFn_decay` (**Prop 1.17**, Decay.lean) PROVED from Prop 7.1 + `cexpect_map`
  (syracZ is definitionally the (1.26) reversed pushforward).

**Next attack on `cexpect_pairing`** (route in its docstring): induction peeling
TWO `geomHalf` coordinates per step, generalizing over (pair index offset j₀,
accumulated prefix L, phase multiplier 3^{2j₀}2^{-L}): the (1.26) sum splits via
`eC_char_add` into head-pair factor × tail; reindex the head double sum by
`b = a₁+a₂` (uniform over b−1 pairs = `pascal b`; `pascal_eq_map_iid` is the
model); the tail depends on the head only through `b`. Odd-n leftover: peel the
final lone coordinate with `‖g‖ ≤ 1` (triangle ineq). Infrastructure that exists:
`expect_iid_succ`/`tsum_iid_succ_mul` (Prob/Basic), `bridge_vector_gen`
(Bridge.lean) is the direct template — same fold shape, but over pairs and with a
complex product instead of a real exponential. Estimated 1–2 laps.

**Node status after lap 53**: un-pinned RED remaining = X5 (Lemma 7.6 joint tail,
paper p.42: renewal steps have mean (4,16), joint exponential tail, aperiodicity —
needed by X11 assembly) and C8 (§5 first passage). X10 next steps unchanged
(lap-51 entry); X9 R-induction assembly unchanged (lap-52 entry).


## Lap 52 (cont): **ROUTE FINDING — paper's Lemma 7.9 proof has a gap; pin corrected to `exp(2ε)`**

While assembling the R-induction the closure ledger was worked in full detail.
**Finding (flag to host judge):**
1. The paper's p.51 display "conditional expectation given `v₁…v_{k₁}` EQUALS
   `exp(−Σ_{p≤k₁}1_W + ε)·Z(endpoint, R−1)`" is FALSE on the `min(r,R)=1` branch:
   there the true sum stops at `t₁ < k₁`, so the display overcounts damping and
   under-estimates the value — invalid as a step in an upper-bound proof.
2. Correcting the ledger (each encounter's `e^ε` paid by the previous block's
   exit-whiteness) meets an adversarial configuration not excluded by `p₀`-type
   inputs: black-strip exits ARE instant re-encounters (`t_{i+1} = k_i`), while
   white exits stop the chain and their damping is then never counted. Sharp toy
   value: chains of instant re-encounters give
   `E = e^ε·p₀/(1−(1−p₀)e^ε) ≈ exp(ε/p₀) > exp(ε)`.
   So (7.57) with `exp(ε)` is likely UNPROVABLE (perhaps false as stated).
3. **Fix**: pin `≤ exp(2ε)` (valid since `p₀ > 1/2`: `X := p₀/(1−(1−p₀)e^ε) ≤ e^ε`
   for small ε). Consumer-safe: p.55 uses only Markov + a choice of `R` AFTER ε,
   so absolute exponent constants wash out. `many_triangles_white` updated.

**Corrected proof route (next laps), all inputs now identified:**
- Two-level claim over fresh states, induction on remaining blocks ρ, inner strong
  induction on T:
  - `Y(entry-state, ρ) ≤ e^ε·X` for just-entered states (count incremented, barrier
    = covering-triangle top): via `encExpect_block_le` (PROVED) reduce to the fpDist
    exit law; four-mass vertex analysis over (white/nonwhite)×(re-enc/not):
    `E ≤ P(NE) + e^εX(e^{−1}P(E∧w) + P(E∧nw))`, optimum at the
    `d = P(E∧nw) ≤ 1−p₀` vertex forces exactly `X ≥ p₀/(1−(1−p₀)e^ε)`.
  - `Z(generic, ρ) ≤ P₀ + (1−P₀)·supY ≤ e^{2ε}`.
- State normalization σ ↦ fresh: the CLAIM-G coupling
  `E_R(T,σ) ≤ e^{ε(σ.c−τ.c)}·max(e^{−(σ.bk−τ.bk)}, e^{−(σ.cw−τ.cw)})·E_{R'}(T,τ)`
  (same pos/barrier, R−σ.c = R'−τ.c) — provable by the encExpect_anti-style fold
  induction (branches depend only on shared fields; enc equalizes Δbk = Δcw).
- White-exit input: needs a (7.59)-shaped variant of `fpDist_white_exit` WITHOUT
  the Case-2 `s ≤ m/log²m` hypothesis (any family triangle, budget `s = O(m)` via
  (7.52)); the pinned X8 kernel has the restrictive hypothesis — plan: generalize
  the kernel statement when proving it (the route (7.50)+(7.11)+separation does not
  use `s ≤ m/log²m` for whiteness, only for the weight bound), or add
  `fpDist_white_exit_deep` as a sibling sorry.
- Also needed: `encNE`-style no-encounter mass functional if the sharp
  `P₀ + (1−P₀)supY` split is formalized (a simpler indicator fold), or concede the
  cruder `Z ≤ supY ⊔ 1` bound (check it still yields `e^{2ε}` — it does:
  `max(1, e^εX) = e^εX ≤ e^{2ε}`), avoiding the extra functional entirely.

## Lap 52 (2026-07-12): **X9 = Lemma 7.9 PINNED (RED→YELLOW)** — encounter-fold encoding, T1 does NOT fire

`DIRECTION.md` mandate 2 executed. All in `Sec7/ManyTriangles.lean`, green,
new proved decls axiom-clean (`#print axioms` checked).

### The D6 encoding decision (recorded per directive; ratified against pp.50–51, 55)
- **No infinite-product measure needed (route-trigger T1 does NOT fire).**
  The ONLY consumption of Lemma 7.9 is p.55 — Markov on the finite window after
  the first passage (`(j',l') := (j,l)+v_{[1,k]}`, horizon `P`), with all stopping
  times inside the window by the deterministic (7.67) argument. So (7.57) is
  pinned for the FINITE `T`-step walk `hold.iid T`, uniformly in `T` (existing
  `PMF.iid` head-peel machinery, `Prob/Basic.lean`). Finite path space is D1-safe.
- **Stopping times = a left fold**: `EncState` (pos, barrier, count, cumWhite,
  banked) with `encStep`: encounter ⟺ phase point `(q₁−1, q₂)` black-strip AND
  `barrier < q₂`; new barrier := top of `Δ(q)` via `coveringTriangle`; `banked`
  freezes `cumWhite` at encounter `min(r,R)`. So `banked = Σ_{p=1}^{t_min(r,R)} 1_W`
  EXACTLY and (7.57)'s integrand is `encVal ε R (final) = exp(−banked + ε·min(count,R))`.
- **ε existentially small** (`∃ ε₀ ∈ (0,1/100]`), not the fixed section constant:
  closure needs `e^{2ε}(1−(1−1/e)p₀) ≤ e^ε` against the EXISTENTIAL `p₀` of
  `fpDist_white_exit`; consumer insensitive (p.55 picks `R` after ε:
  `R := ⌈(10A/ε_Q³+O(A)+1)/ε⌉` re-closes (7.66)).
- **Index shift**: encounters/white read at phase point `(q₁−1, q₂)`, matching
  `fpDist_white_exit` + `Q_black_edge` glue + `whiteStrip`.

### Proved this lap (axiom-clean)
`encVal_le` (envelope `≤ e^{εR}`), `encExpect_zero` (base), **`encExpect_succ`**
(head-peel recursion `encExpect (T+1) σ = Σ'_d hold(d) · encExpect T (encStep σ d)`
— the p.51 first-block conditioning finitized; proof normalizes by `e^{−εR}` into
`expect_iid_succ`'s `[0,1]` window, then cancels), `encExpect_le`.
PIN: `many_triangles_white` (7.57) — the X9 sorry.

### NEXT for X9 (the proof; in order)
1. **Path→`fpDist` bridge** (decisive): from an encounter state (pos `q` in a
   triangle with top `b`, budget `s = (b − q.2).toNat`), iterating `encExpect_succ`
   until the barrier clears reconstructs `fpDist s` (passage time ≤ `s/3+1`,
   `hold_support_snd_ge`). Bridge at the level of `encExpect` (carry the integrand),
   NOT bare laws; mid-block white damping ≤ 1 may be DROPPED (we prove `≤`). Strong
   induction on `s` mirroring `fpDist`'s budget recursion.
2. **Induction on `R`** (p.51 shape): `Z(R,σ) ≤ P(no encounter) + e^{2ε}·
   E[1_enc e^{−1_W(fp endpoint)}]·sup Z(R−1)`, closed by `fpDist_white_exit`
   (`≤ 1−(1−1/e)p₀ ≤ e^{−ε}`). Truncation branch `t₁ ≤ T < k₁`: `min(r_T,R)=1`,
   value ≤ e^ε directly. `fpDist_white_exit` (X8 kernel) is the only open input —
   needed ONLY at the final closure; do bridge + skeleton first.
3. X11 consumption: Markov over the window + deterministic (7.67) pigeonhole
   (needs 7.10's size bound + (7.11) exit-time bound).

### X10 unchanged (Σ-count assembly = its next step; see lap-51 entry)

## Lap 51 (2026-07-12, REVIEW lap): course-correct to §7-tail de-risk; pin Lemma 7.10, design Lemma 7.9

**Direction set** (see `DIRECTION.md` CURRENT DIRECTIVE): S3 + X6 closed; X8 Case-2
is YELLOW (pinned+routed, kernels unblocked). The last RED §7 nodes are X9/X10
(Lemmas 7.9/7.10 — no Lean statement). Per BLUEPRINT §2 de-risk-breadth-first, pin
X9/X10 (red→yellow) BEFORE grinding X8 to completion. X8 kernels demoted to
finish-when-downhill. Read paper pp.50–54 this lap; both lemma statements captured
verbatim below.

### X10 = Lemma 7.10 (7.60) — PIN THIS (single-marginal, directly expressible)
Paper: `(j,l) ∈ black triangle Δ`, `s := l_Δ − l > m/log²m` (`m = ⌊n/2⌋ − j`),
`k` = first-passage time (Lemma 7.7), `p ∈ ℕ`, `1 ≤ s' ≤ m^{0.4}`. `E_{p,s'}` =
event `(j,l)+v_{[1,k+p]}` lies in a triangle `Δ' ∈ 𝒯` of size `s_{Δ'} ≥ s'`. Then
`P(E_{p,s'}) ≪ A²(1+p)/s' + exp(−cA²(1+p))` (constants uniform in n,ξ).
- **Key win**: `v_{[1,k+p]}` has an explicit MARGINAL law: `fpDist s` (the
  first-passage endpoint, X6 machinery) convolved with `iidSum hold p` (p more
  Hold steps). NO stopping-time path-space needed. Define
  `fpDistPlus s p := (fpDist s).bind (e ↦ (iidSum hold p).map (e + ·))`.
- `E_{p,s'}` = the set `{q | ∃ t ∈ F.T, (s':ℝ) ≤ t.2.2 ∧ q ∈ triangle t.1 t.2.1 t.2.2}`
  pulled back by `e ↦ (j+e.1, l+e.2)` — the `bigTriangleSet F s'` def.
- Statement (in new `Sec7/ManyTriangles.lean`): `∃ C c > 0, ∀ A > 0, ∀ … ,
  Σ' e, (fpDistPlus s p e).toReal · 1_{bigTriangleSet}(j+e.1,l+e.2)
  ≤ C·A²(1+p)/s' + C·exp(−c·A²(1+p))`.
- **Proof step 0 DONE (lap 51)**: `fpDistPlus_indicator_sum_le_one` (event prob ≤ 1
  via PMF total mass) + `fpDistPlus_tsum_toReal` — discharges the (7.60) "trivial
  otherwise" regime (`s' < C·A²(1+p)` ⟹ RHS > 1 ≥ LHS), and is general bookkeeping.
- **Apex geometry DONE (lap 51, axiom-clean)**: `apex_gap` — the "two intervals
  share no integer" step (`not_mem_two`: apex-column point of t'' at height l*
  cannot lie in t') ⟹ `s_{t'} < (j''−j')log9 + (l_{t'}−l*)log2`; and `apex_separation`
  — feeding it the (7.65) condition `l_{t'} − s_{t'}/log2 ≤ l_Δ + δ` + `l* =
  l_Δ + ⌊s'/2⌋`, the `s_{t'}` term CANCELS, giving `(⌊s'/2⌋−δ)log2 < (j''−j')log9`,
  i.e. the ≫s'-separation `j''−j' ≫ s'`. The geometric core of (7.63)–(7.65) is closed.
- **Route** remaining Σ-count assembly (all analytic, inputs are theorems):
  (i) derive the (7.65) height condition `l_{t'} − s_{t'}/log2 = l_Δ + O(A²(1+p))`
  for triangles the endpoint could hit outside E′ (from `fpDist_location_bound` X6 +
  (7.11)); (ii) turn `apex_separation` into "size-≥s' apexes obeying (7.65) form a
  ≫s'-separated ℤ-set Σ"; (iii) sum the X6 Gaussian envelope
  `s^{-1/2}G_{1+s}(c(j'−j−s/4))` over Σ ⟹ `≪ A²(1+p)/s'` via `sum_range_exp_neg_sq_le`;
  (iv) the E′ escape event (7.61) killed by X6 + Lemma 2.2 ⟹ `exp(−cA²(1+p))`.

### X9 = Lemma 7.9 (7.57) — DESIGN recorded, pin next lap (needs recursion object)
Paper: iid Hold `v₁,v₂,…`; stopping times `t₁,…,t_r` (`t₁` = first entry into a
triangle; `t_i` = first time after clearing `Δ_{i−1}`'s top that re-enters a
triangle); `r` = #triangles encountered. Then `E exp(−Σ_{p=1}^{t_{min(r,R)}}
1_W((j',l')+v_{[1,p]}) + ε·min(r,R)) ≤ exp(ε)` for any `(j',l')`, `R ≥ 1`.
- **Encoding problem**: LHS is a functional of the WHOLE infinite walk (stopping
  times couple all `v_i`). D1 forbids the product measure. D6 finitizes via the
  proof's own induction on R (p.51): condition on the first block up to the first
  passage `k₁` over the FIRST triangle's top → recursion `Z(·,R) ≤ P(r=0) +
  ∫ K((j',l'),dq)·Z(q,R−1)`, `Z(·,0)=1`, where `K` = the first-triangle
  first-passage sub-law carrying `exp(−Σ_{p=1}^{k₁}1_W + ε)`.
- **Kernel `K` = the decisive new object.** Recommended encoding (B1): the
  first-triangle first-passage is a plain renewal first-passage to the MOVING
  barrier `= top of the triangle currently covering q` (monotone-height insight
  from X6 ⟹ no barrier condition). Reuse `fpDist`-style budget recursion with a
  position-dependent budget `s(q) = l_{Δ(q)} − l`, `Δ(q)` = the (unique) triangle
  covering `q` via `cover`.
- **Prerequisites DONE (lap 51, both axiom-clean)**:
  `TriangleFamily.not_mem_two` (distinct family triangles share no lattice point,
  from `F.separated` const `≈ 0.92 > 0`; also serves 7.10's (7.65) ≫s′-separation)
  and `TriangleFamily.existsUnique_cover` (every black-strip point lies in exactly
  one family triangle — `cover` existence + `not_mem_two` uniqueness ⟹ `∃!`). The
  covering triangle `Δ(q)` is now well-defined.
  NEXT for X9: (a) turn `existsUnique_cover` into a function `Δ : (strip pt) → T`
  (via `Classical.choose` / `ExistsUnique.choose`) + its spec lemmas; (b) the moving-
  barrier budget `s(q) := (Δ(q).2.1 − q.2).toNat`; (c) the `Z` budget recursion on R
  (mirror `Qstop`/`fpDist` recursion shape, `Unroll.lean`); (d) pin (7.57), close by
  induction on R using `fpDist_white_exit` (7.51).
- Induction close (once pinned): `Σ_{p=1}^{k₁}1_W ≥ 1_W(endpoint)` +
  `fpDist_white_exit` (7.51, X8 open kernel) ⟹ `Z(·,R) ≤ exp(ε)`. So 7.9 CONSUMES
  the open `fpDist_white_exit`; 7.10 does not — pin 7.10 first.
- **Route-trigger T1** (`DIRECTION.md`): if K provably needs an infinite-product
  measure (D1 unbreakable), escalate — do not import measure theory.

### NEXT after this lap
Pin 7.10 (this lap) → probe its (7.63)–(7.65) Σ-counting sub-step → pin the
triangle-disjointness lemma + `Δ(q)` + `Z` recursion + Lemma 7.9 (next lap) →
then X8 finish-when-downhill / X11 Case-3 assembly consuming 7.9+7.10.

## Lap 50 (2026-07-12, seventh box session): **LEMMA 7.7 PROVED — NODE X6 CLOSED**

`fpDist_location_bound` is a theorem, axiom-clean. FpLocation.lean is now
SORRY-FREE: the full chain first-passage decomposition → renewal Gaussian
bound → last-step convolution is machine-checked. New machinery (all
numerically validated before formalizing; 200k-trial clean):
- `hold_step_bound` — one hold step ≤ C₇·e^{-γ|d₁-4|}e^{-γ|d₂-16|}
  (hold_local_bound at n=1 + `Gweight_two_le`: Gw 2 x ≤ 4e^{-x/2}, elementary
  via e^{-x/2} ≥ 1/2 on x ≤ 1 — no ExponentialBounds import needed);
  `iidSum_one_apply`.
- `sum_abs_int_le` — step-1 AP sum with ℤ (possibly negative) centre,
  q := w.toNat, abs_cases+omega per branch.
- `conv_Gweight_exp` — discrete Gaussian×exponential convolution: pointwise
  near/far split at |w-μ|/2, output decay min(c/2, γ/4), constant 4+8/γ.
- `Gweight_shift` — recentring by δ costs 2e^{c|δ|} and half the constant
  (case split |X| ≤ 2|δ| via Gweight_le_two vs |X+δ| ≥ |X|/2).
- `sum_sqrt_exp_le` — Σ_{m≤s} e^{-γ(s-m)}/√(1+m) ≤ (2(1+1/γ)+64/γ²)/√(1+s)
  (Finset.sum_range_reflect for the geometric reindex — no nbij needed).
- Assembly: fpDist ≤ renewal⋆hold truncated to the finite box
  range(j+1) ×ˢ Icc 0 s (`renewalMass_zero_of_snd_neg`/`renewalMass_ne_top`
  kill the complement, tsum_eq_single collapses the step), ENNReal→ℝ via
  toReal_mono + toReal_sum, then per-m: j₁-convolution → shift to centre
  j-s/4 at scale 1+s (δ = (s-m)/4-4, e^{c₉(s-m)/4} absorbed since c₉ ≤ γ/4)
  → m-sum. Final c = min(min(c₆/2,γ/4)/2, γ), C = C₆C₇e^{16γ}(4+8/γ)·2e^{4c₉}K.
  l ≤ s case free via fpDist_support_snd_gt.

Gotchas this lap:
- In a huge proof context (giant tsum equalities in scope) plain
  linarith/nlinarith hit isDefEq TIMEOUTS — use `linarith only [facts]`.
- `positivity` can't see `Gweight` nonnegativity — pass
  `mul_nonneg (by positivity) (Gweight_nonneg _ _)` explicitly.
- `hstep (a, b)` leaves unreduced `((a,b)).1` projections in the
  instantiated statement — `dsimp only at h` before rw.
- `tsum_eq_single` side-goal order: the `if_pos` equality goal comes FIRST,
  the ∀ b' ≠ b vanishing goal second.
- `Prod.ext` via `exact` leaves component mvars (`?m.1 = ?m.1`) — use
  `apply Prod.ext` then `show`-pinned component goals.
- `abs_add` → `abs_add_le` (mathlib rename); tuple type ascription must be
  `((a : ℕ), b)` not `(a : ℕ, b)`.
- `Real.one_le_sqrt` needs `1 ≤ x` — `positivity` can't produce it; use
  `le_add_of_nonneg_right (Nat.cast_nonneg m)`.

NEXT (X8 Case-2 kernels, per lap-46 pin): `fpDist_edgeWeight_le`
((7.48)/(7.49)) — consume fpDist_location_bound j-concentration + Geom(4)
tail via edgeWeight; then `fpDist_white_exit` ((7.50)/(7.51)) — endpoint
localization + family separation; then `Q_black_edge_case2` assembly; X9
Lemma 7.9 skeleton for Case 3.

## Lap 49 (2026-07-12, seventh box session): **renewalMass_bound PROVED** (X6 step 2 COMPLETE)

The renewal Gaussian bound (paper p.44 first display) is a theorem,
axiom-clean: `renewalMass (j,l) ≤ C/√(1+l) · Gweight(1+l)(c(j-l/4))` with
`c = c₀/4`, `C = C₀·C₅` off `hold_local_bound`'s `(c₀, C₀)`. All four pinned
route steps landed in FpLocation.lean exactly as validated numerically:
- `sum_abs_AP_le` — two-branch reindex at `q = w/16` (Finset.sum_image with
  the have-key trick from the corpus; k ↦ q-k / k-q-1).
- `iidSum_hold_snd_zero` + `renewalMass_toReal_eq` — support truncation at
  `k ≤ ⌊l/3⌋` (induction on iidSum_succ_apply + hold_zero_of_snd_lt), tsum →
  Finset sum → toReal-distributed.
- `Gweight_factor` — the AB+CD ≤ (A+C)(B+D) peel: `Gw(1+k)(c₁y) ≤
  Gw(1+l)(c₁/2·x)·(e^{-(c₁²/2)z²/(1+k)} + e^{-(c₁/2)z})` from
  `|x| + (3/4)z ≤ y` (via y² ≥ x² + z²/2), `1+k ≤ 1+l`.
- `renewal_weight_sum_le` — the k-sum envelope `Σ (1+k)⁻¹W_k ≤ C₅/√(1+l)`,
  `C₅ = 32/ε² + 256 + 4/b + 8/√a`, `ε = min(a/8,b/2)`: edge region `k < ⌊l/32⌋`
  killed by `exp_neg_le_four_div_sq` (one application suffices:
  `2(1+l)²e^{-εl} ≤ 32/ε²`), central region by `1/(1+k) ≤ 32/(1+l)` +
  `sum_abs_AP_le` + `sum_range_exp_neg_sq_le` (with `√β·√(1+l) = 16√a`) +
  geometric.

Gotchas this lap:
- `div_le_div_iff` → `div_le_div_iff₀` (mathlib rename); `div_add_div_same`
  gone — use `(add_div _ _ _).symm`.
- `rw [neg_mul, neg_div, neg_mul, neg_div]`: when both sides share the SAME
  numerator, the first `neg_mul` rewrites both sides at once and the second
  fails; chain is `[neg_mul, neg_div, neg_div]`.
- linarith atom traps: `2*(2/√β)` vs `4/√β` and `2*(1/(16b))` vs `1/(8b)` are
  UNRELATED atoms — supply `by ring` bridge equations as hypotheses.
- A single `rw [div_le_div_iff₀ h1 h2] at hA ⊢` cannot hit two locations with
  different denominators (rule elaborated once); rewrite separately or bridge
  with ring equations.
- `Nat.cast_le.mpr (α := ℝ)` fails (named arg goes to Iff.mpr); ascribe the
  `have` type instead.
- omega handles `l.toNat`, `t/3`, `t/32` mixed ℕ/ℤ goals natively — all the
  truncation index arithmetic here was pure `omega`.

NEXT (X6 step 3, the last FpLocation sorry): `fpDist_location_bound` =
`fpDist_le_renewal_conv` + `renewalMass_bound` at the pre-passage point
`(j₁,l₁)`, `l₁ ≤ s` + one `hold` step for the overshoot `(j-j₁, l-l₁)` with
`hold_local_bound`/`hold_tail_bound` at n = 1, split `l₁ ≤ s/2` vs `> s/2`
(paper p.44 closing paragraph). Sub-steps: (a) toReal the ≤-inequality of
fpDist_le_renewal_conv (tsum on the right is finite: renewalMass ≤ 1+stepMass
bounded? — no: bound it by the CONVOLUTION's value directly: each term
renewalMass(p)·hold(e-p) ≤ hold(e-p) is false; instead truncate p-support:
p₂ ≤ s and hold(e-p) ≠ 0 forces e₂-p₂ ≥ 3 and p = e - d with d in hold's
support, so the p-sum is a finite sum over d.1 ≤ j, use toReal_mono +
tsum ≤ over finite index); (b) exp(-c(l-s)) factor comes from hold_tail_bound
n=1 on the overshoot when l - l₁ is large, else from the trivial bound 1
absorbed by adjusting c (for l ≤ s the LHS is 0 via fpDist_support_snd_gt —
handle first). Then X8 Case-2 kernels consume this.

## Lap 48 (2026-07-12, seventh box session): renewalMass_bound TOOLKIT LANDED (X6 step 2 in progress)

Numeric validation done FIRST (python): factorization chain
Gw(1+k, c1*y_k) <= Gw(1+l, c4*x) * W_k for y_k=|j-4k|+|l-16k|, x=j-l/4,
W_k = e^{-a z^2/(1+k)} + e^{-b z}, z=|l-16k|; c1=c0/2, c4=c1/2, a=c1^2/2,
b=c1/2 (c0=1/400 from hold_local_bound) — 200k random trials clean; k-sum
envelope numeric max C5 ~ 500/sqrt(1+l) (Lean-shaped derivation ~6e14, fine).

PROVED this lap (FpLocation.lean, axiom-clean via build):
- `Gweight_anti` (antitone in |x|), `exp_neg_le_four_div_sq` (e^{-u} <= 4/u^2
  from e^{u/2} >= 1+u/2 squared), `one_sub_exp_neg_inv_le_one_add`
  ((1-e^{-u})^{-1} <= 1+1/u), `sum_range_geom_le`,
- **`sum_range_exp_neg_sq_le`**: Sum_{m<N} e^{-beta m^2} <= 3 + 2/sqrt(beta) —
  integral-free M-split (M ~ 1/sqrt(beta) unit terms + m^2 >= Mm geometric
  tail). This is the Gaussian AP sum engine for the renewal k-sum.

REMAINING for renewalMass_bound (route fixed, see lap-47 entry + python):
1. `sum_abs_AP_le`: Sum_{k<N} f(|w-16k|) <= 2 Sum_{m<N} f(16m), f antitone
   nonneg, hypothesis w < 16N. Two branches at q := w/16 (Int ediv):
   16k<=w: z >= 16(q-k), reindex i=q-k via Finset.sum_image (i <= q < N);
   16k>w: z >= 16(k-q-1), i=k-q-1. filter split + sum_le_sum + sum_image +
   sum_le_sum_of_subset_of_nonneg.
2. `iidSum_hold_snd_zero`: (3k:Z) > q.2 -> iidSum hold k q = 0 (induction on
   k via iidSum_succ_apply + hold_zero_of_snd_lt) => k-sum truncates at
   K := l.toNat/3, renewalMass = Finset sum (tsum_eq_sum), 1+k <= 1+l.
3. Per-k: hold_local_bound + ||v||inf >= y/2 + Gweight_anti + the AB+CD <=
   (A+C)(B+D) factorization => P_k <= C0/(1+k) * Gw(1+l,c4 x) * W_k.
4. k-sum: split k < L/32 (z > l/2: W_k <= e^{-(a/8)l}+e^{-(b/2)l}, times
   (l+1) terms, kill by exp_neg_le_four_div_sq: (1+l)^{3/2}e^{-eps l} <=
   6/eps^2 constant) vs k >= L/32 (1/(1+k) <= 32/(1+l), quadratic via
   sum_abs_AP_le + sum_range_exp_neg_sq_le at beta = 256a/(1+l), linear via
   sum_abs_AP_le + sum_range_geom_le). C5 symbolic in a,b; C := C0*C5.

## Lap 47 (2026-07-12, seventh box session): X6 CRACKED OPEN — FIRST-PASSAGE RENEWAL DECOMPOSITION PROVED

NEW `Sec7/FpLocation.lean` (imports HoldLocal; `fpDist_location_bound` moved
here from Unroll). KEY STRUCTURAL INSIGHT formalized: hold steps strictly
increase height (`hold_support_snd_ge`), so a path reaching `p` with
`p.2 <= s` automatically kept ALL partial sums <= s — the first-passage
decomposition needs NO barrier condition, just the PLAIN renewal measure.

PROVED (axiom-clean):
- `renewalMass p := Sum_k iidSum hold k p`, `stepMass`, `renewalMass_eq`
  (delta_0 + stepMass peel via tsum_eq_zero_add' ENNReal.summable),
  `iidSum_succ_apply`, `stepMass_eq_conv` (renewal recursion U = d0 + hold*U).
- `tsum_delta_chain`, `tsum_conv_reindex` — reusable ENNReal delta-convolution
  Fubini helpers (collapse intermediate landing points / reindex p = d + q).
- **`fpDist_le_renewal_conv`**: fpDist s e <= Sum_{p.2<=s} renewalMass p *
  hold(e-p) (delta form). Budget strong induction; INEQUALITY suffices for all
  consumers (upper bounds; (7.50) lower bound = complement since fpDist is a
  PMF). This is X6 step 1 of 3.

OPEN (X6 steps 2-3, both statements pinned with route docstrings):
- `renewalMass_bound`: U(j,l) <= C/sqrt(1+l) * Gweight(1+l)(c(j-l/4)).
  ATTACK: insert hold_local_bound per k, sum in k over three regions
  16(k-1) in [l/2,2l] / < l/2 / > 2l (paper p.44 "routine calculation").
  VALIDATE the envelope numerically in python FIRST (c=1/400 upstream;
  region-2/3 terms need Gweight quadratic-vs-linear case split).
- `fpDist_location_bound` (Lemma 7.7): assembly = fpDist_le_renewal_conv +
  renewalMass_bound at (j1,l1) + hold_local/tail at n=1 for overshoot step,
  split l1 <= s/2 vs > s/2.

Gotchas this lap:
- PMF.map_apply/pure_apply produce `Classical.propDecidable` ites that do NOT
  match hand-written ites (instDecidableEqProd): "synthesized instance not
  defeq". Bridge: `map_apply_ite` proved via `tsum_congr fun a => by congr`
  (congr closes Decidable mismatches via Subsingleton). if_pos/if_neg/by_cases
  are instance-agnostic; only calc-LHS/rw pattern matching breaks.
- `rw [zero_mul]` etc rewrite ALL occurrences of the matched instantiation at
  once — chained duplicate rewrites then fail "pattern not found".
- `exact zero_le _` fails where `zero_le` resolves with implicit arg; plain
  `exact zero_le` works (ℝ≥0∞).

## Lap 46 (2026-07-12, seventh box session): X8/X10 STATEMENT DESIGN — Q_black_edge DECOMPOSED

NEW `Sec7/BlackEdge.lean` (imports Monotone + Unroll; Bridge now imports it;
`Q_black_edge`/`prop_7_8`/`Q_polynomial_decay` moved here from Monotone).
Cases 2-3 of Prop 7.8 (paper (7.44)-(7.67), pp.46-49) pinned as named decls:

PROVED (axiom-clean):
- `TriangleFamily` (bundled Lemma 7.4 data) + `exists_triangleFamily`.
- `Q_fp_endpoint_le` — the (7.46) endpoint step: one Q_rec at the
  first-passage endpoint exposes white damping in subtraction form
  `1 - (1-e^{-eps^3})*1_{whiteStrip}` times `edgeWeight * Qm(m-1)`;
  out-of-strip endpoints absorbed via `edgeWeight_of_deep` + `one_le_Qm`.
- `budget_le_of_mem_triangle` — (7.52): s*log2 <= (m+2)*log9 via lattice
  extent point `(j_D + floor(s_D/log9), l_D)` + confinement (floor slack
  vs paper's m; Case 3 only needs s = O(m)).
- `Q_black_edge` — the case split GLUE: black point -> cover -> triangle,
  s := (l_D - l).toNat, split at m/log^2 m. No longer a monolithic sorry.

OPEN (4 new named sorries replacing the old 1 — deliberate decomposition):
1. `fpDist_edgeWeight_le` ((7.42)+(7.48)/(7.49)): E[edgeWeight] <= (1+delta)m^{-A}
   for s <= m/log^2 m. Consumes fpDist_location_bound (X6) j-concentration
   + Geom(4) tail. NEXT ATTACK: prove X6 first (its inputs hold_local_bound/
   hold_tail_bound are theorems since lap 42) — union bound over last step,
   mirror the paper Lemma 7.7 proof p.43-44 (sum in k of k^{-1}G_k(c(j'-(k-1)4,
   s'-(k-1)16)) with the three-region split).
2. `fpDist_white_exit` ((7.50)/(7.51)): white-in-strip exit mass >= p0 absolute.
   Hardest Case-2 kernel: endpoint at (j+s/4+O(sqrt(1+s)), l_D+O(1)) via X6,
   above-top by fpDist_support_snd_gt, outside other triangles via family
   separation vs the fixed eps=1e-4 ring constants (MC-validated 0.99).
3. `Q_black_edge_case2` assembly: mechanical (7.47) split once 1+2 land
   (delta := (1-e^{-eps^3})p0/2; w >= m^{-A} pointwise for the subtraction).
4. `Q_black_edge_case3` ((7.53)-(7.67)): the X9/X10/X11 subtree — Lemma 7.9
   induction on r over the Q-recursion, Lemma 7.10 separated-Sigma counting,
   P-step iterate of (7.35), 0.9m Chernoff split. NEXT: pin Lemma 7.9's
   statement (stopping times t_i over fpDist iterates, r = #triangles met).

Gotchas: anonymous-constructor membership under Set.indicator_of_mem needs a
named `have hmem : _ ∈ whiteStrip ...` (expected-type inference fails inline);
`linarith` missed `0 <= (1/10)*log(10^4)` from `0 <= log(10^4)` (atom mismatch)
— use `mul_nonneg` directly.

**Red-queue state after this lap** (BLUEPRINT §2 steering): S3 GREEN (lap 45),
X8/X10 statements PINNED (this lap). Next reds: X6 (fpDist_location_bound —
now the single blocker for BOTH Case-2 kernels), X9 (Lemma 7.9 skeleton),
X1 (key_fourier_decay chain), X5 (Bridge x3), C8.

## Lap 45 (2026-07-12, seventh box session): ALL THREE d=1 LOCAL BOUNDS PROVED — **NODE S3 FULLY GREEN**

**`geomHalf_local_bound`, `geomQuarter_local_bound`, `pascal_local_bound` are
theorems** (axiom-clean). With laps 41-44, ALL EIGHT Lemma 2.2 obligations
(hold local+tail, 3× d=1 local, 3× d=1 tail) are machine-checked. Machinery
(LocalInstances.lean):
- `iidSum_nat_local_of_quad` — GENERIC d=1 Lemma 2.2(i): any PMF ℕ with mean
  m ≤ 4, quad MGF bound (K = 1000, box 1/200), and two adjacent atoms
  a, a+1 ≤ 3 of mass ≥ 3/16 gets the local bound (c = 1/400, C = 128).
  Chain: tilted atoms keep mass ≥ 1/6 (weights ≥ e^{-3/200}, Z ≤ 209/200,
  validated 0.1767 ≥ 1/6), decay c = 4 via adjacent-atom lemma, tilted center
  128/√(1+n), tilting identity + signed clip + Gweight evenness (`Gweight_abs`).
- signed `chernoff_clip_le` MOVED HoldLocal → LocalInstances.
- instances: geomHalf (m=2, atoms 1,2), geomQuarter (m=4, atoms 1,2; mass at 2
  EXACTLY 3/16), pascal (m=4, atoms 2,3, both 1/4).
Gotcha: λ is a token — cannot appear in hypothesis names (hλlo fails to parse).

**S3 CLOSED. Next per operator red queue** (BLUEPRINT §2 steering: statement
pinned + route validated + hardest sub-step probed):
1. (X8/X10) `Q_black_edge` (Sec7/Monotone.lean:489) — statement design for
   Prop 7.8 Cases 2/3, eqs (7.46)-(7.53) pp.46-48, over Qstop/fpDist. READ THE
   PAPER PAGES FIRST (papers/ dir has the PDF; also SUMMARY pdf).
2. (X9) Lemma 7.9 induction skeleton over Q_rec consuming Q_white_contract.
3. (X1) key_fourier_decay reduction chain (Fourier side).
4. (X5) three bridge sorries in Sec7/Bridge.lean (hold_tsum_step most
   mechanical: split geomQuarter at k=1, peel one pascalNe3 off PMF.iid).
5. (C8) + X6 `fpDist_location_bound` (Unroll.lean:624) — now UNBLOCKED: it
   consumes hold_local_bound/hold_tail_bound which are theorems as of today.
   Check whether X6 is actually the fastest way to spend the analytic win.

## Lap 44 (2026-07-12, seventh box session): d=1 CIRCLE METHOD BUILT (CharFn1.lean)

NEW `Prob/CharFn1.lean` — the ENTIRE d=1 Fourier engine derived from the 2-D
module via the first-coordinate embedding `embMod N L = (L mod N, 0)` (zero
re-proving of Fourier machinery):
- `charFn_map_embMod_snd` — embedded charFn is ξ₂-free (mass off the axis is 0),
  so the 2-D inversion `N⁻² Σ_ξ` collapses to `N⁻¹ Σ_j`;
- `iidSum_nat_apply_toReal_le` — P(S_n = L) ≤ N⁻¹ Σ_j ‖φ(j)‖ⁿ;
- `charFn_embMod_decay_of_adjacent_atoms` — decay 1 − 16μ²(nd j/N)² from atom
  masses ≥ μ at ADJACENT a, a+1 (no triangle step; abstract r, so applies to
  tilted projected walks);
- `iidSum_nat_apply_le_center_of_decay` — the d=1 center bound 32c/√(1+n) at
  N = ⌊√n⌋+1 (mirror of the 2-D Gaussian summation, single factor).
All axiom-clean (checked via full-build warnings only; #print pending next lap
commit). Gotchas: field_simp overshoots `ring` (drop it / add norm_num);
`(embMod N L).2 = 0` needs explicit rfl after rw.

**NEXT — assemble the three d=1 local bounds** (LocalInstances.lean sorries):
per walk p ∈ {geomHalf (atoms 1,2; masses 1/2,1/4), geomQuarter (atoms 1,2;
1/4,3/16), pascal (atoms 2,3; 1/4,1/4)}:
1. Tilted atom-mass lower bounds (mirror tilt_hold_apply_ge, easier):
   tilt p (expW λ) at atom d: p_d·e^{λd}/Z ≥ p_d·e^{-3/200}/Z; Z ≤ quad(1/200)
   ≤ 1.03 ⇒ tilted mass ≥ (3/16)·0.985/1.03 ≥ 1/6 uniform ⇒ μ = 1/6,
   c = (16μ²)⁻¹ = 9/4... use c = 4 (≥ 1 and ≥ (16μ²)⁻¹). VALIDATE numerically.
   Transfer through map: PMF.apply_le_map_apply to (tilt p).map (embMod N).
2. Tilted center bound: iidSum_nat_apply_le_center_of_decay at the tilted walk
   (c uniform on box) ⇒ P_tilt(S̃_n = L) ≤ 128/√(1+n)-ish =: C₀/√(1+n).
3. d=1 Chernoff bridge (mirror holdSum_apply_le_chernoff, 1-D weights expW):
   P(S_n = L) ≤ C₀/√(1+n)·e^{n(mλ+1000λ²) − λL} via iidSum_apply_eq_tilt +
   quad bounds (already proved: tiltZ_{geomHalf,geomQuarter,pascal}_le_quad).
   Note tiltZ_expW_ne_zero gives hZ0; hZt from quad bound.
4. Assembly = hold_local_bound pattern verbatim with √(1+n) and 1-D clip
   (chernoff_clip_le SIGNED version is in HoldLocal — either import or the
   nonneg one + case split on sign of dev; dev = L − mn ∈ ℝ signed: need the
   SIGNED clip: move chernoff_clip_le from HoldLocal to LocalInstances, or
   restate; then Gweight matching via exp_neg_min_le_Gweight + |dev| symmetry:
   exponent bound uses min(dev²/4000n, |dev|/400) — matches Gweight(c·(L−mn))
   since Gweight is even in its argument (|·| and square) — CHECK: Gweight t x
   uses x² and |x| only ⇒ Gweight(c·dev) = Gweight(c·|dev|) ✓ need tiny lemma
   Gweight_abs or just work with x = c*(L−mn) directly, matching hold pattern
   where M was ‖dev‖ ≥ 0 — here pass |dev| and rewrite by evenness).
   Consider a GENERIC `iidSum_nat_local_of_quad_center` mirroring
   iidSum_nat_tail_of_quad to do all three at once (hypotheses: quad bound +
   tilted center bound). Then S3 FULLY GREEN.

## Lap 43 (2026-07-12, seventh box session): ALL THREE d=1 TAIL BOUNDS PROVED

**`geomHalf_tail_bound`, `geomQuarter_tail_bound`, `pascal_tail_bound` are
theorems** (axiom-clean), in NEW `Prob/LocalInstances.lean` (statements moved
from LocalBound.lean — proofs need the Mgf engine, which imports LocalBound;
NOTE at old site; shared `chernoff_clip_le_nonneg` + `exp_neg_min_le_Gweight`
moved here from HoldLocal, which now imports this module). Machinery:
- `tiltZ_expW_ne_zero` — Z ≠ 0 generic on PMF ℕ (weights positive, mass 1);
- 1-D quadratic MGF bounds, uniform K = 1000 (validated numerically):
  `tiltZ_geomHalf_le_quad` (K = 8 tight, envelope E = 1+λ+2λ² through
  frac_closed_le), `tiltZ_pascal_le_quad` (square of geomHalf),
  `tiltZ_geomQuarter_le_quad` (transfer of tiltZ_hold_fst_le via NEW
  `tiltZ_geomQuarter_eq` = hold_map_fst + tiltZ_map);
- `iidSum_nat_halfspace_le` — generic 1-D one-sided Markov under tilt;
- `iidSum_nat_tail_of_quad` — GENERIC d=1 Lemma 2.2(ii): any PMF ℕ with
  Z ≤ 1+mλ+1000λ² on |λ| ≤ 1/200 gets the tail bound (c = 1/400, C = 2);
  the three instances are 3-liners over it.
Gotcha: degree-4 envelope nlinarith needs box-product×λ² hints
(mul_nonneg (1/200±λ) (sq_nonneg λ)).

**S3 ledger now: only the three d=1 LOCAL bounds remain** (sorries in
LocalInstances.lean): geomHalf/geomQuarter/pascal_local_bound. They need the
d=1 center bound C/√(1+n): a single-ZMod circle-method analogue of
`iidSum_apply_le_center_of_decay` (CharFn.lean) — same proof shape, ONE charFn
decay factor, N = ⌊√n⌋+1 gives C·N⁻¹... wait C/N with N ~ √n ✓. Steps:
1. `iidSum_nat_apply_le_center_of_decay (p : PMF ℕ) (c) (hdec : ∀ N [NeZero N],
   4 ≤ N → ∀ ξ : ZMod N, ‖charFn (p.map (Nat.cast) : PMF (ZMod N)) ξ‖^2 ≤
   1 - ((nd ξ : ℝ)/N)^2/c) : ((iidSum p n) v).toReal ≤ (32·c... )/sqrt(1+n)` —
   mirror the 2-D proof in CharFn.lean (read `iidSum_apply_le_center_of_decay`
   first; the 1-D version drops one factor and the constant becomes 32c/√ not
   (32c)²/n).
2. charFn decay for the TILTED 1-D walks from atom masses: need two atoms at
   distance 1 (geomHalf: masses at 1,2 = 1/2,1/4; tilted ≥ ~1/5 on box;
   geomQuarter: atoms 1,2; pascal: atoms 2,3) — reuse `charFn_decay_of_atoms`?
   That one is 2-D (ZMod N × ZMod N); check if a 1-D atom-decay lemma exists in
   CharFn.lean or needs writing (mirror).
3. Tilted-walk assembly identical to hold_local_bound (1-D chernoff bridge +
   clip + Gweight; all shared pieces already factored).
Then S3 is fully GREEN. After that: operator red queue (2) X8/X10 statement
design Prop 7.8 Cases 2/3 (7.46)-(7.53); (3) X9 Lemma 7.9 skeleton; (4) X1;
(5) X5 bridge sorries; (6) C8.

## Lap 42 (2026-07-12, seventh box session): `hold_tail_bound` PROVED — S3 2-D SIDE COMPLETE

**Lemma 2.2(ii) for `Hold` is a theorem** (axiom-clean), same lap-41 engine, no
center bound needed. In `Sec7/HoldLocal.lean`:
- `chernoff_clip_le_nonneg` — sign-exposing clip variant (μ ≥ 0 when dev ≥ 0);
- `exp_neg_min_le_Gweight` — factored Gweight branch matching (n ≥ 1, x ≥ 0);
- `holdSum_halfspace_le` — one-sided Markov under the tilt: region mass ≤
  e^{n·quad(λ) − a} when the tilt weight ≥ e^a on the region (tiltZ_iidSum +
  tiltZ_hold_le_quad + termwise Markov);
- `hold_tail_bound` — c = 1/400, C = 4: sup-norm tail ⊆ 4 sign-pattern
  half-spaces (le_max_iff + le_abs), each with tilt ±μ in the matching
  coordinate; all four exponents collapse to 1000nμ² − μ·lam; ℝ↔ℝ≥0∞ via
  ENNReal.tsum_toReal_eq + apply_ite; n = 0 point mass separate.
Gotchas: `zero_le _` in term position fails in ℝ≥0∞ (use `bot_le`); `set`-atoms
must be re-folded (rw [hB]) after toReal_ofReal unfolds them; `(0:ℕ×ℤ).1` needs
`Prod.fst_zero` simp before norm-num on the norm.

**BOTH Lemma 2.2 instances for Hold done: `hold_local_bound` + `hold_tail_bound`.**

**NEXT — the six d=1 instances in Prob/LocalBound.lean** (geomHalf/geomQuarter/
pascal × local/tail; sorries at :153,:161,:169,:176,:185,:192), now mechanical
with the same pattern:
- tail bounds (easier, do first): 1-D `iidSum_halfspace_le` analogue of
  `holdSum_halfspace_le` generic in a PMF ℕ with a 1-D quad MGF bound; need 1-D
  quadratic bounds for geomHalf (mean 2), geomQuarter (mean 4), pascal (mean 4)
  from the closed forms `tiltZ_geomHalf`/`tiltZ_pascal` (already in Mgf.lean —
  check exact names/envelopes; validate constants numerically first).
- local bounds: need 1-D center bound C/√(1+n) — NOTE the d=1 statements have
  1/√(1+n) not 1/(1+n): the circle-method center bound
  `iidSum_apply_le_center_of_decay` is d=2-specific (product of two coords).
  Check what exists for d=1 (charFn decay in 1-D + N = ⌊√n⌋+1 gives C/√n) —
  likely a 1-D analogue of `iidSum_apply_le_center_of_decay` must be stated
  (same proof shape, single ZMod factor). Then the assembly is identical.
Then Lemma 7.6/7.7 (X6) consume hold_local/tail (`fpDist_location_bound`,
Unroll.lean:624 area) — and the X5 bridge sorries + Q_black_edge remain the
other red nodes (X8/X10, X9, X1, C8 per operator queue).

## Lap 41 (2026-07-12, seventh box session): (F5) DONE — `hold_local_bound` PROVED

**S3's Lemma 2.2(i) for `Hold` is a machine-checked theorem** (axiom-clean), in
`Sec7/HoldLocal.lean` (statement MOVED there from Unroll.lean — the proof consumes
`tiltHold_apply_le_center`, which imports Unroll; a NOTE at the old site points
across). Three pieces, exactly per the lap-40 plan:
- `holdSum_apply_le_chernoff` — the Chernoff bridge: tilting identity
  `iidSum_apply_eq_tilt` + `tiltHold_apply_le_center` + `tiltZ_hold_le_quad`
  + `1+u ≤ e^u`, all `toReal` bookkeeping (`ENNReal.toReal_mul` unconditional;
  weight-inverse via `ENNReal.ofReal_inv_of_pos` + `Real.exp_neg`).
- `chernoff_clip_le` — per-coordinate λ-clip: exponent ≤ −min(dev²/(4000n), |dev|/400)
  (central λ = dev/2000n exact; tail λ = ±1/200, n/40 ≤ |dev|/400).
- `hold_local_bound` — c = 1/400, C = C₀ = 6553600000000; n = 0 point-mass case
  separate; sup-norm max coordinate dominates (other coord's exponent ≤ 0);
  Gaussian branch (M/400)²/(1+n) ≤ M²/4000n, exp branch exact.
Gotcha: `div_le_div_iff` is now `div_le_div_iff₀` (corpus had it).

**NEXT — `hold_tail_bound` (2.2(ii), now the sorry in HoldLocal.lean)**: direct
Chernoff tail, same ingredients, NO center bound: for the half-space
{λ ≤ ‖dev‖∞}, split by which coordinate/sign achieves the sup (4 half-lines ×
2 coords); for a fixed sign pattern use the 1-D Markov/Chernoff:
Σ_{tail} P ≤ Z(λ)ⁿ e^{-λ·(threshold)} with the SAME clip choice at dev = ±lam
(deviation threshold), summing the tilted PMF's tail mass ≤ 1. Concretely:
tail mass ≤ Σ over 4 sign-patterns of e^{n·quad(λ) − λ·(mean shift ± lam)} with
λ clipped as in chernoff_clip_le at dev = lam ⇒ each term ≤ e^{−min(lam²/4000n,
lam/400)} ⇒ ≤ 4·Gweight branch; C = 4 (plus n = 0 edge). Statement's tsum-if:
bound the indicator sum by tilted change-of-measure per point (pointwise
`iidSum_apply_eq_tilt` + e^{-λ·v} ≤ e^{-λ·threshold} on the half-space, tilted
masses sum ≤ 1 via `PMF.tsum_coe`). Then the 6 d=1 LocalBound instances
(mechanical now — same pattern, 1-D closed forms already proved).

## Lap 40 (2026-07-12, sixth box session): (G2c) 2-D MGF BOUND PROVED — (G2) COMPLETE

`Prob/Mgf.lean`: `ennreal_le_of_sq_le_sq` (x² ≤ y² → x ≤ y, via ENNReal.mul_lt_mul
contrapositive) and **`tiltZ_hold_le_quad`** — on |λᵢ| ≤ 1/200:
`Z(λ₁,λ₂) ≤ ofReal(1 + 4λ₁ + 16λ₂ + 1000(λ₁²+λ₂²))`. K = 1000 validated
numerically (K ≤ 700 fails; the CS-doubled cross term 256λ₁λ₂ vs 128λ₁λ₂ costs
−128λ₁λ₂, absorbed). AXIOM-CLEAN. The full Lemma-2.2 Chernoff MGF estimate with
exact mean (4,16) is machine-checked.

**(F5) next — final assembly of `hold_local_bound`** (in Sec7/HoldLocal.lean):
1. Bridge lemma: for λ in the 1/200-box, v = (j,l), n:
   ((iidSum hold n) v).toReal ≤ (C₀/(1+n))·(1+4λ₁+16λ₂+1000|λ|²)ⁿ·e^{-λ·v}
   from iidSum_apply_eq_tilt (needs expW2 v ≠ 0,∞ ✓ ofReal exp) +
   tiltHold_apply_le_center (box 1/200 ⊂ 1/50 ✓) + tiltZ_hold_le_quad; toReal of
   the product; (1+u)ⁿ ≤ e^{nu} for the Z-power (u ≥ -1: Real.add_one_le_exp +
   pow mono) ⇒ exponent n(4λ₁+16λ₂+1000|λ|²) - λ·v = -λ·dev + 1000n|λ|²,
   dev = (j-4n, l-16n).
2. λ-choice per coordinate: λᵢ = clip(devᵢ/(2000n), 1/200). Exponent
   = Σᵢ (1000nλᵢ² - λᵢdevᵢ); per coord: if |devᵢ| ≤ 10n: = -devᵢ²/(4000n);
   else: = -(1/200)|devᵢ| + 1000n/40000 ≤ -(1/200)|devᵢ| + |devᵢ|/40·... check:
   1000n(1/200)² = n/40 ≤ |devᵢ|/400 (n ≤ |devᵢ|/10) ⇒ exponent ≤ -|devᵢ|(1/200 -
   1/400) = -|devᵢ|/400.
3. Gweight matching (sup norm ‖dev‖∞ = max): total exponent ≤ per-max-coord
   bound; case split on which regime the MAX coordinate is in:
   - max coord central (≤ 10n): P ≤ C₀/(1+n)·e^{-‖dev‖²/(4000n)}·e^{+slack from
     other coord ≤ 0} (other coord exponent ≤ 0 by choice at optimum... careful:
     with per-coordinate independent optimization each term is ≤ 0, so total
     ≤ max-coord term) ⇒ Gaussian branch: need -‖dev‖²/(4000n) ≤ -(c‖dev‖)²/(1+n):
     c = 1/100 say with 1+n ≥ n... (c²/(1+n) ≤ 1/(4000n) ⇔ c² ≤ (1+n)/(4000n):
     c = 1/64 ok since (1+n)/4000n ≥ 1/4000).
   - max coord tail: e^{-‖dev‖∞/400} ⇒ exp branch with c = 1/400.
   Gweight t x = exp(-x²/t) + exp(-|x|) ≥ each branch. Statement c existential:
   pick c = 1/400 uniform: Gaussian branch exp(-dev²/(4000n)) ≤ exp(-(dev/400)²/(1+n))?
   (1/4000n ≥ 1/160000(1+n) ⇔ 160000(1+n) ≥ 4000n ✓). n = 0 edge: dev = v-0 …
   check n=0 separately (iidSum 0 = pure 0; mass at v≠0 is 0, at 0: dev=(0,0),
   Gweight ≥ 1 ⇒ need C ≥ 1 ✓).
   ℤ-coordinate signs: l - 16n ∈ ℤ, first coord j - 4n could be negative in ℝ ✓
   all real arithmetic.

## Lap 39 (2026-07-12, sixth box session): (G2b-2) SECOND-COORD MGF BOUND PROVED

`Prob/Mgf.lean`: **`tiltZ_hold_snd`** (closed form Z(0,μ) = (e^{3μ}/4)·
(1-(3/4)Z_ne3(μ))⁻¹ on the 1/50 strip), **`tiltZ_pascalNe3_le_poly`**
(Z_ne3 ≤ 1+(13/3)μ+30μ² — atom-cancel pattern symbolic in μ; the cleared
inequality is TIGHT at μ=0, diff = μ²(26/3 - 76μ - …); nlinarith needs box-product
hints mul_nonneg (h1·h2)·μ² etc.), **`tiltZ_hold_snd_le`** (Z(0,μ) ≤ 1+16μ+400μ²
on |μ| ≤ 1/100 — mean 16 first order exact). AXIOM-CLEAN. Gotchas:
`pow_le_pow_left` is now `pow_le_pow_left₀`; positivity can't see through
`set E := …` atoms (use nlinarith [sq_nonneg μ] with the box); exp(3μ) = (exp μ)³
via `← Real.exp_nat_mul; norm_num`.

**BOTH 1-D LEGS DONE. (G2c) next — combine into the 2-D bound**:
`tiltZ_hold_le_quad {l1 l2} (box |λᵢ| ≤ 1/200)`:
Z(λ₁,λ₂) ≤ ofReal(√((1+8λ₁+128λ₁²)(1+32λ₂+1600λ₂²)))… avoid the square root:
statement Z² ≤ ofReal((1+4·(2λ₁)+32(2λ₁)²)·(1+16(2λ₂)+400(2λ₂)²)) directly from
tiltZ_expW2_sq_le + fst_le/snd_le (ofReal_mul merges) — then keep the SQUARED form
through the Chernoff assembly: P(S=v) ≤ P_tilt·Zⁿ·w(v)⁻¹ gives P² ≤ P_tilt²·Z^{2n}
·w(v)⁻² — no: better square-root helper after all: `le_ofReal_of_sq_le`:
x² ≤ ofReal(a·b) (a,b ≥ 0) → x ≤ ofReal(√a·√b)?? Cleanest: x ≤ ofReal r where
r² ≥ ab: choose r = 1+4λ₁+16λ₂+K|λ|² and prove RATIONAL inequality
(1+8λ₁+128λ₁²)(1+32λ₂+1600λ₂²) ≤ (1+4λ₁+16λ₂+K(λ₁²+λ₂²))² by nlinarith (first
order: 8λ₁+32λ₂ = 2(4λ₁+16λ₂) ✓ matches); K to be found numerically (cross term
8·32λ₁λ₂ vs 2·4·16λ₁λ₂ = 128λ₁λ₂ SAME ✓; so K ≈ 128+16²/…: validate numerically,
K ~ 700?). Helper x ≤ y from x² ≤ y², y = ofReal ≠ 0,∞: contrapositive +
ENNReal.pow_lt_pow_left (see lap 37 entry).
Then (F5) assembly per lap 36 entry.

## Lap 38 (2026-07-12, sixth box session): (G2b-1) FIRST-COORD MGF BOUND PROVED

`Prob/Mgf.lean`: `exp_le_one_add_add_two_sq` (e^u ≤ 1+u+2u², u ≤ 1/2, via
(1-u)⁻¹), `frac_closed_le` (monotone evaluation of a(1-r)⁻¹, free numerator),
**`tiltZ_hold_fst`** (EXACT closed form Z(μ,0) = (e^μ/4)(1-(3/4)e^μ)⁻¹, every μ),
**`tiltZ_hold_fst_le`** (Z(μ,0) ≤ ofReal(1+4μ+32μ²) on |μ| ≤ 1/100 — mean 4 first
order exact). AXIOM-CLEAN. Numerics validated pre-formalization: env1 margin
comfortable, K₁ = 32 (even 16 works); box 1/100 (box 1/25 FAILS for the second
coordinate — K₂ would blow past 600).

**(G2b-2) next — second-coordinate closed form + bound** (numerics already
validated: K₂ = 400 works at box 1/100 with E = 1+u+2u² envelope; (3/4)S < 1 holds):
1. `tiltZ_hold_snd` closed form: Z(0,μ) = ofReal(e^{3μ}/4)·(1-(3/4)·Z_ne3(μ))⁻¹ —
   wait, Z_ne3 is ℝ≥0∞-valued; state as = ofReal(e^{3μ}/4) * (1 - (3·4⁻¹)*tiltZ
   pascalNe3 (expW μ))⁻¹ (ENNReal form, from tiltZ_hold_factor at l1 = 0 + geometric
   sum — needs ENNReal.tsum_geometric on ratio (3/4)Z_ne3 which needs no side
   condition, both sides ∞ together).
2. `tiltZ_pascalNe3_le_poly`: Z_ne3(μ) ≤ ofReal((4/3)(X/(1-X))² - (1/3)(1+3μ)),
   X = E/2 — from tiltZ_pascalNe3_add: cancel the atom term via
   ENNReal.add_le_add_iff_right (pattern of tiltZ_pascalNe3_le, now symbolic);
   uses e^{3μ} ≥ 1+3μ (add_one_le_exp) on the subtracted side and
   Z_pascal = Z_gh² ≤ ofReal((X'/(1-X'))²) (tiltZ_pascal + geom_closed_le square).
3. `tiltZ_hold_snd_le`: ≤ ofReal(1+16μ+400μ²) on |μ| ≤ 1/100: frac_closed_le with
   numerator e^{3μ} ≤ E³ (pow of envelope) wait e^{3μ} = (e^μ)³ ≤ E³ ✓, ratio
   (3/4)S; the final real inequality E³/4 ≤ (1+16μ+400μ²)(1-(3/4)S(μ)) after
   clearing (1-X)² — nlinarith, may need staged haves (degree 8; if nlinarith
   stalls: intermediate bound S ≤ rational quadratic first, numerically:
   S(u) ≈ 1+(13/3)·3u?? no: S'(0) = 13/3·... just S ≤ 1 + 13u + 60u² check
   numerically then chain).
4. Combine via tiltZ_expW2_sq_le + sqrt-free helper (x² ≤ ofReal(a)·ofReal(b) →
   x ≤ ofReal(√(ab)) avoided: state target Z ≤ ofReal(exp(4λ₁+16λ₂+K̄|λ|²)) and
   verify square: need x ≤ y from x² ≤ y²: ENNReal.pow_le_pow_iff_left or
   contrapositive with pow_lt_pow_left, y = ofReal exp ≠ 0).
Then (F5) final assembly (see lap 36 entry).

## Lap 37 (2026-07-12, sixth box session): (G2a) CAUCHY–SCHWARZ MGF SPLIT PROVED

`Prob/Tilt.lean`: **`tsum_mul_mul_sq_le`** — weighted Cauchy–Schwarz
`(Σ p·u·v)² ≤ (Σ p·u²)(Σ p·v²)` entirely in ℝ≥0∞ (double-sum expansion + pointwise
AM–GM `ennreal_mul_le_sq_add_sq_div_two`; no summability side conditions —
mathlib's Hölder is ℝ≥0-only with summability hypotheses).
`Prob/Mgf.lean`: `expW2_eq_mul`, `expW2_sq`, **`tiltZ_expW2_sq_le`** —
`Z(λ₁,λ₂)² ≤ Z(2λ₁,0)·Z(0,2λ₂)`. KEY DESIGN WIN: CS preserves the first-order
(mean) term exactly (AM–GM would not), so the 2-D second-order bound (G2) reduces
to two 1-D closed-form bounds and the hold mean identities (G1) are NOT needed as
separate tsum computations. AXIOM-CLEAN. Gotchas: `ℝ≥0` notation needs
`open scoped NNReal` (use `NNReal` verbatim otherwise); `zero_le _` fails in
ENNReal term mode — use `bot_le`; `ENNReal.div_eq_top` disjuncts are
(num ≠ 0 ∧ den = 0) | (num = ∞ ∧ den ≠ ∞).

**(G2b) next — the two 1-D second-order bounds** (in Mgf.lean), target box
|μ| ≤ 1/25 (doubled tilt):
1. Closed form `tiltZ hold (expW2 μ 0) = (1/4)e^μ(1-(3/4)e^μ)⁻¹` — from
   tiltZ_hold_factor at l2 = 0 (tiltZ pascalNe3 (expW 0) = 1 by PMF mass; need
   tiltZ_one lemma) + geometric series; mean 4 built in.
2. Closed form `tiltZ hold (expW2 0 μ) = (1/4)e^{3μ}(1-(3/4)Z_ne3(μ))⁻¹` with
   Z_ne3(μ) = (4/3)(x/(1-x))² - (1/3)e^{3μ}, x = e^μ/2 (tiltZ_pascalNe3_add,
   ENNReal sub OK since finite); mean 16 built in.
3. Numeric second-order bounds via envelope 1+u ≤ e^u ≤ 1+u+u² (|u| ≤ 1/8 say;
   3μ ∈ [-3/25, 3/25] ok): `Z(μ,0) ≤ ofReal(exp(4μ + K₁μ²))` and
   `Z(0,μ) ≤ ofReal(exp(16μ + K₂μ²))` — prove first `≤ ofReal(1 + 4μ + K₁μ²)` by
   cross-multiplied nlinarith (denominators positive on box), then 1+x ≤ eˣ.
   Numeric check (do BEFORE formalizing, corpus rule): K₁ ≥ ~32, K₂ ≥ ~600?
   compute margins numerically first.
4. Combine: Z(λ)² ≤ e^{8λ₁+4K₁λ₁²}·e^{32λ₂+4K₂λ₂²} ⇒ Z ≤ e^{4λ₁+16λ₂+2K̄|λ|²}
   via ENNReal sqrt-free helper `x² ≤ ofReal(a²) → x ≤ ofReal(a)` (contrapositive
   + ENNReal.pow_lt_pow_left).
Then (F5): assembly with iidSum_apply_eq_tilt + tiltHold_apply_le_center +
per-coordinate λ-clip ⇒ hold_local_bound.

## Lap 36 (2026-07-12, sixth box session): (F4b) TILTED CENTER BOUND PROVED

`Sec7/HoldLocal.lean` NEW (imports Unroll + Mgf; the S3 assembly module):
**`tilt_hold_map_mass`** (four atoms ≥ 1/400 after tilt + mod-N projection) and
**`tiltHold_apply_le_center`** — `P_λ(S̃_n = v) ≤ (32·80000)²/(1+n)` uniformly on
the tilt box |λᵢ| ≤ 1/50 (charFn_decay_of_atoms at μ = 1/400 ⇒ c = 80000 ⇒
iidSum_apply_le_center_of_decay). AXIOM-CLEAN, compiled first try — the parametric
chain (F3a)+(F3b)+(F4a) composed with zero friction.

**(F5) next — the Chernoff assembly for `hold_local_bound`** (in HoldLocal.lean):
1. (G1) hold mean identities: `∑' d, hold d * d.1 = 4`, `∑' d, hold d * d.2.toNat
   = 16` (second coord ≥ 3 on support so ℕ-valued; both as ENNReal tsums; via
   hold's bind/map structure + geometric means: E gQ = 4, E pascalNe3 = 13/3,
   E[3 + (k-1)-fold] = 3 + 3·(13/3) = 16).
2. (G2) second-order MGF bound: `tiltZ hold (expW2 λ) ≤ ofReal (1 + 4λ₁ + 16λ₂
   + K(λ₁²+λ₂²))` on a shrunk box |λᵢ| ≤ δ (δ = 1/100, K explicit): pointwise
   `e^u ≤ 1 + u + u²e^{|u|}/2` (u = λ·d), then Σ hold(d)·u² e^{|u|} ≤
   |λ|²·Σ hold(d)(d₁+|d₂|)² e^{δ(d₁+|d₂|)} ≤ |λ|²·(2/δ²)·Σ hold(d) e^{2δ(d₁+d₂)}
   (x² ≤ (2/δ²)e^{δx}; d₂ ≥ 3 ≥ 0 on support so |d₂| = d₂) = |λ|²·(2/δ²)·
   tiltZ hold (expW2 2δ 2δ) ≤ |λ|²·(2/δ²)·(221/25) with 2δ = 1/50. Mean term from
   (G1). All in ENNReal/ofReal carefully, or via toReal with finiteness.
3. (F5) assembly: `iidSum_apply_eq_tilt` (consumption form) + `tiltHold_apply_le_center`
   ⇒ P(S_n = (j,l)) ≤ C₀/(1+n) · (Z e^{-λ·(4,16)})ⁿ · e^{-λ·dev}, dev = (j-4n, l-16n);
   (G2) ⇒ (Ze^{-λ·mean})ⁿ ≤ exp(nK|λ|²) [need e^{-λ·(4,16)}-multiplied form: restate
   (G2) as Z ≤ ofReal(exp(4λ₁+16λ₂+K|λ|²)) via 1+x ≤ eˣ]. Choose λ = clip:
   center |devᵢ| ≤ 4Kδn: λᵢ = devᵢ/(4Kn) ⇒ exponent ≤ -|dev|²/(8Kn) ⇒ Gaussian
   branch of Gweight (constant c ≤ 1/√(8K·2) etc); else λᵢ = ±δ·sign(devᵢ) ⇒
   ≤ exp(-δ‖dev‖₁/2)-ish ⇒ exp branch. Case split per coordinate — 2-D clip is
   componentwise, exponent separates: nK(λ₁²+λ₂²) - λ₁dev₁ - λ₂dev₂ optimizes
   per-coordinate independently. Gweight consumes sup-norm ‖dev‖_∞; exponent
   bound gives per-coord products ⇒ take the max coord for the bound.

## Lap 35 (2026-07-12, sixth box session): (F4a) PARAMETRIC CENTER BOUND PROVED

`Sec7/Unroll.lean`: **`iidSum_apply_le_center_of_decay`** — the (E) Gaussian
summation generalized over the decay constant: any `p : PMF (ℕ × ℤ)` with
`‖charFn (p.map (modPair N)) ξ‖² ≤ 1 - (nd-sum)/c` uniformly in `N ≥ 4` has
`P(S_n = v) ≤ (32c)²/(1+n)` (a = n/(4cN²) ∈ [1/(8c), 1], sum ≤ 4/a ≤ 32c).
`holdSum_apply_le_center` is now the c = 768 instance ((32·768)² = 603979776,
unchanged). AXIOM-CLEAN.

**(F4b/F5) next — assemble hold_local_bound**:
1. (F4b) tilted center bound: apply `iidSum_apply_le_center_of_decay` to
   `tilt hold (expW2 l1 l2)` with c = 80000 (decay from `charFn_decay_of_atoms` at
   μ = 1/400 via `tilt_hold_apply_ge` transferred through modPair by
   `PMF.apply_le_map_apply`; 2μ² = 1/80000). Yields P_tilt(S̃_n = v) ≤ C₀/(1+n),
   C₀ = (32·80000)² = 2560000² = 6.5536e12.
2. (F5) tilting identity consumption: `iidSum_apply_eq_tilt` at p = hold, w = expW2:
   P(S_n = v) = P_λ(S̃_n = v)·Zⁿ·(w v)⁻¹, so
   (iidSum hold n v).toReal ≤ (C₀/(1+n))·(Z.toReal)ⁿ·e^{-λ·v}. Need in toReal:
   toReal of product (all finite), (expW2 l1 l2 v)⁻¹.toReal = e^{-(l1 v1 + l2 v2)}.
3. λ-optimization → Lemma 2.2(i) Gweight form: need log Z(λ) ≤ λ·(4,16) + K|λ|²
   on the box. Mean: E hold = (4, 16)? verify from paper p.42 (mean of Geom(4) is 4;
   E[second coord] = 3 + E[Σ_{i<k-1} pascalNe3] = 3 + 3·(16/3 - 1)? — compute; the
   claimed Gweight center is (n·4, n·16)). This needs the MGF second-order bound —
   candidate route: Z(λ)·e^{-λ·mean} ≤ exp(K|λ|²) via explicit rational arithmetic
   on the factor formula (hard); OR restate hold_local_bound with the Gweight
   centered at the true mean and ANY exponential decay rate c (statement already
   has ∃ c C — check LocalBound.lean statement shape first!).

## Lap 34 (2026-07-12, sixth box session): (F3b) TILTED ATOM MASSES PROVED

`Prob/Mgf.lean`: **`tiltZ_hold_le`** (Z_hold ≤ 221/25 on the box |λᵢ| ≤ 1/50 —
the ne_top domination series evaluated: 1 + (1 - 171/196)⁻¹; `tiltZ_hold_ne_top`
now a one-line corollary) and **`tilt_hold_apply_ge`** — tilted hold atoms keep
mass ≥ 1/400 in the window y₁ ≤ 2, 0 ≤ y₂ ≤ 8 (weight ≥ e^{-1/5} ≥ 4/5,
(1/32)(4/5)(25/221) = 5/1768 > 1/400). AXIOM-CLEAN. Gotcha: `inv_le_inv_of_le`
is gone — the antitone inverse lemma is `inv_anti₀ (hb : 0 < b) (hba : b ≤ a)`.

**(F4) next — tilted center bound**: `tiltHold l1 l2 := tilt hold (expW2 l1 l2) …`
(abbreviation to tame the proof-term arguments). Transfer the four atoms through
modPair (`PMF.apply_le_map_apply` + `tilt_hold_apply_ge` at (1,3),(2,5),(2,7),(2,8),
hold masses from hold_apply_* ≥ 1/32 in toReal) ⇒ `charFn_decay_of_atoms` at
μ = 1/400 ⇒ decay constant 2·(1/400)⁻²… = 1/80000. Then replay `holdSum_apply_le_center`
with 768 → 80000·(3/8)-ish: generalize the (E) Gaussian-summation proof over the
decay constant `c` (a = n/(4c·N²), threshold a ≥ 1/(8c), sum ≤ (4/a)² ⇒
C(c) = (32c)²) — refactor `holdSum_apply_le_center` into
`iidSum_apply_le_center_of_decay (r : PMF (ℕ × ℤ))` taking the parametric decay
as hypothesis. Then (F5) λ-optimization via the tilting identity
`iidSum_apply_eq_tilt`: P(S_n = v) = P_tilt(S_n = v)·Zⁿ·e^{-λ·v} ≤
(C/(1+n))·exp(n·log Z - λ·v); need log Z ≤ λ·mean + K|λ|² (mean (4,16)) or crude
sign-choice at |λ| = 1/50 for the Gweight branch ⇒ `hold_local_bound`.

## Lap 33 (2026-07-12, sixth box session): (F3a) PARAMETRIC CHARACTER DECAY

`Sec7/Unroll.lean`: **`charFn_decay_of_atoms`** — charFn_hold_decay abstracted over
an atom-mass lower bound `μ ≥ 0` at the four projected points (1,3),(2,5),(2,7),(2,8)
mod N: `‖charFn r ξ‖² ≤ 1 - 2μ²·((nd ξ₁/N)² + (nd ξ₂/N)²)`, any PMF r, N ≥ 4.
`charFn_hold_decay` re-derived as the μ = 1/32 instance (2·(1/32)² = 1/512 ≥ 1/768).
AXIOM-CLEAN. Gotcha: the old proof's final `nlinarith` blows the heartbeat budget
once μ is symbolic — pre-multiply the triangle bounds by μ² via
`mul_le_mul_of_nonneg_left … (sq_nonneg μ)` and finish with plain `linarith`.

**(F3b) next — tilted atom masses**: need `tiltZ_hold_le` (numeric UPPER bound on
the partition function on the box |λᵢ| ≤ 1/50, same geometric-sum route as
tiltZ_hold_ne_top: e^{λ₁+3λ₂}·Σ_k ratio^{k-1} with ratio ≤ 171/196 ⇒ Z ≤
(50/47)-ish·(1-171/196)⁻¹ explicit rational) and per-atom lower bounds
`(tilt hold (expW2 λ)) y ≥ hold(y)·e^{-|λ|·‖y‖₁}/Z ≥ μ₀` at the four points
(worst atom (2,8): (1/32)·e^{-10/50}/C). Then (F4) tilted center bound = (E) verbatim
+ charFn_decay_of_atoms at μ₀; (F5) λ-optimization (needs hold mean (4,16) or the
crude boundary-sign route) ⇒ `hold_local_bound`.

## Lap 32 (2026-07-12, sixth box session): (F2b) HOLD MGF FINITENESS PROVED

`Prob/Mgf.lean` (now imports Sec7/Holding): `exp_le_inv_one_sub` (e^x ≤ (1-x)⁻¹ on
[0,1)), `geom_closed_le` (monotone rational evaluation of r(1-r)⁻¹),
`tiltZ_geomHalf_le` (≤ 25/24 for λ ≤ 1/50), `pascalNe3_apply_two` (= 3⁻¹),
`tiltZ_pascalNe3_ne_zero`, **`tiltZ_pascalNe3_le`** (≤ 57/50 on |λ| ≤ 1/50 — the
b=3 atom removal is what pulls it below 4/3; cancel the atom via
ENNReal.add_le_add_iff_right, margin 625/432 ≤ 218/150), `expW2` 2-D weight (+
zero/add), **`tiltZ_hold_factor`** (conditional factorization: Σ_k gQ(k)·e^{λ₁k+3λ₂}
·Z_ne3^{k-1}, via tsum_bind_mul/tsum_map_mul + tiltZ_iidSum), `tiltZ_hold_ne_zero`,
**`tiltZ_hold_ne_top`** on the box |λᵢ| ≤ 1/50 (geometric domination, ratio
(3/4)(50/49)(57/50) = 171/196 < 1). ALL AXIOM-CLEAN. Paper (7.30) engine done.
Gotchas: `rw [ENNReal.ofReal_mul]` grabs the wrong (LHS) occurrence — rewrite
numeral⁻¹ → ofReal form FIRST then merge with ← ofReal_mul; `.not_le` field gone
(use `not_le.mpr`); gcongr side goals: pre-`have` the ofReal_le_ofReal facts and
let gcongr close by assumption; `unfold hold` where `rw [hold]` fails.

**(F3) next — tilted charFn decay**: refactor `charFn_hold_decay` into a parametric
version `charFn_decay_of_atoms (r : PMF (ZMod N × ZMod N)) (μ : ℝ) (hμ : 0 < μ)`
taking `μ ≤ min` of the four transferred atom masses at (1,3),(2,5),(2,7),(2,8) and
concluding `‖charFn r ξ‖² ≤ 1 - c·μ²·(nd² sum)` (the current proof's pair_transfer
step already isolates the masses — replace the four numerals by μ, constant becomes
explicit in μ). Then tilted hold atoms: (tilt hold w).apply at atom y =
hold(y)·w(y)/Z ≥ atom·e^{-|λ|·|y|}/Z with Z ≤ [bound from factor formula ≤ …] — need
a numeric UPPER bound on tiltZ hold on the box (same geometric sum: ≤ e^{3λ₂}·
Σ ≤ (50/47)·(1+(1-171/196)⁻¹)-ish — or simpler: atoms of tilt ≥ (1/4)·(min-e-power)
/Z with Z ≤ ofReal(C) — derive `tiltZ_hold_le` alongside). Then (F4) center bound
for the tilted walk (reuse (E) Gaussian summation verbatim — it consumed only the
decay + PMF-ness), (F5) λ-optimization: Z(λ)ⁿe^{-λ·v} ≤ Gaussian/exp factor via
log Z ≤ λ·(4,16) + K|λ|² on the box (needs E hold = (4,16) — mean computation) OR
the cruder route: pick λ = ±(1/50) signs to dominate direction, giving the exp(-c|·|)
Gweight branch only near the boundary. Design decision next lap.

## Lap 31 (2026-07-12, sixth box session): (F2a) d=1 MGFs PROVED — Prob/Mgf.lean NEW

`Prob/Tilt.lean` additions: **`tiltZ_map`** (partition functions push forward),
**`tiltZ_iidSum`** (`Z_{S_n} = Zⁿ`, one-line from the tilting identity + PMF mass 1).
`Prob/Mgf.lean` NEW: `expW λ a = ofReal e^{λa}` (+ zero/add), **`tiltZ_geomHalf`**
(exact geometric MGF `r(1-r)⁻¹`, `r = e^λ/2`, unconditional in ℝ≥0∞) + ne_zero/ne_top
(strip `e^λ < 2`), **`tiltZ_pascal`** (= square, via `pascal = iidSum geomHalf 2`),
`pascalNe3_eq_ite`, `pascal_apply_three` (= 4⁻¹), **`tiltZ_pascalNe3_add`** (atom
split: `Z_{pascalNe3} + 3⁻¹e^{3λ} = (4/3)Z_{pascal}`, no ℝ≥0∞ subtraction).
ALL AXIOM-CLEAN. Gotcha: `ENNReal.tsum_eq_add_tsum_ite` bakes in
`Classical.propDecidable`; match hand-written ites via `convert … using 3; funext;
split_ifs <;> rfl`.

**(F2b) next — hold MGF finiteness on the box |λ| ≤ 1/50**:
1. Numeric strip bound: `tiltZ pascalNe3 (expW λ) ≤ ofReal(4/3·((x/(1-x))² - x³/4·…))`
   — concretely from the split identity: Z_ne3 = (4/3)Z_pascal - 3⁻¹e^{3λ} (ENNReal
   sub OK since finite); for |λ| ≤ 1/50: x = e^λ/2 ∈ [49/100, 25/49],
   Z_gh = x/(1-x) ≤ 25/24, Z_pascal ≤ (25/24)², e^{3λ} ≥ (49/50)³ ⇒
   Z_ne3 ≤ (4/3)(25/24)² - 3⁻¹(49/50)³ < 1.135 (target: (3/4)e^{λ₁}Z_ne3 < 1 ⇒
   OK with e^{λ₁} ≤ 50/49: (3/4)(50/49)(1.135) ≈ 0.8686 < 1 ✓).
2. 2-D weight `expW2 (λ₁ λ₂) (d : ℕ × ℤ)` (needs ℤ version of expW for coord 2).
3. Factor `tiltZ hold` through hold's bind/map structure (hold_apply_pin route or
   direct tsum_prod' + tsum_bind_mul/tsum_map_mul): inner sum over increments =
   e^{3λ₂}·Z_ne3(λ₂)^{k-1} (tiltZ_iidSum on ℕ then push through the (3+Σ) map — mind
   the ℕ→ℤ cast: use tiltZ_map with the cast hom), outer = Σ_k gQ(k)e^{λ₁k}(…)^{k-1}
   geometric with ratio (3/4)e^{λ₁}Z_ne3 < 1 ⇒ tiltZ hold ≠ ∞ on the box.
Then (F3) tilted charFn decay (parametrize charFn_hold_decay by atom-mass lower
bounds), (F4) tilted center bound, (F5) λ-optimization ⇒ hold_local_bound.

## Lap 30 (2026-07-12, sixth box session): (F1) TILTING ENGINE PROVED — Prob/Tilt.lean NEW

Generic exponential tilting, entirely in ℝ≥0∞ (no convergence side conditions beyond
0 < Z < ∞): `tiltZ p w = Σ_d p d · w d` (partition function / MGF at the tilt),
`tilt p w` (the tilted PMF, direct subtype construction + ENNReal.mul_inv_cancel),
**`iidSum_tilt_apply`** (product-form tilting identity
`P_λ(S̃_n = v)·Zⁿ = P(S_n = v)·w v`, induction via iidSum_succ; weights recombine on
the diagonal v = a+e by w-multiplicativity), **`iidSum_apply_eq_tilt`**
(consumption form `P(S_n = v) = P_λ(S̃_n = v)·Zⁿ·(w v)⁻¹`). AXIOM-CLEAN.
Gotcha: hand-written `if v = a + e` needs `classical` (PMF.map_apply's ite is
classical); pushing constants into tsums is `← ENNReal.tsum_mul_left/right`.

**(F2) next — instantiate at hold**: w λ d := ENNReal.ofReal (exp (λ₁·d₁ + λ₂·d₂)).
Multiplicativity: ofReal_mul + exp_add. Need `tiltZ hold (w λ) < ∞` for λ in a box:
hold = geomQuarter ⊗ (3 + pascalNe3-sum) — second coordinate ≤ 3·(first coordinate
sum structure)? NO: second coord is 3+Σ of pascalNe3 which has geometric tail 3/4;
first coord geometric 1/4. MGF finite for λ₂ < log(4/3)/const, λ₁ < log 4 - λ₂-slack.
Concretely: tiltZ = Σ_k geomQuarter k · e^{λ₁k} · Π-structure — use hold's bind/map
form (Holding.lean) to factor the MGF as product of geometric MGFs (each a geometric
series). Then (F3): tilted atom masses ≥ half untilted for small λ-box ⇒
charFn decay for tilted hold (refactor charFn_hold_decay to take atom-mass lower
bounds as hypotheses, constant parametric); (F4): center bound for tilted walk;
(F5): optimize λ = clip((v - n·mean)/(Kn)) ⇒ Gweight factor ⇒ hold_local_bound.

## Lap 29 (2026-07-12, sixth box session): (E) GAUSSIAN SUMMATION PROVED — holdSum_apply_le_center

`Prob/CharFn.lean`: **`pow_le_exp_of_sq_le_one_sub`** (x² ≤ 1-D ⇒ xⁿ ≤ exp(-nD/4),
n ≥ 2; floor-of-n/2 absorbed into the 4), `sum_exp_neg_mul_le` (finite geometric
≤ (1-e^{-a})⁻¹ via geom_sum_eq + sign-flip), `sum_zmod_eq_sum_range` (val reindex,
sum_nbij'), **`sum_exp_neg_nd_sq_le`** (1-D Gaussian sum over ZMod N ≤ 2(1-e^{-a})⁻¹:
nd² ≥ nd, exp(-a·min) ≤ sum of the two val-halves, second half reflected by
sum_range_reflect), `one_sub_exp_neg_inv_le` ((1-e^{-a})⁻¹ ≤ 2/a on (0,1]).
`Sec7/Unroll.lean`: **`holdSum_apply_le_center`** — P(holdSum n = v) ≤ 603979776/(1+n)
for ALL n, v. At N = ⌊√n⌋+1 (N² ∈ [n+1, 2n], N ≥ 4 for n ≥ 9; n ≤ 8 by trivial mass
bound), a = n/(3072N²) ∈ [1/6144, 1]; per-frequency ‖φ‖ⁿ ≤ exp(-a·nd₁²)·exp(-a·nd₂²),
2-D sum factorizes into (1-D sum)² ≤ 24576², N⁻² ≤ (1+n)⁻¹. ALL AXIOM-CLEAN.
This is the center-regime core of Lemma 2.2(i) for Hold (node S3).

**(F) exponential tilting (next)**: off-center regime of `hold_local_bound`.
Plan (HANDOFF-2026-07-10-e item 2): tilted PMF hold_λ ∝ e^{λ·d} hold(d) for λ in a
fixed small box (needs MGF finiteness on a strip — the Lemma 7.6 engine, (7.30);
hold second-coordinate tail is pascalNe3/geometric so the MGF is finite for
λ₂ < log(4/3)-ish); identity P(S_n = v) = M(λ)ⁿ e^{-λ·v} P_λ(S̃_n = v); apply the
center bound to the tilted walk (its four atom masses are continuous in λ — a fixed
λ-box keeps them ≥ half the λ=0 values, so charFn_hold_decay generalizes with 768
doubled); optimize λ ≈ direction of (v - n·mean)/n. Alternatively do d=1 instances
(pascal_local_bound via iidSum_pascal_apply + Stirling; corpus
2026-06-19-mathlib-stirling-factorial-bounds.md) first — they are the same tilting
in one dimension and de-risk the design.

## Lap 28 (2026-07-10, fifth box session): (D) CHARACTER DECAY PROVED — charFn_hold_decay

`Prob/CharFn.lean`: `nd` (cyclic distance min(val, N-val)), **`nd_le_natAbs`** (any ℤ
representative bounds nd; emod/ediv case split, generalize-then-omega),
`exists_natAbs_eq_nd`, **`nd_sub_le`** (subadditivity via representatives),
`nd_cast`, `one_sub_re_stdAddChar_ge'` (Jordan in nd form).
`Sec7/Unroll.lean`: `pair_transfer` (helper) + **`charFn_hold_decay`**:
for N ≥ 4, `‖charFn (hold.map (modPair N)) ξ‖² ≤ 1 - ((nd ξ₁/N)² + (nd ξ₂/N)²)/768`.
Route: four atom masses through apply_le_map_apply, distinctness via N ∤ 1,2,3,
three pair anti-concentration bounds at differences (1,2),(0,2),(0,3), Jordan at the
pinned frequencies, nd-subadditivity triangle (ξ₁ = j₁ - j₂, ξ₂ = j₃ - j₂), linarith
assembly. ALL AXIOM-CLEAN. S3's 2-D kernel now needs only:

**(E) Gaussian summation (next lap)**: from `holdSum_toReal_le_charFn` +
`charFn_hold_decay`: P(holdSum n = v) ≤ N⁻² Σ_ξ (1 - (nd²-sum)/768N²·)^{n/2}...
concretely: ‖φ‖ⁿ = (‖φ‖²)^{n/2} ≤ (1 - D/768)^{n/2} ≤ exp(-nD/1536), D = (ndξ₁/N)²+(ndξ₂/N)².
Sum factorizes: N⁻²(Σ_{t : ZMod N} exp(-n(nd t/N)²/1536))². 1-D sum: index by
m = nd t ∈ [0, N/2], each m hit ≤ 2 times: ≤ 2Σ_{m≤N/2} exp(-nm²/(1536N²)).
At N = ⌈√n⌉+1 ≥ √n: n/N² ∈ [c,1], sum ≤ 2Σ_m exp(-m²·c/1536) = O(1) — bound the
series by geometric: exp(-am²) ≤ exp(-am) for m ≥ 1: Σ ≤ 1 + 1/(1-e^{-a}) etc.
→ **center-regime local bound**: P(holdSum n = v) ≤ C/(1+n) for ALL v (no Gweight
needed in center; the Gaussian factor of Lemma 2.2(i) comes from tilting (F) later).
Then state `hold_local_center` and wire toward `hold_local_bound`.

## Lap 27 (2026-07-10, fifth box session): (D) analytic core PROVED — pair bound + Jordan

`Prob/CharFn.lean`: `pairChar_conj`/`pairChar_mul_conj` (conjugate = negated argument),
`sum_toReal_eq_one` (finite PMF mass), **`charFn_normSq_pair_bound`** — the two-atom
anti-concentration bound `2·m₀·m₁·(1 - Re pairChar ξ (y₀-y₁)) ≤ 1 - ‖charFn r ξ‖²`
(double-sum expansion of normSq, all cross terms nonneg, single out (y₀,y₁)+(y₁,y₀));
**`one_sub_re_stdAddChar_ge`** — Jordan bound `8·(min(val, N-val)/N)² ≤ 1 - Re e(j/N)`
(cos → 2sin², Real.mul_le_sin both halves). Axiom-clean.

**(D) remaining assembly (next lap)**:
1. Push the four hold atoms through modPair N (apply_le_map_apply gives
   (hold.map (modPair N)) (y mod N) ≥ atom mass; equality not needed).
   Distinctness of images needs N ≥ 6 (atoms (2,5),(2,7),(2,8) differ in 2nd coord by
   2,3 < N; (1,3) vs (2,·) differ in 1st coord needs N ≥ 2; second coords 5,7,8 distinct
   mod N for N ≥ 6... actually 5≡8 mod 3 fine since 1st coords equal — need N ∤ 2, N ∤ 3,
   N ∤ 1 in coord combos: N ≥ 4 suffices for pairs used: check per-pair).
2. Per-pair: apply charFn_normSq_pair_bound with (y₀,y₁) ∈ {((2,5),(1,3)), ((2,7),(2,5)),
   ((2,8),(2,5))} — differences (1,2),(0,2),(0,3) — then Jordan at j = ξ·(1,2), ξ·(0,2),
   ξ·(0,3). Masses ≥ 1/16·1/4, 3/64·1/16, 1/32·1/16 → constants.
3. Triangle argument: dist(ξ₁/N,ℤ) + dist(ξ₂/N,ℤ) ≤ 2(d₁+d₂+d₃) where
   d_i = min-val-dist of the three pinned args (val arithmetic on ZMod: (ξ·(0,2)).val
   vs 2ξ₂.val mod N — work with the val-dist function zdist j := min(j.val, N-j.val)/N;
   key subadditivity: zdist(a+b) ≤ zdist a + zdist b, zdist(k·a) ≤ k·zdist a).
4. Combine: 1 - ‖φ‖² ≥ c·(zdist ξ₁² + zdist ξ₂²), c = 1/384-ish → ‖φ‖ ≤ exp(-c'·…),
   ‖φ‖ⁿ ≤ exp(-c'n(...)²).
5. (E): N⁻² Σ_ξ exp(-c'n·(zdist ξ₁²+zdist ξ₂²)) factorizes into 1-D sums; at N=⌈√n⌉+1
   the 1-D sum is O(1) (geometric domination); yields center-regime C/(1+n) bound.

## Lap 26 (2026-07-10, fifth box session): (D) nondegeneracy atoms PROVED

`Sec7/Holding.lean`: `hold_apply_pin` (first-coordinate pinning of hold atoms),
`hold_apply_two` (`hold (2, 3+b) = geomQuarter 2 · pascalNe3 b`), `pascalNe3_toReal`,
and the four numeric atoms `hold_apply_one_three/two_five/two_seven/two_eight`
(masses 1/4, 1/16, 3/64, 1/32 at (1,3),(2,5),(2,7),(2,8)). Difference set
{(1,2),(0,2),(0,3)} affinely generates ℤ² — the nondegeneracy input for (D).
All axiom-clean.

**(D) continued — next lap plan** (decay of `‖charFn (hold.map (modPair N)) ξ‖`):
1. `normSq_charFn_pair_bound`: for r : PMF (pair group) and atoms y₀ y₁,
   `‖charFn r ξ‖² ≤ 1 - 2·(r y₀).toReal·(r y₁).toReal·(1 - Re(pairChar ξ (y₀ - y₁)))`
   — expand `normSq (Σ m_y u_y)` as double sum (`Finset.sum_mul_sum` + `Complex.re` map_sum),
   `Σ_y m_y = 1` on finite group (PMF tsum_coe → Finset), drop nonneg off-pair terms
   (1 - Re(u ū') ≥ 0 via Complex.re_le_norm, norms 1).
2. `Re pairChar = cos(2π(ξ·w).val/N)` via ZMod.toCircle_apply + Complex.exp_re? — or
   avoid cos: `1 - Re(stdAddChar j) ≥ 8·(min j.val (N - j.val)/N)²` directly
   (1 - cos(2πt) = 2 sin²(πt), Jordan |sin πt| ≥ 2·dist(t,ℤ)).
3. Push hold atoms through modPair: (hold.map (modPair N)) y ≥ hold-atom mass at a
   preimage (apply_le_map_apply! already proved). For N ≥ 9 the four atoms map to
   DISTINCT pairs — mind collisions for small N (N ≤ 8 handle by crude bound or n small).
4. Assemble: three pair-terms give `1 - ‖φ‖² ≥ c·dist(ξ/N, ℤ²)²` (elementary triangle
   argument on t·(1,2), t·(0,2), t·(0,3); constant ≈ 1/384), then `‖φ‖ⁿ ≤ exp(-cn·dist²)`.
5. (E) Gaussian summation at N = ⌈√n⌉+1 → center-regime C/n local bound.

## Lap 25 (2026-07-10, fifth box session): (C2)+(C3) PROVED — finite Fourier inversion + charFn powers

`Prob/CharFn.lean` NEW, fully proved, axiom-clean: `sum_stdAddChar_mul` (1-D
orthogonality via `AddChar.mulShift` primitivity), `pairChar` product character +
norm/add lemmas, `sum_pairChar` (2-D orthogonality = product of 1-D), `charFn` (the
characteristic function, finite sum), **`charFn_inversion`** (exact Fourier inversion
for PMFs on `ZMod N × ZMod N`), `apply_toReal_le_sum_norm_charFn` (triangle form),
`toReal_bind_apply`/`sum_map_mul_complex` (finite-type PMF calculus),
`charFn_bind`/`charFn_map_add`/**`charFn_iidSum`** (r-hat of iid sum = r-hat^n),
**`iidSum_apply_toReal_le`** (`P(S_n = x) ≤ N⁻² ∑_ξ ‖r̂ ξ‖ⁿ`). In Unroll:
**`holdSum_toReal_le_charFn`** — the composite bound for the Hold walk, every N.

**Remaining for `hold_local_bound`** (all analysis, no more structure):
(D) character decay: `‖charFn (hold.map (modPair N)) ξ‖ ≤ exp(-c·‖ξ/N‖_dist²)` for
ξ ≠ 0 — from two/three explicit hold atoms (e.g. hold(1,3)=1/4, hold(2,4)=(4/3)(3/16)·(1/4)?
compute exact small atoms) via the two-atom identity `‖p·z₁+q·z₂+…‖ ≤ 1 - pq(1-cos θ)`
where θ = angle between atom characters; nondegeneracy: atoms (1,3),(2,5),(2,6) span ℤ²
affinely → the char cannot be unimodular-aligned unless ξ = 0. NOTE `hold` support lives
in ℕ×ℤ with unbounded coords; charFn is of the PROJECTED PMF, sum finite — decay constant
must be uniform in N: expect `1 - ‖φ‖ ≥ c·dist(ξ/N, 0)²` with dist = distance of
(ξ₁.val/N, ξ₂.val/N) to ℤ².
(E) Gaussian summation `N⁻² ∑_ξ (1 - c·dist²)^... ≤ C/n` at `N = ⌈√n⌉+1` — sum of
`exp(-cn·dist(ξ/N,ℤ²)²)` over the N² frequencies.
(F) exponential tilting wrapper (off-center regime) + Hold MGF strip finiteness
(= Lemma 7.6 engine, (7.30)). Center regime (i.e. |v - n(4,16)| ≤ √n) needs no tilt:
(D)+(E) alone give `≤ C/n ≤ C·Gweight/(1+n)` there. Do the untilted center case FIRST.

## Lap 24 (2026-07-10, fifth box session): circle-method probe — iidSum generic + mod-N entry PROVED

`iidSum` GENERALIZED to any `AddCommMonoid` (same proofs, omega→add_assoc);
`iidSum_map` (additive pushforward commutes with iid sums), `PMF.apply_le_map_apply`
(pushforward merges mass — the free-truncation observation: upper bounds via mod-N
reduction need NO tail argument), `holdSum_eq_iidSum` (Prod.fst_sum/snd_sum bridge),
`modPair`, and **`holdSum_le_modPair`** — circle-method step 1 for `hold_local_bound`:
`P(Hold_[1,n] = v) ≤ P(iid walk on ZMod N × ZMod N = v mod N)` for EVERY `N`. All
axiom-clean.

**Remaining S3 decomposition for `hold_local_bound`** (route now concrete):
(C2) finite Fourier inversion bound on `ZMod N × ZMod N`: `(r x).toReal ≤ N⁻² ∑_ξ
‖charFn r ξ‖` with `charFn r ξ := ∑_y (r y).toReal • eC((ξ₁ y₁ + ξ₂ y₂)/N)` (finite
sums; orthogonality of roots of unity — check mathlib `ZMod.dft`/`AddChar` inversion
or prove directly from geometric sums of `eC`);
(C3) `charFn (iidSum r n) ξ = (charFn r ξ)^n` (convolution multiplicativity via
`iidSum_succ` + cexpect product splitting);
(D) character decay `‖charFn (hold.map (modPair N)) ξ‖ ≤ exp(-c ‖ξ/N‖²)` for ξ ≠ 0
(the analytic crux; from hold's explicit mass: `hold (1, 3) = 1/4`, `hold (2, b)`
atoms give nondegeneracy in both directions — two-atom |φ|² identity);
(E) Gaussian summation `N⁻² ∑_ξ exp(-cn‖ξ/N‖²) ≤ C/n` with `N ≈ ⌈√n⌉`;
(F) exponential tilting wrapper for the off-center/exp regime + Hold MGF finiteness
on a strip (= Lemma 7.6 engine, (7.30)).
Choose N per (j,l)? No — N only enters (E); pick `N = ⌈√n⌉ + 1` uniformly.

## Lap 23 (2026-07-10, fifth box session): d=1 warm-up PROVED — negBinomial_apply + pascal_eq_map_iid

**Done (axiom-clean)**: `negBinomial_apply` — exact negative-binomial point mass
`P(|Geom(2)_n| = L) = C(L-1, n-1)·2^{-L}` by induction on `n` over the iid peel
(`tsum_iid_succ_mul`), convolution step = reindexed hockey stick
(`sum_range_choose_col`, `sum_Ico_choose_shift`); `pascal_eq_map_iid` — `pascal` IS
the 2-fold `Geom(2)` sum, immediate from `negBinomial_apply` at `n = 2` plus a
sum-zero support argument (`iid_geomHalf_sum_zero`, generic `PMF.iid_support_coord`
added to Prob/Basic). These give S3's Pascal instance an exact formula to work from:
`iidSum pascal n` = law of `|Geom(2)_{2n}|`, mass `C(L-1, 2n-1)·2^{-L}`.

**NEXT (S3 continued, per session mission)**: (a) the `iidSum pascal n =
iidSum geomHalf (2n)` splice (iid concat lemma) so `pascal_local_bound` reduces to
binomial estimates on `C(L-1, 2n-1)·2^{-L}` (Stirling recipe in corpus:
2026-06-19-mathlib-stirling-factorial-bounds.md); (b) probe the ZMod circle-method
decomposition for `hold_local_bound` (finite Fourier inversion on `ZMod N × ZMod N`,
exponential-tail truncation replaces the paper's `[-π,π]²` integral — no measure
theory); state the key intermediate lemmas.

## Lap 22 (2026-07-10, fifth box session): S3 front OPENED — Lemma 2.2 statements pinned

`Prob/LocalBound.lean` NEW: `Gweight` (2.2) factored from Unroll + `Gweight_pos/
_nonneg/_le_two`, `iidSum`, and Lemma 2.2(i)(ii) STATED (sorries) for `geomHalf`
(mean 2), `geomQuarter` (mean 4), `pascal` (mean 4): `*_local_bound` =
`C/√(1+n)·Gweight(1+n)(c(L-μn))`, `*_tail_bound` = indicator-tsum `≤ C·Gweight(1+n)(cλ)`.
`Sec7/Unroll.lean`: `holdSum` + `hold_local_bound`/`hold_tail_bound` (d=2, mean (4,16),
sup-norm; RATIFY-DRIFT notes: Gweight(1+n) vs G_n, ℕ index set, sup vs Euclidean norm).
Judge should ratify these vs paper pp.14-16 + p.42.

## Lap 21 (2026-07-10, fourth box session): Lemma 7.7 D6 layer — `fpDist` + (7.45) inequality

`Sec7/Unroll.lean` extended (all proved, axiom-clean, except the one named sorry):
* `fpDist : ℕ → PMF (ℕ × ℤ)` — the first-passage endpoint distribution (paper
  `v_{[1,k]}`, (7.44)) by budget recursion mirroring `Qstop`; normalization free
  from PMF combinators. Junk guard `d.2 ≤ 0` fires only on hold-null atoms.
* `fpDist_support_fst_pos`, `fpDist_support_snd_gt` — endpoints move right and
  overshoot the budget (`s < e₂`).
* `Q_le_fpDist_expect` — the (7.45) inequality in ℝ≥0∞ form:
  `ofReal (Q j l) ≤ Σ' e, fpDist s e · ofReal (Q (j+e₁) (l+e₂))` for every budget s.
  Strong induction over `Q_rec`, damping dropped (each factor ≤ 1). This is Case 2's
  (7.46) entry and Case 3's (7.53) at P = 0.
* `Gweight t x = exp(-x²/t) + exp(-|x|)` (paper (2.2)) and
  **`fpDist_location_bound` — Lemma 7.7 stated as the NEW NAMED SORRY** (X6):
  `(fpDist s (j,l)).toReal ≤ C·(e^{-c(l-s)}/√(1+s))·Gweight (1+s) (c(j-s/4))`,
  unconditional (LHS vanishes for l ≤ s by the support lemma).
  Numeric sanity: MC at s=40 → mode j ∈ {10,11,12} ≈ s/4+1, l ∈ {41,42,43} ✓.

**Attack routes for `fpDist_location_bound`** (the paper's pp.43–44 proof):
union bound over the last step (mirror: one `fpDist` unfold), `Hold` exponential
tail (Lemma 7.6 — provable from geomQuarter/pascalNe3 MGFs, finite products), and
the 2-D local bound Lemma 2.2 for iid `Hold` sums (node S3, the real wall; D5:
exponential tilting + circle method — `P(S_k = v) = (2π)^{-2} M(λ)^k e^{-λ·v} ∫|φ_λ|^k`).
NOTE: `fpDist` has no k-index — the D6 route needs a k-free reformulation of the
union bound, e.g. induction on s with the Gaussian weight as the induction invariant
(the paper's (7.33) reduction is already k-summed, which suits this form).

## Laps 18–20 (2026-07-10, fourth box session): X5 FULLY CLOSED — all three bridge sorries PROVED

**Done (axiom-clean)**: `hold_tsum_step` (7.29), `bridge_renewal` (7.27)≡(7.28),
`bridge_vector` (7.26)/(7.28). `Sec7/Bridge.lean` is now sorry-free;
**Proposition 7.3 (`renewal_white_encounters`) is fully proved modulo the single
Q-side sorry `Q_black_edge`** (its `#print axioms` sorryAx traces only through
`Q_polynomial_decay` → `prop_7_8` → `Q_black_edge`).

Infrastructure added (reusable): `PMF.tsum_bind_mul`/`tsum_map_mul`/
`tsum_iid_succ_mul`/`tsum_iid_zero_mul` (ℝ≥0∞ change-of-variables calculus),
`PMF.toReal_tsum_mul_ofReal`/`tsum_mul_ofReal_le_one`/`expect_iid_zero`/
`expect_iid_succ` (real expectation peeling for [0,1] observables) in
`Prob/Basic.lean`; `hold_tsum_expand`, `hold_tsum_step_real`, `pre_cons`,
`bridge_vector_gen` in `Sec7/Bridge.lean`. `bridge_renewal` gained a `0 ≤ ε`
hypothesis (Q_le_one summability).

Gotchas: `(3 + ∑ i, v i : ℤ)` elaborates cast-of-sum OR sum-of-casts depending on
context — spell `(3 : ℤ) + ∑ i, (v i : ℤ)` explicitly to match `hold`'s def;
`Fin.cons_succ` needs `(α := fun _ => ℕ)`; `congr 1` after `Fin.sum_univ_succ`
closes the i=0 head definitionally (don't bullet it); `if_congr` with `refine ?_`
holes gets stuck on Decidable instances — build the `Iff` in a `have` first;
`unfold PMF.expect; dsimp only` to beta-reduce before `rw [← tsum_mul_left]`.

**NEXT (the wall): `Q_black_edge` (Monotone.lean) — Lemma 7.7 D6 statement design.**
Handoff item 4: state the Chernoff/Gaussian first-passage endpoint bound over the
`Qstop` recursion (no infinite sequences; mirror the `Qstop` branch structure).
Paper Lemma 7.7 p.42–44, (7.30)–(7.33), Gaussian-type upper bound `G_k`. Then the
(7.50)/(7.51) white-exit constant (consumes proved `black_structure`) and Lemma
7.9's induction (X9) for the deep case. Parallel threads if blocked:
`key_fourier_decay` X1/X2 chain; S3 negative-binomial in Geometric.lean.

## After lap 11 (2026-07-10, third box session): `hold_weight_expect` PROVED

**Done** (axiom-clean): the (7.43) Case-1 geometric-expectation leaf
`hold_weight_expect` — `E[max(m-d₁,1)^{-A}] ≤ exp(ε³/2)·m^{-A}` for `m ≥ C_A`.
Chain: `hold_map_fst` (first marginal of `hold` is `geomQuarter`, by PMF monad laws) →
`hold_fst_marginal`/`hold_tsum_fst` (ℕ×ℤ-tsum marginalization via `ENNReal.tsum_prod'`)
in `Sec7/Holding.lean`; `geomQuarter_toReal`/`_tsum_toReal`/`_summable_toReal`/
`geomQuarter_tail` (exact tail `(3/4)^t`, injective-shift `hasSum`) in
`Prob/Geometric.lean`; then in `Monotone.lean` the three-region split
(head `k ≤ K` weight `(m-K)^{-A} ≤ (1+δ/3)m^{-A}` via `c := (1+δ/3)^{1/A}`;
middle `K < k ≤ m/2` mass `(3/4)^K ≤ (δ/3)2^{-A}` and weight `≤ 2^A m^{-A}`;
tail `k > m/2` mass `(3/4)^{m/2} ≤ (δ/3)m^{-A}` via
`summable_norm_pow_mul_geometric_of_norm_lt_one` → tendsto → threshold `T`).

**Lap 12 addendum**: `Q_white_case1` (Case 1 proper, (7.41)–(7.43)) PROVED,
axiom-clean — one `Q_rec` step at the white start pulls `exp(-ε³)`, `Q_le_Qm` at
depth `m-1` bounds each hold-atom landing (`half - (half-m+d₁) = m - d₁` by omega),
`hold_weight_expect` gives the `exp(ε³/2)m^{-A}` expectation, and
`exp(-ε³)·exp(ε³/2) = exp(-ε³/2)`. X7's remaining open pieces: Case 2 (black start,
paper (7.44) — needs the triangle/renewal input), the `prop_7_8` assembly from the
two cases, then `Q_polynomial_decay` by induction on `m` from (7.39) + Prop 7.8.

**Original route note (superseded)**: consume `Q_rec` + `Q_le_Qm` +
`hold_weight_expect`. Route: one step of `Q_rec` at the white start `(n/2 - m, l)`
pulls `exp(-ε³)`; each hold-atom `d` lands at `j = n/2 - m + d₁` with
`n/2 - (m-1) ≤ j` (d₁ ≥ 1), so `Q_le_Qm` (depth `m-1`) bounds the landed value by
`max(n/2 - j, 1)^{-A}·Q_{m-1}`; note `n/2 - (n/2 - m + d₁) = m - d₁` (ℕ, m ≤ n/2),
matching `hold_weight_expect`'s weight; needs `Qm_nonneg` to pull the constant
`Q_{m-1}` out of the tsum. Combine: `exp(-ε³)·exp(ε³/2) = exp(-ε³/2)`.
Then Case 2 (paper (7.44), black start) and the Prop 7.8 induction (X9).
Judge follow-up (b) DONE (lap 13): `check12` in `tools/check_blueprint.py` — the
(7.36)-bridge. Pascal-column DP (mirrors `renewal_white_encounters` LHS) vs
hold-jump DP (mirrors `E Q(Hold)` with the D6 recursion + `whiteSet` adapter);
agreement 1e-11 at n=14/16, incl. amplified damping (1/e, 0.5) where any
coordinate off-by-one would show at O(1). Renewal identity (7.26)≡(7.27) and the
paper-vs-0-based seam are pinned end-to-end. All judge follow-ups now closed.

## Lap 14 (2026-07-10): (7.45) unrolling — `Qstop`/`Qstop_eq` PROVED (X8/X9 entry)

New `Sec7/Unroll.lean` (axiom-clean): `hold_support_snd_ge`/`hold_zero_of_snd_lt`
(second coord of `hold` ≥ 3), `Qstop half W ε s j l` — the D6 stopped value (well-
founded on the height budget `s`; a step with `d₂ > s` = the paper's first passage
`l_{[1,k]} > s` lands on plain `Q`), and `Qstop_eq : Qstop s j l = Q j l` (∀ s) —
paper (7.45) verbatim, by strong induction on `s` over `Q_rec`. No stopping-time
measure theory needed. Case 2 (X8) and Lemma 7.9 (X9) both enter through this:
pick `s := l_Δ - l` per triangle; the overshoot branch's endpoint is what the
white-exit bound (7.50)/(7.51) + `Q_le_Qm` control.

**X8 next steps**: (a) a `Qstop_le` bound isolating the overshoot-branch endpoint
expectation (Case 2's (7.46)); (b) the endpoint-distribution facts need Lemma 7.7
(Chernoff for the 2D renewal walk) — the genuinely hard probabilistic kernel;
(c) the white-exit constant (7.50)/(7.51) consumes Lemma 7.4's structure
(`black_structure` proved) + 7.7. **X9**: `Z R j l` recursion on `R` over `Qstop`.

## Lap 15 (2026-07-10): `prop_7_8` ASSEMBLED — open core narrowed to `Q_black_edge`

`prop_7_8` (Prop 7.8, Q_m ≤ Q_{m-1}) is now PROVED modulo one named sorry:
`Q_black_edge` (Monotone.lean) — the (7.41) edge bound for black starts
(Cases 2–3, paper (7.44)–(7.67)). The assembly: `Real.iSup_le` over the `Qm m`
sup; interior points (`p₁ > half - m`) drop to `Q_{m-1}` via `le_Qm` at depth
`m-1` (same weight); edge points (`p₁ = half - m`, weight `m^A`) use
`Q_white_case1` (white) or `Q_black_edge` (black), with the `m^A·m^{-A}` rpow
cancellation. Gotcha: the sup-subtype projections `(⟨(p1,l),_⟩).1` block omega —
normalize with defeq `have`/`show` bridges first.

**The X7→X11 chain now rests entirely on `Q_black_edge`**, whose route is:
`Qstop_eq` (proved) + Lemma 7.7 Chernoff (X6, the hard probabilistic kernel) +
white-exit (7.50)/(7.51) (consumes `black_structure`, proved) for Case 2; +
Lemma 7.9 induction (X9) for Case 3. Next: state Lemma 7.7 (D6 form) and the
Case 2/3 split of `Q_black_edge`; then `Q_polynomial_decay` from `prop_7_8` +
`Qm_le_rpow` by forward induction on m (tractable now).

## Lap 16 (2026-07-10): `Q_polynomial_decay` PROVED (from prop_7_8)

(7.37) closed: forward induction on `m` — below the threshold `Cb := max C0 1`
use `Qm_le_rpow` ((7.39)); above, `prop_7_8` steps down; gives the uniform bound
`Q_m ≤ Cb^A`, then `Q_le_Qm` at depth `n/2 - j` (strip interior) or `Q_le_one`
(past the edge, weight 1). Constant `C := Cb^A`. Depends on `Q_black_edge` via
`prop_7_8` — the whole §7.4 chain is now a cone over that single sorry.
Gotcha: standalone `have h := Q_le_Qm ...` needs `(l := l)` (implicit `l`
unconstrained). Next: the (7.36) seam in Decay.lean (E Q(Hold) ≪ n^{-A} from
`Q_polynomial_decay` + `hold_tsum_fst`-style Geom(4) tail), or start Lemma 7.7's
D6 statement for `Q_black_edge`.

## Lap 17 (2026-07-10): Prop 7.3 (`renewal_white_encounters`) ASSEMBLED — X5 seam named

New `Sec7/Bridge.lean`: `Rcol` (the per-column D6 form of the (7.28) product) and
`renewal_white_encounters` (MOVED from Holding.lean) now PROVED modulo three named
X5 sorries, all numerically pre-validated by harness check12:
- `bridge_vector` — iid-Pascal-vector expectation = `Rcol 0 0` (induction on length
  peeling `Fin.cons`; `pre (cons a v) (i+1) = a + pre v i`, `Fin.succ` filter reindex);
- `hold_tsum_step` — the (7.29) one-column self-similarity of `hold` in tsum/ℝ≥0∞ form
  (split `geomQuarter` at `k = 1`, peel one `pascalNe3` off `PMF.iid`);
- `bridge_renewal` — `Rcol j l = Σ' d, hold(d)·Q((j,l)+d)` (downward induction on
  `half - j` via `hold_tsum_step` + `Q_rec`; boundary `j ≥ half` needs `d₁ ≥ 1`).
The analytic assembly (trivial small-n bound; `Q_polynomial_decay` pointwise +
`hold_weight_expect` at `m = n/2` + `(n/2)^{-A} ≤ 3^A n^{-A}`) is fully proved.

**Open ledger for the §7 probability side is now**: `Q_black_edge` (X8/X10 kernel) +
the three X5 bridge sorries + `key_fourier_decay`'s reduction chain (X1/X2, Fourier
side) + upstream S-chain. Next: prove `hold_tsum_step` (most mechanical of the three),
then `bridge_renewal`, then `bridge_vector`.

## After laps 6–10 (2026-07-10, second box session): **X3 HEAD CLOSED — Lemma 7.4 PROVED**

`black_structure` is now a theorem, `#print axioms` = `[propext, Classical.choice,
Quot.sound]`. The whole chain, all in `Sec7/Triangles.lean`:
`θq_left_run` → `θq_fibre_eq` (exact ℚ fibre identity `θ(j,l) = 9^{j-j*}2^{l*-l}θ*`)
→ `fibre_le_eps`/`corner_phase_pos`/`black_mem_corner_triangle` (Δ*-membership) →
`wb_row_left/right` + `white_row_above` (Claim (*) Cases 2–3 engine) + `lstar_eq_of`/
`jstar_eq_of` (Nat.find corner characterization) → `black_of_mem_corner_triangle`
(Δ* black) + `corner_triangle_confined`/`_strip` (confinement, log numerics) →
`corner_eq` (corner invariance = fibre equality) → assembly via `cornerTriple` image,
`lattice_sq_dist_ge_one`, `sep_const_sq_le_one` (`10¹² ≤ 2⁴⁰` trick for
`(1/10)log(10⁴) < 1`). Note: at ε = 10⁻⁴ the separation conjunct reduces to lattice
disjointness — Case 1 proper was not needed for Lemma 7.4 itself (our fibre identity is
exact where the paper's (7.18) is an inequality). Also done: `unifOddMod` normalization
(judge follow-up a).

**Judge follow-ups still open**: (b) the (7.36)-bridge harness check in
`tools/check_blueprint.py` (judge item 9); (c) Case 1 proper statement per judge item 8
spec (needed for the Q-recursion / Lemma 7.9 series, NOT for Lemma 7.4 — see above).

**Next hardest open obligations** (X3 done → move up the chain): Lemma 7.9 induction
skeleton over `Q_rec` (X9) consuming `Q_white_contract`/Case 1; the (7.45) unrolling
statement design (X8); S3's d=1 negative-binomial half; `renewal_white_encounters`
(Prop 7.3) probabilistic side.

## After lap 5 (2026-07-10)

**Done** (axiom-clean): (a) (7.18) inequality forms — `sfrac_mem`/`sfrac_eq_self`/
`sfrac_idem`, `θq_succ_j_abs_le`, `θq_pred_l_abs_le`, `θq_iterate_abs_le`
(`|θ(j+a,l-b)| ≤ 9^a 2^b |θ(j,l)|` unconditional); (b) the corner map:
`exists_white_above` (via `black_run_le` + archimedean), defs `upRun`/`lstar`/
`leftRun`/`jstar` (Nat.find, classical), spec lemmas `black_of_le_lstar`, `le_lstar`,
`white_above_lstar`, `leftRun_pos`, `black_of_jstar_le`, `jstar_maximal`.
NOTE: our `sfrac` range is `[-1/2, 1/2)` (mirror of the paper's `(-1/2, 1/2]`);
only `|sfrac|` is used and denominators are odd, so no discrepancy — documented at
`sfrac_mem`.

**X3 next**: the corner triangle fibre. Key lemma to state and prove next
(paper (7.17)–(7.18) + Claim (*) — the heart of Lemma 7.4):
  `theorem mem_corner_triangle`: for black (j,l) in the strip, with (j*,l*) its corner
  and s* := log(ε/|θ(j*,l*)|) ≥ 0: `9^(j-j*)·2^(l*-l)·|θ*| ≤ ε` (i.e. (j,l) ∈ Δ* as a
  ℚ-inequality — the ℝ-log triangle membership is monotone algebra on top).
  Route: |θ(j,l)| ≤ ε (black) and θ(j,l) = 9^(j-j*)2^(l*-l)θ* by θq_iterate_exact
  — but the iterate goes from the corner DOWN to (j,l): need the scale < 1/2 premise,
  which needs Claim (*) Case-1-style reasoning (if the scaled value exceeded ε it
  wraps...). Careful: the correct paper route is (7.18) with equality "whenever the
  RHS is strictly less than 1/2". Plan: prove by strong induction down the run using
  the run lemmas (each step black keeps values ≤ ε ≤ 1/4, so exact steps apply and the
  product never wraps). Concretely: (j,l) black, everything between (j,l*)..(j,l) black
  (black_of_le_lstar column) and (j*,l*)..(j,l*) black (row) — then iterate exact steps
  along row then column, all values staying ≤ ε.
  CAUTION: intermediate points of Δ* are NOT all on the row/column path; but the paper's
  Δ* membership only needs the (j,l)↔corner relation, and the run lemmas give exactly
  the path needed. |θ(j,l)| = 2^(l*-l)|θ(j,l*)| (θq_up_run) and
  |θ(j,l*)| = 9^(j-j*)|θ(j*,l*)| (row version of up_run — NEEDS a leftward run-exact
  lemma `θq_left_run`, same proof shape as θq_up_run using θq_succ_j_exact on black row
  points: TO WRITE).
  Then fibre equality Δ* = {p : black, corner p = (j*,l*)} and Claim (*) cases.

## After lap 4 (2026-07-10)

**Done** (axiom-clean): `θq_iterate_j`, `θq_iterate_l`, `θq_iterate_exact` — the (7.18)
equality-case scaling `θ(j+a, l-b) = 9^a·2^b·θ(j,l)` when the final scale is < 1/2 (the
triangle-fibre engine); `θq_up_run` (upward black run ⇒ exact doubling downward) and
`black_run_le` (`2^t ≤ ε·3^{n-2j}` caps upward black runs ⇒ paper's l* exists).

**X3 remaining for `black_structure`**: (a) leftward run at l* (j*-existence — runs
hit j=0 or a white point; finite by construction, no analytic input needed);
(b) DEFINE the corner map + triangle size (`s* := log(ε/|θ*|)` — lives in ℝ, ties ℚ-θ
to the ℝ-triangle (7.11)); (c) fibre equivalence via `θq_iterate_exact` both directions
(Claim (*) Cases 1–3 using claims (i)–(iii)); (d) assemble. This is now bounded work but
a lot of it — decompose into named sorries inside Triangles.lean when starting assembly.

## After lap 3 (2026-07-10)

**Done**: (7.16) formalized — `θq_lower_bound` (`3^{-(n-2j)} ≤ |θ(j,l)|` for ξ coprime
to 3, `2j+1 ≤ n`, via the ±1/3-mod-ℤ 3-adic argument: `sfrac_phase_absorb` +
`abs_sfrac_le` + argRel scaling) and `black_nine_le` (black ⇒ `n - 2j ≥ 9`). All
axiom-clean. This is the strip-confinement input to Lemma 7.4's conjunct 4.

**Next attack on X3 (`black_structure`)**: with (7.16) + claims (i)–(iii) in hand, the
remaining Lemma 7.4 ingredients are (a) l*-existence: an upward black run from a black
point terminates (uses `black_nine_le` at growing powers via `θq_pred_l_exact` doubling:
|θ(j,l')| = 2^{l-l'}|θ(j,l)| forces whiteness once above ε... paper argument p.38 uses
3^{n+1-2j}2^{l-l'}ε ≥ 1/3 — formalize as: black run upward of length > log₂(3^{n-2j}ε)
impossible); (b) j*-existence (leftward run hits j=1); (c) the Δ* fibre equivalence
(7.17)/(7.18) — the equality case identity |θ(j',l')| = 9^{Δj}2^{Δl}|θ*| when RHS < 1/2,
provable by induction from the two exact lemmas.

## After lap 2 (2026-07-10)

**Done this lap** (all `#print axioms`-clean, build green):
- `Sec7/Triangles.lean`: θ-identity exactness (`θq_succ_j_exact`, `θq_pred_l_exact` —
  no-wraparound forms of (7.13)/(7.14)) and the paper-p.38 weakly-black claims
  (i) j-form + l-form, (ii), (iii) (`black_of_weaklyBlack_succ_j/pred_l`,
  `weaklyBlack_of_succ_j_pred_l`, `weaklyBlack_of_pred_j_pred_l`). These are the engine
  of every case of Lemma 7.4's Claim (*).
- `Sec7/Monotone.lean`: `Q_white_contract` (Case 1 warm-up) and `Qm_le_rpow` (7.39,
  the Prop 7.8 induction base) proved.

**Crux state / next attack** (hardest-first):
1. **X3 — Lemma 7.4 `black_structure`**: claims (i)–(iii) now proved. Next: formalize
   (7.16)-strip confinement (`black → j ≤ n/2 - (1/10)log(1/ε)`; needs the "ξ·3^{n-1}·…
   is 1/3 or 2/3 mod 1" 3-adic step), then l*/j* existence (finite runs: the check-8
   argument — upward black runs terminate since 3^{n+1-2j}2^{l-l'}ε ≥ 1/3 fails), then
   the (7.17)/(7.18) triangle-fibre equivalence. Decompose into named sub-sorries in
   Triangles.lean next lap.
2. **X8 Case 2 / X9 Lemma 7.9 skeleton**: (7.45) iterate of `Q_rec` (unrolling along the
   first-passage time) is the next structural lemma; needs a finitized stopping-time
   unrolling over `Q` — statement design work.
3. **S3 (Lemma 2.2)**: untouched; awaits D5 tilting route. Consider starting the d=1
   exact-formula half (negative binomial Gaussian bounds) as an independent thread.

**Notes / traps recorded**: triangle sizes are NOT O(log 1/ε) (giant triangles exist,
harness check 8); Lemma 7.4 separation is between point SETS (statement fixed lap 1).
