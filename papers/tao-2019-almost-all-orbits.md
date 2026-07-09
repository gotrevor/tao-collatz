# Tao 2019 — Almost all orbits of the Collatz map attain almost bounded values

**PDF**: `tao-2019-almost-all-orbits.pdf` (symlink → `~/src/collatz-cryptid/data/refs/`;
gitignored — copyrighted, this repo may eventually go public)
**Source**: arXiv:1909.03562 (v5, 2022-02-15), https://arxiv.org/abs/1909.03562
**Published**: Terence Tao, *Almost all orbits of the Collatz map attain almost bounded
values*, Forum of Mathematics, Pi **10** (2022), e12. DOI: 10.1017/fmp.2022.8
**Length**: 57 pp + figures. MSC 37P99.

## What it is

The strongest known "almost all" result on the Collatz conjecture. For ANY function
`f : ℕ+1 → ℝ` with `f(N) → ∞` — however slowly, e.g. `log log log log N` — the Collatz
orbit minimum satisfies `Col_min(N) < f(N)` for almost all `N`, in **logarithmic density**
(Theorem 1.3). Supersedes Terras/Everett (`< N`), Allouche (`< N^θ, θ > 0.869`), and Korec
(`θ > log3/log4 ≈ 0.7924`), all of which used natural density and fixed powers.

This repo formalizes exactly this paper; the node-by-node decomposition lives in
`../BLUEPRINT.md` (26 nodes, design decisions D1–D8) — this summary is the paper-facing
companion, not a duplicate of the ledger.

## Proof architecture (one breath)

Work with the Syracuse map `Syr(N) = (3N+1)/2^{ν₂(3N+1)}` on odd numbers. The n-fold
iterate is an explicit affine map determined by the valuation vector
`a⃗(N) = (ν₂(3N+1), ν₂(3Syr(N)+1), …)` (eq. 1.7). For `N` drawn log-uniformly,
`a⃗(N)` is close in total variation to iid `Geom(2)` (Prop 1.9, §4) — so the 3-adic residue
`Syrⁿ(N) mod 3ⁿ` is governed by the **Syracuse random variables**
`Syrac(ℤ/3ⁿℤ) = F_n(Geom(2)ⁿ) mod 3ⁿ` (1.21). The heart of the paper: these become
equidistributed at fine 3-adic scales (Prop 1.14), which follows from superpolynomial decay
of their characteristic function, `E e(-ξ·Syrac/3ⁿ) ≪_A n^{-A}` uniformly in `ξ ∤ 3` (Prop
1.17, §7 — the hard section). Fine-scale mixing feeds a Bourgain-style invariant-measure
surrogate: the first-passage locations `Pass_x(N_y)` stabilize in distribution across scales
`y = x^α` vs `x^{α²}` (Prop 1.11, §5), and iterating the passage map across a telescoping
tower of scales pulls almost every orbit below any slowly-growing `f` (Thm 3.1 → 1.6 → 1.3, §3).

§7 proves Prop 1.17 by pairing the geometric variables (`b_j = a_{2j-1} + a_{2j}` ~ Pascal),
factoring the characteristic function into an average of cosines over a **2-D renewal
process**, and showing the walk keeps hitting "white" points (where the cosine contracts).
The black set — where no contraction happens — is exactly a union of well-separated
**triangles** in `(j,l)`-space (Lemma 7.4, elementary 3-adic number theory), and the walk's
drift (slope 4 vs triangle-diagonal slope log9/log2 ≈ 3.17) forces it out of any triangle,
through the white buffer Lemma 7.4 guarantees around it (Prop 7.8's three-case induction,
Lemmas 7.9/7.10).

## Key recallable facts

- **Log density, not natural density**: forced by the `exp(O(√n))` multiplicative spread of
  `Syrⁿ(N) ≈ (3/4)ⁿN` (1.17); log-uniform measure is what the Syracuse flow approximately
  transports (Remark 1.16 sketches the natural-density upgrade as plausible but unpursued).
- **Quantitative core** (Thm 3.1): `P(Col_min(Log(ℕ∩[1,x])) ≤ N₀) ≥ 1 - O(log^{-c} N₀)`
  uniformly in `x ≥ 2`; Remark 1.4: sharpening to a constant `C₀` would be nearly
  Collatz-complete (heuristic obstruction), so this "almost bounded" form is the natural wall.
- **The paper's own waypoint** (Remark 5.1): the §4/§5 machinery alone already recovers
  `Syr_min(N) ≤ N^θ` for a.a. N (Korec-strength) — our campaign's Series-β milestone.
- **Syrac(ℤ/9ℤ) table** (p.10, our harness check 3): values 0..8 have masses
  `0, 8/63, 16/63, 0, 11/63, 4/63, 0, 2/63, 22/63` — multiples of 3 are never hit.
- **Footnote 6 trap**: §7 REVERSES the variable order of (1.5) → (1.26); same law since
  `Geom(2)ⁿ` is exchangeable. Encoded in our skeleton as `syracZ_eq_rev_fnat`.
- **Only two geometric distributions appear**: `Geom(2)` (valuations) and `Geom(4)`
  (renewal holding-time first coordinate); `Pascal = Geom(2)+Geom(2)`; `Hold` has mean (4,16).
- Constants: `α = 1.001` (1.18); §7's `ε < 1/100` absolute; `A`-dependence threads
  `C_A → C_{A,ε} → P → R = ⌊A²/ε⁴⌋` (our D7 ledger).
- Acknowledgments note the 2-D renewal formulation is due to a suggestion of **Marek Biskup**;
  Ben Green suggested the diagonalisation remark (fn. 2).

## Why it matters to the Lean work

- Greenfield: no formalization exists in any prover (checked 2026-07-08); this repo is the
  first attempt. Everything in the paper is *discrete* probability — hence our D1 (PMF/tsum,
  no measure theory) and D6 (finitized renewal recursion) design bets, both kernel-validated.
- The three formalization risk kernels map to: Lemma 2.2 (local 2-D Gaussian bounds; the
  paper's one complex-analytic proof, we take a real-variable tilting route — D5), Lemma 7.4
  (triangle structure), and §7.4's Cases 2–3 (Lemmas 7.9/7.10). See `../EXECUTABILITY.md`.
- Related reading in the sibling repo: Lagarias surveys + Krasikov–Lagarias density bounds
  (`~/src/collatz-cryptid/data/refs/`, indexed at `collatz-cryptid/notes/refs.md`).
