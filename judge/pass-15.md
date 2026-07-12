# Judge pass 15 (2026-07-12 ~20:45 EDT, Ren/Fable — consumer-pages read, Trevor-prompted) — BOTH X9 RIDERS DISCHARGED ✅

Scope: judge read of pp.48–49 + 54–56 (the X11 consumer pages — the last unread
§7 text). No new commits judged; this pass de-risks the interface the box is
building toward, before the Z-induction gets built on it.

## Rider (a) — "R chosen after ε": DISCHARGED (main clause)

p.55, verbatim structure: apply Lemma 7.9 at `(j′,l′) := (j,l)+v_{[1,k]}` →
Markov's inequality → outside `F_*` with `ℙ(F_*) ≤ 10^{−A−2}`, the integrand is
`≪ 10^A`, giving `Σ 1_W ≫ ε·min(r,R) − O(A)` → **"In particular, if we set
R := ⌊A²/ε⁴⌋"** → (7.66). So:

- **R is chosen explicitly as ⌊A²/ε⁴⌋ — after ε and A.** The ManyTriangles
  docstring claim is verified against the text.
- **The −O(A) slack absorbs any absolute constant in X9's bound.** exp(2ε)
  costs an additive 2ε inside the O(A); even the ∃C fallback (exp(2ε+εg))
  would have been consumable. The pass-9 wash-out claim is now judge-verified,
  not just asserted.

**Residual burden, sharpened**: the ε on p.55 is the FIXED black/white
dichotomy constant — the repo's `epsBW = 10⁻⁴`. X11 must instantiate
`many_triangles_white` at `ε = epsBW`, so **X9's proof must exhibit
ε₀ ≥ 10⁻⁴**. Numerically comfortable (the pin's own cap is 1/100; the ledger
constraints — `hsmall` at p₀ ≈ 0.99, `e^{2ε−1} ≤ 1` — allow far more), but it
is now a precise certification obligation on the box, no longer a
maybe-the-consumer-rescues-us contingency.

## Rider (b) — gate consumer-safety: DISCHARGED

- p.49, verbatim: the (7.54) analysis splits on `j_{[1,k+P]} ≥ 0.9m`, kills
  that branch by `ℙ ≪_P exp(−cm)` (Lemma 7.7 + (7.52) for the first-passage
  leg, Lemma 2.2 for the P extra holds), and on the surviving branch
  `max(1 − j_{[1,k+P]}/m, 1/m)^{−A} ≤ 10^A`. So the surviving branch keeps the
  walk's `j`-advance `< 0.9m` — depth `> 0.1m` — through the whole window.
- p.55–56: the deterministic claim (7.67) produces its `r`-increments by
  iterating triangle exits WITHIN the window (`t_R ≤ P`), so every encounter
  it counts is deep. With `m ≥ C_{A,ε}` and `C_{A,ε} ≥ 10g`, every one clears
  the gate: **the gated count still reaches R.** The box's consumer-safety
  argument is correct as stated.

## Bonus — X10's ∀A-strengthening confirmed at its consumption site

p.54: the union bound takes `E_{p,4^A(1+p)³}` over `0 ≤ p ≤ m^{0.1}`, giving
`ℙ(E_*) ≪ A²·4^{−A}` (the `(1+p)^{−2}` sum converges; the exp term collapses).
This needs Lemma 7.10 with constants uniform over the varying `p, s′` at each
`A` — exactly the `∀A>0`-with-uniform-`C,c` form ratified at pass 8.

## Fronts state

**All of §7 is now judge-read (pp.33–56).** Remaining unread front: §5 (C8) —
the last un-pinned node. X11's eventual ratification is now pre-cleared on
both consumer checks; what remains for X11 is ratifying its own statement pins
(E_*, F_*, R = ⌊A²/ε⁴⌋, (7.67), the Prop 7.8 → 1.17 assembly) when they land.
