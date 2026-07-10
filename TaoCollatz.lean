import TaoCollatz.Basic.Collatz
import TaoCollatz.Basic.LogDensity
import TaoCollatz.Basic.Valuation
import TaoCollatz.Prob.Basic
import TaoCollatz.Prob.Geometric
import TaoCollatz.Prob.LocalBound
import TaoCollatz.Syracuse.SyracRV
import TaoCollatz.Syracuse.ValuationDist
import TaoCollatz.Fourier.ZMod3
import TaoCollatz.Sec5.FirstPassage
import TaoCollatz.Sec6.MixingFromDecay
import TaoCollatz.Sec7.Setup
import TaoCollatz.Sec7.White
import TaoCollatz.Sec7.Triangles
import TaoCollatz.Sec7.Holding
import TaoCollatz.Sec7.Unroll
import TaoCollatz.Sec7.Monotone
import TaoCollatz.Sec7.Bridge
import TaoCollatz.Sec7.Decay
import TaoCollatz.Statement

/-!
# TaoCollatz

Lean 4 formalization of Tao 2019, *Almost all orbits of the Collatz map attain almost
bounded values* (arXiv:1909.03562). Phase-A skeleton: ratified statement chain per
`SKELETON-SPEC.md`; design decisions in `BLUEPRINT.md`.

Trusted base: `TaoCollatz/Statement.lean` (Theorems 1.3 and 3.1).
-/
