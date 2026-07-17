import Lean
/-!
# Explicitness closure walk (big-C campaign, step-0 guard)

Judge amendment (DIRECTION.md, Ruling II, binding): the explicitness audit must walk
`C_tao_assembled`'s **definitional closure** — a `collectAxioms`-style constant traversal
of the environment — and must NEVER grep files (`Nat.sInf` legitimately appears in
`syrMin`/`passTime`, which are statement objects, not the constant's spine; and a walk
seeded wrong walks nothing and passes green, which is strictly worse).

Run: `lake env lean --run tools/ExplicitnessClosure.lean`  (invoked by
`tools/big_c_cutoff_audit.py --complete`).

Contract enforced (BIG_C_EXPLICIT_BOUND_PLAN.md, "Explicitness contract"): the transitive
def-spine of `TaoCollatz.C_tao_assembled` — recursing through every project-local (`TaoCollatz.*`)
definition's value, treating mathlib/core constants as leaves — contains no
`Classical.choose` / `Exists.choose` / `Classical.indefiniteDescription` / `Classical.choice`,
no `sInf`/`sSup`-component leaf, no `Nat.find`, and no value-less (axiom/opaque) project
constant. The walk PRINTS the closure size it visited (`CLOSURE_SIZE=…`) and FAILS LOUD when
the seed is unknown or the walked closure is empty — a vacuous pass is the failure mode this
script exists to prevent.
-/
open Lean

def seedName : Name := `TaoCollatz.C_tao_assembled

/-- Leaves whose appearance in the def-spine means a hidden witness selector. -/
def forbiddenExact : List Name :=
  [`Classical.choose, `Classical.choice, `Exists.choose, `Classical.indefiniteDescription,
   `Nat.find, `Nat.findGreatest]

def isForbidden (n : Name) : Bool :=
  forbiddenExact.contains n ||
  n.components.any (fun c => c == `sInf || c == `sSup || c == `iInf || c == `iSup ||
                             c == `csInf || c == `csSup)

/-- Recurse into a constant's value iff it is project-local. -/
def isProject (n : Name) : Bool := n.getRoot == `TaoCollatz

def main (args : List String) : IO UInt32 := do
  -- Optional CLI arg: override the seed (smoke-testing the walker itself only; the
  -- audit's --complete gate always uses the default seed).
  let seedName := match args with
    | [s] => s.toName
    | _ => seedName
  initSearchPath (← findSysroot)
  let env ← importModules #[{module := `TaoCollatz}] {} (trustLevel := 1024)
  let some seedInfo := env.find? seedName
    | do IO.eprintln s!"FAIL: seed {seedName} not found in environment — a walk with no seed \
                        walks nothing; refusing to pass vacuously."
         return 1
  let some seedVal := seedInfo.value?
    | do IO.eprintln s!"FAIL: seed {seedName} has no value (axiom/opaque?)"
         return 1
  let mut queue : Array Name := seedVal.getUsedConstants
  let mut visited : NameSet := {}
  let mut walked : Nat := 0        -- project defs whose value we recursed into
  let mut leaves : NameSet := {}
  let mut bad : Array Name := #[]
  visited := visited.insert seedName
  walked := walked + 1
  while h : queue.size > 0 do
    let n := queue[queue.size - 1]
    queue := queue.pop
    if visited.contains n then continue
    visited := visited.insert n
    if isForbidden n then
      bad := bad.push n
      continue
    if isProject n then
      match env.find? n with
      | some (.thmInfo _) =>
        -- Theorems are proofs riding inside the term (e.g. a `dite` guard's
        -- certificate); proof content cannot affect the value. Leaf.
        leaves := leaves.insert n
      | some (.axiomInfo _) =>
        IO.eprintln s!"FAIL: project AXIOM {n} in the def-spine — not explicit."
        bad := bad.push n
      | some info =>
        match info.value? with
        | some v =>
          walked := walked + 1
          queue := queue ++ v.getUsedConstants
        | none =>
          IO.eprintln s!"FAIL: project constant {n} in the def-spine has no value \
                         (opaque) — not explicit."
          bad := bad.push n
      | none =>
        IO.eprintln s!"FAIL: {n} used but not found in environment"
        bad := bad.push n
    else
      leaves := leaves.insert n
  IO.println s!"CLOSURE_SIZE={walked}"
  IO.println s!"LEAF_COUNT={leaves.size}"
  if walked ≤ 1 then
    IO.eprintln "FAIL: walked closure is trivial (≤ 1 project def) — seed likely wrong."
    return 1
  if bad.isEmpty then
    IO.println "EXPLICITNESS: clean (no witness selectors in the definitional spine)"
    return 0
  else
    for n in bad do IO.eprintln s!"FORBIDDEN: {n}"
    return 1
