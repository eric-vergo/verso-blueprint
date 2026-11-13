/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

import Lean.Util.CollectAxioms

/-!
The axioms a declaration depends on, as `#print axioms` reports them, and the
class each axiom belongs to.

Every Lean declaration a Blueprint node refers to is asked once, when the node
is captured. Lean answers for an imported declaration from the axiom table its
module exports, but walks the bodies of declarations from the module being
elaborated on every call; `declarationAxioms` keeps one answer per name for the
lifetime of an environment, so declarations shared by many nodes are walked
once.
-/

namespace Informal.Data

open Lean

/-- What an axiom a declaration depends on says about how far its proof can be trusted. -/
inductive AxiomClass where
  /-- `propext`, `Classical.choice` and `Quot.sound`: the axioms of Lean's logic. -/
  | standard
  /-- `sorryAx`: a `sorry` somewhere in the declaration or in something it uses. -/
  | sorryAx
  /-- An axiom asserting the result of compiled code, as `native_decide` and `bv_decide` add:
  the proof trusts the compiler and the code it runs, not only the kernel. -/
  | compilerTrusted
  /-- Any other axiom, such as one the project declares itself. -/
  | other
deriving Repr, Inhabited, DecidableEq, ToJson, FromJson

/-- The axioms of Lean's logic, which every classical proof may use. -/
def standardAxioms : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

/-- The axiom a `sorry` elaborates to. -/
def sorryAxiom : Name := ``sorryAx

/-- The class of an axiom, from its name. Lean names the axiom a compiled-code tactic adds
`<declaration>._native.<tactic>.ax_<n>` (`Lean.Meta.nativeEqTrue`). -/
def AxiomClass.ofName (name : Name) : AxiomClass :=
  if name == sorryAxiom then .sorryAx
  else if standardAxioms.contains name then .standard
  else if name.components.contains `_native then .compilerTrusted
  else .other

/-- A short description of the class, for tooltips and legends. -/
def AxiomClass.description : AxiomClass → String
  | .standard => "Standard axiom of Lean's logic"
  | .sorryAx => "A sorry: the proof is incomplete"
  | .compilerTrusted => "Trusts compiled code (native_decide or a similar tactic)"
  | .other => "Axiom outside Lean's standard three"

/-- The class as a token for markup (`data-bp-axiom-class`, CSS modifiers). -/
def AxiomClass.token : AxiomClass → String
  | .standard => "standard"
  | .sorryAx => "sorry"
  | .compilerTrusted => "compiler-trusted"
  | .other => "other"

/-- Display order: what most limits trust first, the standard axioms last. -/
def AxiomClass.rank : AxiomClass → Nat
  | .sorryAx => 0
  | .other => 1
  | .compilerTrusted => 2
  | .standard => 3

/-- Distinct axioms in display order: by class (`AxiomClass.rank`), then by name. -/
def sortAxioms (axioms : Array Name) : Array Name :=
  let distinct := axioms.foldl (init := #[]) fun acc a => if acc.contains a then acc else acc.push a
  distinct.qsort fun a b =>
    let ra := (AxiomClass.ofName a).rank
    let rb := (AxiomClass.ofName b).rank
    ra < rb || (ra == rb && a.toString < b.toString)

/-- Answers of `declarationAxioms`, one per declaration name, shared by every query in one
environment. A declaration cannot change once it is in the checked environment, and every
constant it uses is there with it, so a stored answer stays exact. Each environment starts
with its own empty map (`mkInitial` runs per environment), so answers never cross
environments. -/
initialize declarationAxiomsCache : EnvExtension (Option (IO.Ref (NameMap (Array Name)))) ←
  registerEnvExtension (some <$> IO.mkRef {}) (asyncMode := .local)

/-- The axioms `name` depends on, sorted by name (`Lean.collectAxioms`), memoised per name in
`declarationAxiomsCache`. A name missing from the checked environment has none and is not
stored, so a later environment that has it is asked again. -/
def declarationAxioms [Monad m] [MonadEnv m] [MonadLiftT BaseIO m] (name : Name) :
    m (Array Name) := do
  let env ← getEnv
  let some cache := declarationAxiomsCache.getState env
    | collectAxioms name
  if let some known := (← (cache.get : BaseIO _)).find? name then
    return known
  let axioms ← collectAxioms name
  if (env.checked.get.find? name).isSome then
    (cache.modify (·.insert name axioms) : BaseIO Unit)
  return axioms

end Informal.Data
