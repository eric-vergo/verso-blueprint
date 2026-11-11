/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Emilio J. Gallego Arias
-/

import Lean.OriginalConstKind
import Std.Data.HashMap.Lemmas
import VersoBlueprint.Data

namespace Informal.Data

open Lean

/-- Whether a declaration has an inspectable body, no body, or a body hidden by import. -/
inductive BodyAccess where
  | available (value : Expr)
  | unavailable
  | absent

/-- A bodyless axiom view is genuinely bodyless only when Lean records its
original kind as axiom. A collector footprint can be synthesized from a hidden
axiom view when extension state is missing, so it never establishes body access.
Missing original-kind evidence remains unverified. -/
def ConstantInfo.blueprintBodyAccess (env : Environment) (info : ConstantInfo) : BodyAccess :=
  match info.value? (allowOpaque := true) with
  | some value => .available value
  | none =>
    match info with
    | .axiomInfo _ => if getOriginalConstKind? env info.name == some .axiom then .absent else .unavailable
    | _ => .absent

/-- Actual dependencies read from a checked declaration, with explicit coverage.
Cached positive footprints are observations; cached absence never grants coverage. -/
structure InspectedDeclaration where
  dependencies : Array Name := #[]
  directSorry : Bool := false
  cachedSorry : Bool := false
  unverified : Option VerificationReason := none
deriving Repr, Inhabited

/-- The graph actually inspected by the production absence checker. -/
abbrev InspectedDeclarations := Std.HashMap Name InspectedDeclaration

/-- An inspection certificate must cover the roots and every outgoing edge.
It fails on holes, hidden/missing information, or an open graph boundary. -/
def certifiedNoSorry (roots : Array Name) (declarations : InspectedDeclarations) : Bool :=
  roots.all declarations.contains && declarations.toList.all fun (name, info) =>
    name != ``sorryAx && !info.directSorry && !info.cachedSorry && info.unverified.isNone &&
      info.dependencies.all declarations.contains

/-- One actual dependency edge in the inspected production graph. -/
def InspectedDeclarations.edge (declarations : InspectedDeclarations) (source target : Name) : Prop :=
  ∃ info, declarations[source]? = some info ∧ target ∈ info.dependencies.toList

/-- Reflexive transitive reachability, expressed as membership in every closed
region. This is a specification over the production graph, not another graph model. -/
def InspectedDeclarations.reachable (declarations : InspectedDeclarations) (root target : Name) : Prop :=
  ∀ region : Name → Prop, region root →
    (∀ source target, region source → declarations.edge source target → region target) → region target

/-- The certificate establishes a closed set of inspected, hole-free declarations. -/
theorem certifiedNoSorry_closed (roots : Array Name) (declarations : InspectedDeclarations)
    (h : certifiedNoSorry roots declarations = true) :
    (∀ root ∈ roots.toList, root ∈ declarations) ∧
    (∀ source target, source ∈ declarations → declarations.edge source target → target ∈ declarations) ∧
    (∀ name ∈ declarations, name ≠ ``sorryAx) := by
  have hroots := (Bool.and_eq_true_iff.mp h).1
  have hnodes := (Bool.and_eq_true_iff.mp h).2
  have checked (name : Name) (info : InspectedDeclaration)
      (hget : declarations[name]? = some info) :=
    List.all_eq_true.mp hnodes (name, info)
      (Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hget)
  constructor
  · intro root hroot
    exact Std.HashMap.contains_iff_mem.mp (List.all_eq_true.mp (by simpa using hroots) root hroot)
  constructor
  · intro source target _ hedge
    obtain ⟨info, hget, hdep⟩ := hedge
    have hdeps := (Bool.and_eq_true_iff.mp (checked source info hget)).2
    exact Std.HashMap.contains_iff_mem.mp (List.all_eq_true.mp (by simpa using hdeps) target hdep)
  · intro name hmem
    obtain ⟨info, hget⟩ := Option.isSome_iff_exists.mp (Std.HashMap.mem_iff_isSome_getElem?.mp hmem)
    have hn := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp
      (Bool.and_eq_true_iff.mp (checked name info hget)).1).1).1).1
    simpa using hn

/-- Core soundness law: certified completion excludes a reachable sorryAx.
The production checker uses this exact certificate; no negative cache premise
appears in the statement. Extraction uses the ordinary checked Lean declaration API. -/
theorem certifiedNoSorry_not_reachable (roots : Array Name) (declarations : InspectedDeclarations)
    (h : certifiedNoSorry roots declarations = true) (root : Name) (hroot : root ∈ roots.toList) :
    ¬declarations.reachable root ``sorryAx := by
  intro hreach
  obtain ⟨hroots, hclosed, hnoSorry⟩ := certifiedNoSorry_closed roots declarations h
  have hmem := hreach (fun name => name ∈ declarations) (hroots root hroot) hclosed
  exact hnoSorry ``sorryAx hmem rfl

/-- Runtime result of the full inspection, before axis attribution. -/
structure SorryInspection where
  roots : Array Name := #[]
  declarations : InspectedDeclarations := {}
deriving Inhabited

def SorryInspection.isComplete (inspection : SorryInspection) : Bool :=
  certifiedNoSorry inspection.roots inspection.declarations

def SorryInspection.hasSorry (inspection : SorryInspection) : Bool :=
  inspection.declarations.toList.any fun (name, info) =>
    name == ``sorryAx || info.directSorry || info.cachedSorry

def SorryInspection.verificationGaps (inspection : SorryInspection) (location : SorryWhere) :
    Array VerificationGap :=
  inspection.declarations.toList.toArray.filterMap fun (name, info) =>
    info.unverified.map fun reason => { location, declaration := name, reason }

/-- Extract every relevant expression from a checked declaration. Recursor
reduction rules and inductive constructors are included, not only owner types. -/
def declarationExpressions (info : ConstantInfo) : Array Expr :=
  let expressions := #[info.type]
  match info.value? (allowOpaque := true) with
  | some value => expressions.push value
  | none => match info with
    | .recInfo rec => expressions ++ rec.rules.toArray.map (·.rhs)
    | _ => expressions

/-- Inspect one constant. A bodyless axiom view is covered only when Lean's
original-kind metadata identifies a genuine axiom; otherwise it can hide a body.
Collector footprints supply positive sorry observations, never body coverage. -/
def inspectDeclaration [Monad m] [MonadEnv m] (name : Name) : m InspectedDeclaration := do
  let env ← getEnv
  let some info := env.checked.get.find? name
    | return { unverified := some .declarationUnavailable }
  let axioms ← match info with
    | .axiomInfo _ => collectAxioms name
    | _ => pure #[]
  let expressions := declarationExpressions info
  let mut dependencies := expressions.foldl (fun deps expression =>
    deps ++ expression.getUsedConstants) #[]
  let directSorry := dependencies.contains ``sorryAx
  if let .inductInfo induct := info then
    dependencies := dependencies ++ induct.ctors.toArray
  if let .recInfo rec := info then
    dependencies := dependencies ++ rec.all.toArray ++ rec.rules.toArray.map (·.ctor)
  let unverified :=
    if expressions.any (fun expression => expression.hasMVar || expression.hasFVar) then
      some .uncheckedExpression
    else match ConstantInfo.blueprintBodyAccess env info with
      | .unavailable => some .bodyUnavailable
      | _ => none
  return {
    dependencies
    directSorry
    cachedSorry := axioms.contains ``sorryAx
    unverified
  }

/-- Cache of actual declaration views within one stable environment inspection.
It stores graph nodes, not premature empty closure results for recursive names. -/
abbrev SorryInspectionM (m : Type → Type) := StateT InspectedDeclarations m

/-- Inspected views of imported declarations, shared by every inspection in one imported
environment. An imported declaration cannot change while its environment exists, so its view, once
computed, stays exact; declarations of the module being elaborated are never stored. Each imported
environment starts with its own empty cache (`mkInitial` runs per environment), so views never
cross environments. Like the per-inspection cache, it stores graph nodes only, never closures. -/
initialize importedInspectionCache : EnvExtension (Option (IO.Ref InspectedDeclarations)) ←
  registerEnvExtension (some <$> IO.mkRef {}) (asyncMode := .local)

/-- Breadth-first inspection of actual checked dependencies. In blocker-search
mode, stop at the first observed hole or verification failure. Partial graphs
never certify absence: `isComplete` still requires closed coverage of every edge.
Full mode collects the entire closure, including cycles, before certification.

Views of imported declarations come from the environment's `importedInspectionCache` when present:
one snapshot is read at the start and the views computed here are added in one update at the
end, so parallel inspections never contend on the shared map. -/
partial def inspectSorryDependencies [Monad m] [MonadEnv m] [MonadLiftT BaseIO m] (roots : Array Name)
    (stopAtBlocker : Bool := false) : SorryInspectionM m SorryInspection := do
  let shared? := importedInspectionCache.getState (← getEnv)
  let shared ← match shared? with
    | some ref => (ref.get : BaseIO InspectedDeclarations)
    | none => pure {}
  let (declarations, fresh) ← visit shared { dList := roots.toList } {} {}
  if let some ref := shared? then
    unless fresh.isEmpty do
      (ref.modify fun known => fresh.fold (fun known name info => known.insert name info) known :
        BaseIO Unit)
  return { roots, declarations }
where
  visit (shared : InspectedDeclarations) (pending : Std.Queue Name)
      (declarations fresh : InspectedDeclarations) :
      SorryInspectionM m (InspectedDeclarations × InspectedDeclarations) := do
    match pending.dequeue? with
    | none => return (declarations, fresh)
    | some (name, pending) =>
      if declarations.contains name then return ← visit shared pending declarations fresh
      let cache ← get
      let (info, fresh) ← match cache[name]? <|> shared[name]? with
        | some info => pure (info, fresh)
        | none =>
          let info ← inspectDeclaration name
          modify (·.insert name info)
          let imported := ((← getEnv).getModuleIdxFor? name).isSome
          pure (info, if imported then fresh.insert name info else fresh)
      let declarations := declarations.insert name info
      if stopAtBlocker && (name == ``sorryAx || info.directSorry ||
          info.cachedSorry || info.unverified.isSome) then
        return (declarations, fresh)
      let pending := info.dependencies.foldl (fun queue dep => queue.enqueue dep) pending
      visit shared pending declarations fresh

end Informal.Data
