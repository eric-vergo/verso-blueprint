/- 
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Emilio J. Gallego Arias
-/

import VersoBlueprintTests.BlueprintGraph.Shared

namespace Verso.VersoBlueprintTests.BlueprintGraph.NodeStatus

open Lean
open Informal
open Informal.Data
open Informal.Environment
open Informal.Graph
open Verso.VersoBlueprintTests.BlueprintGraph.Shared

def stateStatus : Environment.State := mkState [
  (`def_formal,
    {
      kind := .definition
      statement := some (mkInformal #[])
      literateCodes := #[mkDefCode `def_formal_decl]
    }),
  (`def_ready,
    {
      kind := .definition
      statement := some (mkInformal #[`def_formal])
    }),
  (`def_blocked,
    {
      kind := .definition
      statement := some (mkInformal #[`missing_dep])
    }),
  (`thm_ready,
    {
      kind := .theorem
      statement := some (mkInformal #[`def_formal])
    }),
  (`lean_only,
    {
      kind := .definition
      literateCodes := #[mkDefCode `lean_only_decl]
    }),
  (`local_sorry,
    {
      kind := .theorem
      statement := some (mkInformal #[])
      literateCodes := #[mkTheoremCode `local_sorry_decl false true]
    }),
  (`thm_type_sorry,
    {
      kind := .theorem
      statement := some (mkInformal #[])
      literateCodes := #[mkTheoremCode `thm_type_sorry_decl true false]
    })
]

def graphStatus : Graph Unit :=
  build stateStatus #[`def_formal, `def_ready, `def_blocked, `thm_ready, `lean_only, `local_sorry, `thm_type_sorry]

def graphDataStatus : GraphData :=
  buildModel stateStatus
      #[`def_formal, `def_ready, `def_blocked, `thm_ready, `lean_only, `local_sorry, `thm_type_sorry]
      (resolveHref? := fun
        | `def_formal => some "#def-formal"
        | _ => none)
      (resolveTitle? := fun
        | `def_formal => some "Definition 1"
        | _ => none)
    |>.finish "node-status" {}

/-- info: true -/
#guard_msgs in
#eval
  hasNodeWith graphStatus `def_formal (fun n =>
    n.shape == "box" &&
    n.color == statementBorderFormalizedColor &&
    n.fillcolor == proofBackgroundFormalizedAncColor) &&
  hasNodeWith graphStatus `def_ready (fun n =>
    n.shape == "box" &&
    n.color == statementBorderReadyColor) &&
  hasNodeWith graphStatus `def_blocked (fun n =>
    n.color == statementBorderBlockedColor) &&
  hasNodeWith graphStatus `thm_ready (fun n =>
    n.shape == "ellipse" &&
    n.color == statementBorderReadyColor &&
    n.fillcolor == proofBackgroundReadyColor)

/-- info: true -/
#guard_msgs in
#eval
  hasNodeWith graphStatus `lean_only (fun n =>
    n.color == statementBorderFormalizedColor &&
    n.fillcolor == proofBackgroundFormalizedAncColor &&
    styleHasToken n.style "dashed" &&
    n.gradientangle?.isNone) &&
  hasNodeWith graphStatus `local_sorry (fun n =>
    n.color == statementBorderFormalizedColor &&
    n.fillcolor == proofBackgroundIncompleteColor &&
    !styleHasToken n.style "bold" &&
    n.gradientangle?.isNone) &&
  hasNodeWith graphStatus `thm_type_sorry (fun n =>
    n.color == statementBorderReadyColor &&
    n.fillcolor == proofBackgroundIncompleteColor &&
    !styleHasToken n.style "bold" &&
    n.gradientangle?.isNone)

/-- info: true -/
#guard_msgs in
#eval
  hasNodeWith graphStatus `missing_dep (fun n =>
    n.shape == "box" &&
    n.color == unresolvedBorderColor &&
    n.fillcolor == unresolvedFillColor &&
    n.fontcolor == unresolvedFontColor)

/-- info: true -/
#guard_msgs in
#eval
  hasGraphDataNodeWith graphDataStatus `def_formal (fun n =>
    n.title == "Definition 1" &&
    n.href == some "#def-formal" &&
    n.previewKey == PreviewKey.ofString? "def_formal--statement" &&
    n.kind == some Data.NodeKind.definition &&
    n.statementStatus == .formalized &&
    n.proofStatus == .formalizedWithAncestors &&
    n.visual.fillcolor == proofBackgroundFormalizedAncColor) &&
  hasGraphDataNodeWith graphDataStatus `missing_dep (fun n =>
    n.warnings.unknownRef &&
    n.kind.isNone &&
    n.statementStatus == .blocked) &&
  hasGraphDataEdge graphDataStatus `missing_dep `def_blocked #[.statement]

def stateAncestorsOk : Environment.State := mkState [
  (`def_ok,
    {
      kind := .definition
      statement := some (mkInformal #[])
      literateCodes := #[mkDefCode `def_ok_decl]
    }),
  (`thm_dep_ok,
    {
      kind := .theorem
      statement := some (mkInformal #[`def_ok])
      literateCodes := #[mkTheoremCode `thm_dep_ok_decl]
    }),
  (`thm_top_ok,
    {
      kind := .theorem
      statement := some (mkInformal #[`thm_dep_ok])
      literateCodes := #[mkTheoremCode `thm_top_ok_decl]
    })
]

def graphAncestorsOk : Graph Unit := build stateAncestorsOk #[`thm_top_ok]

/-- info: true -/
#guard_msgs in
#eval
  hasNodeWith graphAncestorsOk `thm_top_ok (fun n =>
    n.fillcolor == proofBackgroundFormalizedAncColor &&
    n.peripheries == 1)

def stateAncestorsBad : Environment.State := mkState [
  (`def_unfinished,
    {
      kind := .definition
      statement := some (mkInformal #[])
    }),
  (`thm_dep_bad,
    {
      kind := .theorem
      statement := some (mkInformal #[`def_unfinished])
      literateCodes := #[mkTheoremCode `thm_dep_bad_decl]
    }),
  (`thm_top_bad,
    {
      kind := .theorem
      statement := some (mkInformal #[`thm_dep_bad])
      literateCodes := #[mkTheoremCode `thm_top_bad_decl]
    })
]

def graphAncestorsBad : Graph Unit := build stateAncestorsBad #[`thm_top_bad]

/-- info: true -/
#guard_msgs in
#eval
  hasNodeWith graphAncestorsBad `thm_dep_bad (fun n =>
    n.fillcolor == proofBackgroundFormalizedColor &&
    n.peripheries == 1) &&
  hasNodeWith graphAncestorsBad `thm_top_bad (fun n =>
    n.fillcolor == proofBackgroundFormalizedColor &&
    n.peripheries == 1)

def stateExternalCode : Environment.State := mkState [
  (`def_ext_ok,
    {
      kind := .definition
      statement := some (mkInformal #[])
      externalRefs := #[
        { (Data.ExternalRef.ofName `Ext.good) with
          present := true
          provedStatus := .proved
        }
      ]
    }),
  (`def_ext_bad,
    {
      kind := .definition
      statement := some (mkInformal #[])
      externalRefs := #[
        { (Data.ExternalRef.ofName `Ext.bad) with
          present := true
          provedStatus := .incomplete { knownSorry := #[{ location := .statement }, { location := .proof }] }
        }
      ]
    }),
  (`def_ext_missing,
    {
      kind := .definition
      statement := some (mkInformal #[])
      externalRefs := #[
        { (Data.ExternalRef.ofName `Ext.missing) with
          present := false
          provedStatus := .proved
        }
      ]
    })
]

def externalStatus : ExternalCodeStatus := {
  isMissing := fun n => n == `Ext.missing
  provedStatus := fun n =>
    if n == `Ext.bad then
      .incomplete { knownSorry := #[{ location := .statement }, { location := .proof }] }
    else
      .proved
}

def externalStatusOverride : ExternalCodeStatus := {
  isMissing := fun n => n == `Ext.missing || n == `Ext.override_missing
  provedStatus := fun n =>
    if n == `Ext.bad || n == `Ext.override_bad then
      .incomplete { knownSorry := #[{ location := .statement }, { location := .proof }] }
    else
      .proved
}

def graphExternalCode : Graph Unit :=
  buildWithExternal stateExternalCode #[`def_ext_ok, `def_ext_bad, `def_ext_missing] externalStatus

/-- info: true -/
#guard_msgs in
#eval
  hasNodeWith graphExternalCode `def_ext_ok (fun n =>
    n.color == statementBorderFormalizedColor) &&
  hasNodeWith graphExternalCode `def_ext_bad (fun n =>
    n.color == statementBorderReadyColor &&
    n.fillcolor == proofBackgroundIncompleteColor &&
    !styleHasToken n.style "bold" &&
    n.gradientangle?.isNone) &&
  hasNodeWith graphExternalCode `def_ext_missing (fun n =>
    n.color == statementBorderReadyColor &&
    n.fillcolor == proofBackgroundReadyColor &&
    styleHasToken n.style "dotted" &&
    n.gradientangle?.isNone)

def stateExternalOverride : Environment.State := mkState [
  (`def_ext_override_bad,
    {
      kind := .definition
      statement := some (mkInformal #[])
      externalRefs := #[
        { (Data.ExternalRef.ofName `Ext.override_bad) with
          present := true
          provedStatus := .proved
        }
      ]
    }),
  (`def_ext_override_missing,
    {
      kind := .definition
      statement := some (mkInformal #[])
      externalRefs := #[
        { (Data.ExternalRef.ofName `Ext.override_missing) with
          present := true
          provedStatus := .proved
        }
      ]
    })
]

def graphExternalOverride : Graph Unit :=
  buildWithExternal stateExternalOverride #[`def_ext_override_bad, `def_ext_override_missing] externalStatusOverride

/-- info: true -/
#guard_msgs in
#eval
  hasNodeWith graphExternalOverride `def_ext_override_bad (fun n =>
    n.color == statementBorderReadyColor &&
    n.fillcolor == proofBackgroundIncompleteColor &&
    !styleHasToken n.style "bold" &&
    n.gradientangle?.isNone) &&
  hasNodeWith graphExternalOverride `def_ext_override_missing (fun n =>
    n.color == statementBorderReadyColor &&
    n.fillcolor == proofBackgroundReadyColor &&
    styleHasToken n.style "dotted" &&
    n.gradientangle?.isNone)

def stateLeanOnlyExternalMissing : Environment.State := mkState [
  (`lean_only_ext_missing,
    {
      kind := .definition
      externalRefs := #[
        { (Data.ExternalRef.ofName `Ext.missing) with
          present := false
          provedStatus := .proved
        }
      ]
    })
]

def warningLeanOnlyExternalMissing : WarningFlags :=
  match stateLeanOnlyExternalMissing.data.get? `lean_only_ext_missing with
  | some node => nodeWarnings externalStatus stateLeanOnlyExternalMissing `lean_only_ext_missing node
  | none => {}

/-- info: true -/
#guard_msgs in
#eval
  warningLeanOnlyExternalMissing.leanOnlyNoStatement &&
  warningLeanOnlyExternalMissing.missingExternalDecl

/-! ## Dependency closures on a graph with exponentially many paths

`layers` layers of two theorems each, every theorem of a layer using both of the layer below:
`2 ^ layers` paths from the top to the bottom. Whether a node is complete with its dependencies is
found for every node by one walk over the reversed dependencies (`Closures.of`), so building the
graph's model takes time linear in its nodes and edges, not in its paths. -/

/-- The label of theorem `i` (0 or 1) of layer `l`. -/
def layered (l i : Nat) : Name := .mkSimple s!"layer{l}_{i}"

/-- The layered graph; `bottomDone` says whether the bottom layer's Lean code is complete. -/
def layeredState (layers : Nat) (bottomDone : Bool := true) : Environment.State :=
  mkState <| (List.range layers).flatMap fun l => [0, 1].map fun i =>
    (layered l i, {
      kind := .theorem
      statement := some (mkInformal (if l == 0 then #[] else #[layered (l - 1) 0, layered (l - 1) 1]))
      literateCodes := #[mkTheoremCode (layered l i).appendAfter "_decl"
        (proofSorry := l == 0 && !bottomDone)] })

/-- info: true -/
#guard_msgs in
#eval show IO Bool from do
  let layers := 48
  let started ← IO.monoMsNow
  let done := buildModel (layeredState layers) #[layered (layers - 1) 0]
  let open_ := buildModel (layeredState layers (bottomDone := false)) #[layered (layers - 1) 0]
  let top (m : GraphModel) := m.nodes.find? (·.label == layered (layers - 1) 0)
  let ok := (top done).any (·.proofStatus == .formalizedWithAncestors) &&
    (top open_).any (·.proofStatus == .formalized)
  -- `2 ^ 48` paths would never be walked; one walk of 96 nodes and 188 edges takes milliseconds,
  -- and the bound leaves room for a loaded machine
  return ok && (← IO.monoMsNow) - started < 20000

-- A cycle of nodes that are complete on their own is complete with its dependencies; one that
-- reaches a node with a `sorry` is not.
/-- info: true -/
#guard_msgs in
#eval
  let cycle (bad : Bool) := mkState [
    (`a, { kind := .theorem, statement := some (mkInformal #[`b])
           literateCodes := #[mkTheoremCode `a_decl] }),
    (`b, { kind := .theorem, statement := some (mkInformal #[`a, `c])
           literateCodes := #[mkTheoremCode `b_decl] }),
    (`c, { kind := .theorem, statement := some (mkInformal #[])
           literateCodes := #[mkTheoremCode `c_decl (proofSorry := bad)] })]
  let status (bad : Bool) (label : Name) :=
    ((buildModel (cycle bad) #[`a]).nodes.find? (·.label == label)).map (·.proofStatus)
  status false `a == some .formalizedWithAncestors && status true `a == some .formalized &&
    status true `c == some .incomplete

end Verso.VersoBlueprintTests.BlueprintGraph.NodeStatus
