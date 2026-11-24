/- 
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Emilio J. Gallego Arias
-/

import VersoBlueprintTests.BlueprintGraph.Shared

namespace Verso.VersoBlueprintTests.BlueprintGraph.Legend

open Informal.Graph

def legendGroupByKey (groups : Array LegendGroup) (key : String) : Option LegendGroup :=
  groups.find? (·.key == key)

def legendItemByLabel (group : LegendGroup) (label : String) : Option LegendItem :=
  group.items.find? (·.label == label)

-- The legend of a site whose kernel replay accepted the build and covers every node.
def defaultLegend : Array LegendGroup := graphLegendGroups false .accepted
def legendWithMathlib : Array LegendGroup := graphLegendGroups true .accepted
-- The legend when nothing is said about a replay: no replay stands behind the site.
def unreplayedLegend : Array LegendGroup := graphLegendGroups false
def groupLegend : Array LegendGroup := groupGraphLegendGroups

/-- info: true -/
#guard_msgs in
#eval
  let hasMathlibLabel : Bool :=
    defaultLegend.any fun group => (group.items.any (·.label == "In Mathlib"))
  let hasIncompleteProofLabel : Bool :=
    defaultLegend.any fun group => (group.items.any (·.label == proofStatusIncompleteText))
  let hasUpdatedProofLabel : Bool :=
    defaultLegend.any fun group => (group.items.any fun item =>
      item.label == proofStatusFormalizedAncestorsLabel &&
        item.label == "Lean code without sorry, dependencies too")
  let warningHasNoIncompleteCodeItem : Bool :=
    !(defaultLegend.any fun group => (group.items.any (·.label == proofStatusIncompleteText) && group.title == "Warning Markers"))
  let hasWarningMarkerTitle : Bool :=
    defaultLegend.any (·.title == "Warning Markers")
  let hasUpdatedDashedText : Bool :=
    defaultLegend.any fun group => (group.items.any (·.label == "Dashed: statement deps from box-shaped sources"))
  !hasMathlibLabel && hasIncompleteProofLabel && hasUpdatedProofLabel &&
    warningHasNoIncompleteCodeItem && hasWarningMarkerTitle && hasUpdatedDashedText

/-- info: true -/
#guard_msgs in
#eval
  legendWithMathlib.any fun group => (group.items.any (·.label == "In Mathlib"))

-- Without an accepted replay every entry about `sorry`-free Lean code says what it rests on, and
-- no entry keeps the bare label; after a rejected replay it says that.
/-- info: true -/
#guard_msgs in
#eval
  let labels (legend : Array LegendGroup) : Array String := legend.flatMap (·.items.map (·.label))
  let reported := "(as the compiled files report, not replayed by a kernel)"
  let rejected := "(a kernel checker rejected this build)"
  let bare := #["In Lean, no sorry", "Lean code without sorry",
    "Lean code without sorry, dependencies too", "In Mathlib"]
  bare.all (fun label => (labels (graphLegendGroups true)).contains s!"{label} {reported}" &&
    !(labels (graphLegendGroups true)).contains label) &&
  bare.all (fun label => (labels (graphLegendGroups true .rejected)).contains s!"{label} {rejected}") &&
  bare.all (labels legendWithMathlib).contains &&
  (labels unreplayedLegend).contains proofStatusIncompleteText

/-- info: true -/
#guard_msgs in
#eval
  match legendGroupByKey defaultLegend "proof" with
  | none => false
  | some proofGroup =>
    match legendItemByLabel proofGroup proofStatusIncompleteText with
    | none => false
    | some item =>
      match item.swatch? with
      | none => false
      | some swatch =>
        swatch.background == Informal.StatusColors.incomplete.cssVarOr &&
        proofStatusIncompleteText == "Lean code incomplete" &&
        graphLegendGroupViewNote.length > 0

/-- info: true -/
#guard_msgs in
#eval
  match legendGroupByKey groupLegend "group-edge" with
  | none => false
  | some edgeGroup =>
    edgeGroup.items.any (·.label == groupEdgeMixedText) &&
    graphLegendGroupViewNote.contains "tab-shaped"

end Verso.VersoBlueprintTests.BlueprintGraph.Legend
