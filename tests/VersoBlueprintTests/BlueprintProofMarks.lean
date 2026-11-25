/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

import VersoBlueprint
import VersoBlueprintTests.Blueprint.Support

/-!
A node's mark counts the Lean declarations attached to its proof as well as its statement's, and
those can only lower it (`CodeSummary.markSource?`).

The cases: a statement whose Lean code is complete with a proof declaration that has a `sorry`,
rests on an axiom outside Lean's standard three, or is missing; a statement without Lean code with
a complete proof declaration and with one that has a `sorry`; the same declaration on both facets
with different snapshots. For each, with no kernel replay and with one that accepted the build,
the table shows the mark of the heading (and the node view and the graph, which derive theirs the
same way), the Lean chip and its class, the standing of the kernel replay, whether the replay
covers the node (the success colours) and whether the site's check of what rests on an axiom
lists it; the first columns show the mark the statement's code alone would get.
-/

namespace Verso.VersoBlueprintTests.BlueprintProofMarks

open Lean
open Verso Genre Manual
open Informal
open Verso.VersoBlueprintTests.Blueprint.Support

private def directSorry : Data.ProvedStatus :=
  .incomplete { knownSorry := #[{ location := .proof, origin := .direct }] }

/-- A theorem of module `P`. -/
private def ref (name : Name) (status : Data.ProvedStatus := .proved) (axioms : Array Name := #[])
    (present : Bool := true) : Data.ExternalRef :=
  { written := name, canonical := name, present, provedStatus := status, axioms
    provenance := .inWorkspace `P "P.lean", kind := .theorem }

/-- The checkers' runs of an accepted replay. -/
private def run (name : String) : Replay.CheckerRun :=
  { name, version := some "4.36.0", answer := .accepted, declarations := some 10 }

/-- A replay that accepted the build: it checked the complete declarations and found `sorryAx`
under `P.sorry` and `Demo.ax` under `P.rests`. -/
private def accepted : Replay.Result :=
  { outcome := .accepted, version := some "4.36.0"
    declarations := Stats.replayOrder #[`P.stmt, `P.done, `P.shared]
    axioms := #[(`P.sorry, #[``sorryAx]), (`P.rests, #[`Demo.ax])]
    constants := 12, records := 10
    checkers := #[run "con-leche", run "con-ron"] }

/-- The cases: a name, the statement's declarations and the proof's. -/
private def cases : List (String × Array Data.ExternalRef × Array Data.ExternalRef) := [
  ("statement complete, no proof declaration", #[ref `P.stmt], #[]),
  ("statement extra axiom, no proof declaration", #[ref `P.rests .proved #[`Demo.ax]], #[]),
  ("statement complete, proof sorry", #[ref `P.stmt], #[ref `P.sorry directSorry #[``sorryAx]]),
  ("statement complete, proof extra axiom", #[ref `P.stmt], #[ref `P.rests .proved #[`Demo.ax]]),
  ("statement complete, proof missing", #[ref `P.stmt], #[ref `P.gone .missing (present := false)]),
  ("statement none, proof complete", #[], #[ref `P.done]),
  ("statement none, proof sorry", #[], #[ref `P.sorry directSorry #[``sorryAx]]),
  ("same declaration, proof snapshot sorry", #[ref `P.shared], #[ref `P.shared directSorry])]

private def node (name : String) (statement proof : Array Data.ExternalRef) : RenderNode :=
  { label := Name.mkSimple name, kind := .theorem, externalRefs := statement
    proofExternalRefs := proof }

private def code? (refs : Array Data.ExternalRef) : Option BlockCodeData :=
  if refs.isEmpty then none else some { externalDecls := refs }

/-- The text between `before` and the next `"` in `html`. -/
private def after (html before : String) : String :=
  toString (((html.splitOn before).getD 1 "").takeWhile (· != '"'))

/-- The text between `before` and the next `<` in `html`. -/
private def textAfter (html before : String) : String :=
  toString (((html.splitOn before).getD 1 "").takeWhile (· != '<'))

/-- One row per case and replay: the case, the replay, the glyph of the statement's code alone,
then the glyph of the heading, the chip's symbol and class, the replay standing, whether the
replay covers the node, whether the site counts it as resting on an axiom. -/
private def rows : List String := Id.run do
  let nodes := cases.toArray.map fun (name, s, p) => node name s p
  let mut rows := []
  for (replayName, replay?) in [("no replay", none), ("accepted", some accepted)] do
    let state := TraversalIndex.Nodes.install (TraverseState.initialize default) nodes
    let index := ReplayView.Index.buildWith state replay?
    for (name, statement, proof) in cases do
      let alone := (statusGlyph (CodeSummary.statusMark? .theorem (code? statement)) replay?).1
      let heading := (statusGlyph (CodeSummary.statusMark? .theorem (code? statement) proof)
        replay?).1
      let data : BlockData := { label := Name.mkSimple name, kind := .theorem, count := 1 }
      let chip := (CodeSummary.renderParts data { source := code? statement } (fun _ => none)
        replay? (proofDecls := proof)).codeEntry.render
      let standing := ((node name statement proof).markCode?.map
        (ReplayView.standingOfCode replay?) |>.map (·.token)).getD "-"
      let label := Name.mkSimple name
      rows := rows ++ [" | ".intercalate [replayName, name, alone.glyph, heading.glyph,
        textAfter chip "<span class=\"bp_code_status_symbol\">",
        after chip "bp_code_link_status_", standing,
        if index.accepted label then "covered" else "-",
        if index.resting.contains label then "resting" else "-"]]
  return rows

/--
info: no replay | statement complete, no proof declaration | ◇ | ◇ | ◇ | reported | none | - | -
no replay | statement extra axiom, no proof declaration | ⚠ | ⚠ | ⚠ | warning | none | - | -
no replay | statement complete, proof sorry | ◇ | ◐ | ⚠ | warning | none | - | -
no replay | statement complete, proof extra axiom | ◇ | ⚠ | ⚠ | warning | none | - | -
no replay | statement complete, proof missing | ◇ | ✗ | ! | missing | none | - | -
no replay | statement none, proof complete | ○ | ○ | X | absent bp_code_link_empty | - | - | -
no replay | statement none, proof sorry | ○ | ◐ | ⚠ | warning | none | - | -
no replay | same declaration, proof snapshot sorry | ◇ | ◐ | ⚠ | warning | none | - | -
accepted | statement complete, no proof declaration | ✓ | ✓ | ✓ | proved | accepted | covered | -
accepted | statement extra axiom, no proof declaration | ⚠ | ⚠ | ⚠ | warning | none | - | resting
accepted | statement complete, proof sorry | ✓ | ◐ | ⚠ | warning | none | - | -
accepted | statement complete, proof extra axiom | ✓ | ⚠ | ⚠ | warning | none | - | resting
accepted | statement complete, proof missing | ✓ | ✗ | ! | missing | accepted | - | -
accepted | statement none, proof complete | ○ | ○ | X | absent bp_code_link_empty | - | - | -
accepted | statement none, proof sorry | ○ | ◐ | ⚠ | warning | none | - | -
accepted | same declaration, proof snapshot sorry | ✓ | ◐ | ⚠ | warning | accepted | - | -
-/
#guard_msgs in
#eval IO.println ("\n".intercalate rows)

/-! ## Never raised -/

/-- The glyphs from the strongest to the weakest claim. -/
private def strength (kind : StatusGlyphKind) : Nat :=
  if kind.modifier == StatusGlyphKind.proved.modifier then 2
  else if kind.modifier == StatusGlyphKind.reported.modifier then 1
  else 0

-- In every case and replay state the heading claims no more than the statement's code alone,
-- and a node whose statement has no Lean code never claims anything.
/-- info: true -/
#guard_msgs in
#eval
  [none, some accepted].all fun replay? => cases.all fun (_, statement, proof) =>
    let alone := (statusGlyph (CodeSummary.statusMark? .theorem (code? statement)) replay?).1
    let heading := (statusGlyph (CodeSummary.statusMark? .theorem (code? statement) proof)
      replay?).1
    strength heading ≤ strength alone && (!statement.isEmpty || strength heading == 0)

-- The chip's summary names what the mark also counts: the proof's declarations, with their
-- statuses, under their own heading.
/-- info: true -/
#guard_msgs in
#eval
  let data : BlockData := { label := `n, kind := .theorem, count := 1 }
  let html := (CodeSummary.renderParts data { source := code? #[ref `P.stmt] } (fun _ => none)
    (proofDecls := #[ref `P.sorry directSorry #[``sorryAx]])).codeEntry.render
  let alone := (CodeSummary.renderParts data { source := code? #[ref `P.stmt] }
    (fun _ => none)).codeEntry.render
  hasSubstr html Meaning.proofDeclsTitle && appearsBefore html Meaning.proofDeclsTitle "P.sorry" &&
    appearsBefore html "P.sorry" "bp_code_decl_status" && !hasSubstr alone Meaning.proofDeclsTitle

/-! ## On the pages -/

theorem pmStmtA : True := trivial
theorem pmStmtB : True := trivial
theorem pmStmtC : True := trivial
theorem pmStmtF : True := trivial
theorem pmDone : True := trivial
theorem pmOpen : True := by sorry
axiom pmAx : True
theorem pmRests : True := pmAx

#docs (Manual) proofMarksDoc "Proof marks" :=
:::::::
:::theorem "pm.sorry" (lean := "pmStmtA")
Statement.
:::
:::proof "pm.sorry" (lean := "pmOpen")
Proof.
:::
:::theorem "pm.axiom" (lean := "pmStmtB")
Statement.
:::
:::proof "pm.axiom" (lean := "pmRests")
Proof.
:::
:::theorem "pm.missing" (lean := "pmStmtC")
Statement.
:::
:::proof "pm.missing" (lean := "No.Such.Declaration")
Proof.
:::
:::theorem "pm.none.done"
Statement.
:::
:::proof "pm.none.done" (lean := "pmDone")
Proof.
:::
:::theorem "pm.none.open"
Statement.
:::
:::proof "pm.none.open" (lean := "pmOpen")
Proof.
:::
:::theorem "pm.base" (lean := "pmStmtF")
Statement.
:::

{blueprint_node "pm.sorry"}

{blueprint_graph}
:::::::

/-- What `html` shows for node `label` after `marker` (an attribute naming the node): the text
from `start` to the next `"`. -/
private def shownAfter (html marker start : String) : String :=
  let rest := marker.intercalate ((html.splitOn marker).drop 1)
  after rest start

/-- The glyph modifier, chip class, scope and whether the chip's summary lists the proof's
declarations, for each node, on a page rendered in the side-by-side layout or not. -/
private def pageRows (html : String) (sideBySide : Bool) : List String :=
  ["pm.sorry", "pm.axiom", "pm.missing", "pm.none.done", "pm.none.open", "pm.base"].map fun label =>
    let marker := if sideBySide then s!"data-bp-node=\"«{label}»\"" else s!"title=\"«{label}»\""
    let glyph := if sideBySide then shownAfter html marker "bp_status_glyph bp_status_glyph_" else "-"
    let chip := shownAfter html marker "bp_code_link_status_"
    let scope := shownAfter html marker "data-bp-replay-scope=\""
    -- the chip's summary up to the next node
    let next := if sideBySide then "<div class=\"bp_sbs\" " else "class=\"bp_wrapper "
    let block := ((((marker.intercalate ((html.splitOn marker).drop 1)).splitOn next).headD "")
      |>.splitOn "data-bp-blueprint-node").headD ""
    let listed := hasSubstr block Meaning.proofDeclsTitle
    " | ".intercalate [label, glyph, chip, scope, if listed then "lists proof" else "-"]

/--
info: plain | pm.sorry | - | warning | none | lists proof
plain | pm.axiom | - | warning | none | lists proof
plain | pm.missing | - | missing | none | lists proof
plain | pm.none.done | - | absent bp_code_link_empty | none | lists proof
plain | pm.none.open | - | warning | none | lists proof
plain | pm.base | - | reported | none | -
side by side | pm.sorry | partial | warning | none | lists proof
side by side | pm.axiom | problem | warning | none | lists proof
side by side | pm.missing | missing | missing | none | lists proof
side by side | pm.none.done | none | absent bp_code_link_empty | none | lists proof
side by side | pm.none.open | partial | warning | none | lists proof
side by side | pm.base | reported | reported | none | -
-/
#guard_msgs in
#eval show IO Unit from do
  let (plain, _) ← renderManualDocHtmlStringAndState extension_impls% proofMarksDoc
  let (sbs, _) ← DeclarationSource.withEnabled true <|
    renderManualDocHtmlStringAndState extension_impls% proofMarksDoc
  IO.println ("\n".intercalate ((pageRows plain false).map ("plain | " ++ ·) ++
    (pageRows sbs true).map ("side by side | " ++ ·)))

-- The placement's chip, the graph's words and the node view say what the heading says.
/-- info: true -/
#guard_msgs in
#eval show IO Bool from do
  let (html, state) ← DeclarationSource.withEnabled true <|
    renderManualDocHtmlStringAndState extension_impls% proofMarksDoc
  let placement := shownAfter html "data-bp-label=\"pm.sorry\"" "bp_code_link_status_"
  let index := ReplayView.Index.buildWith state none
  let words (label : String) : String :=
    (GraphApi.nodeStateText state index
      { (default : Graph.NodeData) with label := Name.mkSimple label }).getD ""
  let files ← PreviewManifest.buildPreviewDataFiles extension_impls%
    (fun message => throw <| IO.userError message)
    (PreviewManifest.PreparedPreviewState.prepare state)
    ({ mode := .none } : ExternalMarkupRender.Config)
  let view (label : String) : String :=
    (files.nodeViews.entries.find? (·.label == s!"«{label}»")).map (·.html) |>.getD ""
  let viewGlyph (label : String) := after (view label) "bp_status_glyph bp_status_glyph_"
  return placement == "warning" &&
    (words "pm.sorry").startsWith "Lean code incomplete" &&
    (words "pm.axiom").startsWith "Lean proof without sorry" &&
      hasSubstr (words "pm.axiom") "resting on" &&
    (words "pm.none.done").startsWith "No Lean declaration" &&
    (words "pm.none.open").startsWith "Lean code incomplete" &&
    viewGlyph "pm.sorry" == "partial" && viewGlyph "pm.axiom" == "problem" &&
    viewGlyph "pm.missing" == "missing" && viewGlyph "pm.none.done" == "none" &&
    viewGlyph "pm.none.open" == "partial" && viewGlyph "pm.base" == "reported" &&
    hasSubstr (view "pm.sorry") Meaning.proofDeclsTitle && hasSubstr (view "pm.sorry") "pmOpen" &&
    -- the axioms line counts the proof's declarations
    hasSubstr (view "pm.axiom") "pmAx" && hasSubstr (view "pm.none.open") Meaning.proofDeclsTitle

end Verso.VersoBlueprintTests.BlueprintProofMarks
