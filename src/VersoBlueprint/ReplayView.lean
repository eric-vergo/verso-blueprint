/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

import VersoBlueprint.Replay
import VersoBlueprint.TraversalIndex
import VersoBlueprint.Informal.CodeSummary

/-!
What the kernel replay of a build establishes for the nodes of a site, read from the traversal
state: the standing of each node's Lean code, and the state of the site as a whole.

One rule decides every positive display (`Replay.provedStanding`). A node's check mark and its
success colours (the graph's fill and border, the status chips of its Lean code) need an accepted
replay that covers every Lean declaration of the node, each checked with everything it depends
on, under which the replay found no axiom outside Lean's standard three (`sorryAx` is one). A
declaration whose module is not known, or that the replay did not check, is covered by nothing.
Counts, bars and legends are about every node at once, so they take the success colours only
when the replay accepted the build, no node with Lean code is left uncovered, and no node
without `sorry` rests on such an axiom (`Replay.siteState`).

After a rejected replay nothing is drawn in a success colour, also not the nodes whose
declarations the checker did not complain about: it stops at its first problem, and what else
it would have rejected is not known.
-/

namespace Informal.ReplayView

open Lean
open Verso.Genre.Manual (TraverseState)

/-- The kernel replay made while the site is generated, captured with the project statistics. -/
def replay? (state : TraverseState) : Option Replay.Result := do
  let json ← TraversalIndex.RenderOverviews.field? state `stats "replay"
  (fromJson? (α := Replay.Result) json).toOption

/-- What `replay?` establishes for the Lean code `code`: accepted only when every declaration is
in the Lean environment and its module is known, the replay checked each with everything it
depends on and accepted them, and it found no axiom outside Lean's standard three under them. A
missing declaration was not checked: the code is not covered. -/
def standingOfCode (replay? : Option Replay.Result) (code : BlockCodeData) : Replay.Standing :=
  match Replay.provedStanding replay? code.declarations code.unplaced code.sourceChange?,
      code.externalDecls.find? (!·.present) with
  -- a missing declaration is not among what the replay checked: the code is not covered
  | .accepted, some missing =>
    .notReplayed s!"not part of the replay: {missing.written} is not in the Lean environment"
  | standing, _ => standing

/-- The Lean code of a node's statement, whichever facet its occurrence is. -/
def _root_.Informal.RenderNode.statementCode? (node : RenderNode) : Option BlockCodeData :=
  let code : BlockCodeData :=
    { externalDecls := node.externalRefs, literateDeclarations := node.literateDeclarations }
  if code.isLeanStatement then some code else none

/-- The Lean code a node's mark is about: its statement's, lowered by the declarations attached
to its proof (`CodeSummary.markSource?`); `none` when the mark is "no Lean declaration". -/
def _root_.Informal.RenderNode.markCode? (node : RenderNode) : Option BlockCodeData :=
  CodeSummary.markSource? node.kind node.statementCode? node.proofExternalRefs

/-- The mark of a node (`CodeSummary.statusMark?`), from its statement's Lean code and the
declarations attached to its proof. -/
def _root_.Informal.RenderNode.mark? (node : RenderNode) (kind : Data.NodeKind := node.kind) :
    Option BlockStatusMark :=
  CodeSummary.statusMark? kind node.statementCode? node.proofExternalRefs

/-- `RenderNode.markCode?` of node `label` of `state`. -/
def markCode? (state : TraverseState) (label : Name) : Option BlockCodeData :=
  (TraversalIndex.Nodes.node? state label).bind (·.markCode?)

/-- The declarations attached to the proof of node `label` of `state`. -/
def proofDecls (state : TraverseState) (label : Name) : Array Data.ExternalRef :=
  ((TraversalIndex.Nodes.node? state label).map (·.proofExternalRefs)).getD #[]

/-- The standing of a node's Lean code, the code its heading's mark is about
(`RenderNode.markCode?`); `none` for a node whose mark is "no Lean declaration". -/
def standingOfNode (replay? : Option Replay.Result) (node : RenderNode) :
    Option Replay.Standing :=
  node.markCode?.map (standingOfCode replay?)

/-- The nodes of a site with what the replay establishes for each. -/
structure Index where
  /-- The replay, when the generator ran one. -/
  replay? : Option Replay.Result := none
  /-- The standing of each node that has Lean code. -/
  standings : Std.HashMap Name Replay.Standing := {}
  /-- The nodes each node depends on, statement and proof sides together. -/
  uses : Std.HashMap Name (Array Name) := {}
  /-- The nodes whose Lean code the compiled files (or the site's data) report as having no
  `sorry`: they are counted as complete. -/
  reportedProved : NameHashSet := {}
  /-- The nodes whose mark is the check mark under the replay: the replay accepted their Lean code
  and their mark shows nothing that lowers it. -/
  checked : NameHashSet := {}
deriving Inhabited

/-- The index of the captured nodes of `state` under the replay `replay?`. Nodes that do not
decode are left out: nothing is established for them. -/
def Index.buildWith (state : TraverseState) (replay? : Option Replay.Result) : Index := Id.run do
  let mut index : Index := { replay? }
  for entry in TraversalIndex.Nodes.allEntries state do
    let .ok stored := entry | continue
    let node := stored.data
    let label : Name := node.label
    if let some standing := standingOfNode replay? node then
      index := { index with standings := index.standings.insert label standing }
    if (node.mark? .theorem).any (·.status.isProved) then
      index := { index with reportedProved := index.reportedProved.insert label }
    let mark? := node.mark?
    if (statusGlyph mark? replay?).1.modifier == StatusGlyphKind.proved.modifier then
      index := { index with checked := index.checked.insert label }
    let uses := (node.statementUses ++ node.proofUses).map fun use => (use.label : Name)
    index := { index with uses := index.uses.insert label uses }
  return index

/-- The index of the captured nodes of `state` under the replay captured with it. -/
def Index.build (state : TraverseState) : Index :=
  Index.buildWith state (ReplayView.replay? state)

/-- The standing of the Lean code of node `label`; `none` when it has none or is not a node. -/
def Index.standing? (index : Index) (label : Name) : Option Replay.Standing :=
  index.standings.get? label

/-- Whether an accepted replay covers the Lean code of node `label` and its mark is the check
mark: a node whose mark shows something lower gets no success colour. -/
def Index.accepted (index : Index) (label : Name) : Bool :=
  (index.standing? label).any (·.isAccepted) && index.checked.contains label

/-- Whether an accepted replay covers the Lean code of node `label` and of every node it
depends on, directly or not. A node without Lean code establishes nothing either way. -/
def Index.acceptedWithDependencies (index : Index) (label : Name) : Bool := Id.run do
  if !index.accepted label then return false
  let mut seen : NameSet := NameSet.empty.insert label
  let mut todo : Array Name := index.uses.getD label #[]
  -- every edge is taken at most once
  let fuel := index.uses.fold (fun n _ uses => n + uses.size + 1) 1
  for _ in [0:fuel] do
    let some next := todo.back? | break
    todo := todo.pop
    if seen.contains next then continue
    seen := seen.insert next
    if (index.standing? next).isSome && !index.accepted next then return false
    todo := todo ++ index.uses.getD next #[]
  return todo.all seen.contains

/-- The nodes with Lean code that an accepted replay does not cover, sorted. Empty when the
replay did not accept the build: then no node is covered and the site says so as a whole. -/
def Index.uncovered (index : Index) : Array Name :=
  if (index.replay?.map (·.outcome)) != some .accepted then #[] else
    (index.standings.toArray.filterMap fun (label, standing) =>
      match standing with
      | .notReplayed _ => some label
      | _ => none).qsort (·.toString < ·.toString)

/-- The nodes whose Lean code has no `sorry` but rests on an axiom outside Lean's standard three,
as an accepted replay found by walking the terms, sorted: not exported and not checked, since
both checkers decline an export that uses such an axiom. Only nodes whose marked Lean code
(`RenderNode.markCode?`) the compiled files report as having no `sorry` are among them: not a
node whose Lean code is the axiom itself (declared without a proof), nor one with a `sorry`. A
node without a Lean statement whose proof's declarations rest on such an axiom is among them:
its mark warns of the axiom, and the site does not show the replay as covering everything. -/
def Index.resting (index : Index) : Array Name :=
  (index.standings.toArray.filterMap fun (label, standing) =>
    match standing with
    | .notChecked _ => if index.reportedProved.contains label then some label else none
    | _ => none).qsort (·.toString < ·.toString)

/-- The nodes whose Lean source is not known to be the text that was compiled (its module's
source changed since the build), sorted. -/
def Index.sourceChanged (index : Index) : Array Name :=
  (index.standings.toArray.filterMap fun (label, standing) =>
    match standing with
    | .sourceChanged _ => some label
    | _ => none).qsort (·.toString < ·.toString)

/-- The axioms outside Lean's standard three under the nodes of `Index.resting`, each once. -/
def Index.restingAxioms (index : Index) : Array Name :=
  let resting := index.resting
  Data.sortAxioms <| index.standings.fold (init := #[]) fun acc label standing =>
    match standing with
    | .notChecked axioms => if resting.contains label then acc ++ axioms else acc
    | _ => acc

/-- What the site as a whole may show in the success colour. -/
def Index.siteState (index : Index) : Replay.SiteState :=
  Replay.siteState index.replay? index.uncovered index.resting index.restingAxioms
    index.sourceChanged

/-- What the replay establishes for node `label` of a dependency graph. -/
def Index.nodeReplay (index : Index) (label : Name) : Graph.NodeReplay :=
  if !index.accepted label then .none
  else if index.acceptedWithDependencies label then .acceptedWithDependencies
  else .accepted

/-- `Index.siteState` of the captured nodes of `state`. -/
def siteState (state : TraverseState) : Replay.SiteState :=
  (Index.build state).siteState

end Informal.ReplayView
