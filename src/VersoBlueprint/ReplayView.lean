/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

import VersoBlueprint.Replay
import VersoBlueprint.TraversalIndex

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

/-- What `replay?` establishes for the Lean code `code`: accepted only when every declaration's
module is known, the replay checked each with everything it depends on and accepted them, and
it found no axiom outside Lean's standard three under them. -/
def standingOfCode (replay? : Option Replay.Result) (code : BlockCodeData) : Replay.Standing :=
  Replay.provedStanding replay? code.declarations code.unplaced

/-- The standing of a node's Lean code, the code its heading's mark is about; `none` for a node
without Lean code. -/
def standingOfNode (replay? : Option Replay.Result) (node : RenderNode) :
    Option Replay.Standing :=
  node.toBlockData.codeData.map (standingOfCode replay?)

/-- The nodes of a site with what the replay establishes for each. -/
structure Index where
  /-- The replay, when the generator ran one. -/
  replay? : Option Replay.Result := none
  /-- The standing of each node that has Lean code. -/
  standings : Std.HashMap Name Replay.Standing := {}
  /-- The nodes each node depends on, statement and proof sides together. -/
  uses : Std.HashMap Name (Array Name) := {}
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
    let uses := (node.statementUses ++ node.proofUses).map fun use => (use.label : Name)
    index := { index with uses := index.uses.insert label uses }
  return index

/-- The index of the captured nodes of `state` under the replay captured with it. -/
def Index.build (state : TraverseState) : Index :=
  Index.buildWith state (ReplayView.replay? state)

/-- The standing of the Lean code of node `label`; `none` when it has none or is not a node. -/
def Index.standing? (index : Index) (label : Name) : Option Replay.Standing :=
  index.standings.get? label

/-- Whether an accepted replay covers the Lean code of node `label`. -/
def Index.accepted (index : Index) (label : Name) : Bool :=
  (index.standing? label).any (·.isAccepted)

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
    if (index.standing? next).any (!·.isAccepted) then return false
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
both checkers decline an export that uses such an axiom. -/
def Index.resting (index : Index) : Array Name :=
  (index.standings.toArray.filterMap fun (label, standing) =>
    match standing with
    | .notChecked axioms => if axioms.contains Data.sorryAxiom then none else some label
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

/-- What the replay establishes for node `label` of a dependency graph. -/
def Index.nodeReplay (index : Index) (label : Name) : Graph.NodeReplay :=
  if !index.accepted label then .none
  else if index.acceptedWithDependencies label then .acceptedWithDependencies
  else .accepted

/-- `Index.siteState` of the captured nodes of `state`. -/
def siteState (state : TraverseState) : Replay.SiteState :=
  (Index.build state).siteState

end Informal.ReplayView
