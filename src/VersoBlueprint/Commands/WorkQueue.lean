/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

import Lean
import Verso
import VersoManual
import VersoBlueprint.Commands.Common
import VersoBlueprint.Commands.SerializedExtension
import VersoBlueprint.Graph
import VersoBlueprint.Lib.ExtensionDecode
import VersoBlueprint.TeX
import VersoBlueprint.TraversalIndex

/-!
The `{blueprint_work_queue}` page: the nodes that can be worked on next.

The queue is read from the project's finalized dependency graph, the same
planning data as the dependency graph page and `vbp query work-queue`: a node is
listed when its statement is ready to formalize, or, for theorem-like nodes,
when its proof is ready to formalize or has incomplete Lean code. Ready nodes
come first, then nodes with incomplete Lean code, each group in document order.
-/

namespace Informal.Commands

open Lean Elab Command
open Informal Data
open Verso Doc Html Genre Manual
open Verso.Output.Html
open Verso.Multi (AllRemotes)

/-- One entry of the work queue. -/
structure WorkQueueEntry where
  node : Graph.NodeData
  /-- `"statement"` or `"proof"`. -/
  stage : String
  /-- Whether the stage is ready to formalize (as opposed to having incomplete Lean code). -/
  ready : Bool
  /-- Direct dependencies of the stage that are not yet formalized. -/
  needs : Array Graph.NodeData

private def statementDone (node : Graph.NodeData) : Bool :=
  node.statementStatus == .formalized || node.statementStatus == .mathlib

private def proofDone (node : Graph.NodeData) : Bool :=
  node.proofStatus == .formalized || node.proofStatus == .formalizedWithAncestors

/-- Whether a dependency still needs work before it can be relied on. -/
private def dependencyOpen (node : Graph.NodeData) : Bool :=
  match node.kind with
  | some kind => if kind.isTheoremLike then !(statementDone node && proofDone node) else !statementDone node
  | Option.none => !statementDone node

/-- The work queue of a graph model: ready entries first, then incomplete ones, in model order. -/
def workQueue (model : Graph.GraphModel) : Array WorkQueueEntry :=
  let byLabel : Std.HashMap Name Graph.NodeData :=
    model.nodes.foldl (init := {}) fun m node => m.insert node.label node
  let entries := model.nodes.filterMap fun node => do
    let stage ← node.actionableStage?
    let ready :=
      if stage == "proof" then node.proofStatus == .ready else node.statementStatus == .ready
    let uses := if stage == "proof" then node.statementUses ++ node.proofUses else node.statementUses
    let needs := uses.foldl (init := #[]) fun acc use =>
      match byLabel.get? use.label with
      | some dep =>
        if dependencyOpen dep && !acc.any (·.label == dep.label) then acc.push dep else acc
      | Option.none => acc
    pure { node, stage, ready, needs }
  entries.filter (·.ready) ++ entries.filter (!·.ready)

def workQueueCss : String := include_str "work-queue.css"

def workQueueAssetBundle : BlueprintAssetBundle :=
  blueprintCssAssetBundle [workQueueCss]

private def nodeLink (state : TraverseState) (node : Graph.NodeData) (text : String) : Output.Html :=
  match Informal.TraversalIndex.Nodes.href? state node.label <|> node.href with
  | some href => {{<a href={{href}}>{{.text true text}}</a>}}
  | Option.none => .text true text

private def nodeHeading (node : Graph.NodeData) : String :=
  if node.title.isEmpty || node.title == node.displayLabel then node.displayLabel
  else s!"{node.displayLabel}: {node.title}"

private def stageText (entry : WorkQueueEntry) : String :=
  match entry.stage, entry.ready with
  | "proof", true => "proof ready to formalize"
  | "proof", false => "proof: Lean code incomplete"
  | _, true => "statement ready to formalize"
  | _, false => "statement: Lean code incomplete"

private def renderEntry (state : TraverseState) (entry : WorkQueueEntry) : Output.Html :=
  let needs : Output.Html :=
    if entry.needs.isEmpty then .empty
    else
      let links := entry.needs.map fun dep => nodeLink state dep dep.displayLabel
      let separated := links.foldl (init := #[]) fun acc link =>
        if acc.isEmpty then #[link] else acc ++ #[.text true ", ", link]
      {{<div class="bp_work_queue_needs"><span class="bp_work_queue_needs_key">"needs: "</span>{{separated}}</div>}}
  let stateClass := if entry.ready then "bp_work_queue_ready" else "bp_work_queue_incomplete"
  {{
    <li class={{s!"bp_work_queue_item {stateClass}"}} data-bp-node={{entry.node.label.toString}}
        data-bp-stage={{entry.stage}}>
      <div class="bp_work_queue_head">
        {{nodeLink state entry.node (nodeHeading entry.node)}}
        <span class="bp_work_queue_stage">{{.text true (stageText entry)}}</span>
      </div>
      {{needs}}
    </li>
  }}

/-- The work queue page body: optionally a custom graph model, else the project graph. -/
structure WorkQueueBlockData where
  graphModel : Option Graph.GraphModel := none
deriving Inhabited, FromJson, ToJson

private def workQueueToHtml : BlockToHtml Manual (ReaderT AllRemotes (ReaderT ExtensionImpls (BuildLogT IO))) :=
  fun _goI _goB _id json _blocks => do
    let some data ← Informal.ExtensionDecode.decode? (α := WorkQueueBlockData) json
        (fun err => s!"Malformed data in Block.workQueue.toHtml ({err})")
      | pure .empty
    let s ← HtmlT.state
    let model? : Option Graph.GraphModel ← match data.graphModel with
      | some model => pure (some model)
      | Option.none =>
        match Informal.TraversalIndex.RenderOverviews.required (α := Graph.GraphModel) s `graph with
        | .ok model => pure (some model)
        | .error message => Verso.reportError message; pure Option.none
    let some model := model? | pure .empty
    let entries := workQueue model
    let ready := entries.filter (·.ready)
    let incomplete := entries.filter (!·.ready)
    let renderSection (title : String) (items : Array WorkQueueEntry) : Output.Html :=
      if items.isEmpty then .empty
      else {{
        <section class="bp_work_queue_section">
          <h2 class="bp_work_queue_title">{{.text true s!"{title} ({items.size})"}}</h2>
          <ol class="bp_work_queue_list">{{items.map (renderEntry s)}}</ol>
        </section>
      }}
    if entries.isEmpty then
      pure {{<div class="bp_work_queue"><p class="bp_work_queue_empty">"Nothing is ready to formalize."</p></div>}}
    else
      pure {{
        <div class="bp_work_queue">
          {{renderSection "Ready to formalize" ready}}
          {{renderSection "Lean code incomplete" incomplete}}
        </div>
      }}

block_extension Block.workQueue (data : WorkQueueBlockData) where
  data := toJson data
  traverse _id _data _contents := pure none
  toTeX :=
    some <| fun _goI _goB _id _data _blocks =>
      pure <| .text "The work queue is available in the HTML output."
  toHtml := some workQueueToHtml
  extraCss := workQueueAssetBundle.css
  extraJs := workQueueAssetBundle.js

open Verso Doc Elab Syntax in
def mkWorkQueuePart (stx : Syntax) (endPos : String.Pos.Raw) : PartElabM FinishedPart := do
  let titlePreview := "Ready to Prove"
  let titleInlines ← `(inline | "Ready to Prove")
  let expandedTitle ← #[titleInlines].mapM (elabInline ·)
  let metadata : Option (TSyntax `term) := some (← `(term| { number := false }))
  let block ← serializedBlockTerm `Informal.Commands.Block.workQueue ({} : WorkQueueBlockData)
  pure <| FinishedPart.mk stx stx expandedTitle titlePreview metadata #[block] #[] endPos

open Verso Doc Elab Syntax PartElabM in
@[part_command Lean.Doc.Syntax.command]
public meta def blueprintWorkQueueCmd : PartCommand
  | stx@`(block|command{blueprint_work_queue}) => do
    let endPos := stx.getTailPos?.get!
    closePartsUntil 1 endPos
    addPart (← mkWorkQueuePart stx endPos)
  | _ => (Lean.Elab.throwUnsupportedSyntax : PartElabM Unit)

end Informal.Commands
