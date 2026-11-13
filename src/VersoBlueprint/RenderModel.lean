/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Emilio J. Gallego Arias
-/

import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import VersoBlueprint.Stats.Comparator

open Lean Verso Doc
open Verso.Genre (Manual)
open Verso.Genre.Manual

namespace Informal

/--
Runtime rendering data captured after project imports. Its nodes become the traversal's
canonical registry; blocks contain references and presentation settings only.
-/
structure RenderModel where
  nodes : Array RenderNode := #[]
  graph : Graph.GraphModel := {}
  summary : Commands.Summary := {}
  /-- What the project is, how big, how far along and what its proofs rest on. -/
  stats : Stats.ProjectStats := {}
deriving Inhabited

def RenderModel.fromJsonString! (serialized : String) : RenderModel := Id.run do
  match Json.parse serialized >>=
      fromJson? (α := Array RenderNode × Graph.GraphModel × Commands.Summary × Stats.ProjectStats) with
  | .error error => panic! s!"Invalid Blueprint render model: {error}"
  | .ok (nodes, graph, summary, stats) => return { nodes, graph, summary, stats }

/--
The serialized render model of the Blueprint state in the current environment: what
`blueprint_render_model%` embeds and `RenderModel.fromJsonString!` reads back.
-/
def RenderModel.captureJson : CoreM String := do
  Environment.reportImportedConflicts
  let state := Environment.informalExt.getState (← getEnv)
  let nodes := TraversalIndex.Nodes.capture state
  let graph := Graph.buildModel state (state.data.toArray.map (·.1)) (groupTitles := state.groups.toArray)
  let summary ← Commands.buildSummary
  let stats ← (← Stats.ProjectStats.capture graph).withHeadline
  return (toJson (nodes, graph, summary, stats)).compress

/-- Capture runtime data without carrying a Lean environment into the generator. -/
elab "blueprint_render_model%" : term => do
  let serialized ← RenderModel.captureJson
  Lean.Elab.Term.elabTerm (← `(RenderModel.fromJsonString! $(quote serialized))) none


/-- Initialize the same node registry later completed by document traversal. -/
def RenderModel.install (model : RenderModel) (state : TraverseState) : TraverseState :=
  let state := TraversalIndex.Nodes.install state model.nodes
  let state := TraversalIndex.RenderOverviews.saveData state `graph model.graph
  let state := TraversalIndex.RenderOverviews.saveData state `summary model.summary
  TraversalIndex.RenderOverviews.saveData state `stats model.stats

/--
Read the project's files again for the statistics (`Stats.ProjectStats.refreshWorkspace`): the
model is captured when the generator is compiled, and Lake does not rebuild it when only files
no Lean module imports change, such as the README or a module the Blueprint does not use.
-/
def RenderModel.refreshStats (model : RenderModel) : IO RenderModel := do
  return { model with stats := ← model.stats.refreshWorkspace }

/-- Use Verso's initialization boundary for HTML, TeX, previews, and saved traversal states. -/
def RenderModel.withExtensions (model : RenderModel) (impls : ExtensionImpls) : ExtensionImpls :=
  TraversalIndex.withInitializer impls model.install

/-- A document paired with its complete project rendering context. -/
structure BlueprintDocument where
  text : Part Manual
  model : RenderModel

/-- Capture once at the project boundary; wrappers pass the selected model explicitly. -/
def BlueprintDocument.capture (text : Part Manual)
    (model : RenderModel := by exact blueprint_render_model%) : BlueprintDocument :=
  { text, model }

end Informal
