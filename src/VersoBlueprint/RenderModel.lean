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

/-- Reads a render model serialized by `RenderModel.captureJson`; the error says what did not read
back. -/
def RenderModel.fromJsonString? (serialized : String) : Except String RenderModel := do
  let (nodes, graph, summary, stats) ← Json.parse serialized >>=
    fromJson? (α := Array RenderNode × Graph.GraphModel × Commands.Summary × Stats.ProjectStats)
  return { nodes, graph, summary, stats }

/-- `RenderModel.fromJsonString?` for a model `blueprint_render_model%` has already read back. -/
def RenderModel.fromJsonString! (serialized : String) : RenderModel :=
  match RenderModel.fromJsonString? serialized with
  | .ok model => model
  | .error error => panic! s!"Invalid Blueprint render model: {error}"

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

/-- Capture runtime data without carrying a Lean environment into the generator. The model is
read back here, so a model that would not read back fails the elaboration with the reason instead of
the generator at run time. -/
elab "blueprint_render_model%" : term => do
  let serialized ← RenderModel.captureJson
  if let .error error := RenderModel.fromJsonString? serialized then
    throwError "The Blueprint render model of this environment does not read back: {error}"
  Lean.Elab.Term.elabTerm (← `(RenderModel.fromJsonString! $(quote serialized))) none


/-- Initialize the same node registry later completed by document traversal. -/
def RenderModel.install (model : RenderModel) (state : TraverseState) : TraverseState :=
  let state := TraversalIndex.Nodes.install state model.nodes
  let state := TraversalIndex.RenderOverviews.saveData state `graph model.graph
  let state := TraversalIndex.RenderOverviews.saveData state `summary model.summary
  TraversalIndex.RenderOverviews.saveData state `stats model.stats

/-- The Lean declarations of the model's nodes that a kernel replay is asked to check, each
once: every present declaration a node refers to and every declaration of its code blocks, with
the module the node's data places it in. A declaration whose module is not known is not asked
for; nothing covers it (`BlockCodeData.unplaced`). -/
def RenderModel.replayTargets (model : RenderModel) : Array Stats.ReplayTarget := Id.run do
  let mut seen : NameSet := {}
  let mut out := #[]
  for node in model.nodes do
    let code : BlockCodeData := {
      literateDeclarations := node.literateDeclarations
      externalDecls := node.externalRefs ++ node.proofExternalRefs }
    for (name, module) in code.placedDeclarations do
      unless seen.contains name do
        seen := seen.insert name
        out := out.push { name, module? := some module }
  return out

/-- The model with the modules `changes` not known to be the source their compiled modules were
compiled from (`Stats.SourceChange`): each Lean declaration of such a module that a node refers
to says so (`Data.ExternalRef.withSourceChange`), the graph does not draw or count its node as
complete (`Graph.GraphModel.withSourceChanged`), the counts follow the graph, and the statistics
list the modules. -/
def RenderModel.withSourceChanges (model : RenderModel) (changes : Array Stats.SourceChange) :
    RenderModel := Id.run do
  let changes := changes.qsort (·.module.toString < ·.module.toString)
  if changes.isEmpty then return { model with stats := { model.stats with sourceChanged := #[] } }
  let mark (ref : Data.ExternalRef) : Data.ExternalRef :=
    match ref.provenance.moduleName? >>= fun m => changes.find? (·.module == m) with
    | some change => if ref.present then ref.withSourceChange change.text change.changed else ref
    | none => ref
  let mut changed : NameSet := {}
  let mut nodes := #[]
  for node in model.nodes do
    let node' := { node with externalRefs := node.externalRefs.map mark
                             proofExternalRefs := node.proofExternalRefs.map mark }
    if (node'.externalRefs ++ node'.proofExternalRefs).any (·.sourceChange?.isSome) then
      changed := changed.insert node.label
    nodes := nodes.push node'
  let graph := model.graph.withSourceChanged changed
  let stats := { model.stats with
    sourceChanged := changes
    progress := Stats.progressOf graph
    leanProgress := Stats.leanProgressWith model.stats.leanProgress graph }
  return { model with nodes, graph, stats }

/--
Read the project's files again for the statistics (`Stats.ProjectStats.refreshWorkspace`): the
model is captured when the generator is compiled, and Lake does not rebuild it when only files
no Lean module imports change, such as the README or a module the Blueprint does not use.
With `kernelReplay` the Lean declarations of the nodes and the theorems the headline judges are
also checked again in Lean's kernel, with everything they depend on
(`Stats.ProjectStats.withKernelReplay`); statistics that carry no replay make the pages say
what the compiled files report, and no more.
-/
def RenderModel.refreshStats (model : RenderModel) (kernelReplay : Bool := false) :
    IO RenderModel := do
  let stats ← model.stats.refreshWorkspace
  -- a Blueprint's modules against what their build records said when it was elaborated; a site
  -- from compiled-code data has made that comparison itself (`CodeSite.sourceChangesOf`)
  let model ← if stats.builtSources.isEmpty then pure { model with stats } else
    let root ← Stats.projectRoot stats.layout.projectRoot
    let changes ← Stats.sourceChangesNow stats.builtSources root
    -- no highlighted source of these modules is shown, and none is built: the files are not
    -- what the Blueprint was elaborated against (a module that only imports such a module is)
    DeclarationSource.excludeModules (changes.filter (!·.isImported) |>.map (·.module))
    pure <| { model with stats }.withSourceChanges changes
  let stats ← if kernelReplay then model.stats.withKernelReplay model.replayTargets
    else pure model.stats
  -- a headline is about the compiled modules: checked against the sources as they read now
  let stats ← stats.withHeadlineSourcesNow
  return { model with stats }

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
