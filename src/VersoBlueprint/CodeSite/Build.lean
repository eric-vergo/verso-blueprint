/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

import VersoManual
import VersoBlueprint.CodeSite.Data
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Stats
import VersoBlueprint.Commands.Summary
import VersoBlueprint.ExternalDeclRender
import VersoBlueprint.Informal.Block
import VersoBlueprint.RenderModel
import VersoBlueprint.Stats.Collect
import VersoBlueprint.Stats.Comparator

/-!
A Blueprint site from compiled code: the document and the render model a generator renders,
built from `Informal.CodeSite.Project` data.

The data becomes the same two things a written Blueprint gives its generator:

* a **Blueprint state** (`stateOf`): one node per declaration, labelled by the declaration's
  name, with its Lean declaration attached (its status, axioms, source range and the rendered
  signature, docstring and source), the uses of other declarations as statement and proof
  dependencies, and the module as the node's group. The render model (`modelOf`) is captured
  from this state exactly as `blueprint_render_model%` captures a written Blueprint's: the node
  registry, the dependency graph, the summary and the project statistics;
* a **document** (`documentOf`): a front page, one chapter per module with a node block per
  declaration, the dependency graph and the summary page. Generators add the Project Stats page.

Nodes have no informal statement: the node view and the chapter cards show the Lean side alone.
Nothing here loads the project's environment; the source excerpts are read from the files under
the project root.
-/

namespace Informal.CodeSite

open Lean
open Verso Doc
open Verso.Genre (Manual)
open Verso.Genre.Manual

/-! ## Sources -/

/-- Lines `start` to `stop` (0-based, inclusive) of `text`. -/
def linesBetween (text : String) (start stop : Nat) : String :=
  let lines := (text.splitOn "\n").toArray
  "\n".intercalate (lines.extract start (stop + 1)).toList

/-- The source text of a declaration (its whole range), from its file's text. -/
def excerpt? (text? : Option String) (decl : Declaration) : Option String := do
  let text ← text?
  let range ← decl.range
  let s := (linesBetween text range.start.line range.«end».line).trimAsciiEnd.copy
  if s.isEmpty then none else some s

/-- A Lean declaration range from an LSP range (columns are taken as UTF-16 and as code
points, which agree outside the astral planes). -/
def declarationRange (r : Range) : DeclarationRange where
  pos := ⟨r.start.line + 1, r.start.character⟩
  charUtf16 := r.start.character
  endPos := ⟨r.«end».line + 1, r.«end».character⟩
  endCharUtf16 := r.«end».character

/-! ## The Blueprint state -/

/-- The Lean declaration a node is attached to. -/
def externalRef (m : Module) (decl : Declaration) (text? : Option String) : Data.ExternalRef :=
  let kind := nodeKind decl.kind
  let line := decl.range.map (·.start.line + 1)
  let headerSource : Option ExternalDeclHeaderSource :=
    if m.source.isEmpty then none
    else some { text := m.source ++ (line.map (s!":{·}")).getD "" }
  {
    written := decl.shownName
    canonical := decl.name
    present := true
    provedStatus := provedStatus decl
    axioms := decl.axioms.qsort (·.toString < ·.toString)
    provenance := if m.source.isEmpty then .unknown else .inWorkspace m.module m.source
    range? := decl.range.map declarationRange
    selectionRange? := decl.selection.map declarationRange
    kind
    render := .ok (renderPlainDecl decl.shownName decl.kind decl.signature decl.doc
      (excerpt? text? decl) headerSource)
  }

/-- The node of a declaration. Only uses of declarations in `known` become dependencies; a use
that is a statement use is not repeated as a proof use. -/
def nodeOf (m : Module) (decl : Declaration) (text? : Option String) (known : NameSet) :
    Data.Node :=
  let useRef (u : Use) : Data.UseRef := { label := u.name, origin := .automatic }
  let uses := decl.uses.filter fun u => known.contains u.name && u.name != decl.name
  let statementUses := uses.filter (·.kind == "statement") |>.map useRef
  let proofUses := uses.filter (·.kind != "statement") |>.map useRef
    |>.filter fun u => !statementUses.any (·.label == u.label)
  let kind := nodeKind decl.kind
  let body (deps : Array Data.UseRef) : Data.InformalData :=
    { stx := .missing, useDeclarations := deps }
  {
    kind
    kindIsExplicit := true
    statement := some (body statementUses)
    proof := if kind.isTheoremLike || !proofUses.isEmpty then some (body proofUses) else none
    externalRefs := #[externalRef m decl text?]
    parent := some (moduleGroup m.module)
  }

/-- The Blueprint state of the data. `sources` gives a module's source text when it can be read. -/
def stateOf (project : Project) (sources : Name → Option String) : Environment.State := Id.run do
  let known : NameSet := project.modules.foldl (init := {}) fun acc m =>
    m.declarations.foldl (fun acc d => acc.insert d.name) acc
  let mut state : Environment.State := {}
  let mut count := 1
  for m in project.modules do
    state := { state with groups := state.groups.insert (moduleGroup m.module) m.module.toString }
    for decl in m.declarations do
      if state.data.contains decl.name then continue
      let node := { nodeOf m decl (sources m.module) known with count }
      state := { state with
        data := state.data.insert decl.name { toNode := node, origin := m.module,
                                              modules := #[m.module] }
        leanNameLabels := state.leanNameLabels.insert decl.name #[decl.name] }
      count := count + 1
  return { state with nextCount := count }

/-! ## Statistics -/

/-- The source directory of a module's file: what remains of `source` without the module's own
path (`"."` at the root). -/
def sourceDirOf? (m : Module) : Option String := do
  let rel := Stats.modulePath m.module "lean"
  guard (!m.source.isEmpty && m.source.endsWith rel)
  let dir := (m.source.dropEnd rel.length).copy
  let dir := if dir.endsWith "/" then (dir.dropEnd 1).copy else dir
  return if dir.isEmpty then "." else dir

/-- Where the project's sources and compiled modules are, from the modules' source files: each
source directory, and beside it Lake's library directory when it exists. -/
def layoutOf (root : System.FilePath) (project : Project) : IO Stats.WorkspaceLayout := do
  let sourceDirs := project.modules.filterMap sourceDirOf? |>.foldl (init := #[]) fun acc d =>
    if acc.contains d then acc else acc.push d
  let mut libraryDirs := #[]
  for dir in sourceDirs do
    let lib := if dir == "." then ".lake/build/lib/lean" else s!"{dir}/.lake/build/lib/lean"
    if ← (root / lib).isDir then libraryDirs := libraryDirs.push lib
  return { sourceDirs := sourceDirs.qsort (· < ·), libraryDirs := libraryDirs.qsort (· < ·) }

/-- The statistics key a declaration kind is counted under. -/
def countKey : String → String
  | "theorem" => "theorems"
  | "instance" => "instances"
  | "structure" => "structures"
  | "class" => "classes"
  | "inductive" => "inductives"
  | "axiom" => "axioms"
  | "opaque" => "opaques"
  | _ => "definitions"

/-- The project statistics of the data: the files under `root`, the project's identity, and the
graph's progress, size and trust ledger. The headline is `headline?` when the caller compared the
project's Comparator challenge; a challenge without it is reported as not compared. -/
def statsOf (root : System.FilePath) (project : Project) (state : Environment.State)
    (graph : Graph.GraphModel) (headline? : Option Stats.Headline := none) :
    IO Stats.ProjectStats := do
  let layout ← layoutOf root project
  let modules := project.modules.map fun m =>
    ({ name := m.module, path := m.source, declarations := m.declarations.size } : Stats.ModuleStats)
  let declarations := project.modules.foldl (init := ({} : Stats.DeclarationCounts)) fun acc m =>
    m.declarations.foldl (fun acc d => acc.add (countKey d.kind)) acc
  let sources ← Stats.SourceStats.read root layout modules
  let identity ← Stats.ProjectIdentity.read root
  let challenge ← Stats.ChallengeConfig.find? root layout.sourceDirs
  let headline := headline? <|> challenge.map fun
    | .ok config => {
        challengeModule := config.challengeModule, solutionModule := config.solutionModule
        config := config.configFile, permittedAxioms := config.permittedAxioms
        unavailable := some .solutionNotImported
        unavailableDetail := some config.solutionModule.toString }
    | .error msg => {
        challengeModule := .anonymous, solutionModule := .anonymous
        config := some Stats.comparatorConfigFile, unavailable := some .configInvalid
        unavailableDetail := some msg }
  return {
    identity, layout, modules := modules.qsort (·.name.toString < ·.name.toString)
    declarations, sources
    progress := Stats.progressOf graph
    graph := Stats.graphSizeOf graph
    trust := Stats.trustLedgerOf state graph
    headline
    hasComparatorChallenge := challenge.isSome
  }

/-- The render model of the data's Blueprint state, as `RenderModel.captureJson` captures a
written Blueprint's. -/
def modelOf (root : System.FilePath) (project : Project) (state : Environment.State)
    (headline? : Option Stats.Headline := none) : IO RenderModel := do
  let labels := state.data.toArray.map (·.1)
  let graph := Graph.buildModel state labels (groupTitles := state.groups.toArray)
  -- Graph nodes show the name as written (a private declaration without Lean's prefix).
  let shown : Lean.NameMap Name := project.modules.foldl (init := {}) fun acc m =>
    m.declarations.foldl (fun acc d => acc.insert d.name d.shownName) acc
  let graph := { graph with nodes := graph.nodes.map fun n =>
    { n with displayLabel := ((shown.find? n.label).getD n.label).toString } }
  return {
    nodes := TraversalIndex.Nodes.capture state
    graph
    summary := Commands.summaryOfState state
    stats := ← statsOf root project state graph headline?
  }

/-! ## The document -/

/-- The site's title: the data's, else the README's first heading, else the Lake package's
name, else the project root's folder name. -/
def titleOf (root : System.FilePath) (project : Project) (identity : Stats.ProjectIdentity) :
    String :=
  project.title <|> identity.title <|> identity.name |>.getD (root.fileName.getD "Lean project")

/-- Above this many declarations the dependency graph opens on its module view. -/
def moduleViewThreshold : Nat := 300

private def para (inlines : Array (Inline Manual)) : Block Manual := .para inlines

private def moduleList (modules : Array Name) : Block Manual :=
  .ul (modules.map fun m => ⟨#[para #[.code m.toString]]⟩)

/-- The front page: what the site is, and what it leaves out. -/
def frontMatter (project : Project) : Array (Block Manual) := Id.run do
  let decls := project.modules.foldl (·  + ·.declarations.size) 0
  let mut blocks := #[
    para #[.text s!"This site was generated from the compiled Lean code: {decls} declarations \
      in {project.modules.size} modules, one chapter per module. Each declaration is a node \
      of the ", .link #[.text "dependency graph"] "Dependency-Graph/",
      .text "; there are no informal statements, so every node shows its Lean side."]]
  if let some toolchain := project.toolchain then
    blocks := blocks.push (para #[.text "Toolchain: ", .code toolchain])
  unless project.unbuilt.isEmpty do
    blocks := blocks.push (para #[.text s!"Not built ({project.unbuilt.size}), so not in this \
      site: build them and generate the site again."])
    blocks := blocks.push (moduleList project.unbuilt)
  unless project.skipped.isEmpty do
    blocks := blocks.push (para #[.text "Left out:"])
    blocks := blocks.push <| .ul (project.skipped.map fun s =>
      ⟨#[para #[.code s.module.toString, .text s!": {s.reason}"]]⟩)
  return blocks

/-- A node block for each declaration of a module. -/
def moduleChapter (m : Module) : Part Manual :=
  let intro := if m.source.isEmpty then #[] else #[para #[.text "Source: ", .code m.source]]
  let nodes : Array (Block Manual) := m.declarations.map fun d =>
    .other (Informal.Block.informal { label := d.name, count := 0 }) #[]
  { title := #[.code m.module.toString]
    titleString := m.module.toString
    metadata := none
    content := intro ++ nodes
    subParts := #[] }

/-- An unnumbered page holding one block. -/
def pagePart (title : String) (block : Block Manual) : Part Manual :=
  { title := #[.text title], titleString := title, metadata := some { number := false }
    content := #[block], subParts := #[] }

/-- The document: the front page, a chapter per module that has declarations, the dependency
graph (on its module view above `moduleViewThreshold` declarations, laid out while the site is
built with the Graphviz program `layoutProgram` when one is given) and the summary page. -/
def documentOf (title : String) (project : Project) (layoutProgram : Option String := none) :
    Part Manual :=
  let chapters := project.modules.filter (!·.declarations.isEmpty) |>.map moduleChapter
  let decls := project.modules.foldl (· + ·.declarations.size) 0
  let initialView := if decls > moduleViewThreshold then some Graph.groupVariantKey else none
  let graph := pagePart "Dependency Graph"
    (.other (Informal.Commands.Block.graph { initialView, layoutProgram }) #[])
  let summary := pagePart Commands.summaryPageTitle
    (.other (Informal.Commands.Block.summary {}) #[])
  { title := #[.text title]
    titleString := title
    metadata := none
    content := frontMatter project
    subParts := chapters ++ #[graph, summary] }

end Informal.CodeSite
