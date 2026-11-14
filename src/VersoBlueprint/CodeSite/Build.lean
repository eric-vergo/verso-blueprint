/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

import MD4Lean
import VersoManual
import VersoManual.Markdown
import VersoBlueprint.CodeSite.Data
import VersoBlueprint.CodeSite.Highlight
import VersoBlueprint.CodeSite.Search
import VersoBlueprint.Git
import VersoBlueprint.LeanSourceAnchor
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Stats
import VersoBlueprint.Commands.Summary
import VersoBlueprint.ExternalDeclRender
import VersoBlueprint.Informal.Block
import VersoBlueprint.Math
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

A declaration with an informal statement in the data (`Declaration.statement`: Markdown with TeX
math, from a LaTeX blueprint, a docstring, …) gets it as the node's statement, its informal proof
below it, so the node view and the chapter card show it beside the Lean side as on a written
Blueprint; a declaration without one shows the Lean side alone. Each declaration's card is its module's API entry: the signature and the source excerpt
highlighted (`Informal.CodeSite.Highlight`, with the hovers the data gives), the docstring
rendered as Markdown, where it is defined (a link to the file on GitHub when the project is a
GitHub checkout) and a link to its neighbourhood in the dependency graph. A chapter starts with
the module's docstrings. Nothing here loads the project's environment; the source excerpts and
module docstrings are read from the files under the project root.
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

/-! ## Docstrings -/

/-- Whether a link target is safe to keep in generated pages: a web or mail address, or a
reference within the site (no scheme). -/
def safeHref (href : String) : Bool :=
  let h := href.trimAscii.toString.toLower
  let scheme := (h.splitOn ":").head!
  let hasScheme := (h.splitOn ":").length > 1 && !scheme.any (fun c => c == '/' || c == '?' || c == '#')
  !hasScheme || scheme == "http" || scheme == "https" || scheme == "mailto"

/-- `html` with every `href` and `src` that `safeHref` rejects replaced by `#`. -/
def sanitizeLinks (html : String) : String := Id.run do
  let mut out := html
  for attr in ["href=\"", "src=\""] do
    let parts := out.splitOn attr
    let mut acc := parts.head!
    for part in parts.tail! do
      let value := (part.splitOn "\"").head!
      let rest := (part.drop value.length).toString
      acc := acc ++ attr ++ (if safeHref value then value else "#") ++ rest
    out := acc
  return out

/-- A docstring as HTML: Markdown rendered by md4c, raw HTML in it shown as text, unsafe link
targets dropped; the escaped text in a `pre` when it cannot be rendered. -/
def docHtml (doc : String) : String :=
  match MD4Lean.renderHtml doc with
  | some html => sanitizeLinks html
  | none => (Verso.Output.Html.tag "pre" #[] (.text true doc)).asString

/-- The module docstrings (`/-! … -/`) of a source text, without their delimiters, in order. -/
def moduleDocs (text : String) : Array String :=
  (Highlight.lex text.toList.toArray ⟨0, 0⟩).filterMap fun lx =>
    if lx.kind matches .docComment && lx.text.startsWith "/-!" then
      let body := ((lx.text.drop 3).dropEnd 2).toString
      some (dedent body).trimAscii.toString
    else none
where
  dedent (s : String) : String :=
    let lines := s.splitOn "\n"
    let indents := lines.filterMap fun l =>
      if l.trimAscii.isEmpty then none else some (l.length - l.trimAsciiStart.toString.length)
    let k := indents.foldl min (indents.headD 0)
    "\n".intercalate (lines.map fun l => (l.drop k).toString)

/-- `inline` without links whose target `safeHref` rejects (their text stays). -/
partial def safeInline : Inline Manual → Inline Manual
  | .link inls href => if safeHref href then .link (inls.map safeInline) href
      else .concat (inls.map safeInline)
  | .emph inls => .emph (inls.map safeInline)
  | .bold inls => .bold (inls.map safeInline)
  | .concat inls => .concat (inls.map safeInline)
  | i => i

/-- `block` with `safeInline` applied to its text. -/
partial def safeBlock : Block Manual → Block Manual
  | .para inls => .para (inls.map safeInline)
  | .blockquote bs => .blockquote (bs.map safeBlock)
  | .ul items => .ul (items.map fun i => ⟨i.contents.map safeBlock⟩)
  | .ol n items => .ol n (items.map fun i => ⟨i.contents.map safeBlock⟩)
  | .concat bs => .concat (bs.map safeBlock)
  | b => b

/-- How docstring and statement Markdown is read: CommonMark with TeX math spans (`$…$`,
`$$…$$`), raw HTML as text. -/
def statementFlags : UInt32 :=
  MD4Lean.MD_DIALECT_COMMONMARK ||| MD4Lean.MD_FLAG_LATEXMATHSPANS ||| MD4Lean.MD_FLAG_NOHTML

/-- Verso's docstring math in a sequence of inlines: a text ending in `$$` or `$` directly
followed by a code span is the span's TeX as display or inline math (`` $$`x^2` ``, `` $`x` ``),
as a docstring written in Verso's syntax means it. -/
partial def versoMath (inls : Array (Inline Manual)) : Array (Inline Manual) := Id.run do
  let mut out : Array (Inline Manual) := #[]
  let mut i := 0
  while h : i < inls.size do
    match inls[i], inls[i + 1]? with
    | .text t, some (.code tex) =>
      if t.endsWith "$" then
        let display := t.endsWith "$$"
        let before := (t.dropEnd (if display then 2 else 1)).toString
        unless before.isEmpty do out := out.push (.text before)
        out := out.push (.math (if display then .display else .inline) tex)
        i := i + 2
        continue
      out := out.push (.text t)
    | .emph xs, _ => out := out.push (.emph (versoMath xs))
    | .bold xs, _ => out := out.push (.bold (versoMath xs))
    | .link xs href, _ => out := out.push (.link (versoMath xs) href)
    | .concat xs, _ => out := out.push (.concat (versoMath xs))
    | x, _ => out := out.push x
    i := i + 1
  return out

/-- `block` with `versoMath` applied to its text. -/
partial def versoMathBlock : Block Manual → Block Manual
  | .para inls => .para (versoMath inls)
  | .blockquote bs => .blockquote (bs.map versoMathBlock)
  | .ul items => .ul (items.map fun i => ⟨i.contents.map versoMathBlock⟩)
  | .ol n items => .ol n (items.map fun i => ⟨i.contents.map versoMathBlock⟩)
  | .concat bs => .concat (bs.map versoMathBlock)
  | b => b

/-- A module docstring as document blocks (Verso's Markdown reading, `statementFlags`: headers
become bold or emphasised paragraphs, raw HTML is text, TeX math spans and Verso's docstring math
are math), so it is rendered with the page's math and indexed by its search; the text in a code
block when it has Markdown Verso does not read (tables, …). -/
def moduleDocBlocks (doc : String) : Array (Block Manual) :=
  let fallback : Array (Block Manual) := #[.code doc]
  match MD4Lean.parse doc statementFlags with
  | none => fallback
  | some md =>
    match md.blocks.mapM (Verso.Genre.Manual.Markdown.blockFromMarkdown'
        (handleHeaders := Verso.Genre.Manual.Markdown.strongEmphHeaders')) with
    | .ok blocks => blocks.map fun b => safeBlock (versoMathBlock b)
    | .error _ => fallback

/-! ## Informal statements -/

/-- The TeX prelude as it goes into the pages' script: angle brackets written as `\lt` and `\gt`,
so no text in it can end the script element it is embedded in. -/
def safePrelude (prelude : String) : String :=
  prelude.foldl (init := "") fun acc c =>
    if c == '<' then acc ++ "\\lt{}" else if c == '>' then acc ++ "\\gt{}" else acc.push c

/-- `inline` with each formula as Blueprint math (`Informal.Math.Inline.bpMath`, rendered by the
pages' KaTeX after `prelude`, also in the dependency graph's node view). -/
partial def bpMathInline (prelude : String) : Inline Manual → Inline Manual
  | .math mode source =>
    .other (Informal.Math.Inline.bpMath { mode, source, texPrelude := safePrelude prelude }) #[]
  | .link inls href => .link (inls.map (bpMathInline prelude)) href
  | .emph inls => .emph (inls.map (bpMathInline prelude))
  | .bold inls => .bold (inls.map (bpMathInline prelude))
  | .concat inls => .concat (inls.map (bpMathInline prelude))
  | i => i

/-- `block` with `bpMathInline` applied to its text. -/
partial def bpMathBlock (prelude : String) : Block Manual → Block Manual
  | .para inls => .para (inls.map (bpMathInline prelude))
  | .blockquote bs => .blockquote (bs.map (bpMathBlock prelude))
  | .ul items => .ul (items.map fun i => ⟨i.contents.map (bpMathBlock prelude)⟩)
  | .ol n items => .ol n (items.map fun i => ⟨i.contents.map (bpMathBlock prelude)⟩)
  | .concat bs => .concat (bs.map (bpMathBlock prelude))
  | b => b

/-- A statement's Markdown text as document blocks, so the page renders its math (after the TeX
definitions `prelude`) and its search indexes it; the text in a code block when it has Markdown
that Verso does not read (tables, …). -/
def statementTextBlocks (text : String) (prelude : String := "") : Array (Block Manual) :=
  let fallback : Array (Block Manual) := #[.code text]
  match MD4Lean.parse text statementFlags with
  | none => fallback
  | some md =>
    match md.blocks.mapM (Verso.Genre.Manual.Markdown.blockFromMarkdown'
        (handleHeaders := Verso.Genre.Manual.Markdown.strongEmphHeaders')) with
    | .ok blocks => blocks.map fun b => bpMathBlock prelude (safeBlock b)
    | .error _ => fallback

/-- The blocks of a declaration's informal statement: its title in bold (Markdown, as the
text), then the text. -/
def statementBlocks (s : Statement) (prelude : String := "") : Array (Block Manual) :=
  let title : Array (Block Manual) := match s.title with
    | some t =>
      if t.trimAscii.isEmpty then #[] else
      let inls := (statementTextBlocks t prelude).foldl (init := #[]) fun acc b => match b with
        | .para xs => acc ++ (if acc.isEmpty then #[] else #[.text " "]) ++ xs
        | _ => acc
      #[.para #[.bold (if inls.isEmpty then #[.text t.trimAscii.toString] else inls)]]
    | none => #[]
  title ++ statementTextBlocks s.text prelude

/-- The blocks of a declaration's informal proof, if it has one. -/
def proofBlocks? (s : Statement) (prelude : String := "") : Option (Array (Block Manual)) := do
  let p ← s.proof
  guard !p.trimAscii.isEmpty
  return statementTextBlocks p prelude

/-! ## The Blueprint state -/

/-- What rendering the declarations needs besides their data. -/
structure RenderContext where
  /-- The hover of each constant the sources mention (`Project.hovers`). -/
  hovers : Lean.NameMap Hover := {}
  /-- The web address of the project root's files, ending in `/` (a GitHub checkout's
  `https://github.com/<owner>/<repository>/blob/<commit>/<path>/`), when there is one. -/
  sourceBase? : Option String := none
  /-- The dependency graph's page, relative to the site root as the pages' links are (the
  declarations' neighbourhood links); `none` for no such links. -/
  graphPage? : Option String := some "Dependency-Graph/"
deriving Inhabited

/-- The web address of the project root's files, when the project is a Git checkout with a
GitHub `origin` (as Blueprint source links are made). -/
def sourceBaseOf? (root : System.FilePath) : IO (Option String) := do
  let some top ← Git.toplevelAt? root | return none
  let some info ← Git.repositoryInfoAtRoot? top | return none
  let top ← (try IO.FS.realPath top catch _ => pure top)
  let root ← (try IO.FS.realPath root catch _ => pure root)
  let topText := top.toString ++ "/"
  let rel := if root.toString ++ "/" == topText then ""
    else if root.toString.startsWith topText then (root.toString.drop topText.length).toString ++ "/"
    else ""
  return some s!"{info.githubUrl}/blob/{info.commit}/{rel}"

/-- The Lean declaration a node is attached to. -/
def externalRef (m : Module) (decl : Declaration) (text? : Option String)
    (ctx : RenderContext := {}) : Data.ExternalRef :=
  let kind := nodeKind decl.kind
  let line := decl.range.map (·.start.line + 1)
  let endLine := decl.range.map (·.«end».line + 1)
  let href? : Option String := do
    let base ← ctx.sourceBase?
    guard !m.source.isEmpty
    let fragment := match line, endLine with
      | some l, some e => if e > l then s!"#L{l}-L{e}" else s!"#L{l}"
      | some l, none => s!"#L{l}"
      | _, _ => ""
    pure s!"{base}{m.source}{fragment}"
  let headerSource : Option ExternalDeclHeaderSource :=
    if m.source.isEmpty then none
    else some { text := m.source ++ (line.map (s!":{·}")).getD "", href? }
  let links : Array ExternalDeclHeaderLink := match ctx.graphPage? with
    | some page => #[{ text := "Neighbourhood", className := "bp_external_decl_ego"
                       href := page ++ "#ego=" ++ LeanSourceAnchor.percentEncode decl.name.toString
                       title? := some "What it uses and what uses it, in the dependency graph" }]
    | none => #[]
  let source? := (excerpt? text? decl).map fun src =>
    let start := (decl.range.map (·.start.line)).getD 0
    Highlight.highlight src ⟨start, 0⟩ decl.occurrences ctx.hovers
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
    render := .ok (renderCodeDecl decl.shownName decl.kind (Highlight.highlightPlain decl.signature)
      (decl.doc.map docHtml) source? headerSource links)
  }

/-- The node of a declaration. Only uses of declarations in `known` become dependencies; a use
that is a statement use is not repeated as a proof use. -/
def nodeOf (m : Module) (decl : Declaration) (text? : Option String) (known : NameSet)
    (ctx : RenderContext := {}) (prelude : String := "") : Data.Node :=
  let useRef (u : Use) : Data.UseRef := { label := u.name, origin := .automatic }
  let uses := decl.uses.filter fun u => known.contains u.name && u.name != decl.name
  let statementUses := uses.filter (·.kind == "statement") |>.map useRef
  let proofUses := uses.filter (·.kind != "statement") |>.map useRef
    |>.filter fun u => !statementUses.any (·.label == u.label)
  let kind := nodeKind decl.kind
  let body (deps : Array Data.UseRef) (blocks : Array (Block Manual) := #[]) : Data.InformalData :=
    { stx := .missing, previewBlocks := blocks, useDeclarations := deps }
  let proofText? := decl.statement.bind (proofBlocks? · prelude)
  {
    kind
    kindIsExplicit := true
    statement := some (body statementUses ((decl.statement.map (statementBlocks · prelude)).getD #[]))
    proof := if kind.isTheoremLike || !proofUses.isEmpty || proofText?.isSome then
        some (body proofUses (proofText?.getD #[]))
      else none
    externalRefs := #[externalRef m decl text? ctx]
    parent := some (moduleGroup m.module)
  }

/-- The Blueprint state of the data. `sources` gives a module's source text when it can be read. -/
def stateOf (project : Project) (sources : Name → Option String) (ctx : RenderContext := {}) :
    Environment.State := Id.run do
  let known : NameSet := project.modules.foldl (init := {}) fun acc m =>
    m.declarations.foldl (fun acc d => acc.insert d.name) acc
  let mut state : Environment.State := {}
  let mut count := 1
  for m in project.modules do
    state := { state with groups := state.groups.insert (moduleGroup m.module) m.module.toString }
    for decl in m.declarations do
      if state.data.contains decl.name then continue
      let node := { nodeOf m decl (sources m.module) known ctx project.texPrelude with count }
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

/-- The compiled-module directories of the project at `root`: its own build, its packages'
(`.lake/packages/*`) and those `layout` names. -/
def libraryPathOf (root : System.FilePath) (layout : Stats.WorkspaceLayout) :
    IO System.SearchPath := do
  let mut path : System.SearchPath := layout.libraryDirs.toList.map fun dir : String => root / dir
  let own := root / ".lake" / "build" / "lib" / "lean"
  if ← own.isDir then path := path ++ [own]
  let packages := root / ".lake" / "packages"
  if ← packages.isDir then
    for entry in (← packages.readDir).qsort (·.fileName < ·.fileName) do
      let lib := entry.path / ".lake" / "build" / "lib" / "lean"
      if ← lib.isDir then path := path ++ [lib]
  return path

/-- The headline of the project's Comparator challenge, compared as a Blueprint site compares it
(`Stats.Headline.compute`): the solution module and the challenge's imports are imported from the
project's build for the comparison alone (only when the project has a challenge), and each judged
theorem's node is its declaration's. `none` without a challenge; a headline saying why when the
comparison cannot be made (the challenge not built, the solution's environment not loadable, …).
With `notBuilt?` the caller could not build the challenge (the reason): nothing is imported, and the
headline says the challenge was not built, with that reason.
-/
def headlineOf? (root : System.FilePath) (project : Project) (known : NameSet)
    (notBuilt? : Option String := none) : IO (Option Stats.Headline) := do
  let layout ← layoutOf root project
  let some found ← Stats.ChallengeConfig.find? root layout.sourceDirs | return none
  let .ok config := found | return none  -- `statsOf` reports an invalid configuration
  let base : Stats.Headline := {
    challengeModule := config.challengeModule, solutionModule := config.solutionModule
    config := config.configFile, permittedAxioms := config.permittedAxioms }
  let unavailable (why : Stats.Unavailable) (detail : String) : Stats.Headline :=
    { base with unavailable := some why, unavailableDetail := some detail }
  -- the caller could not build the challenge: nothing is compared, and the page says why
  if let some why := notBuilt? then return some (unavailable .challengeNotBuilt why)
  let libraryPath ← libraryPathOf root layout
  let some olean ← Stats.findCompiledModule? libraryPath config.challengeModule
    | return some (unavailable .challengeNotBuilt config.challengeModule.toString)
  let imports ← match ← (Stats.ChallengeModule.read olean).toBaseIO with
    | .ok challenge => pure challenge.imports
    | .error e => return some (unavailable .challengeUnreadable (toString e))
  let env ← try
      let sysroot ← match ← IO.getEnv "LEAN_SYSROOT" with
        | some dir => pure (System.FilePath.mk dir)
        | none => Lean.findSysroot
      Lean.initSearchPath sysroot libraryPath
      let wanted := (#[config.solutionModule] ++ imports).foldl (init := #[]) fun acc m =>
        if acc.contains m then acc else acc.push m
      importModules (wanted.map ({ module := · })) {} (loadExts := false)
    catch e =>
      return some (unavailable .importsNotAvailable s!"the solution could not be loaded: {e}")
  let ctx : Core.Context := { fileName := "<code-site>", fileMap := default, maxHeartbeats := 0 }
  let computed ← ((Stats.Headline.compute config root layout libraryPath).toIO ctx { env }).toBaseIO
  match computed with
  | .error e => return some (unavailable .importsNotAvailable (toString e))
  | .ok (headline, _) =>
    return some { headline with theorems := headline.theorems.map fun t =>
      { t with node := t.node <|> if known.contains t.name then some t.name else none } }

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
  let stated := project.modules.foldl (init := 0) fun n m =>
    n + (m.declarations.filter (·.statement.isSome)).size
  let statements := if stated == 0 then
      "; there are no informal statements, so every node shows its Lean side."
    else if stated == decls then
      "; every node shows its informal statement beside its Lean side."
    else
      s!"; {stated} of them have an informal statement, shown beside the Lean side, the \
        others show their Lean side alone."
  let mut blocks := #[
    para #[.text s!"This site was generated from the compiled Lean code: {decls} declarations \
      in {project.modules.size} modules, one chapter per module. Each declaration is a node \
      of the ", .link #[.text "dependency graph"] "Dependency-Graph/", .text statements]]
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

/-- The search entries of a declaration (`Block.declSearch`): its name, signature, docstring and
informal statement. -/
def declSearchBlock (d : Declaration) : Block Manual :=
  let text := #[para #[.code d.shownName.toString], para #[.code d.signature]] ++
    (d.doc.map fun doc => #[para #[.text doc]]).getD #[] ++
    (d.statement.map fun s => #[para #[.text s.text]]).getD #[]
  .other (Block.declSearch d.name) text

/-- A declaration's node blocks: the statement block (its informal statement as contents, empty
without one) and, when the statement has an informal proof, the proof block. -/
def nodeBlocks (d : Declaration) (prelude : String := "") : Array (Block Manual) :=
  let statement := (d.statement.map (statementBlocks · prelude)).getD #[]
  let proof := (d.statement.bind (proofBlocks? · prelude)).map fun blocks =>
    #[.other (Informal.Block.informal { label := d.name, count := 0, isProof := true }) blocks]
  #[.other (Informal.Block.informal { label := d.name, count := 0 }) statement] ++ proof.getD #[]

/-- A module's page: where its source is, its module docstrings (`text?`, its source text), and
for each declaration its search entries and its node blocks (formulas after `prelude`). -/
def moduleChapter (m : Module) (text? : Option String := none) (prelude : String := "") :
    Part Manual :=
  let intro := if m.source.isEmpty then #[] else #[para #[.text "Source: ", .code m.source]]
  let docs := (text?.map moduleDocs).getD #[] |>.flatMap moduleDocBlocks
  let nodes : Array (Block Manual) := m.declarations.flatMap fun d =>
    #[declSearchBlock d] ++ nodeBlocks d prelude
  { title := #[.code m.module.toString]
    titleString := m.module.toString
    metadata := none
    content := intro ++ docs ++ nodes
    subParts := #[] }

/-- An unnumbered page holding one block. -/
def pagePart (title : String) (block : Block Manual) : Part Manual :=
  { title := #[.text title], titleString := title, metadata := some { number := false }
    content := #[block], subParts := #[] }

/-- The document: the front page, a chapter per module that has declarations, the dependency
graph (on its module view above `moduleViewThreshold` declarations, laid out while the site is
built with the Graphviz program `layoutProgram` when one is given) and the summary page. -/
def documentOf (title : String) (project : Project) (layoutProgram : Option String := none)
    (sources : Name → Option String := fun _ => none) : Part Manual :=
  let chapters := project.modules.filter (!·.declarations.isEmpty) |>.map fun m =>
    moduleChapter m (sources m.module) project.texPrelude
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
