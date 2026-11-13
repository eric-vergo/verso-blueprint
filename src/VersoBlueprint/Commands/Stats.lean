/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

import Lean
import Verso
import VersoManual
import VersoBlueprint.Axioms
import VersoBlueprint.Commands.Common
import VersoBlueprint.Commands.SerializedExtension
import VersoBlueprint.Commands.WorkQueue
import VersoBlueprint.Graph
import VersoBlueprint.Informal.Block.Store
import VersoBlueprint.Lib.ExtensionDecode
import VersoBlueprint.Stats.Data
import VersoBlueprint.StatusColors
import VersoBlueprint.TraversalIndex

/-!
The "Project Stats" page: what a first-time reader of a project wants to know, on one page.

The page shows the project's identity (name, description, license, toolchain, key dependency
revisions, links), its headline result (the theorems of its Comparator challenge, when it has one),
how far along it is (nodes by progress status, overall and per chapter), how big it is, whether it
builds, and a short trust ledger (`sorry`, extra axioms, proofs that trust compiled code). Every
number comes from the project statistics captured with the render model (`Informal.Stats`); the
page holds no version-control data and needs no script.

Generators add the page to every site (`withStatsPage`), as an unnumbered page at the end of the
table of contents, unless the document places it itself with `{blueprint_stats}` or the generator
turns it off (`statsPage := false`, or the `--no-stats-page` flag).

The page is drawn in two steps: `StatsPageView.build` gathers what the page shows from the
statistics and the traversal (chapter titles, node links, the addresses of the summary and
work-queue pages), and `statsPageHtml` renders a view as a pure function.
-/

namespace Informal.Commands

open Lean
open Informal Data
open Informal.Stats
open Verso Doc Html Genre Manual
open Verso.Output.Html
open Verso.Multi (AllRemotes)

/-! ## The page's data -/

/-- An external link shown with the project's identity, such as its repository. -/
structure StatsLink where
  label : String
  href : String
deriving Inhabited, Repr, BEq, ToJson, FromJson

/-- The data of the stats page block: what the generator knows that the statistics do not. -/
structure StatsPageData where
  /-- The document's title, shown when the README has no heading. -/
  documentTitle : Option String := none
  /-- External links shown with the identity (generators pass their sidebar links). -/
  links : Array StatsLink := #[]
deriving Inhabited, Repr, BEq, ToJson, FromJson

/-- A Blueprint node as the page links to it. -/
structure StatsNodeRef where
  label : Name
  /-- The node's numbered title ("Theorem 6.1"), or its label. -/
  title : String
  href : Option String := none
deriving Inhabited, Repr

/-- A row of the per-chapter table. -/
structure StatsChapterRow where
  /-- The chapter's title, or the directory that names it in the site. -/
  title : String
  /-- The chapter's number, when it is numbered. -/
  number : Option String := none
  href : Option String := none
  progress : ProgressCounts := {}
deriving Inhabited, Repr

/-- Everything the page shows. -/
structure StatsPageView where
  stats : ProjectStats
  page : StatsPageData := {}
  /-- Per-chapter progress, in the order chapters first appear in the graph. -/
  chapters : Array StatsChapterRow := #[]
  /-- The nodes the ledger and the headline name. -/
  nodes : Array StatsNodeRef := #[]
  /-- Entries of the work queue (`workQueue`). -/
  workQueueSize : Nat := 0
  summaryHref : Option String := none
  workQueueHref : Option String := none
deriving Inhabited

/-- The title of the page in the table of contents. -/
def statsPageTitle : String := "Project Stats"

/-- The title of the page `{blueprint_summary}` adds. -/
def summaryPageTitle : String := "Blueprint Summary"

/-- The title of the page `{blueprint_work_queue}` adds. -/
def workQueuePageTitle : String := "Ready to Prove"

/-- Generator flag that turns the automatic stats page off. -/
def noStatsPageFlag : String := "--no-stats-page"

/-! ## Formatting -/

/-- A natural number with thousands separators: `13616` gives `"13,616"`. -/
def formatCount (n : Nat) : String := Id.run do
  let digits := (toString n).toList
  let len := digits.length
  let mut out := ""
  let mut i := 0
  for c in digits do
    if i > 0 && (len - i) % 3 == 0 then
      out := out.push ','
    out := out.push c
    i := i + 1
  return out

/-- `part` as a whole percentage of `total`, rounded down, so that 100% means all of it. -/
def percentOf (part total : Nat) : Nat :=
  if total == 0 then 0 else part * 100 / total

/-- The plural of an English noun as the page uses them (`proof`, `lemma`, `corollary`). -/
def pluralNoun (noun : String) : String :=
  if noun.endsWith "y" then (noun.dropEnd 1).copy ++ "ies" else noun ++ "s"

/-- A count with its noun: `1 theorem`, `2,133 lines`. -/
def countOf (n : Nat) (noun : String) : String :=
  s!"{formatCount n} {if n == 1 then noun else pluralNoun noun}"

/-- The part of `lean-toolchain` after the repository: `leanprover/lean4:v4.35.0` gives
`v4.35.0`. -/
def toolchainVersion (toolchain : String) : String :=
  let t := toolchain.trimAscii.copy
  match t.splitOn ":" with
  | [_, version] => version
  | _ => t

/-- The first seven characters of a commit. -/
def shortRev (rev : String) : String := (rev.take 7).copy

/-! ## Progress statuses -/

/-- A progress status as the page names and draws it. -/
structure ProgressBucket where
  /-- The class modifier and `data-bp-status` value. -/
  token : String
  label : String
  count : Nat
deriving Inhabited, Repr

/-- The progress counts as buckets, most complete first. -/
def progressBuckets (c : ProgressCounts) : Array ProgressBucket := #[
  { token := "fully-proved", label := "fully proved", count := c.formalizedWithAncestors },
  { token := "open-ancestors", label := "proved, open ancestors", count := c.formalized },
  { token := "incomplete", label := "Lean code incomplete", count := c.incomplete },
  { token := "ready", label := "ready to formalize", count := c.ready },
  { token := "not-ready", label := "not ready", count := c.notReady }
]

/-! ## HTML helpers -/

private def txt (s : String) : Output.Html := .text true s

private def el (tag cls : String) (content : Output.Html)
    (attrs : Array (String × String) := #[]) : Output.Html :=
  .tag tag (#[("class", cls)] ++ attrs) content

private def link (href? : Option String) (content : Output.Html) : Output.Html :=
  match href? with
  | some href => .tag "a" #[("href", href)] content
  | Option.none => content

private def code (s : String) : Output.Html := .tag "code" #[] (txt s)

/-- Items separated by `", "`. -/
private def commaList (items : Array Output.Html) : Output.Html :=
  .seq <| items.foldl (init := #[]) fun acc item =>
    if acc.isEmpty then #[item] else acc ++ #[txt ", ", item]

private def band (cls title : String) (content : Array Output.Html) : Output.Html :=
  el "section" s!"bp_stats_band {cls}" (.seq (#[el "h2" "bp_stats_band_title" (txt title)] ++ content))

/-! ## Identity -/

private def identityHtml (view : StatsPageView) : Output.Html :=
  let identity := view.stats.identity
  let name := identity.title <|> view.page.documentTitle <|> identity.name
  let license : Output.Html := match identity.license with
    | some info =>
      el "li" "bp_stats_chip bp_stats_chip_license" (txt s!"License: {info.spdx.getD info.file}")
        #[("data-bp-license-file", info.file)]
    | Option.none => el "li" "bp_stats_chip bp_stats_chip_license bp_stats_chip_missing"
        (txt "No license file")
  let toolchain : Output.Html := match identity.toolchain with
    | some t => el "li" "bp_stats_chip bp_stats_chip_toolchain" (txt s!"Lean {toolchainVersion t}")
    | Option.none => .empty
  let packages := identity.packages.filter (!·.inherited) |>.map fun pkg =>
    let version := match pkg.rev with
      | some rev => match pkg.inputRev with
        | some input => if input == rev then shortRev rev else s!"{input} · {shortRev rev}"
        | Option.none => shortRev rev
      | Option.none => pkg.dir.map (fun _ => "local") |>.getD pkg.source
    el "li" "bp_stats_chip bp_stats_chip_package" (.seq #[el "span" "bp_stats_chip_name" (txt pkg.name),
      txt " ", el "span" "bp_stats_chip_version" (txt version)]) #[("data-bp-package", pkg.name)]
  let links : Output.Html :=
    if view.page.links.isEmpty then .empty
    else el "ul" "bp_stats_links" (.seq <| view.page.links.map fun l =>
      .tag "li" #[] (.tag "a" #[("href", l.href)] (txt l.label)))
  el "section" "bp_stats_band bp_stats_identity" (.seq #[
    match name with
    | some n => el "p" "bp_stats_name" (txt n)
    | Option.none => .empty,
    match identity.description with
    | some d => el "p" "bp_stats_description" (txt d)
    | Option.none => .empty,
    el "ul" "bp_stats_chips" (.seq (#[license, toolchain] ++ packages)),
    links
  ])

/-! ## Headline -/

/-- The verdict on a theorem of the challenge: a token for markup and the words shown. -/
def headlineVerdict (t : HeadlineTheorem) : String × String :=
  if t.proved then ("proved", "Proved")
  else match t.solution with
    | .same =>
      if t.sorryFree == some false then ("sorry", "Same statement; the proof uses sorry")
      else ("open", "Same statement; not proved")
    | .differs =>
      let what := match t.difference, t.differingDeclaration with
        | some d, some decl => s!": {d} ({decl})"
        | some d, Option.none => s!": {d}"
        | Option.none, some decl => s!" ({decl})"
        | Option.none, Option.none => ""
      ("differs", s!"Statement differs{what}")
    | .missing => ("missing", "Not in the solution")
    | .hole => ("hole", "Definition hole")
    | .notCompared => ("not-compared", "Not compared")

/-- How the solution declares a definition of the challenge, in a few words. -/
def definitionVerdict : Correspondence → String
  | .same => "same"
  | .hole => "definition hole, supplied by the solution"
  | .differs => "differs"
  | .missing => "not in the solution"
  | .notCompared => "not compared"

/-- Why the challenge could not be compared, in a sentence. -/
def unavailableText : Unavailable → String
  | .configInvalid => "comparator.json could not be read or lacks the fields lake comparator needs."
  | .challengeNotBuilt => "The challenge module has not been built."
  | .challengeOutOfDate => "The compiled challenge module does not match its source."
  | .challengeUnreadable => "The compiled challenge module could not be read."
  | .solutionNotImported => "The Blueprint does not import the solution module."
  | .importsNotAvailable => "The challenge imports a module the Blueprint does not import."

private def axiomChip (a : Name) : Output.Html :=
  let cls := AxiomClass.ofName a
  el "li" s!"bp_stats_axiom bp_stats_axiom_{cls.token}" (code a.toString)
    #[("data-bp-axiom-class", cls.token), ("title", cls.description)]

private def axiomsHtml (t : HeadlineTheorem) : Output.Html :=
  if t.solution == .missing || t.solution == .notCompared then .empty else
  let note : String :=
    if t.axioms.isEmpty then "no axioms"
    else if t.axioms.all (AxiomClass.ofName · == .standard) then
      "the standard axioms of Lean's logic only"
    else ""
  let permitted : Output.Html := match t.axiomsPermitted with
    | some false => el "span" "bp_stats_axioms_note bp_stats_axioms_not_permitted"
        (txt "uses an axiom the challenge does not permit")
    | _ => .empty
  el "div" "bp_stats_axioms" (.seq #[
    el "span" "bp_stats_caption" (txt "Axioms"),
    el "ul" "bp_stats_axiom_list" (.seq (t.axioms.map axiomChip)),
    if note.isEmpty then .empty else el "span" "bp_stats_axioms_note" (txt note),
    permitted])

private def nodeRef? (view : StatsPageView) (label : Name) : Option StatsNodeRef :=
  view.nodes.find? (·.label == label)

private def nodeLink (view : StatsPageView) (label : Name) : Output.Html :=
  match nodeRef? view label with
  | some ref => link ref.href (txt ref.title)
  | Option.none => txt label.toString

private def headlineTheoremHtml (view : StatsPageView) (t : HeadlineTheorem) : Output.Html :=
  let (token, verdict) := headlineVerdict t
  el "div" "bp_stats_theorem" (.seq #[
    el "div" "bp_stats_theorem_head" (.seq #[
      match t.node with
      | some label => el "span" "bp_stats_theorem_node" (nodeLink view label)
      | Option.none => .empty,
      el "code" "bp_stats_theorem_name" (txt t.name.toString),
      el "span" s!"bp_stats_verdict bp_stats_verdict_{token}" (txt verdict)]),
    match t.docstring with
    | some d => el "p" "bp_stats_theorem_doc" (txt d)
    | Option.none => .empty,
    if t.statement.isEmpty then .empty
    else el "pre" "bp_stats_statement" (code t.statement),
    axiomsHtml t
  ]) #[("data-bp-theorem", t.name.toString), ("data-bp-verdict", token)]

/-- The one line a page without a Comparator challenge shows instead of the card. -/
def headlineHintText : String :=
  "No headline result: a Comparator challenge (a module that states the main theorems with " ++
    "sorry, and a solution module that proves them) would add one here."

private def headlineHtml (view : StatsPageView) : Output.Html :=
  match view.stats.headline with
  | Option.none => el "p" "bp_stats_headline_hint" (txt headlineHintText)
  | some h =>
    let source : Output.Html :=
      let challenge := code (h.challengeFile.getD h.challengeModule.toString)
      let solution := code (h.solutionFile.getD h.solutionModule.toString)
      el "p" "bp_stats_headline_source" (.seq #[txt "From the Comparator challenge ", challenge,
        txt ", proved in ", solution, txt ". A summary for readers; lake comparator is the authority."])
    let unavailable : Output.Html := match h.unavailable with
      | some u =>
        let detail := h.unavailableDetail.map (s!" ({·})") |>.getD ""
        el "p" "bp_stats_headline_unavailable" (txt s!"Not compared: {unavailableText u}{detail}")
      | Option.none => .empty
    let definitions : Output.Html :=
      if h.definitions.isEmpty then .empty
      else el "p" "bp_stats_headline_definitions" (.seq #[
        el "span" "bp_stats_caption" (txt "Definitions"), txt " ",
        commaList (h.definitions.map fun d =>
          .seq #[code d.name.toString, txt s!" ({definitionVerdict d.solution})"])])
    let theorems : Output.Html :=
      if h.theorems.isEmpty then el "p" "bp_stats_headline_unavailable" (txt "The challenge states no theorem.")
      else .seq (h.theorems.map (headlineTheoremHtml view))
    band "bp_stats_headline" "Headline result" #[unavailable, theorems, definitions, source]

/-! ## Progress -/

private def progressBar (c : ProgressCounts) : Output.Html :=
  let buckets := (progressBuckets c).filter (·.count > 0)
  let description := ", ".intercalate (buckets.toList.map fun b => s!"{formatCount b.count} {b.label}")
  el "div" "bp_stats_bar" (.seq <| buckets.map fun b =>
    el "span" s!"bp_stats_seg bp_stats_status_{b.token}" .empty
      #[("style", s!"flex-grow: {b.count}"), ("data-bp-status", b.token),
        ("title", s!"{b.label}: {formatCount b.count}")])
    #[("role", "img"), ("aria-label", s!"{countOf c.total "node"}: {description}")]

private def progressLegend (c : ProgressCounts) : Output.Html :=
  el "ul" "bp_stats_legend" (.seq <| (progressBuckets c).map fun b =>
    el "li" (if b.count == 0 then "bp_stats_legend_item bp_stats_legend_zero" else "bp_stats_legend_item")
      (.seq #[el "span" s!"bp_stats_swatch bp_stats_status_{b.token}" .empty #[("aria-hidden", "true")],
        txt s!"{b.label} ", el "strong" "bp_stats_legend_count" (txt (formatCount b.count))])
      #[("data-bp-status", b.token)])

private def chapterTable (rows : Array StatsChapterRow) : Output.Html :=
  if rows.isEmpty then .empty else
  let body := rows.map fun row =>
    let total := row.progress.total
    let done := row.progress.formalizedWithAncestors
    .tag "tr" #[("data-bp-chapter", row.title)] (.seq #[
      el "td" "bp_stats_chapter_title" (.seq #[
        match row.number with
        | some n => el "span" "bp_stats_chapter_number" (txt n)
        | Option.none => .empty,
        link row.href (txt row.title)]),
      el "td" "bp_stats_num" (txt (formatCount total)),
      el "td" "bp_stats_chapter_bar" (progressBar row.progress),
      el "td" "bp_stats_num" (txt s!"{formatCount done}/{formatCount total}")])
  el "table" "bp_stats_chapters" (.seq #[
    .tag "thead" #[] (.tag "tr" #[] (.seq #[
      .tag "th" #[("scope", "col")] (txt "Chapter"),
      el "th" "bp_stats_num" (txt "Nodes") #[("scope", "col")],
      .tag "th" #[("scope", "col")] (txt "Progress"),
      el "th" "bp_stats_num" (txt "Fully proved") #[("scope", "col")]])),
    .tag "tbody" #[] (.seq body)])

private def progressHtml (view : StatsPageView) : Output.Html :=
  let c := view.stats.progress
  let lead := s!"{countOf c.total "node"} · {percentOf c.formalizedWithAncestors c.total}% fully proved"
  let queue : Output.Html := match view.workQueueHref with
    | some href => el "p" "bp_stats_links_line" (.seq #[
        .tag "a" #[("href", href)] (txt s!"{workQueuePageTitle} ({formatCount view.workQueueSize})")])
    | Option.none => .empty
  band "bp_stats_progress" "How far along" #[
    el "p" "bp_stats_lead" (txt lead),
    progressBar c,
    progressLegend c,
    queue,
    chapterTable view.chapters]

/-! ## Size -/

private def tile (key value label : String) (detail : String) : Output.Html :=
  el "div" "bp_stats_tile" (.seq #[
    el "span" "bp_stats_tile_value" (txt value),
    el "span" "bp_stats_tile_label" (txt label),
    if detail.isEmpty then .empty else el "span" "bp_stats_tile_detail" (txt detail)])
    #[("data-bp-stat", key)]

private def joinCounts (items : List (Nat × String)) : String :=
  " · ".intercalate (items.filter (·.1 > 0) |>.map fun (n, noun) => countOf n noun)

private def sizeHtml (view : StatsPageView) : Output.Html :=
  let s := view.stats
  let d := s.declarations
  let lines := s.sources.lines
  band "bp_stats_size" "How big" #[el "div" "bp_stats_tiles" (.seq #[
    tile "files" (formatCount s.sources.files.size) "Lean files"
      (countOf s.modules.size "module" ++ " in the site's build"),
    tile "lines" (formatCount lines.total) "lines"
      (joinCounts [(lines.code, "code line"), (lines.comment, "comment line"), (lines.blank, "blank line")]),
    tile "declarations" (formatCount d.total) "declarations"
      (joinCounts [(d.theorems, "theorem"), (d.definitions, "definition"), (d.instances, "instance"),
        (d.structures, "structure"), (d.classes, "class"), (d.inductives, "inductive"),
        (d.axioms, "axiom"), (d.opaques, "opaque")]),
    tile "nodes" (formatCount s.graph.nodes) "Blueprint nodes"
      (joinCounts (s.graph.byKind.toList.map fun (k, n) => (n, k))),
    tile "chapters" (formatCount view.chapters.size) "chapters" "with Blueprint nodes",
    tile "edges" (formatCount s.graph.edges) "dependencies"
      (joinCounts [(s.graph.statementEdges, "statement use"), (s.graph.proofEdges, "proof use")])
  ])]

/-! ## Build -/

/-- How many of the listed files are shown before the rest are folded away. -/
private def shownFiles : Nat := 8

private def fileList (files : Array SourceFile) : Output.Html :=
  let item (f : SourceFile) : Output.Html := .tag "li" #[] (code f.path)
  if files.size ≤ shownFiles then el "ul" "bp_stats_files" (.seq (files.map item))
  else .seq #[
    el "ul" "bp_stats_files" (.seq ((files.extract 0 shownFiles).map item)),
    el "details" "bp_stats_more" (.seq #[
      .tag "summary" #[] (txt s!"and {formatCount (files.size - shownFiles)} more"),
      el "ul" "bp_stats_files" (.seq ((files.extract shownFiles files.size).map item))])]

private def sorryDeclarations (t : TrustLedger) : Nat :=
  (t.sorryDirect.map (·.declaration)).foldl (init := (#[] : Array Name))
    (fun acc n => if acc.contains n then acc else acc.push n) |>.size

private def buildHtml (view : StatsPageView) : Output.Html :=
  let s := view.stats
  let files := s.sources.files
  let imported := (files.filter (·.status == .imported)).size
  let compiled := (files.filter (·.status == .compiled)).size
  let notBuilt := s.sources.notBuilt
  let compiledLine :=
    s!"{formatCount (imported + compiled)} of {countOf files.size "Lean file"} compiled: " ++
      s!"{formatCount imported} imported by the site" ++
      (if compiled > 0 then s!", {formatCount compiled} built by another target." else ".")
  let sorries := sorryDeclarations s.trust
  let sorryLine :=
    if sorries == 0 then "No declaration has a sorry of its own."
    else s!"{countOf sorries "declaration"} with a sorry of {if sorries == 1 then "its" else "their"} own."
  let notBuiltPart : Output.Html :=
    if notBuilt.isEmpty then el "p" "bp_stats_build_line" (txt "Every Lean file on disk is in a build.")
      #[("data-bp-build", "not-built")]
    else .seq #[
      el "p" "bp_stats_build_line" (txt s!"{countOf notBuilt.size "Lean file"} on disk in no build:")
        #[("data-bp-build", "not-built")],
      fileList notBuilt]
  band "bp_stats_build" "Does it build" #[
    el "p" "bp_stats_build_line" (txt compiledLine) #[("data-bp-build", "compiled")],
    el "p" "bp_stats_build_line" (txt sorryLine) #[("data-bp-build", "sorry")],
    notBuiltPart]

/-! ## Trust -/

/-- How many node links a ledger row shows before it says how many more there are. -/
private def shownEntries : Nat := 12

private def distinctLabels (labels : Array Name) : Array Name :=
  labels.foldl (init := #[]) fun acc l => if acc.contains l then acc else acc.push l

private def trustRow (view : StatsPageView) (key label : String) (labels : Array Name) : Output.Html :=
  let labels := distinctLabels labels
  let shown := (labels.extract 0 shownEntries).map (nodeLink view)
  let more : Output.Html :=
    if labels.size > shownEntries then txt s!", and {formatCount (labels.size - shownEntries)} more"
    else .empty
  .tag "tr" #[("class", if labels.isEmpty then "bp_stats_trust_clear" else "bp_stats_trust_open"),
      ("data-bp-trust", key), ("data-bp-count", toString labels.size)] (.seq #[
    .tag "th" #[("scope", "row")] (txt label),
    el "td" "bp_stats_num" (txt (formatCount labels.size)),
    .tag "td" #[] (.seq #[commaList shown, more])])

private def trustHtml (view : StatsPageView) : Output.Html :=
  let t := view.stats.trust
  let lead :=
    if t.isClear then "Nothing in the ledger limits trust: no sorry, no extra axiom, no proof that " ++
      "trusts compiled code."
    else "Blueprint nodes whose Lean declarations rest on more than Lean's logic."
  band "bp_stats_trust" "Trust" #[
    el "p" "bp_stats_lead" (txt lead),
    el "table" "bp_stats_ledger" (.seq #[
      .tag "thead" #[] (.tag "tr" #[] (.seq #[
        .tag "th" #[("scope", "col")] (txt "Rests on"),
        el "th" "bp_stats_num" (txt "Nodes") #[("scope", "col")],
        .tag "th" #[("scope", "col")] (txt "Where")])),
      .tag "tbody" #[] (.seq #[
        trustRow view "sorry-direct" "sorry in the proof" (t.sorryDirect.map (·.label)),
        trustRow view "sorry-dependency" "sorry through a dependency"
          (t.sorryThroughDependency.map (·.label)),
        trustRow view "extra-axioms" "axioms beyond Lean's standard three" (t.extraAxioms.map (·.label)),
        trustRow view "compiler-trusted" "trust in compiled code (native_decide)"
          (t.compilerTrusted.map (·.label)),
        trustRow view "missing-declarations" "Lean names not found"
          (t.missingDeclarations.map (·.label)),
        trustRow view "unknown-references" "references to no node"
          (t.unknownReferences.foldl (init := #[]) fun acc r => acc ++ r.referencedBy)])])]

/-! ## The page -/

/-- The page body of a view. -/
def statsPageHtml (view : StatsPageView) : Output.Html :=
  let summary : Output.Html := match view.summaryHref with
    | some href => el "p" "bp_stats_summary_link" (.seq #[txt "Detailed breakdown: ",
        .tag "a" #[("href", href)] (txt summaryPageTitle)])
    | Option.none => .empty
  el "div" "bp_project_stats" (.seq #[
    identityHtml view,
    headlineHtml view,
    progressHtml view,
    sizeHtml view,
    buildHtml view,
    trustHtml view,
    summary])
    #[("data-bp-schema-version", toString view.stats.schemaVersion)]

/-! ## Reading the traversal -/

/-- A section of the site as Verso's section domain records it. -/
structure SiteSection where
  title : String
  number : Option String := none
  link : Verso.Multi.Link
  /-- How many headers enclose it, itself and the document's root included. -/
  depth : Nat
deriving Inhabited

/-- Every section of the site that has an address. -/
def siteSections (state : TraverseState) : Array SiteSection :=
  match state.domains.get? sectionDomain with
  | Option.none => #[]
  | some domain => domain.objects.foldl (init := #[]) fun acc _ obj =>
    let title? := (obj.data.getObjValAs? String "title").toOption
    let number := (obj.data.getObjValAs? String "sectionNum").toOption
    let depth := ((obj.data.getObjValAs? (Array Json) "context").toOption.map (·.size)).getD 0
    let link? := obj.ids.toArray.foldl (init := none) fun found id =>
      found <|> state.externalTags[id]?
    match title?, link? with
    | some title, some link => acc.push { title, number, link, depth }
    | _, _ => acc

/-- The outermost section of the page in directory `dir` (a chapter's own heading). -/
def chapterSection? (sections : Array SiteSection) (dir : String) : Option SiteSection :=
  sections.foldl (init := none) fun best s =>
    if s.link.path != #[dir] then best
    else match best with
      | some b => if s.depth < b.depth then some s else some b
      | Option.none => some s

/-- The outermost section with the given title, such as the summary page. -/
def pageSection? (sections : Array SiteSection) (title : String) : Option SiteSection :=
  sections.foldl (init := none) fun best s =>
    if s.title != title then best
    else match best with
      | some b => if s.depth < b.depth then some s else some b
      | Option.none => some s

/-- The node's numbered title ("Lemma 4.2"), falling back to the graph's display label. -/
private def nodeTitle (state : TraverseState) (node : Graph.NodeData) : String :=
  match Informal.TraversalIndex.Nodes.display? state node.label with
  | some display => display.title
  | Option.none => node.displayLabel

/-- A section number as numbers: `"4.2"` gives `[4, 2]`. -/
def sectionNumberKey (number : String) : List Nat :=
  (number.splitOn ".").filterMap (·.trimAscii.copy.toNat?)

/-- Chapter rows in the order of their numbers, the unnumbered ones after them, each group in
the order it came in. -/
def sortChapterRows (rows : Array StatsChapterRow) : Array StatsChapterRow :=
  let lt (a b : StatsChapterRow) : Bool :=
    match a.number.map sectionNumberKey, b.number.map sectionNumberKey with
    | some x, some y => x < y
    | some _, Option.none => true
    | _, _ => false
  rows.insertionSort lt

/-- Gather what the page shows. -/
def StatsPageView.build (state : TraverseState) (stats : ProjectStats) (graph : Graph.GraphModel)
    (page : StatsPageData) : StatsPageView :=
  let graphNodes := graph.nodes.filter (!·.warnings.unknownRef) |>.map fun node =>
    { node with href := Informal.TraversalIndex.Nodes.href? state node.label <|> node.href }
  let nodes := graphNodes.map fun node =>
    ({ label := node.label, title := nodeTitle state node, href := node.href } : StatsNodeRef)
  let sections := siteSections state
  let chapters := (chapterProgress graphNodes).map fun c =>
    match chapterSection? sections c.chapter with
    | some s => { title := s.title, number := s.number, href := some s.link.relativeLink,
                  progress := c.progress }
    | Option.none => { title := c.chapter, progress := c.progress }
  let stats := stats.withChapters graphNodes
  let chapters := sortChapterRows chapters
  {
    stats, page, chapters, nodes
    workQueueSize := (workQueue graph).size
    summaryHref := (pageSection? sections summaryPageTitle).map (·.link.relativeLink)
    workQueueHref := (pageSection? sections workQueuePageTitle).map (·.link.relativeLink)
  }

/-! ## The block and the page -/

def statsCss : String := include_str "stats.css"

def statsAssetBundle : BlueprintAssetBundle :=
  blueprintCssAssetBundle [statsCss]

private def statsToHtml :
    BlockToHtml Manual (ReaderT AllRemotes (ReaderT ExtensionImpls (BuildLogT IO))) :=
  fun _goI _goB _id json _blocks => do
    let some data ← Informal.ExtensionDecode.decode? (α := StatsPageData) json
        (fun err => s!"Malformed data in Block.projectStats.toHtml ({err})")
      | pure .empty
    let s ← HtmlT.state
    let stats ← match Informal.TraversalIndex.RenderOverviews.required (α := ProjectStats) s `stats with
      | .ok stats => pure (some stats)
      | .error message => Verso.reportError message; pure none
    let graph ← match Informal.TraversalIndex.RenderOverviews.required (α := Graph.GraphModel) s `graph with
      | .ok graph => pure (some graph)
      | .error message => Verso.reportError message; pure none
    let (some stats, some graph) := (stats, graph) | pure .empty
    pure (statsPageHtml (StatsPageView.build s stats graph data))

block_extension Block.projectStats (data : StatsPageData) where
  data := toJson data
  traverse _id _data _contents := pure none
  toTeX :=
    some <| fun _goI _goB _id _data _blocks =>
      pure <| .text "The project statistics are available in the HTML output."
  toHtml := some statsToHtml
  extraCss := statsAssetBundle.css
  extraJs := statsAssetBundle.js

/-- The unnumbered "Project Stats" page. -/
def statsPart (data : StatsPageData) : Part Manual :=
  { title := #[.text statsPageTitle]
    titleString := statsPageTitle
    metadata := some { number := false }
    content := #[.other (Block.projectStats data) #[]]
    subParts := #[] }

private def isStatsBlock : Doc.Block Manual → Bool
  | .other block _ => block.name == ``Block.projectStats
  | _ => false

/-- Whether the document already has a stats page (`{blueprint_stats}`). -/
partial def hasStatsPage (part : Part Manual) : Bool :=
  part.content.any isStatsBlock || part.subParts.any hasStatsPage

/-- The document with every stats page block given `data`. -/
private partial def fillStatsBlocks (data : StatsPageData) (part : Part Manual) : Part Manual :=
  { part with
    content := part.content.map fun b =>
      if isStatsBlock b then .other (Block.projectStats data) #[] else b
    subParts := part.subParts.map (fillStatsBlocks data) }

/-- The document with the stats page added at the end of its table of contents. A document that
places the page itself (`{blueprint_stats}`) keeps it where it is, with `data` filled in. -/
def withStatsPage (text : Part Manual) (data : StatsPageData := {}) : Part Manual :=
  let data := { data with documentTitle := data.documentTitle <|> some text.titleString }
  if hasStatsPage text then fillStatsBlocks data text
  else { text with subParts := text.subParts.push (statsPart data) }

open Verso Doc Elab Syntax in
def mkStatsPart (stx : Syntax) (endPos : String.Pos.Raw) : PartElabM FinishedPart := do
  let titleInlines ← `(inline | "Project Stats")
  let expandedTitle ← #[titleInlines].mapM (elabInline ·)
  let metadata : Option (TSyntax `term) := some (← `(term| { number := false }))
  let block ← serializedBlockTerm `Informal.Commands.Block.projectStats ({} : StatsPageData)
  pure <| FinishedPart.mk stx stx expandedTitle statsPageTitle metadata #[block] #[] endPos

open Verso Doc Elab Syntax PartElabM in
/-- `{blueprint_stats}` places the Project Stats page; without it, generators add the page at the
end of the document. -/
@[part_command Lean.Doc.Syntax.command]
public meta def blueprintStatsCmd : PartCommand
  | stx@`(block|command{blueprint_stats}) => do
    let endPos := stx.getTailPos?.get!
    closePartsUntil 1 endPos
    addPart (← mkStatsPart stx endPos)
  | _ => (Lean.Elab.throwUnsupportedSyntax : PartElabM Unit)

end Informal.Commands
