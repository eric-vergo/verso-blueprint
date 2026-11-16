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
import VersoBlueprint.Meaning
import VersoBlueprint.ReplayView
import VersoBlueprint.Stats.Claims
import VersoBlueprint.Stats.Data
import VersoBlueprint.StatusColors
import VersoBlueprint.TraversalIndex

/-!
The "Project Stats" page: what a first-time reader of a project wants to know, on one page.

The page shows the project's identity (name, description, license, toolchain, key dependency
revisions, links), its headline result (the theorems of its Comparator challenge, when it has one),
how far along it is (nodes by progress status, overall and per chapter), how big it is, whether it
builds, and a short ledger of what the Lean code rests on (`sorry`, extra axioms, compiled code).
Every number comes from the project statistics captured with the render model
(`Informal.Stats`); the page holds no version-control data and needs no script.

Each sentence on the page says what was looked at and no more. A status is about Lean code: its
words are "Lean complete" (no `sorry` in a node's declarations or in what they use), never
"proved" for a definition and never a word about an informal statement. The headline's verdict
is about the Lean statement, in the build the site was generated from; it says "proved" only
when a kernel replay accepted the theorem with everything it depends on (`Informal.Replay`), and
the page has a band that says what was checked, by which checker, and what that leaves trusted.
Informal text (a
challenge's docstring, an author's claim about a manuscript) is shown with a caption naming its
source and the sentence that no tool compared it with the Lean statement
(`Informal.Meaning`); the page ends with a short explanation of the marks
(`Informal.Meaning.anchor`), which the notes link to.

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
  /-- The page of the explanation of the marks is this page, so its notes link to the anchor
  alone. -/
  meaningHref : Option String := Option.some s!"#{Informal.Meaning.anchor}"
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
  /-- What the site as a whole may show in the success colour (`Replay.siteState`): without an
  accepted replay that covers every node, counts, bars and legends are neutral and say why. -/
  site : Replay.SiteState := .none Replay.noReplayText
  /-- The nodes with Lean code that an accepted replay does not cover, sorted. -/
  notReplayed : Array Name := #[]
  /-- The nodes whose Lean code an accepted replay covers, under which it found an axiom outside
  Lean's standard three, sorted (`ReplayView.Index.resting`). -/
  resting : Array Name := #[]
deriving Inhabited

/-- The title of the page in the table of contents. -/
def statsPageTitle : String := "Project Stats"

/-- The title of the page `{blueprint_summary}` adds. -/
def summaryPageTitle : String := "Blueprint Summary"

/-- The title of the page `{blueprint_work_queue}` adds. -/
def workQueuePageTitle : String := "Ready to Prove"

/-- Generator flag that turns the automatic stats page off. -/
def noStatsPageFlag : String := "--no-stats-page"

/-- The folder of the automatic stats page in a multi-page site: its title as a page slug. -/
def statsPageFolder : String := (Verso.Multi.Slug.ofString statsPageTitle).toString

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

/-- The words for a node whose Lean declarations, with everything they use, contain no `sorry`.
It is said of theorems and definitions alike, and says nothing about an informal statement. -/
def leanCompleteLabel : String := "Lean complete"

/-- The progress counts as buckets, most complete first. The tokens are the status tokens of
the stylesheet; the labels say what was looked at: the node's Lean code and the nodes it depends
on. The two buckets of `sorry`-free code are drawn in a success colour only under an accepted
kernel replay; in any other `site` state their labels say what the count rests on. -/
def progressBuckets (c : ProgressCounts)
    (site : Replay.SiteState := .none Replay.noReplayText) : Array ProgressBucket :=
  let note := (site.note?.map (s!" ({·})")).getD ""
  #[
  { token := "fully-proved", label := s!"Lean complete, dependencies too{note}",
    count := c.formalizedWithAncestors },
  { token := "open-ancestors", label := s!"Lean complete, a dependency is not{note}",
    count := c.formalized },
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

/-- What the page's reports are reports of: one build. A site of a port, or of a project built
with other revisions than its release names, must not read as a check of that release. -/
def thisBuildText (identity : ProjectIdentity) : String :=
  let lean := identity.toolchain.map fun t => s!"Lean {toolchainVersion t}"
  let packages : Option String :=
    if (identity.packages.filter (!·.inherited)).isEmpty then Option.none
    else some "the package revisions above"
  let made := match lean, packages with
    | some l, some p => s!", made with {l} and {p}"
    | some l, Option.none => s!", made with {l}"
    | Option.none, some p => s!", made with {p}"
    | Option.none, Option.none => ""
  s!"This page reports on one build{made}. No other toolchain or revision was checked."

private def identityHtml (view : StatsPageView) : Output.Html :=
  let identity := view.stats.identity
  let name := identity.shownTitle? <|> view.page.documentTitle <|> identity.name
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
    el "p" "bp_stats_this_build" (txt (thisBuildText identity)) #[("data-bp-build", "this-build")],
    links
  ])

/-! ## Headline -/

/-- The axioms a verdict does not allow, in words: against the challenge's list when it states
one, else against Lean's standard three. -/
private def notAllowedText (t : HeadlineTheorem) : String :=
  let names := ", ".intercalate (t.axiomsNotAllowed.toList.map (·.toString))
  let one := t.axiomsNotAllowed.size == 1
  if t.axiomsPermitted.isSome then
    s!"{if one then "an axiom" else "axioms"} the challenge does not permit ({names})"
  else s!"{if one then "an axiom" else "axioms"} outside Lean's standard three ({names})"

/-- The verdict when the comparison's conditions are met and no kernel replay stands behind
them: exactly what the compiled files report. -/
def conditionsMetText : String :=
  "Same Lean statement as the challenge; no sorry; permitted axioms: as the compiled files \
    report, not replayed by a kernel"

/-- The verdict on a theorem of the challenge: a token for markup and the words shown. The
words are about the Lean statement. "Proved" is said only of the same Lean statement as the
challenge's, without `sorry`, without an axiom the verdict does not allow, and with the theorem
and everything it depends on accepted by a kernel replay (`standing`). When the replay rejected
the build the verdict says so; without a verdict of a replay it says what the compiled files
report (`conditionsMetText`). -/
def headlineVerdict (t : HeadlineTheorem)
    (standing : Replay.Standing := .notReplayed Replay.noReplayText) : String × String :=
  if t.conditionsMet then
    match standing with
    | .accepted => ("proved", "Lean statement proved")
    | .rejected => ("rejected", "Proof rejected by the kernel checker")
    | .notReplayed _ | .assumed _ => ("not-replayed", conditionsMetText)
  else match t.solution with
    | .same =>
      if t.sorryFree == some false then
        ("sorry", "Same Lean statement as the challenge; the proof uses sorry")
      else if !t.axiomsNotAllowed.isEmpty then
        ("axioms", s!"Same Lean statement as the challenge; the proof rests on {notAllowedText t}")
      else ("open", "Same Lean statement as the challenge; not proved")
    | .differs =>
      let what := match t.difference, t.differingDeclaration with
        | some d, some decl => s!": {d} ({decl})"
        | some d, Option.none => s!": {d}"
        | Option.none, some decl => s!" ({decl})"
        | Option.none, Option.none => ""
      ("differs", s!"Lean statement differs from the challenge{what}")
    | .missing => ("missing", "Not in the solution")
    | .hole => ("hole", "Definition hole")
    | .notCompared => ("not-compared", "Not compared")

/-- How the solution declares a definition of the challenge, in a few words. -/
def definitionVerdict : Correspondence → String
  | .same => "same in the solution"
  | .hole => "definition hole, supplied by the solution"
  | .differs => "differs in the solution"
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
  | .modulesNotLoaded => "The compiled modules were not loaded for the comparison."

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
  let permitted : Output.Html :=
    if t.axiomsNotAllowed.isEmpty then .empty
    else el "span" "bp_stats_axioms_note bp_stats_axioms_not_permitted"
      (txt s!"uses {notAllowedText t}")
  el "div" "bp_stats_axioms" (.seq #[
    el "span" "bp_stats_caption" (txt "Axioms of the solution's proof"),
    el "ul" "bp_stats_axiom_list" (.seq (t.axioms.map axiomChip)),
    if note.isEmpty then .empty else el "span" "bp_stats_axioms_note" (txt note),
    permitted])

private def nodeRef? (view : StatsPageView) (label : Name) : Option StatsNodeRef :=
  view.nodes.find? (·.label == label)

private def nodeLink (view : StatsPageView) (label : Name) : Output.Html :=
  match nodeRef? view label with
  | some ref => link ref.href (txt ref.title)
  | Option.none => txt label.toString

/-- The link to the explanation of the marks, with a space before it. -/
private def meaningLink (view : StatsPageView) : Output.Html :=
  match view.page.meaningHref with
  | some href => .seq #[txt " ", .tag "a" #[("href", href), ("class", "bp_meaning_link")]
      (txt Informal.Meaning.linkText)]
  | Option.none => .empty

/-- The caption of a challenge theorem's docstring: whose words they are, and that nothing
compared them with the Lean statement. -/
def challengeDocCaption : String :=
  s!"Docstring in the challenge ({Informal.Meaning.uncheckedTag})"

/-- The link from a judged theorem to its node. The node's title is the site's own: a written
Blueprint numbers its nodes, so the link says that the number is the Blueprint's. -/
private def theoremNodeHtml (view : StatsPageView) (t : HeadlineTheorem) : Output.Html :=
  match t.node with
  | Option.none => .empty
  | some label =>
    let ref? := nodeRef? view label
    let title := (ref?.map (·.title)).getD label.toString
    let text := if title.endsWith t.name.toString || title.endsWith label.toString then
        "Its node on this site"
      else s!"This site's {title}"
    el "span" "bp_stats_theorem_node" (link (ref?.bind (·.href)) (txt text))

/-- The line under a verdict that rests on the comparison's conditions: what the kernel replay
did for the judged theorem (`standing`). -/
def replayNoteText (replay? : Option Replay.Result) (standing : Replay.Standing) : String :=
  let checker := (replay?.map (·.checkerName)).getD "the kernel checker"
  match standing with
  | .accepted =>
    let earlier := if replay?.any (·.recorded) then
        " (in an earlier run, for an export identical to this build's)" else ""
    s!"Kernel replay: {checker} accepted this theorem and every constant it depends on, in \
      this project, in its dependencies and in Lean's own library, starting from an empty \
      environment{earlier}."
  | .rejected =>
    let message := ((replay?.bind (·.message)).map (s!": {·}")).getD "."
    s!"Kernel replay: {checker} rejected this build{message}"
  | .notReplayed why => s!"No kernel replay: {why}."
  | .assumed _ => s!"No verdict of a kernel replay: {standing.why}."

/-- What the replay establishes for a judged theorem of a headline: whether it checked the
theorem with everything it depends on, and found no axiom under it beyond those the challenge
permits (Lean's standard three when it states no list). -/
def headlineStanding (replay? : Option Replay.Result) (h : Headline) (t : HeadlineTheorem) :
    Replay.Standing :=
  Replay.provedStanding replay? #[t.name]
    (permitted := h.permittedAxioms.getD Data.standardAxioms)

private def headlineTheoremHtml (view : StatsPageView) (h : Headline) (t : HeadlineTheorem) :
    Output.Html :=
  let replay? := view.stats.replay
  let standing := headlineStanding replay? h t
  let (token, verdict) := headlineVerdict t standing
  let claim? := view.stats.claims.bind (·.view? t.name)
  let replayNote : Output.Html :=
    if !t.conditionsMet then .empty
    else el "p" s!"bp_stats_replay_note bp_stats_replay_note_{token}"
      (txt (replayNoteText replay? standing)) #[("data-bp-replay", token)]
  -- the card's success colours follow the replay behind this verdict
  el "div" s!"bp_stats_theorem {standing.scopeClass}" (.seq #[
    el "div" "bp_stats_theorem_head" (.seq #[
      el "code" "bp_stats_theorem_name" (txt t.name.toString),
      el "span" s!"bp_stats_verdict bp_stats_verdict_{token}" (txt verdict),
      theoremNodeHtml view t]),
    replayNote,
    if t.statement.isEmpty then .empty
    else .seq #[
      el "p" "bp_stats_caption bp_stats_statement_caption" (txt "Lean statement, from the challenge"),
      el "pre" "bp_stats_statement" (code t.statement)],
    axiomsHtml t,
    match t.docstring with
    | some d => el "div" "bp_stats_theorem_informal" (.seq #[
        el "p" "bp_stats_caption bp_stats_doc_caption" (txt challengeDocCaption),
        el "p" "bp_stats_theorem_doc" (txt d)]) #[("data-bp-statement-source", "docstring")]
    | Option.none => .empty,
    match claim? with
    | some c => c.render view.page.meaningHref
    | Option.none => .empty
  ]) #[("data-bp-theorem", t.name.toString), ("data-bp-verdict", token)]

/-- The one line a page without a Comparator challenge shows instead of the card. -/
def headlineHintText : String :=
  "No headline result: a Comparator challenge (a module that states the main theorems with " ++
    "sorry, and a solution module that proves them) would add one here."

/-- What the headline's comparison is and is not, in one sentence after the two file names. The
comparison itself runs no kernel; whether a kernel replay stands behind a verdict is said with
the verdict (`replayNoteText`) and in the replay band. -/
def headlineMethodText : String :=
  "Compared by this site's generator from the compiled modules of this build, which it does not \
    rebuild in a sandbox as lake comparator does. The comparison runs no kernel: a verdict says \
    \"proved\" only when a kernel replay accepted the theorem with everything it depends on."

private def headlineHtml (view : StatsPageView) : Output.Html :=
  match view.stats.headline with
  | Option.none => el "p" "bp_stats_headline_hint" (txt headlineHintText)
  | some h =>
    let source : Output.Html :=
      let challenge := code (h.challengeFile.getD h.challengeModule.toString)
      let solution := code (h.solutionFile.getD h.solutionModule.toString)
      -- what the comparison is and is not, only where one was made
      let method : Output.Html :=
        if h.unavailable.isSome then txt "."
        else .seq #[txt s!". {headlineMethodText}", meaningLink view]
      el "p" "bp_stats_headline_source" (.seq #[txt "Comparator challenge ", challenge,
        txt ", solution ", solution, method])
    let unavailable : Output.Html := match h.unavailable with
      | some u =>
        let detail := h.unavailableDetail.map (s!" ({·})") |>.getD ""
        el "p" "bp_stats_headline_unavailable" (txt s!"Not compared: {unavailableText u}{detail}")
      | Option.none => .empty
    let definitions : Output.Html :=
      if h.definitions.isEmpty then .empty
      else el "p" "bp_stats_headline_definitions" (.seq #[
        el "span" "bp_stats_caption" (txt "Definitions of the challenge"), txt " ",
        commaList (h.definitions.map fun d =>
          .seq #[code d.name.toString, txt s!" ({definitionVerdict d.solution})"])])
    let theorems : Output.Html :=
      if !h.theorems.isEmpty then .seq (h.theorems.map (headlineTheoremHtml view h))
      -- a challenge that could not be read states nothing either way
      else if h.unavailable.isSome then .empty
      else el "p" "bp_stats_headline_unavailable" (txt "The challenge states no theorem.")
    band "bp_stats_headline" "Headline result" #[unavailable, theorems, definitions, source]

/-! ## Kernel replay -/

/-- The token of a replay for markup: `accepted`, `rejected` or `none`. -/
def replayToken (replay? : Option Replay.Result) : String :=
  match replay?.map (·.outcome) with
  | some Replay.Outcome.accepted => "accepted"
  | some Replay.Outcome.rejected => "rejected"
  | _ => "none"

/-- What the page says when the generator ran no replay. -/
def noReplaySummary : String :=
  s!"Not replayed by a kernel: {Replay.noReplayText}. The marks on this site say what the \
    compiled files report."

/-- The band on the kernel replay: its result, the checker with its version, the checker's
message when it rejected the build or could not run, the declarations checked and those left
out, the axioms found, and what a replay leaves trusted. -/
private def replayHtml (view : StatsPageView) : Output.Html :=
  let replay? := view.stats.replay
  let token := replayToken replay?
  let summary := (replay?.map (·.summary)).getD noReplaySummary
  -- the checker's message; what kept a replay from a verdict is in the summary already
  let message : Output.Html := match replay?.filter (·.outcome == .rejected) |>.bind (·.message) with
    | some m => el "pre" "bp_stats_replay_message" (txt m)
    | Option.none => .empty
  let listed (cls caption : String) (items : Array Output.Html) : Output.Html :=
    if items.isEmpty then .empty
    else el "details" s!"bp_stats_more {cls}" (.seq #[
      .tag "summary" #[] (txt s!"{caption} ({formatCount items.size})"),
      el "ul" "bp_stats_files" (.seq (items.map fun item => .tag "li" #[] item))])
  let byName (names : Array Name) := names.qsort (·.toString < ·.toString)
  let modules : Output.Html := match replay? with
    | some r => .seq #[
        listed "bp_stats_replay_declarations"
          (if r.outcome == .accepted then
            "Declarations checked, each with everything it depends on"
          else "Declarations to check")
          ((byName r.declarations).map fun d => code d.toString),
        listed "bp_stats_replay_not_covered"
          "Declarations of the site that the replay does not cover"
          (r.notCovered.map fun (d, why) => .seq #[code d.toString, txt s!" {why}"]),
        listed "bp_stats_replay_axioms"
          "Declarations that depend on an axiom outside Lean's standard three, as the replay \
            found by walking the terms"
          (r.axioms.map fun (d, axioms) => .seq #[code d.toString,
            txt s!": {", ".intercalate (axioms.toList.map (·.toString))}"])]
    | Option.none => .empty
  -- the sentence that the replay accepted the build is itself a positive statement
  let scope := if token == "accepted" then s!" {StatusColors.replayAcceptedClass}" else ""
  let uncovered : Output.Html :=
    if view.notReplayed.isEmpty then .empty
    else el "details" "bp_stats_more bp_stats_replay_uncovered" (.seq #[
      .tag "summary" #[] (txt s!"Nodes with Lean code that is not part of the replay \
        ({formatCount view.notReplayed.size})"),
      el "ul" "bp_stats_files" (.seq (view.notReplayed.map fun label =>
        .tag "li" #[] (nodeLink view label)))])
  let resting : Output.Html :=
    if view.resting.isEmpty then .empty
    else el "details" "bp_stats_more bp_stats_replay_resting" (.seq #[
      .tag "summary" #[] (txt s!"Nodes without sorry whose Lean code rests on an axiom outside \
        Lean's standard three ({formatCount view.resting.size})"),
      el "ul" "bp_stats_files" (.seq (view.resting.map fun label =>
        .tag "li" #[] (nodeLink view label)))])
  band "bp_stats_replay" "Kernel replay" #[
    el "p" s!"bp_stats_lead bp_stats_replay_summary bp_stats_replay_{token}{scope}" (txt summary)
      #[("data-bp-replay", token)],
    message,
    modules,
    uncovered,
    resting,
    el "p" "bp_stats_replay_trusted" (txt Replay.trustedText)]

/-! ## Author's claims -/

/-- The claims the headline does not already show: those about declarations that are not
judged theorems. Each is shown with its declaration and, when a node has it, the node. -/
private def claimsHtml (view : StatsPageView) : Output.Html :=
  match view.stats.claims with
  | Option.none => .empty
  | some claims =>
    let judged : Array Name := (view.stats.headline.map (·.theorems.map (·.name))).getD #[]
    let rest := claims.claims.filter fun c => !judged.contains c.declaration
    let error : Output.Html := match claims.error with
      | some e => el "p" "bp_stats_claims_error" (txt s!"{claimsFile} could not be read: {e}")
      | Option.none => .empty
    if rest.isEmpty && claims.error.isNone then .empty else
    let items := rest.filterMap fun c => (claims.view? c.declaration).map fun v =>
      el "div" "bp_stats_claim_item" (.seq #[
        el "code" "bp_stats_theorem_name" (txt c.declaration.toString),
        v.render view.page.meaningHref]) #[("data-bp-claim-declaration", c.declaration.toString)]
    band "bp_stats_claims" "Author's claims" (#[error] ++ items)

/-! ## Progress -/

private def progressBar (c : ProgressCounts) (site : Replay.SiteState) : Output.Html :=
  let buckets := (progressBuckets c site).filter (·.count > 0)
  let description := ", ".intercalate (buckets.toList.map fun b => s!"{formatCount b.count} {b.label}")
  el "div" "bp_stats_bar" (.seq <| buckets.map fun b =>
    el "span" s!"bp_stats_seg bp_stats_status_{b.token}" .empty
      #[("style", s!"flex-grow: {b.count}"), ("data-bp-status", b.token),
        ("title", s!"{b.label}: {formatCount b.count}")])
    #[("role", "img"), ("aria-label", s!"{countOf c.total "node"}: {description}")]

private def progressLegend (c : ProgressCounts) (site : Replay.SiteState) : Output.Html :=
  el "ul" "bp_stats_legend" (.seq <| (progressBuckets c site).map fun b =>
    el "li" (if b.count == 0 then "bp_stats_legend_item bp_stats_legend_zero" else "bp_stats_legend_item")
      (.seq #[el "span" s!"bp_stats_swatch bp_stats_status_{b.token}" .empty #[("aria-hidden", "true")],
        txt s!"{b.label} ", el "strong" "bp_stats_legend_count" (txt (formatCount b.count))])
      #[("data-bp-status", b.token)])

private def chapterTable (rows : Array StatsChapterRow) (site : Replay.SiteState) : Output.Html :=
  if rows.isEmpty then .empty else
  let body := rows.map fun row =>
    let total := row.progress.total
    let done := row.progress.formalizedWithAncestors + row.progress.formalized
    .tag "tr" #[("data-bp-chapter", row.title)] (.seq #[
      el "td" "bp_stats_chapter_title" (.seq #[
        match row.number with
        | some n => el "span" "bp_stats_chapter_number" (txt n)
        | Option.none => .empty,
        link row.href (txt row.title)]),
      el "td" "bp_stats_num" (txt (formatCount total)),
      el "td" "bp_stats_chapter_bar" (progressBar row.progress site),
      el "td" "bp_stats_num" (txt s!"{formatCount done}/{formatCount total}")])
  el "table" "bp_stats_chapters" (.seq #[
    .tag "thead" #[] (.tag "tr" #[] (.seq #[
      .tag "th" #[("scope", "col")] (txt "Chapter"),
      el "th" "bp_stats_num" (txt "Nodes") #[("scope", "col")],
      .tag "th" #[("scope", "col")] (txt "Progress"),
      el "th" "bp_stats_num" (txt leanCompleteLabel) #[("scope", "col")]])),
    .tag "tbody" #[] (.seq body)])

/-- `n of m theorems` (or definitions), for the progress lines. -/
private def ofKind (n : Nat) (k : KindProgress) (noun : String) : String :=
  s!"{formatCount n} of {countOf k.total noun}"

/-- The sentence that counts nodes with Lean code free of `sorry`, by kind group. A definition
is never said to be proved, and a kind group without nodes is left out. -/
def leanCompleteText (p : LeanProgress) : String :=
  let parts :=
    (if p.theorems.total == 0 then [] else
      [ofKind p.theorems.leanComplete p.theorems "theorem"]) ++
    (if p.definitions.total == 0 then [] else
      [ofKind p.definitions.leanComplete p.definitions "definition"])
  if parts.isEmpty then "No nodes."
  else s!"{leanCompleteLabel} (no sorry in a node's Lean code or in what that code uses): \
    {", ".intercalate parts}."

/-- The sentence that counts informal statements. It never calls one checked. -/
def informalText (p : LeanProgress) : String :=
  if p.total == 0 then ""
  else if p.informal == 0 then
    "Informal statements: none. Every node shows its Lean code alone."
  else
    s!"Informal statements: {formatCount p.informal} of {countOf p.total "node"} \
      {if p.informal == 1 then "has" else "have"} one. \
      No tool has checked any of them against the Lean statements."

private def progressHtml (view : StatsPageView) : Output.Html :=
  let c := view.stats.progress
  let p := view.stats.leanProgress
  let kinds := joinKinds p
  let lead := if kinds.isEmpty then countOf c.total "node" else s!"{countOf c.total "node"}: {kinds}"
  let informal := informalText p
  let queue : Output.Html := match view.workQueueHref with
    | some href => el "p" "bp_stats_links_line" (.seq #[
        .tag "a" #[("href", href)] (txt s!"{workQueuePageTitle} ({formatCount view.workQueueSize})")])
    | Option.none => .empty
  -- what stands behind the counts, when it is not an accepted replay of every node
  let replayCounts : Output.Html :=
    if view.site.sentence.isEmpty then .empty
    else el "p" s!"bp_stats_progress_line bp_stats_replay_counts bp_stats_replay_counts_{view.site.token}"
      (txt view.site.sentence) #[("data-bp-progress", "replay")]
  band "bp_stats_progress" "How far along" #[
    el "p" "bp_stats_lead" (txt lead),
    el "p" "bp_stats_progress_line" (txt (leanCompleteText p)) #[("data-bp-progress", "lean")],
    if informal.isEmpty then .empty
    else el "p" "bp_stats_progress_line"
      (.seq #[txt informal, if p.informal == 0 then .empty else meaningLink view])
      #[("data-bp-progress", "informal")],
    replayCounts,
    progressBar c view.site,
    progressLegend c view.site,
    queue,
    chapterTable view.chapters view.site]
where
  joinKinds (p : LeanProgress) : String :=
    ", ".intercalate <|
      (if p.theorems.total == 0 then [] else [countOf p.theorems.total "theorem"]) ++
      (if p.definitions.total == 0 then [] else [countOf p.definitions.total "definition"])

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
    if sorries == 0 then "No Lean declaration of a node has a sorry of its own."
    else s!"{countOf sorries "Lean declaration"} of nodes with a sorry of \
      {if sorries == 1 then "its" else "their"} own."
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
    if t.isClear then "No node's Lean code uses sorry, an axiom outside Lean's standard three or " ++
      "the result of compiled code, as Lean reports the axioms of this build."
    else "Nodes whose Lean declarations rest on more than Lean's standard three axioms, as " ++
      "Lean reports the axioms of this build."
  band "bp_stats_trust" "What the Lean code rests on" #[
    el "p" "bp_stats_lead" (txt lead),
    el "table" "bp_stats_ledger" (.seq #[
      .tag "thead" #[] (.tag "tr" #[] (.seq #[
        .tag "th" #[("scope", "col")] (txt "Rests on"),
        el "th" "bp_stats_num" (txt "Nodes") #[("scope", "col")],
        .tag "th" #[("scope", "col")] (txt "Where")])),
      .tag "tbody" #[] (.seq #[
        trustRow view "sorry-direct" "a sorry of its own" (t.sorryDirect.map (·.label)),
        trustRow view "sorry-dependency" "sorry through a dependency"
          (t.sorryThroughDependency.map (·.label)),
        trustRow view "extra-axioms" "axioms beyond Lean's standard three" (t.extraAxioms.map (·.label)),
        trustRow view "compiler-trusted" "the result of compiled code (native_decide)"
          (t.compilerTrusted.map (·.label)),
        trustRow view "missing-declarations" "Lean names not found"
          (t.missingDeclarations.map (·.label)),
        trustRow view "unknown-references" "references to no node"
          (t.unknownReferences.foldl (init := #[]) fun acc r => acc ++ r.referencedBy)])])]

/-! ## What the marks mean -/

/-- The explanation of the marks: what each statement on a site reports, in the order a reader
meets them, ending with what no tool here checks. One short sentence each. -/
def meaningItems : Array (String × String) := #[
  ("Lean complete",
    "the node's Lean declarations, and everything they use, contain no sorry. The generator reads \
      this from the compiled modules, which is not a check by a kernel. Code that rests on an \
      axiom beyond Lean's standard three gets the warning mark, with the axiom named."),
  ("Green",
    "a success colour is drawn only where a kernel replay accepted the Lean code concerned: on a \
      node whose declarations the replay checked with everything they depend on, finding no \
      axiom outside Lean's standard three under them, and on counts, bars and legends only when \
      that holds for every node with Lean code that has no sorry. Everywhere else the same \
      statuses are drawn in grey, and after a rejected replay nothing is green."),
  ("Kernel replay, and the check mark on a node",
    "while this site was generated, the Lean declarations of its nodes and every constant they \
      depend on, in this project, in its dependencies and in Lean's own library, were exported \
      and checked again in Lean's kernel by the toolchain's leanchecker, starting from an empty \
      environment. A node has the check mark only when its Lean code is complete and the replay \
      accepted it; otherwise its mark is the diamond, which says what the compiled files \
      report. A file can keep Lean's kernel from seeing a declaration, in a project or in \
      something it depends on, and only a replay notices."),
  ("Axioms",
    "the axioms each declaration depends on, as Lean reports them for this build. propext, \
      Classical.choice and Quot.sound are Lean's standard three; a sorry, the result of compiled \
      code (native_decide) and any other axiom are named."),
  ("Lean statement proved, in the headline",
    "the solution states the same Lean terms as the Comparator challenge, without sorry and \
      without an axiom the challenge does not permit, and the kernel replay accepted the \
      solution's theorem with every constant it depends on. The comparison reads the compiled \
      modules of this build; lake comparator also rebuilds the project in a sandbox."),
  ("This build",
    "every report here is about the build the site was generated from, with the Lean version \
      and package revisions shown with the project's name. A port or an update is a different \
      build."),
  ("Not checked by any tool",
    "that a Lean statement says what an informal statement, a docstring or a manuscript says. \
      Informal text is shown with its source so that a reader can compare. An attestation \
      records that a named person says they compared them; it is not a check.")]

/-- The link a viewer that documents the marks itself may show beside the explanation: hidden
unless the viewer opts in with `<html data-lean-links>`, as the source links are. -/
def meaningViewerHref : String := "lean:help/marks"

private def meaningHtml : Output.Html :=
  el "section" "bp_stats_band bp_stats_meaning" (.seq #[
    el "h2" "bp_stats_band_title" (txt "What this page reports, and what it does not"),
    el "dl" "bp_stats_meaning_list" (.seq <| meaningItems.map fun item =>
      .seq #[.tag "dt" #[] (txt item.1), .tag "dd" #[] (txt item.2)]),
    el "p" "bp_stats_meaning_more" (.tag "a" #[("href", meaningViewerHref)]
      (txt "More in the viewer's guide"))])
    #[("id", Informal.Meaning.anchor)]

/-! ## The page -/

/-- The page body of a view. -/
def statsPageHtml (view : StatsPageView) : Output.Html :=
  let summary : Output.Html := match view.summaryHref with
    | some href => el "p" "bp_stats_summary_link" (.seq #[txt "Detailed breakdown: ",
        .tag "a" #[("href", href)] (txt summaryPageTitle)])
    | Option.none => .empty
  el "div" s!"bp_project_stats {view.site.scopeClass}" (.seq #[
    identityHtml view,
    headlineHtml view,
    replayHtml view,
    claimsHtml view,
    progressHtml view,
    sizeHtml view,
    buildHtml view,
    trustHtml view,
    meaningHtml,
    summary])
    #[("data-bp-schema-version", toString view.stats.schemaVersion),
      ("data-bp-replay-state", view.site.token)]

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

/-- The address of the explanation of the marks from another page of the site: the Project
Stats page's anchor, when the site has the page. -/
def meaningHref? (state : TraverseState) : Option String :=
  (pageSection? (siteSections state) "Project Stats").map fun s =>
    String.join (s.link.path.toList.map (· ++ "/")) ++ "#" ++ Informal.Meaning.anchor

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
  -- the replay of the statistics the page reports on
  let replays := Informal.ReplayView.Index.buildWith state stats.replay
  {
    stats, page, chapters, nodes
    site := replays.siteState
    notReplayed := replays.uncovered
    resting := replays.resting
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
