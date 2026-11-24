/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

import VersoManual
import VersoBlueprint.CodeSite.Highlight
import VersoBlueprint.Commands.Stats
import VersoBlueprint.DeclarationSource
import VersoBlueprint.Informal.ExternalCode
import VersoBlueprint.RepoFile
import VersoBlueprint.Stats.ComparatorLayout

/-!
The Comparator pages of a site: a page "Comparator" that lists the project's Comparator
challenges with their verdicts, and below it one page per challenge
(`Informal.Stats.ComparatorLayout`) with the challenge and the solution in full, highlighted with
hovers as the side-by-side Lean column is, its `comparator.json` in full, its verdict, the axioms
its solution rests on, what stays trusted, and links: each file's source at the commit the site
is built from, the continuous-integration run that built the site, the dependency graph's node of
each judged theorem and the Project Stats page.

Every verdict on these pages is drawn from the same statistics as the Project Stats page's
headline, by the same code (`challengeBandHtml`, `headlineVerdict`): a page never computes a
verdict of its own. A challenge that was not compared says so, with the reason the headline
records.

The pages are added by the generators when the project has challenges (`withComparatorPages`),
with the files read when the site is generated (`challengePages`), each at most
`ComparatorLayout.leanFileLimit` or `ComparatorLayout.configLimit` bytes. File contents and names
are the project's data and are only ever shown as text: escaped, never run.
-/

namespace Informal.Commands

open Lean
open Informal.Stats
open Verso Doc Html Genre Manual
open Verso.Output.Html
open Verso.Multi (AllRemotes)

/-! ## The pages' data -/

/-- A file of a challenge as a page shows it. -/
structure ComparatorFile where
  /-- The path, relative to the project root. -/
  path : String
  /-- The text, in full. -/
  text : String := ""
  /-- Why the text is not there, when it is not. -/
  missing : Option String := none
  /-- The file in the project's repository at the commit the site is built from. -/
  href : Option String := none
deriving Inhabited, Repr, ToJson, FromJson

/-- One challenge's page. -/
structure ChallengePageData where
  /-- The challenge's name: its folder under `Comparator/`. -/
  name : String
  challenge : ComparatorFile
  solution : ComparatorFile
  config : ComparatorFile
  challengeModule : Name
  solutionModule : Name
  /-- The challenge's code highlighted by the generator, when it highlights it itself (a site from
  compiled-code data); otherwise the page takes the module's highlighted source. -/
  challengeCode : Option SubVerso.Highlighting.Highlighted := none
  /-- The solution's code, as `challengeCode`. -/
  solutionCode : Option SubVerso.Highlighting.Highlighted := none
  /-- The continuous-integration run that built the site, when it ran in one. -/
  ciRun : Option String := none
deriving Inhabited, ToJson, FromJson

/-- The data of the index page: the challenges' names. -/
structure ComparatorIndexData where
  names : Array String := #[]
deriving Inhabited, Repr, ToJson, FromJson

/-! ## The words -/

/-- What a challenge's page is, in its first paragraph. -/
def challengePageIntroText (name : String) : String :=
  s!"The Comparator challenge {name}: the challenge file states the theorems with sorry as \
    their proofs, the solution file proves them, and comparator.json says which theorems are \
    judged and which axioms a proof may use. The verdict is the one the Project Stats page shows \
    for this challenge, from the same comparison and the same kernel replay."

/-- The sentence before what a kernel replay leaves trusted. -/
def challengeTrustedCaption : String := "What a verdict of the kernel replay leaves trusted"

/-- The caption of a file shown with its syntax colours only. -/
def plainHighlightText : String :=
  "Shown with syntax colours only: no highlighted build of this module matches the file."

/-- The sentence for a challenge the statistics have no result for. -/
def challengeWithoutResultText : String :=
  "Not compared: the site's statistics hold no result for this challenge."

/-- The sentence of the link to the run that built the site. -/
def ciRunText : String := "The continuous-integration run that built this site"

/-- The index page's first paragraph. -/
def comparatorIndexIntroText : String :=
  "The project's Comparator challenges. Each states theorems in a challenge file and proves them \
    in a solution file; lake comparator, run from the project root with \
    --config Comparator/<Name>/comparator.json, judges a solution against its challenge. The \
    verdicts below are the ones the Project Stats page shows, from the same comparison and the \
    same kernel replay."

/-- The caption of a file's source link. -/
def sourceLinkText : String := "source at the commit this site is built from"

/-! ## Reading the files -/

/-- The address of `path` (relative to the project root `root`) in the project's repository at the
commit the site is built from, when `root` is in a Git checkout with a GitHub `origin` and the
repository tracks the file. -/
def repositoryHref? (root : System.FilePath) (path : String) : IO (Option String) := do
  let some top ← Informal.Git.toplevelAt? root | return none
  let realRoot ← (try IO.FS.realPath root catch _ => pure root)
  let realTop ← (try IO.FS.realPath top catch _ => pure top)
  let rootText := realRoot.toString
  let topText := realTop.toString
  let repoPath ← if rootText == topText then pure path
    else if rootText.startsWith (topText ++ "/") then
      pure ((rootText.drop (topText.length + 1)).toString ++ "/" ++ path)
    else return none
  -- a file the repository does not track has no address there
  let tracked ← Informal.Process.runTrimmedCommand? "git"
    #["-C", topText, "ls-files", "--error-unmatch", "--", repoPath]
  if tracked.isNone then return none
  Informal.RepoFile.href? root repoPath

/-- The continuous-integration run that is building the site: in GitHub Actions, from
`GITHUB_SERVER_URL`, `GITHUB_REPOSITORY` and `GITHUB_RUN_ID`, when all three are there and
well-formed (an `https://` server without anything but a host, a repository `owner/name` of
letters, digits, `-`, `_` and `.`, and a numeric run). None elsewhere. -/
def ciRunHref? : IO (Option String) := do
  let (some server, some repo, some run) :=
      (← IO.getEnv "GITHUB_SERVER_URL", ← IO.getEnv "GITHUB_REPOSITORY", ← IO.getEnv "GITHUB_RUN_ID")
    | return none
  let host := (server.drop 8).toString
  let hostOk := server.startsWith "https://" && !host.isEmpty &&
    host.all fun c => c.isAlphanum || c == '.' || c == '-'
  let parts := repo.splitOn "/"
  let repoOk := parts.length == 2 && parts.all (fun p => !p.isEmpty && p != "." && p != "..") &&
    repo.all fun c => c.isAlphanum || c == '-' || c == '_' || c == '.' || c == '/'
  let runOk := !run.isEmpty && run.all Char.isDigit
  if hostOk && repoOk && runOk then return some s!"{server}/{repo}/actions/runs/{run}"
  return none

/-- A file of the project as a page shows it, read with `limit`. -/
def comparatorFile (root : System.FilePath) (path : String) (limit : Nat) : IO ComparatorFile := do
  let href ← repositoryHref? root path
  match ← ComparatorLayout.readLimited (root / path) limit with
  | .ok content => return { path, text := content, href }
  | .error why => return { path, missing := some why, href }

/-- The pages of the challenges of `stats`, the files read under the project root `root`.
`codeOf` gives a module's highlighted code from its text when the generator highlights it itself.
-/
def challengePages (stats : ProjectStats) (root : System.FilePath)
    (codeOf : Name → String → Option SubVerso.Highlighting.Highlighted := fun _ _ => none) :
    IO (Array ChallengePageData) := do
  let ciRun ← ciRunHref?
  stats.challenges.mapM fun h => do
    let folder := ComparatorLayout.folderOf h.name
    let challenge ← comparatorFile root (h.challengeFile.getD s!"{folder}/{ComparatorLayout.challengeFileName}")
      ComparatorLayout.leanFileLimit
    let solution ← comparatorFile root (h.solutionFile.getD s!"{folder}/{ComparatorLayout.solutionFileName}")
      ComparatorLayout.leanFileLimit
    let config ← comparatorFile root (h.config.getD s!"{folder}/{comparatorConfigFile}")
      ComparatorLayout.configLimit
    return {
      name := h.name, challenge, solution, config
      challengeModule := h.challengeModule, solutionModule := h.solutionModule
      challengeCode := codeOf h.challengeModule challenge.text
      solutionCode := codeOf h.solutionModule solution.text
      ciRun }

/-! ## Rendering -/

private def txt (s : String) : Output.Html := .text s

private def el (tag cls : String) (content : Output.Html)
    (attrs : Array (String × String) := #[]) : Output.Html :=
  .element tag (#[("class", cls)] ++ attrs) content

/-- A label as a fragment value: every byte outside the unreserved characters percent-encoded. -/
def percentEncode (s : String) : String :=
  let hex := "0123456789ABCDEF".toList.toArray
  String.join <| s.toUTF8.toList.map fun byte =>
    let b := byte.toNat
    let c := Char.ofNat b
    if b < 128 && (c.isAlphanum || c == '-' || c == '_' || c == '.' || c == '~') then c.toString
    else String.ofList ['%', hex[b / 16]!, hex[b % 16]!]

/-- Whether highlighted code is the file's text exactly, line endings and trailing white space
aside. -/
def codeMatches (code : SubVerso.Highlighting.Highlighted) (text : String) : Bool :=
  let norm := fun (t : String) => (t.replace "\r\n" "\n").trimAsciiEnd.toString
  norm code.toString == norm text

/-- The highlighted code of a challenge's file: the generator's, else the module's highlighted
build when it matches the file, else the file with syntax colours only (and the caption that says
so). -/
def fileCode (file : ComparatorFile) (mod : Name)
    (supplied : Option SubVerso.Highlighting.Highlighted) :
    IO (SubVerso.Highlighting.Highlighted × Bool) := do
  if let some code := supplied then
    if codeMatches code file.text then return (code, true)
  if let some code ← Informal.DeclarationSource.moduleCode? mod then
    if codeMatches code file.text then return (code, true)
  return (Informal.CodeSite.Highlight.highlightPlain file.text, false)

/-- A file's section: its title, its path linked to its source, and its text in full. -/
def fileSectionHtml {m : Type → Type} [Monad m] [MonadLiftT IO m] (title : String) (file : ComparatorFile)
    (lean? : Option (Name × Option SubVerso.Highlighting.Highlighted)) (id : String) :
    Verso.Doc.Html.HtmlT Verso.Genre.Manual m Output.Html := do
  let pathHtml : Output.Html := match file.href with
    | some href => .seq #[
        .element "a" #[("href", href), ("class", "bp_comparator_source_link")] (.element "code" #[] (txt file.path)),
        txt s!" ({sourceLinkText})"]
    | Option.none => .element "code" #[] (txt file.path)
  let body ← match file.missing, lean? with
    | some why, _ => pure (el "p" "bp_comparator_missing" (txt s!"The file cannot be shown: {why}."))
    | Option.none, some (mod, supplied) => do
      let (code, full) ← (fileCode file mod supplied : IO _)
      let rendered ← Informal.ExternalCode.renderSourceWithPageHovers code "bp_comparator_source"
      -- every token with a hover is reachable by the keyboard: the page's hovers open on focus
      let rendered := match rendered with
        | .raw html =>
          .raw (html.replace " data-verso-hover=\"" " tabindex=\"0\" data-verso-hover=\"")
        | other => other
      pure <| .seq #[
        if full then .empty else el "p" "bp_comparator_plain_note" (txt plainHighlightText),
        el "div" "bp_comparator_code" rendered]
    | Option.none, Option.none =>
      pure (el "pre" "bp_comparator_config" (.element "code" #[] (txt file.text)))
  pure <| el "section" "bp_comparator_file" (.seq #[
      el "h2" "bp_comparator_file_title" (txt title),
      el "p" "bp_comparator_file_path" pathHtml,
      body]) #[("id", id)]

/-- The links of a challenge's page: the dependency graph's node of each judged theorem, the
Project Stats page, and the run that built the site. -/
def challengeLinksHtml (state : TraverseState) (h : Headline)
    (ciRun : Option String) : Output.Html :=
  let sections := siteSections state
  let graph? := (pageSection? sections "Dependency Graph").map (·.link.relativeLink)
  let stats? := (pageSection? sections statsPageTitle).map (·.link.relativeLink)
  let nodes := h.theorems.filterMap fun t => t.node.map fun label => (t.name, label)
  let nodeLinks := nodes.filterMap fun (name, label) => graph?.map fun g =>
    let base := (g.splitOn "#").head!
    .element "li" #[] (.seq #[
      .element "a" #[("href", s!"{base}#ego={percentEncode label.toString}&k=1"),
                     ("class", "bp_comparator_graph_link")]
        (txt s!"{name} in the dependency graph")])
  let items := nodeLinks ++
    (stats?.map fun href => #[.element "li" #[] (.element "a"
      #[("href", href), ("class", "bp_comparator_stats_link")] (txt statsPageTitle))]).getD #[] ++
    (ciRun.map fun href => #[.element "li" #[] (.element "a"
      #[("href", href), ("class", "bp_comparator_ci_link")] (txt ciRunText))]).getD #[]
  if items.isEmpty then .empty
  else el "section" "bp_comparator_links" (.seq #[
    el "h2" "bp_comparator_file_title" (txt "Links"),
    el "ul" "bp_comparator_link_list" (.seq items)])

/-- A challenge's page body. -/
def challengePageHtml {m : Type → Type} [Monad m] [MonadLiftT IO m] (data : ChallengePageData) (view : StatsPageView)
    (state : TraverseState) : Verso.Doc.Html.HtmlT Verso.Genre.Manual m Output.Html := do
  let verdict : Output.Html := match view.stats.challenges.find? (·.name == data.name) with
    | some h => .seq #[challengeBandHtml view h (several := false) (pageLink := false),
        el "section" "bp_comparator_trusted" (.seq #[
          el "h2" "bp_comparator_file_title" (txt challengeTrustedCaption),
          el "p" "bp_stats_replay_trusted" (txt Replay.trustedText)])]
    | Option.none => el "p" "bp_stats_headline_unavailable" (txt challengeWithoutResultText)
  let challenge ← fileSectionHtml "Challenge" data.challenge
    (some (data.challengeModule, data.challengeCode)) "challenge-file"
  let solution ← fileSectionHtml "Solution" data.solution
    (some (data.solutionModule, data.solutionCode)) "solution-file"
  let config ← fileSectionHtml "Configuration" data.config none "comparator-config"
  let links := match view.stats.challenges.find? (·.name == data.name) with
    | some h => challengeLinksHtml state h data.ciRun
    | Option.none => .empty
  pure <| el "div" s!"bp_comparator_page bp_project_stats {view.site.scopeClass}" (.seq #[
      el "p" "bp_comparator_intro" (txt (challengePageIntroText data.name)),
      verdict, challenge, solution, config, links])
    #[("data-bp-challenge", data.name), ("data-bp-replay-state", view.site.token)]

/-- The index page body: each challenge with a link to its page and the verdict of each judged
theorem, in the words of the Project Stats page. -/
def comparatorIndexHtml (view : StatsPageView) : Output.Html :=
  let rows := view.stats.challenges.map fun h =>
    let title : Output.Html := match view.challengeHrefs.find? (·.1 == h.name) with
      | some (_, href) => .element "a" #[("href", href), ("class", "bp_comparator_index_link")]
          (txt h.name)
      | Option.none => txt h.name
    let verdicts : Output.Html := match h.unavailable with
      | some u =>
        el "p" "bp_stats_headline_unavailable" (txt (notComparedText u h.unavailableDetail))
      | Option.none =>
        el "ul" "bp_comparator_verdicts" (.seq (h.theorems.map fun t =>
          let standing := headlineStanding view.stats.replay h t
          let (token, words) := headlineVerdict t standing view.stats.replay
          el "li" s!"bp_comparator_verdict {standing.scopeClass}" (.seq #[
            el "code" "bp_stats_theorem_name" (txt t.name.toString), txt " ",
            el "span" s!"bp_stats_verdict bp_stats_verdict_{token}" (txt words)])
            #[("data-bp-theorem", t.name.toString), ("data-bp-verdict", token)]))
    el "section" "bp_comparator_index_item" (.seq #[
      el "h2" "bp_comparator_index_title" title,
      el "p" "bp_comparator_index_modules" (.seq #[
        .element "code" #[] (txt h.challengeModule.toString), txt " and ",
        .element "code" #[] (txt h.solutionModule.toString)]),
      verdicts]) #[("data-bp-challenge", h.name)]
  el "div" s!"bp_comparator_index bp_project_stats {view.site.scopeClass}" (.seq (#[
    el "p" "bp_comparator_intro" (txt comparatorIndexIntroText)] ++ rows))
    #[("data-bp-replay-state", view.site.token)]

/-! ## The blocks and the pages -/

def comparatorCss : String := include_str "comparator.css"

/-- What both blocks need from the traversal: the statistics' view, or nothing after reporting
why. -/
private def statsView? :
    HtmlT Manual (ReaderT AllRemotes (ReaderT ExtensionImpls (BuildLogT IO))) (Option StatsPageView) := do
  let s ← HtmlT.state
  let stats ← match Informal.TraversalIndex.RenderOverviews.required (α := ProjectStats) s `stats with
    | .ok stats => pure (some stats)
    | .error message => Verso.reportError message; pure none
  let graph ← match Informal.TraversalIndex.RenderOverviews.required (α := Graph.GraphModel) s `graph with
    | .ok graph => pure (some graph)
    | .error message => Verso.reportError message; pure none
  let (some stats, some graph) := (stats, graph) | pure none
  pure (some (StatsPageView.build s stats graph { meaningHref := meaningHref? s }))

block_extension Block.comparatorIndex (data : ComparatorIndexData) where
  data := toJson data
  traverse _id _data _contents := pure none
  toTeX := some fun _goI _goB _id _data _blocks =>
    pure <| .text "The Comparator challenges are listed in the HTML output."
  toHtml := some fun _goI _goB _id _json _blocks => do
    let some view ← statsView? | pure .empty
    pure (comparatorIndexHtml view)
  extraCss := statsAssetBundle.css ++ [comparatorCss]
  extraJs := statsAssetBundle.js

block_extension Block.comparatorChallenge (data : ChallengePageData) where
  data := toJson data
  traverse _id _data _contents := pure none
  toTeX := some fun _goI _goB _id _data _blocks =>
    pure <| .text "The Comparator challenge's files are shown in the HTML output."
  toHtml := some fun _goI _goB _id json _blocks => do
    let some data ← Informal.ExtensionDecode.decode? (α := ChallengePageData) json
        (fun err => s!"Malformed data in Block.comparatorChallenge.toHtml ({err})")
      | pure .empty
    let some view ← statsView? | pure .empty
    challengePageHtml data view (← HtmlT.state)
  extraCss := statsAssetBundle.css ++ [comparatorCss]
  extraJs := statsAssetBundle.js

/-- An unnumbered page. -/
private def unnumberedPart (title : String) (content : Array (Doc.Block Manual))
    (subParts : Array (Part Manual) := #[]) : Part Manual :=
  { title := #[.text title], titleString := title, metadata := some { number := false }
    content, subParts }

/-- The document with the Comparator pages at the end of its table of contents: the page
`comparatorPageTitle` listing the challenges, with a page for each below it. Without challenges,
the document as it is. -/
def withComparatorPages (text : Part Manual) (pages : Array ChallengePageData) : Part Manual :=
  if pages.isEmpty then text else
  let challengeParts := pages.map fun page =>
    unnumberedPart page.name #[.other (Block.comparatorChallenge page) #[]]
  let index := unnumberedPart comparatorPageTitle
    #[.other (Block.comparatorIndex { names := pages.map (·.name) }) #[]] challengeParts
  { text with subParts := text.subParts.push index }

end Informal.Commands
