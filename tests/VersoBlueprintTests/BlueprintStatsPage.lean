/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

import VersoBlueprint
import VersoBlueprint.PreviewManifest
import VersoBlueprintTests.Blueprint.Support

/-!
The Project Stats page: the formatting helpers, the rendered bands of a view (identity, headline
card or hint, progress, size, build, trust ledger, summary link), the page in a rendered
document, and the page that generators add to every site (and leave out when asked).
-/

namespace Verso.VersoBlueprintTests.BlueprintStatsPage

open Lean
open Verso Genre Manual
open Informal
open Informal.Commands
open Informal.Stats
open Verso.VersoBlueprintTests.Blueprint.Support

set_option doc.verso true

-- Formatting

/-- info: true -/
#guard_msgs in
#eval
  formatCount 0 == "0" && formatCount 999 == "999" && formatCount 1000 == "1,000" &&
    formatCount 13616 == "13,616" && formatCount 1234567 == "1,234,567" &&
    percentOf 54 58 == 93 && percentOf 57 58 == 98 && percentOf 58 58 == 100 && percentOf 0 0 == 0 &&
    countOf 1 "theorem" == "1 theorem" && countOf 2133 "line" == "2,133 lines" &&
    countOf 3 "corollary" == "3 corollaries" &&
    toolchainVersion "leanprover/lean4:v4.35.0\n" == "v4.35.0" && toolchainVersion "v4.9.0" == "v4.9.0"

/-- info: true -/
#guard_msgs in
#eval
  let proved : HeadlineTheorem := { name := `main, solution := .same, sorryFree := some true, proved := true }
  let withSorry : HeadlineTheorem := { name := `main, solution := .same, sorryFree := some false }
  let differs : HeadlineTheorem :=
    { name := `main, solution := .differs, difference := some "the statement differs",
      differingDeclaration := some `main }
  (headlineVerdict proved).1 == "proved" && (headlineVerdict withSorry).1 == "sorry" &&
    (headlineVerdict differs).2 == "Statement differs: the statement differs (main)" &&
    (headlineVerdict { name := `main, solution := .missing }).1 == "missing"

-- Chapters follow their numbers, the unnumbered ones last, in the order they came in.
/-- info: true -/
#guard_msgs in
#eval
  let rows : Array StatsChapterRow := #[
    { title := "Five", number := some "5" }, { title := "Appendix" }, { title := "Ten", number := some "10" },
    { title := "Two", number := some "2" }, { title := "Notes" }]
  (sortChapterRows rows).map (·.title) == #["Two", "Five", "Ten", "Appendix", "Notes"]

-- A view

private def rokickiLike : ProjectStats := {
  identity := {
    name := some "RokickiConstant"
    title := some "Rokicki's constant is irrational"
    description := some "A Lean 4 proof that Rokicki's constant is irrational."
    license := some { file := "LICENSE", spdx := some "Apache-2.0" }
    toolchain := some "leanprover/lean4:v4.35.0"
    packages := #[
      { name := "mathlib", source := "git", rev := some "56a00585aaaaaaaa", inputRev := some "v4.35.0" },
      { name := "batteries", source := "git", rev := some "66e46918", inherited := true }]
  }
  modules := #[{ name := `A, path := "A.lean", declarations := 3 }]
  declarations := { theorems := 73, definitions := 22 }
  sources := {
    files := #[
      { path := "A.lean", status := .imported },
      { path := "Comparator/Challenge.lean", status := .compiled },
      { path := "scripts/Probe.lean", status := .notBuilt }]
    lines := { blank := 378, comment := 402, code := 1353 }
  }
  progress := { formalizedWithAncestors := 54, formalized := 2, incomplete := 1, ready := 1 }
  graph := { nodes := 58, statementEdges := 62, proofEdges := 84, edges := 146,
             byKind := #[("definition", 10), ("lemma", 40), ("theorem", 8)] }
  headline := some {
    challengeModule := `Comparator.Challenge
    solutionModule := `Comparator.Solution
    challengeFile := some "Comparator/Challenge.lean"
    solutionFile := some "Comparator/Solution.lean"
    theorems := #[{
      name := `rho_irrational
      docstring := some "Rokicki's constant is irrational."
      statement := "theorem rho_irrational : Irrational rho"
      solution := .same, sorryFree := some true, proved := true
      axioms := #[``Classical.choice, ``Quot.sound, ``propext]
      node := some `main }]
    definitions := #[{ name := `rho, solution := .same }]
  }
  hasComparatorChallenge := true
}

private def view (stats : ProjectStats) : StatsPageView := {
  stats
  page := { links := #[{ label := "GitHub", href := "https://example.org/repo" }] }
  chapters := #[
    { title := "Binary expansions", number := some "1", href := some "/Binary/#binary",
      progress := { formalizedWithAncestors := 10 } },
    { title := "Character sums", number := some "3", href := some "/Sums/#sums",
      progress := { formalizedWithAncestors := 16, incomplete := 1, ready := 1 } }]
  nodes := #[{ label := `main, title := "Theorem 6.1", href := some "/Main/#main" },
             { label := `lem, title := "Lemma 3.2", href := some "/Sums/#lem" }]
  workQueueSize := 1
  summaryHref := some "/Blueprint-Summary/#blueprint-summary"
  workQueueHref := some "/Ready-to-Prove/#ready-to-prove"
}

-- Identity, headline, progress, size and build bands of a project with a proved challenge.
/-- info: true -/
#guard_msgs in
#eval
  let html := (statsPageHtml (view rokickiLike)).asString
  hasSubstr html "class=\"bp_project_stats\"" &&
    hasSubstr html "Rokicki's constant is irrational</p>" && hasSubstr html "class=\"bp_stats_name\"" &&
    hasSubstr html "License: Apache-2.0" && hasSubstr html "Lean v4.35.0" &&
    -- direct dependencies only, with the revision asked for and the locked commit
    hasSubstr html "data-bp-package=\"mathlib\"" && hasSubstr html "v4.35.0 · 56a0058" &&
    !hasSubstr html "data-bp-package=\"batteries\"" &&
    hasSubstr html "<a href=\"https://example.org/repo\">GitHub</a>" &&
    -- the headline card
    hasSubstr html "class=\"bp_stats_band bp_stats_headline\"" &&
    hasSubstr html "data-bp-theorem=\"rho_irrational\" data-bp-verdict=\"proved\"" &&
    hasSubstr html "<a href=\"/Main/#main\">Theorem 6.1</a>" &&
    hasSubstr html "theorem rho_irrational : Irrational rho" &&
    hasSubstr html "the standard axioms of Lean's logic only" &&
    hasSubstr html "<code>Comparator/Challenge.lean</code>" &&
    hasSubstr html "<code>rho</code> (same)" &&
    !hasSubstr html headlineHintText &&
    -- progress: counts as text, a segment per non-empty status, the per-chapter table
    hasSubstr html "58 nodes · 93% fully proved" &&
    hasSubstr html "style=\"flex-grow: 54\" data-bp-status=\"fully-proved\"" &&
    !hasSubstr html "data-bp-status=\"not-ready\" title=" &&
    hasSubstr html "aria-label=\"58 nodes: 54 fully proved, 2 proved, open ancestors, 1 Lean code incomplete, 1 ready to formalize\"" &&
    hasSubstr html "<a href=\"/Ready-to-Prove/#ready-to-prove\">Ready to Prove (1)</a>" &&
    hasSubstr html "data-bp-chapter=\"Character sums\"" && hasSubstr html "16/18" &&
    -- size and build
    hasSubstr html "2,133" && hasSubstr html "1,353 code lines · 402 comment lines · 378 blank lines" &&
    hasSubstr html "73 theorems · 22 definitions" && hasSubstr html "10 definitions · 40 lemmas · 8 theorems" &&
    hasSubstr html "2 of 3 Lean files compiled: 1 imported by the site, 1 built by another target." &&
    hasSubstr html "1 Lean file on disk in no build:" && hasSubstr html "<code>scripts/Probe.lean</code>" &&
    hasSubstr html "No declaration has a sorry of its own." &&
    -- trust and the summary link
    hasSubstr html "Nothing in the ledger limits trust" &&
    hasSubstr html "data-bp-trust=\"sorry-direct\" data-bp-count=\"0\"" &&
    hasSubstr html "Detailed breakdown: <a href=\"/Blueprint-Summary/#blueprint-summary\">Blueprint Summary</a>" &&
    appearsBefore html "bp_stats_identity" "bp_stats_headline" &&
    appearsBefore html "bp_stats_headline" "bp_stats_progress" &&
    appearsBefore html "bp_stats_progress" "bp_stats_size" &&
    appearsBefore html "bp_stats_size" "bp_stats_build" &&
    appearsBefore html "bp_stats_build" "bp_stats_trust" &&
    appearsBefore html "bp_stats_trust" "bp_stats_summary_link"

-- Without a Comparator challenge there is no card, only the one-line hint; no license file shows.
/-- info: true -/
#guard_msgs in
#eval
  let stats := { rokickiLike with
    headline := none, hasComparatorChallenge := false
    identity := { rokickiLike.identity with license := none } }
  let html := (statsPageHtml (view stats)).asString
  hasSubstr html "class=\"bp_stats_headline_hint\"" && hasSubstr html headlineHintText &&
    !hasSubstr html "bp_stats_band bp_stats_headline" && !hasSubstr html "data-bp-theorem" &&
    hasSubstr html "No license file"

-- A ledger with open rows lists the nodes with links; a theorem with a sorry gets its verdict.
/-- info: true -/
#guard_msgs in
#eval
  let trust : TrustLedger := {
    sorryDirect := #[{ label := `lem, declaration := `lem_decl, axioms := #[``sorryAx] }]
    sorryThroughDependency := #[{ label := `main, declaration := `main_decl, axioms := #[``sorryAx] },
      { label := `main, declaration := `main_other, axioms := #[``sorryAx] }]
    compilerTrusted := #[{ label := `lem, declaration := `lem_decl, axioms := #[`lem_decl._native.native_decide.ax_1_1] }]
  }
  let headline := rokickiLike.headline.map fun h => { h with theorems := h.theorems.map fun t =>
    { t with proved := false, sorryFree := some false, axioms := t.axioms.push ``sorryAx } }
  let html := (statsPageHtml (view { rokickiLike with trust, headline })).asString
  hasSubstr html "1 declaration with a sorry of its own." &&
    hasSubstr html "data-bp-trust=\"sorry-direct\" data-bp-count=\"1\"" &&
    hasSubstr html "<a href=\"/Sums/#lem\">Lemma 3.2</a>" &&
    -- a node is listed once, however many of its declarations are on the row
    hasSubstr html "data-bp-trust=\"sorry-dependency\" data-bp-count=\"1\"" &&
    hasSubstr html "data-bp-trust=\"compiler-trusted\" data-bp-count=\"1\"" &&
    hasSubstr html "data-bp-trust=\"extra-axioms\" data-bp-count=\"0\"" &&
    !hasSubstr html "Nothing in the ledger limits trust" &&
    hasSubstr html "data-bp-verdict=\"sorry\"" && hasSubstr html "Same statement; the proof uses sorry" &&
    hasSubstr html "data-bp-axiom-class=\"sorry\"" &&
    !hasSubstr html "the standard axioms of Lean's logic only"

-- Many files in no build: the first ones are listed, the rest folded away.
/-- info: true -/
#guard_msgs in
#eval
  let files := (List.range 11).toArray.map fun i =>
    ({ path := s!"Extra/F{i}.lean", status := .notBuilt } : SourceFile)
  let html := (statsPageHtml (view { rokickiLike with sources := { files } })).asString
  hasSubstr html "11 Lean files on disk in no build:" && hasSubstr html "<summary>and 3 more</summary>" &&
    hasSubstr html "<code>Extra/F10.lean</code>" &&
    hasSubstr html "0 of 11 Lean files compiled: 0 imported by the site."

-- The page in a document

#docs (Genre.Manual) statsDoc "Stats Doc" :=
:::::::
:::definition "st.base"
A base definition.
:::

:::theorem "st.top" (uses := "st.base")
A theorem.
:::

{blueprint_stats}
:::::::

-- The block renders the captured statistics; the node count is the model's.
/-- info: true -/
#guard_msgs in
#eval
  show IO Bool from do
    let model : RenderModel := blueprint_render_model%
    let out ← renderManualDocHtmlString extension_impls% statsDoc (model := model)
    let total := model.stats.progress.total
    pure (
      hasSubstr out "class=\"bp_project_stats\"" &&
      hasSubstr out s!"{countOf total "node"} · " &&
      hasSubstr out "class=\"bp_stats_band bp_stats_trust\"" &&
      total ≥ 2)

-- The page on every site

-- The page is added once, at the end of the table of contents, unnumbered.
/-- info: true -/
#guard_msgs in
#eval
  let chapter : Doc.Part Manual := ⟨#[], "Chapter", Option.none, #[], #[]⟩
  let text : Doc.Part Manual := ⟨#[], "Root", Option.none, #[], #[chapter]⟩
  let once := withStatsPage text { links := #[{ label := "Paper", href := "https://example.org" }] }
  let twice := withStatsPage once
  !hasStatsPage text && hasStatsPage once &&
    once.subParts.map (·.titleString) == #["Chapter", statsPageTitle] &&
    twice.subParts.size == 2 &&
    (once.subParts.back?.bind (·.metadata) |>.map (·.number)) == some false

-- A document that places the page keeps it in place, with the generator's data filled in.
/-- info: true -/
#guard_msgs in
#eval
  let text := statsDoc.toPart
  let filled := withStatsPage text { links := #[{ label := "Paper", href := "https://example.org" }] }
  let rec blocks (p : Doc.Part Manual) : Array (Doc.Block Manual) := p.content ++ p.subParts.flatMap blocks
  let data := (blocks filled).filterMap fun
    | .other b _ => if b.name == ``Block.projectStats then some b.data else none
    | _ => none
  filled.subParts.size == text.subParts.size &&
    data.size == 1 && (data[0]!.compress.splitOn "example.org").length > 1

private partial def freshRoot (name : String) : IO System.FilePath := do
  let root := (← IO.currentDir) / ".lake" / "build" / "tmp" / name / toString (← IO.rand 0 1000000000000)
  if ← root.pathExists then freshRoot name else pure root

#docs (Manual) siteDoc "Stats Site" :=
:::::::
# Sums

:::definition "site.base"
A base definition.
:::

:::theorem "site.top" (uses := "site.base")
A theorem.
:::
:::::::

-- `blueprintMain` adds the page to the site's table of contents, with the chapter's progress row;
-- `--no-stats-page` and `statsPage := false` leave it out.
/-- info: true -/
#guard_msgs in
#eval
  show IO Bool from do
    let root ← freshRoot "verso-blueprint-stats-page-test"
    let build (dir : String) (flags : List String) (statsPage : Bool) : IO UInt32 :=
      Informal.PreviewManifest.blueprintMain siteDoc.toPart
        (extensionImpls := by exact extension_impls%)
        (options := ["--output", (root / dir).toString, "--without-html-single"] ++ flags)
        (statsPage := statsPage)
        (sidebar? := some { links := #[{ label := "Repository", href := "https://example.org/repo" }] })
    let c1 ← build "on" [] true
    let c2 ← build "flag" [noStatsPageFlag] true
    let c3 ← build "off" [] false
    let page := root / "on" / "html-multi" / "Project-Stats" / "index.html"
    let html ← if ← page.pathExists then IO.FS.readFile page else pure ""
    let index ← IO.FS.readFile (root / "on" / "html-multi" / "index.html")
    pure (c1 == 0 && c2 == 0 && c3 == 0 &&
      hasSubstr html "class=\"bp_project_stats\"" &&
      hasSubstr html "data-bp-chapter=\"Sums\"" &&
      hasSubstr html "<a href=\"https://example.org/repo\">Repository</a>" &&
      hasSubstr index "Project-Stats" &&
      !(← (root / "flag" / "html-multi" / "Project-Stats").pathExists) &&
      !(← (root / "off" / "html-multi" / "Project-Stats").pathExists))

end Verso.VersoBlueprintTests.BlueprintStatsPage
