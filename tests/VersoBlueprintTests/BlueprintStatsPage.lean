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
card or hint, progress, size, build, what the Lean code rests on, the explanation of the marks,
summary link), the page in a rendered document, and the page that generators add to every site
(and leave out when asked). `BlueprintMeaning` pins the wording of each state.
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
  let proved : HeadlineTheorem := { name := `main, solution := .same, sorryFree := some true, conditionsMet := true }
  let withSorry : HeadlineTheorem := { name := `main, solution := .same, sorryFree := some false }
  let differs : HeadlineTheorem :=
    { name := `main, solution := .differs, difference := some "the statement differs",
      differingDeclaration := some `main }
  (headlineVerdict proved .accepted).1 == "proved" && (headlineVerdict withSorry).1 == "sorry" &&
    (headlineVerdict proved .accepted).2 == "Lean statement proved" &&
    (headlineVerdict proved).1 == "not-replayed" &&
    (headlineVerdict withSorry).2 == "Same Lean statement as the challenge; the proof uses sorry" &&
    (headlineVerdict differs).2 ==
      "Lean statement differs from the challenge: the statement differs (main)" &&
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
      { path := "Comparator/Main/Challenge.lean", status := .compiled },
      { path := "scripts/Probe.lean", status := .notBuilt }]
    lines := { blank := 378, comment := 402, code := 1353 }
  }
  progress := { formalizedWithAncestors := 54, formalized := 2, incomplete := 1, ready := 1 }
  leanProgress := {
    theorems := { total := 48, leanComplete := 46, leanCompleteWithDependencies := 44, informal := 48 }
    definitions := { total := 10, leanComplete := 10, leanCompleteWithDependencies := 10, informal := 9 } }
  graph := { nodes := 58, statementEdges := 62, proofEdges := 84, edges := 146,
             byKind := #[("definition", 10), ("lemma", 40), ("theorem", 8)] }
  challenges := #[{
    name := "Main"
    challengeModule := `Comparator.Main.Challenge
    solutionModule := `Comparator.Main.Solution
    challengeFile := some "Comparator/Main/Challenge.lean"
    solutionFile := some "Comparator/Main/Solution.lean"
    theorems := #[{
      name := `rho_irrational
      docstring := some "Rokicki's constant is irrational."
      statement := "theorem rho_irrational : Irrational rho"
      solution := .same, sorryFree := some true, conditionsMet := true
      axioms := #[``Classical.choice, ``Quot.sound, ``propext]
      node := some `main }]
    definitions := #[{ name := `rho, solution := .same }]
  }]
  hasComparatorChallenge := true
  replay := some { outcome := .accepted, version := some "4.35.0", declarations := #[`rho_irrational] }
}

private def view (stats : ProjectStats) : StatsPageView := {
  stats
  page := { links := #[{ label := "GitHub", href := "https://example.org/repo" }]
            meaningHref := some s!"Project-Stats/#{Informal.Meaning.anchor}" }
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
  -- a site whose kernel replay accepted the build and covers every node
  site := .accepted
}

-- Identity, headline, progress, size and build bands of a project with a proved challenge.
/-- info: true -/
#guard_msgs in
#eval
  let html := (statsPageHtml (view rokickiLike)).render
  hasSubstr html "class=\"bp_project_stats bp_replay_accepted\"" &&
    hasSubstr html "Rokicki's constant is irrational</p>" && hasSubstr html "class=\"bp_stats_name\"" &&
    hasSubstr html "<dt class=\"bp_stats_fact_label\">License</dt>" &&
    hasSubstr html ">Apache-2.0</span>" && hasSubstr html "Lean v4.35.0" &&
    -- direct dependencies only, with the revision asked for and the locked commit
    hasSubstr html "data-bp-package=\"mathlib\"" && hasSubstr html "v4.35.0 · 56a0058" &&
    !hasSubstr html "data-bp-package=\"batteries\"" &&
    hasSubstr html "<a href=\"https://example.org/repo\">GitHub</a>" &&
    -- the headline card
    hasSubstr html "class=\"bp_stats_band bp_stats_headline\"" &&
    hasSubstr html "data-bp-theorem=\"rho_irrational\" data-bp-verdict=\"proved\"" &&
    -- the node's number is the Blueprint's own, and the link says so
    hasSubstr html "<a href=\"/Main/#main\">This site's Theorem 6.1</a>" &&
    hasSubstr html "Lean statement proved</span>" &&
    hasSubstr html "Lean statement, from the challenge" &&
    hasSubstr html "Docstring in the challenge (not checked against the Lean statement)" &&
    -- the Lean statement comes before the docstring
    appearsBefore html "theorem rho_irrational : Irrational rho" "Rokicki's constant is irrational.</p>" &&
    hasSubstr html headlineMethodText &&
    hasSubstr html (thisBuildText rokickiLike.identity) &&
    thisBuildText rokickiLike.identity == "This page reports on one build, made with Lean v4.35.0 \
      and the package revisions above. No other toolchain or revision was checked." &&
    hasSubstr html "theorem rho_irrational : Irrational rho" &&
    hasSubstr html "the standard axioms of Lean's logic only" &&
    hasSubstr html "<code>Comparator/Main/Challenge.lean</code>" &&
    hasSubstr html "<code>rho</code> (same in the solution)" &&
    !hasSubstr html headlineHintText &&
    -- progress: counts as text, a segment per non-empty status, the per-chapter table
    hasSubstr html "58 nodes: 48 theorems, 10 definitions</p>" &&
    hasSubstr html "Lean complete (a Lean statement, and no sorry in a node's Lean code or in \
      what that code uses): 46 of 48 theorems, 10 of 10 definitions.</p>" &&
    hasSubstr html "Informal statements: 57 of 58 nodes have one. No tool has checked any of \
      them against the Lean statements." &&
    !hasSubstr html "fully proved" && !hasSubstr html "Fully proved" &&
    hasSubstr html "style=\"flex-grow: 54\" data-bp-status=\"fully-proved\"" &&
    !hasSubstr html "data-bp-status=\"not-ready\" title=" &&
    hasSubstr html "aria-label=\"58 nodes: 54 Lean complete, dependencies too, 2 Lean complete, a dependency is not, 1 Lean code incomplete, 1 ready to formalize\"" &&
    hasSubstr html "<a href=\"/Ready-to-Prove/#ready-to-prove\">Ready to Prove (1)</a>" &&
    hasSubstr html "data-bp-chapter=\"Character sums\"" && hasSubstr html "16/18" &&
    -- size and build
    hasSubstr html "2,133" && hasSubstr html "1,353 code lines · 402 comment lines · 378 blank lines" &&
    hasSubstr html "73 theorems · 22 definitions" && hasSubstr html "10 definitions · 40 lemmas · 8 theorems" &&
    hasSubstr html "2 of 3 Lean files compiled: 1 imported by the site, 1 built by another target." &&
    hasSubstr html "1 Lean file on disk in no build:" && hasSubstr html "<code>scripts/Probe.lean</code>" &&
    hasSubstr html "No Lean declaration of a node has a sorry of its own." &&
    -- what the Lean code rests on, the explanation of the marks and the summary link
    hasSubstr html "No node's Lean code uses sorry, an axiom outside Lean's standard three or the \
      result of compiled code, as Lean reports the axioms of this build." &&
    hasSubstr html s!"id=\"{Informal.Meaning.anchor}\"" &&
    hasSubstr html s!"<a href=\"Project-Stats/#{Informal.Meaning.anchor}\" class=\"bp_meaning_link\">What this means</a>" &&
    meaningItems.all (fun item => hasSubstr html item.1) &&
    hasSubstr html "<a href=\"lean:help/marks\">" &&
    appearsBefore html "bp_stats_trust" "bp_stats_meaning" &&
    hasSubstr html "data-bp-trust=\"sorry-direct\" data-bp-count=\"0\"" &&
    hasSubstr html "Detailed breakdown: <a href=\"/Blueprint-Summary/#blueprint-summary\">Blueprint Summary</a>" &&
    appearsBefore html "bp_stats_identity" "bp_stats_headline" &&
    appearsBefore html "bp_stats_headline" "bp_stats_progress" &&
    appearsBefore html "bp_stats_progress" "bp_stats_size" &&
    appearsBefore html "bp_stats_size" "bp_stats_build" &&
    appearsBefore html "bp_stats_build" "bp_stats_trust" &&
    appearsBefore html "bp_stats_trust" "bp_stats_summary_link"

-- Addresses of the identity's facts: a package's tree at its locked commit on GitHub, in each
-- spelling of a GitHub remote, and nothing for a path package, another host or a revision that
-- is not a full commit.
/-- info: true -/
#guard_msgs in
#eval
  let rev := "fc4f59e577feb1a4956671bc04ac18aaaf8cd842"
  let tree := s!"https://github.com/leanprover-community/mathlib4/tree/{rev}"
  let git (url : String) (rev : String := rev) : ManifestPackage :=
    { name := "mathlib", source := "git", url := some url, rev := some rev }
  (packageTreeHref? (git "https://github.com/leanprover-community/mathlib4")) == some tree &&
    (packageTreeHref? (git "https://github.com/leanprover-community/mathlib4.git")) == some tree &&
    (packageTreeHref? (git "https://github.com/leanprover-community/mathlib4/")) == some tree &&
    (packageTreeHref? (git "http://github.com/leanprover-community/mathlib4")) == some tree &&
    (packageTreeHref? (git "git@github.com:leanprover-community/mathlib4.git")) == some tree &&
    (packageTreeHref? (git "ssh://git@github.com/leanprover-community/mathlib4")) == some tree &&
    -- another host, a path beyond the repository, a revision that is not a commit
    (packageTreeHref? (git "https://gitlab.com/group/project")) == none &&
    (packageTreeHref? (git "https://github.com/a/b/c")) == none &&
    (packageTreeHref? (git "https://github.com/a/b\"onclick")) == none &&
    (packageTreeHref? (git "https://github.com/a/b" "v4.36.0")) == none &&
    (packageTreeHref? (git "https://github.com/a/b" "fc4f59e")) == none &&
    -- a path package
    (packageTreeHref? { name := "local", source := "path", dir := some "../local" }) == none &&
    (packageTreeHref? { git "https://github.com/a/b" with source := "path" }) == none &&
    -- a package in a folder of its repository links to that folder at the revision
    (packageTreeHref? { git "https://github.com/eric-vergo/PILean" with subDir := some "verso" }) ==
      some s!"https://github.com/eric-vergo/PILean/tree/{rev}/verso" &&
    (packageTreeHref? { git "https://github.com/a/b" with subDir := some "x/y/" }) ==
      some s!"https://github.com/a/b/tree/{rev}/x/y" &&
    (packageTreeHref? { git "https://github.com/a/b" with subDir := some "../c" }) == none &&
    (packageTreeHref? { git "https://github.com/a/b" with subDir := some "a b" }) == none &&
    -- a name quoted in the manifest is shown as written
    shownPackageName "«pilean-verso»" == "pilean-verso" && shownPackageName "mathlib" == "mathlib"

-- The release page of a toolchain: a release or release candidate of `leanprover/lean4` only.
/-- info: true -/
#guard_msgs in
#eval
  let release (v : String) := some s!"https://github.com/leanprover/lean4/releases/tag/{v}"
  leanReleaseHref? "leanprover/lean4:v4.36.0\n" == release "v4.36.0" &&
    leanReleaseHref? "v4.36.0" == release "v4.36.0" &&
    leanReleaseHref? "leanprover/lean4:v4.36.0-rc1" == release "v4.36.0-rc1" &&
    leanReleaseHref? "leanprover/lean4-nightly:nightly-2026-11-01" == none &&
    leanReleaseHref? "leanprover/lean4:nightly-2026-11-01" == none &&
    leanReleaseHref? "leanprover/lean4:stable" == none &&
    leanReleaseHref? "someone/lean4:v4.36.0" == none &&
    leanReleaseHref? "leanprover/lean4:v4.36" == none &&
    leanReleaseHref? "leanprover/lean4:v4.36.0-rc" == none &&
    leanReleaseHref? "leanprover/lean4:4.36.0" == none &&
    leanReleaseHref? "../my-toolchain" == none

-- Lean's standard axioms link to the Lean Language Reference of the build's release when it is
-- published under its version, and to the latest reference otherwise; no other axiom has an
-- address.
/-- info: true -/
#guard_msgs in
#eval
  let latest := "https://lean-lang.org/doc/reference/latest"
  let r436 := "https://lean-lang.org/doc/reference/4.36.0"
  leanReferenceBase (some "leanprover/lean4:v4.36.0\n") == r436 &&
    leanReferenceBase (some "v4.19.0") == "https://lean-lang.org/doc/reference/4.19.0" &&
    leanReferenceBase (some "leanprover/lean4:v4.18.0") == latest &&
    leanReferenceBase (some "leanprover/lean4:v4.37.0") == latest &&
    leanReferenceBase (some "leanprover/lean4:v4.36.1") == latest &&
    leanReferenceBase (some "leanprover/lean4:v4.036.0") == latest &&
    leanReferenceBase (some "leanprover/lean4:v4.36.0-rc1") == latest &&
    leanReferenceBase (some "leanprover/lean4-nightly:nightly-2026-11-01") == latest &&
    leanReferenceBase (some "someone/lean4:v4.36.0") == latest &&
    leanReferenceBase none == latest &&
    axiomDocHref? r436 ``propext == some s!"{r436}/The-Type-System/Propositions/#propext" &&
    axiomDocHref? r436 ``Quot.sound == some s!"{r436}/The-Type-System/Quotients/#Quot___sound" &&
    axiomDocHref? r436 ``Classical.choice == some s!"{r436}/Axioms/#standard-axioms" &&
    axiomDocHref? latest ``sorryAx == none && axiomDocHref? latest `My.axiom == none

-- Each verdict links to the entry of the explanation that explains it, and the page has each
-- entry: the replay's entry for what a replay decided or did not check, the axioms' entry for a
-- proof that rests on an axiom the verdict does not allow, the headline's for the rest.
/-- info: true -/
#guard_msgs in
#eval
  let replay := "bp-meaning-kernel-replay"
  let headline := "bp-meaning-lean-statement-proved"
  let html := (statsPageHtml (view rokickiLike)).render
  let expected : List (String × Bool × String) := [
    ("proved", true, headline), ("rejected", true, replay), ("not-replayed", true, replay),
    ("axioms", true, replay), ("axioms", false, "bp-meaning-axioms"), ("sorry", false, headline),
    ("open", false, headline), ("differs", false, headline), ("missing", false, headline),
    ("hole", false, headline), ("not-compared", false, headline), ("not-theorem", false, headline)]
  expected.all fun (token, met, id) =>
    meaningEntryId (verdictMeaningTitle token met) == id && hasSubstr html s!"<dt id=\"{id}\">"

-- Every chip with an address is a link that leaves the site safely, and every chip without one is
-- not a link; the verdict links to the entry of the explanation that explains it, an entry the
-- page has; the theorem's name and the files link to the challenge's page.
/-- info: true -/
#guard_msgs in
#eval
  let rev := "56a0058500000000000000000000000000000000"
  let identity := { rokickiLike.identity with
    toolchain := some "leanprover/lean4:v4.35.0"
    packages := #[
      { name := "mathlib", source := "git", rev := some rev, inputRev := some "v4.35.0",
        url := some "https://github.com/leanprover-community/mathlib4.git" },
      { name := "local", source := "path", dir := some "../local" }] }
  let v := { (view { rokickiLike with identity }) with
    licenseHref := some "https://github.com/o/p/blob/abc/LICENSE"
    challengeHrefs := #[("Main", "Comparator/Main/#Main")] }
  let html := (statsPageHtml v).render
  hasSubstr html s!"<a class=\"bp_stats_chip bp_stats_chip_package bp_stats_external\" \
      href=\"https://github.com/leanprover-community/mathlib4/tree/{rev}\" title=\"github.com\" \
      data-bp-package=\"mathlib\">" &&
    hasSubstr html "<span class=\"bp_stats_chip bp_stats_chip_package\" data-bp-package=\"local\">" &&
    hasSubstr html "<a class=\"bp_stats_chip bp_stats_chip_license bp_stats_external\" \
      href=\"https://github.com/o/p/blob/abc/LICENSE\" title=\"github.com\"" &&
    hasSubstr html "href=\"https://github.com/leanprover/lean4/releases/tag/v4.35.0\" title=\"github.com\"" &&
    hasSubstr html "<a class=\"bp_stats_axiom bp_stats_axiom_standard bp_stats_external\" \
      href=\"https://lean-lang.org/doc/reference/4.35.0/The-Type-System/Propositions/#propext\" \
      data-bp-axiom-class=\"standard\"" &&
    !hasSubstr html "noopener" &&
    -- the verdict's entry, on the page that has the explanation
    hasSubstr html "<a class=\"bp_stats_verdict_link bp_stats_verdict_link_proved\" \
      href=\"Project-Stats/#bp-meaning-lean-statement-proved\"><span class=\"bp_stats_verdict \
      bp_stats_verdict_proved\">Lean statement proved</span></a>" &&
    hasSubstr html "<dt id=\"bp-meaning-lean-statement-proved\">" &&
    -- the theorem's name and the files go to the challenge's page
    hasSubstr html "<a class=\"bp_stats_theorem_name_link\" href=\"Comparator/Main/#challenge-file\">\
      <code class=\"bp_stats_theorem_name\">rho_irrational</code></a>" &&
    hasSubstr html ">Challenge Main: files, configuration and verdict</a>" &&
    hasSubstr html "<a class=\"bp_stats_file_link\" href=\"Comparator/Main/#solution-file\">\
      <code>Comparator/Main/Solution.lean</code></a>" &&
    -- the method sentence quotes the word it is about
    hasSubstr html "a verdict says “proved” only when" && !hasSubstr html "\"proved\" only"

-- The license links to the file of the project the statistics describe at the checkout's commit,
-- also when the site is generated from a folder below the project (`verso.blueprint.projectRoot`),
-- whose own license file it must not take.
/-- info: true -/
#guard_msgs in
#eval show IO Bool from do
  let root ← IO.FS.realPath (← IO.FS.createTempDir)
  let git (args : Array String) := IO.Process.output { cmd := "git", args, cwd := root }
  IO.FS.writeFile (root / "LICENSE") "MIT License"
  IO.FS.createDirAll (root / "blueprint")
  IO.FS.writeFile (root / "blueprint" / "LICENSE") "Apache License"
  let _ ← git #["init", "-q"]
  let _ ← git #["remote", "add", "origin", "https://github.com/o/p.git"]
  let _ ← git #["add", "LICENSE", "blueprint/LICENSE"]
  let _ ← git #["-c", "user.name=test", "-c", "user.email=test@example.org", "-c",
    "commit.gpgsign=false", "commit", "-q", "-m", "files"]
  let commit := (← git #["rev-parse", "HEAD"]).stdout.trimAscii.toString
  let cwd ← IO.currentDir
  try
    IO.Process.setCurrentDir (root / "blueprint")
    let license : ProjectIdentity := { license := some { file := "LICENSE", spdx := some "MIT" } }
    let project ← licenseHref? { identity := license, layout := { projectRoot := some ".." } }
    let own ← licenseHref? { identity := license }
    return project == some s!"https://github.com/o/p/blob/{commit}/LICENSE" &&
      own == some s!"https://github.com/o/p/blob/{commit}/blueprint/LICENSE"
  finally
    IO.Process.setCurrentDir cwd
    IO.FS.removeDirAll root

-- A judged theorem's name breaks only after its dots.
/-- info: "<code class=\"bp_stats_theorem_name\">Dif.<wbr/>add_swap</code>" -/
#guard_msgs in
#eval (theoremNameHtml `Dif.add_swap).render

-- A statement is cut from its module's highlighted code, tokens and all, when the code has its
-- text; otherwise there is none to cut.
/-- info: true -/
#guard_msgs in
#eval
  let tok (k : SubVerso.Highlighting.Token.Kind) (s : String) : SubVerso.Highlighting.Highlighted :=
    .token ⟨k, s⟩
  let code : SubVerso.Highlighting.Highlighted := .seq #[
    tok .docComment "/-- Doubling. -/", .text "\n", tok (.keyword none none none) "theorem",
    .text " ", tok (.const `double_even "Prop" none false none) "double_even", .text " : True := by\n  ",
    tok (.keyword none none none) "trivial", .text "\n"]
  let statement := "theorem double_even : True"
  match Informal.DeclarationSource.sliceByText? code statement with
  | some cut => cut.toString == statement &&
      (Informal.DeclarationSource.leaves cut).any (· matches .token ⟨.const .., _⟩) &&
      (Informal.DeclarationSource.sliceByText? code "theorem double_ev").isNone &&
      (Informal.DeclarationSource.sliceByText? code "theorem odd").isNone
  | none => false

-- Without the explanation on the site, a verdict is a plain pill; without a license address, the
-- license is a plain chip.
/-- info: true -/
#guard_msgs in
#eval
  let v := { (view rokickiLike) with page := { (view rokickiLike).page with meaningHref := none } }
  let html := (statsPageHtml v).render
  !hasSubstr html "bp_stats_verdict_link" &&
    hasSubstr html "<span class=\"bp_stats_chip bp_stats_chip_license\" data-bp-license-file=\"LICENSE\">Apache-2.0</span>"

-- Without a Comparator challenge there is no card, only the one-line hint; no license file shows.
/-- info: true -/
#guard_msgs in
#eval
  let stats := { rokickiLike with
    challenges := #[], hasComparatorChallenge := false
    identity := { rokickiLike.identity with license := none } }
  let html := (statsPageHtml (view stats)).render
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
  let challenges := rokickiLike.challenges.map fun h => { h with theorems := h.theorems.map fun t =>
    { t with conditionsMet := false, sorryFree := some false, axioms := t.axioms.push ``sorryAx } }
  let html := (statsPageHtml (view { rokickiLike with trust, challenges })).render
  hasSubstr html "1 Lean declaration of nodes with a sorry of its own." &&
    hasSubstr html "data-bp-trust=\"sorry-direct\" data-bp-count=\"1\"" &&
    hasSubstr html "<a href=\"/Sums/#lem\">Lemma 3.2</a>" &&
    -- a node is listed once, however many of its declarations are on the row
    hasSubstr html "data-bp-trust=\"sorry-dependency\" data-bp-count=\"1\"" &&
    hasSubstr html "data-bp-trust=\"compiler-trusted\" data-bp-count=\"1\"" &&
    hasSubstr html "data-bp-trust=\"extra-axioms\" data-bp-count=\"0\"" &&
    !hasSubstr html "No node's Lean code uses sorry" &&
    hasSubstr html "Nodes whose Lean declarations rest on more than Lean's standard three axioms" &&
    hasSubstr html "data-bp-verdict=\"sorry\"" &&
    hasSubstr html "Same Lean statement as the challenge; the proof uses sorry" &&
    !hasSubstr html ">Lean statement proved</span>" &&
    hasSubstr html "data-bp-axiom-class=\"sorry\"" &&
    !hasSubstr html "the standard axioms of Lean's logic only"

-- Many files in no build: the first ones are listed, the rest folded away.
/-- info: true -/
#guard_msgs in
#eval
  let files := (List.range 11).toArray.map fun i =>
    ({ path := s!"Extra/F{i}.lean", status := .notBuilt } : SourceFile)
  let html := (statsPageHtml (view { rokickiLike with sources := { files } })).render
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
      hasSubstr out "class=\"bp_project_stats bp_replay_none\"" &&
      hasSubstr out s!"{countOf total "node"}: 1 theorem, 1 definition</p>" &&
      -- both nodes have a written statement, and neither has Lean code
      hasSubstr out "Lean complete (a Lean statement, and no sorry in a node's Lean code or in \
        what that code uses): 0 of 1 theorem, 0 of 1 definition." &&
      hasSubstr out "Informal statements: 2 of 2 nodes have one." &&
      hasSubstr out "class=\"bp_stats_band bp_stats_trust\"" &&
      total ≥ 2)

-- A judged theorem's statement is cut from the challenge's code as the challenge's page shows it,
-- with the hovers of its tokens and without a tab stop for each.
/-- info: true -/
#guard_msgs in
#eval
  show IO Bool from do
    let model : RenderModel := blueprint_render_model%
    let model := { model with stats := { model.stats with challenges := rokickiLike.challenges } }
    let tok (k : SubVerso.Highlighting.Token.Kind) (s : String) : SubVerso.Highlighting.Highlighted :=
      .token ⟨k, s⟩
    registerChallengeCode `Comparator.Main.Challenge (.seq #[
      tok .docComment "/-- Rokicki's constant is irrational. -/", .text "\n",
      tok (.keyword none none none) "theorem", .text " ",
      tok (.const `rho_irrational "Irrational rho" none true none) "rho_irrational", .text " : ",
      tok (.const `Irrational "ℝ → Prop" (some "An irrational number.") false none) "Irrational",
      .text " ", tok (.const `rho "ℝ" none false none) "rho", .text " := by\n  sorry\n"])
    let out ← renderManualDocHtmlString extension_impls% statsDoc (model := model)
    let code := ((out.splitOn "bp_stats_statement_code").getD 1 "").splitOn "</code>" |>.head!
    pure (hasSubstr code "data-verso-hover" && hasSubstr code ">Irrational</span>" &&
      !hasSubstr code "tabindex" && !hasSubstr code "sorry")

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
      hasSubstr html "class=\"bp_project_stats bp_replay_none\"" &&
      hasSubstr html "data-bp-chapter=\"Sums\"" &&
      hasSubstr html "<a href=\"https://example.org/repo\">Repository</a>" &&
      -- the page's links to its own explanation resolve against the site's root (`<base href>`)
      hasSubstr html s!"href=\"Project-Stats/#{Informal.Meaning.anchor}\"" &&
      !hasSubstr html s!"href=\"#{Informal.Meaning.anchor}\"" &&
      hasSubstr index "Project-Stats" &&
      !(← (root / "flag" / "html-multi" / "Project-Stats").pathExists) &&
      !(← (root / "off" / "html-multi" / "Project-Stats").pathExists))

end Verso.VersoBlueprintTests.BlueprintStatsPage
