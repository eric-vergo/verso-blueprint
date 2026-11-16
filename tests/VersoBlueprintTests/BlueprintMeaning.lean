/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

import VersoBlueprint
import VersoBlueprint.PreviewManifest
import VersoBlueprintTests.Blueprint.Support
import VersoBlueprintTests.BlueprintCodeSite

/-!
What a site says about what was checked: each state, with the sentences it must show and the
words it must not.

A site reports facts about Lean code and shows informal text beside it. These tests pin the
wording to the state behind it, row by row:

* a node's mark, for a theorem and a definition, with and without an axiom beyond Lean's
  standard three, with a `sorry`, under an accepted kernel replay and without one;
* the headline of a Comparator challenge: proved, statement differs, a `sorry`, an axiom that is
  not allowed, challenge not built, no challenge;
* the counts of the Project Stats page, with and without informal statements, and for a
  Blueprint whose theorems have no statement yet;
* an author's claim, with and without an attestation, on the page and in the node view;
* a site generated from code: no numbers, the statement's source under it, the title of a
  project whose README starts with a generic heading.

No row may say "proved" of a definition, "fully proved" of anything, or "checked" of informal
text.
-/

namespace Verso.VersoBlueprintTests.BlueprintMeaning

open Lean
open Informal
open Informal.Commands
open Informal.Stats
open Verso.VersoBlueprintTests.Blueprint.Support
open Verso.VersoBlueprintTests.BlueprintCodeSite (fixture statedFixture)

/-! ## A node's mark -/

private def mark (kind : Data.NodeKind) (status : Data.ProvedStatus)
    (extraAxioms : Array Name := #[]) : BlockStatusMark :=
  { status, title := "Lean statement: no sorry; Lean proof: blocked by sorry", kind, extraAxioms }

/-- A kernel replay that accepted the project's modules (`BlueprintKernelReplay` has the other
outcomes). -/
private def accepted : Replay.Result :=
  { outcome := .accepted, version := some "4.35.0", modules := #[`Solution] }

private def directSorry : Data.ProvedStatus :=
  .incomplete { knownSorry := #[{ location := .proof, origin := .direct }] }

-- A theorem and a definition without `sorry`, under an accepted kernel replay: the check mark,
-- in words about the Lean code. A definition is never called proved. Without a replay neither
-- gets the check mark.
/-- info: true -/
#guard_msgs in
#eval
  let thm := statusGlyph (some (mark .theorem .proved)) (some accepted)
  let defn := statusGlyph (some (mark .definition .proved)) (some accepted)
  thm.1.modifier == "proved" &&
    thm.2 == "Lean proof complete: no sorry in it or in what it uses; checked again in Lean's \
      kernel by leanchecker (Lean 4.35.0)" &&
    defn.1.modifier == "proved" &&
    defn.2 == "Lean definition complete: no sorry in it or in what it uses; checked again in \
      Lean's kernel by leanchecker (Lean 4.35.0)" &&
    !hasSubstr defn.2 "roved" && !hasSubstr thm.2 "Proved" &&
    (statusGlyph (some (mark .theorem .proved))).1.modifier == "reported" &&
    (statusGlyph (some (mark .definition .proved))).2 == "Lean definition without sorry, as the \
      compiled files report; not replayed by a kernel (this site was generated without a kernel \
      replay)"

-- No `sorry`, but an axiom beyond the standard three, or compiled code: no check mark, and the
-- text names what the code rests on.
/-- info: true -/
#guard_msgs in
#eval
  let extra := statusGlyph (some (mark .theorem .proved #[`Demo.ax]))
  let native := statusGlyph (some (mark .theorem .proved #[`Demo.t._native.native_decide.ax_1]))
  let both := statusGlyph (some (mark .theorem .proved #[`A.ax, `B.ax, `T._native.bv_decide.ax_2]))
  extra.1.modifier == "problem" &&
    extra.2 == "Lean proof without sorry, resting on an axiom outside Lean's standard three \
      (Demo.ax)" &&
    native.1.modifier == "problem" &&
    native.2 == "Lean proof without sorry, resting on the result of compiled code \
      (Demo.t._native.native_decide.ax_1)" &&
    both.2 == "Lean proof without sorry, resting on axioms outside Lean's standard three \
      (A.ax, B.ax) and the result of compiled code (T._native.bv_decide.ax_2)"

-- A `sorry`, a missing declaration, no declaration.
/-- info: true -/
#guard_msgs in
#eval
  let withSorry := statusGlyph (some (mark .theorem directSorry))
  let missing := statusGlyph (some (mark .theorem .missing))
  let none := statusGlyph Option.none
  withSorry.1.modifier == "partial" &&
    withSorry.2 == "Lean code incomplete: a sorry in the proof or in what it uses \
      (Lean statement: no sorry; Lean proof: blocked by sorry)" &&
    missing.1.modifier == "missing" && hasSubstr missing.2 "Lean declaration missing" &&
    -- an axiom, or an opaque constant, as a node: assumed, and said so
    (statusGlyph (some (mark .definition .axiomLike))).1.modifier == "problem" &&
    (statusGlyph (some (mark .definition .axiomLike))).2 == "Declared without a proof or a body \
      (an axiom or an opaque constant): assumed, not proved" &&
    none.1.modifier == "none" && none.2 == "No Lean declaration"

-- The legend: every meaning is about Lean code, and it ends with what no mark is about.
/-- info: true -/
#guard_msgs in
#eval
  let legend := statusLegendTemplate.asString
  StatusGlyphKind.all.all (fun kind => hasSubstr kind.meaning "Lean") &&
    hasSubstr legend "A mark is about the Lean code only. No tool checks that an informal \
      statement says the same as the Lean statement." &&
    !hasSubstr legend "Proved"

-- The axes of a mark's detail: a definition's second axis is its body.
/-- info: true -/
#guard_msgs in
#eval
  let ref (kind : Data.NodeKind) : Data.ExternalRef :=
    { (Data.ExternalRef.ofName `Demo.x) with present := true, kind, provedStatus := .proved }
  let title (kind : Data.NodeKind) : String :=
    let data : BlockData := { kind, label := `x, count := 1,
                              codeData := some { externalDecls := #[ref kind] } }
    ((CodeSummary.renderParts data { source := data.codeData } (fun _ => Option.none)).statusMark.map
      (·.title)).getD ""
  title .theorem == "Lean statement: no sorry; Lean proof: no sorry" &&
    title .definition == "Lean statement: no sorry; Lean body: no sorry"

-- The axioms that keep the check mark away are read from the node's declarations.
/-- info: true -/
#guard_msgs in
#eval
  let ref : Data.ExternalRef := { (Data.ExternalRef.ofName `Demo.x) with
    present := true, kind := .theorem, provedStatus := .proved
    axioms := #[``propext, `Demo.ax, ``Classical.choice] }
  let data : BlockData := { kind := .theorem, label := `x, count := 1,
                            codeData := some { externalDecls := #[ref] } }
  let mark := (CodeSummary.renderParts data { source := data.codeData } (fun _ => Option.none)).statusMark
  (mark.map (·.extraAxioms)) == some #[`Demo.ax] && (statusGlyph mark).1.modifier == "problem"

/-! ## The headline -/

private def proved : HeadlineTheorem :=
  { name := `main, statement := "theorem main : P", solution := .same, sorryFree := some true
    conditionsMet := true, axioms := #[``propext], docstring := some "The main result." }

-- Each verdict, in words about the Lean statement.
/-- info: true -/
#guard_msgs in
#eval
  let sorry_ := { proved with conditionsMet := false, sorryFree := some false }
  let extra := { proved with
    conditionsMet := false, axioms := #[`Demo.ax, ``propext], axiomsNotAllowed := #[`Demo.ax] }
  let notPermitted := { extra with axiomsPermitted := some false }
  let differs : HeadlineTheorem := { name := `main, solution := .differs
                                     difference := some "the statement differs" }
  headlineVerdict proved .accepted == ("proved", "Lean statement proved") &&
    -- the same theorem without a kernel replay is not called proved
    headlineVerdict proved == ("not-replayed", conditionsMetText) &&
    headlineVerdict sorry_ ==
      ("sorry", "Same Lean statement as the challenge; the proof uses sorry") &&
    headlineVerdict extra == ("axioms", "Same Lean statement as the challenge; the proof rests \
      on an axiom outside Lean's standard three (Demo.ax)") &&
    headlineVerdict notPermitted == ("axioms", "Same Lean statement as the challenge; the proof \
      rests on an axiom the challenge does not permit (Demo.ax)") &&
    headlineVerdict differs ==
      ("differs", "Lean statement differs from the challenge: the statement differs") &&
    headlineVerdict { name := `main, solution := .missing } == ("missing", "Not in the solution") &&
    headlineVerdict { name := `main } == ("not-compared", "Not compared")

-- Which axioms the comparison allows: the challenge's list, else Lean's standard three;
-- a `sorry` is reported on its own.
/-- info: true -/
#guard_msgs in
#eval
  let axioms := #[``propext, ``Classical.choice, `Demo.ax, ``sorryAx]
  axiomsNotAllowed Option.none axioms == #[`Demo.ax] &&
    axiomsNotAllowed (some #[``propext]) axioms == #[``Classical.choice, `Demo.ax] &&
    axiomsNotAllowed (some #[``propext, ``Classical.choice, `Demo.ax]) axioms == #[] &&
    axiomsNotAllowed Option.none #[``propext, ``Classical.choice, ``Quot.sound] == #[]

private def stats (headline : Option Headline) (leanProgress : LeanProgress := {}) : ProjectStats :=
  { identity := { name := some "demo", toolchain := some "leanprover/lean4:v4.35.0"
                  packages := #[{ name := "mathlib", source := "git", rev := some "56a00585aa" }] }
    headline, hasComparatorChallenge := headline.isSome, leanProgress
    replay := some accepted
    progress := { formalizedWithAncestors := leanProgress.total } }

private def page (s : ProjectStats) : String :=
  (statsPageHtml { stats := s, nodes := #[{ label := `n, title := "Theorem 6.1", href := some "/M/#n" }] }).asString

private def challenge (theorems : Array HeadlineTheorem) : Headline :=
  { challengeModule := `Challenge, solutionModule := `Solution
    challengeFile := some "Challenge.lean", solutionFile := some "Solution.lean", theorems
    solutionModules := #[`Solution] }

-- Proved: the verdict, then the Lean statement, then the docstring under its own caption, then
-- what the comparison is and is not; and which build the page reports on.
/-- info: true -/
#guard_msgs in
#eval
  let html := page (stats (some (challenge #[{ proved with node := some `n }])))
  hasSubstr html "data-bp-verdict=\"proved\"" && hasSubstr html ">Lean statement proved</span>" &&
    hasSubstr html "<a href=\"/M/#n\">This site's Theorem 6.1</a>" &&
    appearsBefore html "Lean statement, from the challenge" "theorem main : P" &&
    appearsBefore html "theorem main : P"
      "Docstring in the challenge (not checked against the Lean statement)" &&
    appearsBefore html "Docstring in the challenge" "The main result." &&
    hasSubstr html "Kernel replay: leanchecker (Lean 4.35.0) accepted the project module the \
      solution rests on." &&
    hasSubstr html "Compared by this site" && hasSubstr html "The comparison runs no kernel" &&
    hasSubstr html "This page reports on one build, made with Lean v4.35.0 and the package \
      revisions above. No other toolchain or revision was checked." &&
    !hasSubstr html "lake comparator is the authority" && !hasSubstr html ">Proved<"

-- Statement differs; a `sorry`; an axiom the verdict does not allow.
/-- info: true -/
#guard_msgs in
#eval
  let differs := page (stats (some (challenge #[{
    name := `main, solution := .differs, difference := some "the statement differs",
    differingDeclaration := some `main }])))
  let sorry_ := page (stats (some (challenge #[{ proved with conditionsMet := false, sorryFree := some false }])))
  let extra := page (stats (some (challenge #[{ proved with
    conditionsMet := false, axioms := #[`Demo.ax], axiomsNotAllowed := #[`Demo.ax] }])))
  hasSubstr differs "data-bp-verdict=\"differs\"" &&
    hasSubstr differs "Lean statement differs from the challenge: the statement differs (main)" &&
    !hasSubstr differs ">Lean statement proved</span>" &&
    hasSubstr sorry_ "data-bp-verdict=\"sorry\"" &&
    hasSubstr sorry_ "Same Lean statement as the challenge; the proof uses sorry" &&
    !hasSubstr sorry_ ">Lean statement proved</span>" &&
    hasSubstr extra "data-bp-verdict=\"axioms\"" &&
    hasSubstr extra "the proof rests on an axiom outside Lean's standard three (Demo.ax)" &&
    hasSubstr extra "data-bp-axiom-class=\"other\"" && !hasSubstr extra ">Lean statement proved</span>"

-- Challenge not built: nothing is compared and the page says why. No challenge: the hint.
/-- info: true -/
#guard_msgs in
#eval
  let notBuilt := page (stats (some { (challenge #[]) with
    unavailable := some .challengeNotBuilt, unavailableDetail := some "Challenge" }))
  let noChallenge := page (stats Option.none)
  hasSubstr notBuilt "Not compared: The challenge module has not been built. (Challenge)" &&
    !hasSubstr notBuilt ">Lean statement proved</span>" &&
    -- nothing was compared, so the page does not say how, nor what the challenge states
    !hasSubstr notBuilt "Compared by this site's generator" &&
    !hasSubstr notBuilt "The challenge states no theorem." &&
    hasSubstr (page (stats (some (challenge #[])))) "The challenge states no theorem." &&
    hasSubstr noChallenge headlineHintText && !hasSubstr noChallenge "bp_stats_theorem"

/-! ## The counts -/

private def progress (theorems definitions : Nat × Nat × Nat) : LeanProgress :=
  { theorems := { total := theorems.1, leanComplete := theorems.2.1
                  leanCompleteWithDependencies := theorems.2.1, informal := theorems.2.2 }
    definitions := { total := definitions.1, leanComplete := definitions.2.1
                     leanCompleteWithDependencies := definitions.2.1, informal := definitions.2.2 } }

-- No informal statements at all (a site generated from code without docstring math): the page
-- counts Lean code, says there are no statements, and never says "proved" of the nodes.
/-- info: true -/
#guard_msgs in
#eval
  let p := progress (32, 32, 0) (19, 19, 0)
  let html := page (stats Option.none p)
  leanCompleteText p == "Lean complete (no sorry in a node's Lean code or in what that code \
      uses): 32 of 32 theorems, 19 of 19 definitions." &&
    informalText p == "Informal statements: none. Every node shows its Lean code alone." &&
    hasSubstr html "51 nodes: 32 theorems, 19 definitions</p>" &&
    hasSubstr html "32 of 32 theorems, 19 of 19 definitions." &&
    hasSubstr html "Informal statements: none." &&
    !hasSubstr html "fully proved" && !hasSubstr html "% " && !hasSubstr html "Statement: completed"

-- Informal statements on some nodes: how many, and that none was checked against the Lean.
/-- info: true -/
#guard_msgs in
#eval
  let p := progress (40, 38, 40) (10, 10, 7)
  informalText p == "Informal statements: 47 of 50 nodes have one. No tool has checked any of \
      them against the Lean statements." &&
    informalText (progress (1, 1, 1) (0, 0, 0)) == "Informal statements: 1 of 1 node has one. \
      No tool has checked any of them against the Lean statements." &&
    leanCompleteText p == "Lean complete (no sorry in a node's Lean code or in what that code \
      uses): 38 of 40 theorems, 10 of 10 definitions." &&
    leanCompleteText (progress (0, 0, 0) (3, 2, 0)) == "Lean complete (no sorry in a node's Lean \
      code or in what that code uses): 2 of 3 definitions."

-- A Blueprint whose theorems have no statement yet (one made from code): its theorems count as
-- Lean complete and as having no informal statement, which is what is true of them.
/-- info: true -/
#guard_msgs in
#eval
  let p := progress (32, 32, 0) (19, 19, 16)
  informalText p == "Informal statements: 16 of 51 nodes have one. No tool has checked any of \
    them against the Lean statements."

-- The counts are read from the graph and the Blueprint state: a node counts as having an
-- informal statement only when its statement has a body.
/-- info: true -/
#guard_msgs in
#eval
  let state := BlueprintCodeSite.fixtureState
  let labels := state.data.toArray.map (·.1)
  let graph := Graph.buildModel state labels
  let p := leanProgressOf state graph
  let stated := CodeSite.stateOf statedFixture fun _ => Option.none
  let statedGraph := Graph.buildModel stated (stated.data.toArray.map (·.1))
  -- four theorems (two with a sorry) and two definitions (one an axiom), none with a statement
  p.theorems.total == 4 && p.theorems.leanComplete == 2 && p.theorems.informal == 0 &&
    p.definitions.total == 2 && p.definitions.leanComplete == 1 && p.definitions.informal == 0 &&
    (leanProgressOf stated statedGraph).informal == 2

/-! ## An author's claim -/

private def claimsText : String := "{
  \"source\": { \"title\": \"Finite lattices\", \"authors\": \"A. Author\", \"version\": \"v2\",
              \"url\": \"https://example.org/paper\" },
  \"claims\": [
    { \"declaration\": \"Demo.double_eq\", \"reference\": \"Theorem 2.2\",
      \"statement\": \"Doubling is adding <b>twice</b>.\",
      \"attestations\": [ { \"by\": \"R. Reader\", \"date\": \"2026-01-31\",
                            \"note\": \"compared with v2\" }, { \"date\": \"no name\" } ] },
    { \"declaration\": \"Demo.double\", \"reference\": \"Definition 2.1\" },
    { \"declaration\": \"Demo.double\", \"reference\": \"a second claim is left out\" },
    { \"reference\": \"no declaration\" } ] }"

-- The file: one claim per declaration; entries without a declaration, and attestations without
-- a name, are left out; only a web address becomes a link.
/-- info: true -/
#guard_msgs in
#eval
  match (Claims.parse claimsText : Except String Claims) with
  | .error _ => false
  | .ok claims =>
    claims.claims.map (fun (c : Claim) => c.declaration) == #[`Demo.double_eq, `Demo.double] &&
      (claims.find? `Demo.double_eq).map (fun (c : Claim) => c.attestations.size) == some 1 &&
      (claims.view? `Demo.double_eq).bind (fun (v : ClaimView.ClaimView) => v.sourceLink) ==
        some "https://example.org/paper" &&
      claimLink? "javascript:alert(1)" == Option.none && claimLink? "paper.pdf" == Option.none &&
      claimLink? "https://example.org/a b" == Option.none &&
      (Claims.parse "[]" matches .error _)

-- The block: whose words they are, the paper's own number, the text escaped, an attestation as
-- a person's statement; without one, that nobody recorded a comparison. Never a check mark.
/-- info: true -/
#guard_msgs in
#eval
  match (Claims.parse claimsText : Except String Claims) with
  | .error _ => false
  | .ok claims =>
    let html (v? : Option ClaimView.ClaimView) (href? : Option String) : String :=
      match v? with
      | some v => (v.render href?).asString
      | Option.none => ""
    let attested := html (claims.view? `Demo.double_eq) (some "#m")
    let bare := html (claims.view? `Demo.double) Option.none
    hasSubstr attested ">Author's claim</span>" &&
      hasSubstr attested "<a href=\"https://example.org/paper\" class=\"bp_claim_cite\">Theorem 2.2 \
        of Finite lattices (A. Author; v2)</a>" &&
      hasSubstr attested "Doubling is adding &lt;b&gt;twice&lt;/b&gt;." &&
      hasSubstr attested "Attested by R. Reader, 2026-01-31: compared with v2" &&
      hasSubstr attested "No tool has checked that this text says the same as the Lean statement. \
        An attestation is a person's statement, not a check." &&
      hasSubstr attested "<a href=\"#m\" class=\"bp_meaning_link\">What this means</a>" &&
      hasSubstr attested "data-bp-attestations=\"1\"" && !hasSubstr attested "✓" &&
      hasSubstr bare "Definition 2.1 of Finite lattices (A. Author; v2)" &&
      hasSubstr bare "No tool has checked that this text says the same as the Lean statement. \
        Nobody has recorded comparing it with the Lean statement." &&
      hasSubstr bare "data-bp-attestations=\"0\"" && !hasSubstr bare "Attested"

-- On the page: the claim of a judged theorem on its card, after the Lean statement; the others
-- in their own band; a file that cannot be read is reported.
/-- info: true -/
#guard_msgs in
#eval
  match (Claims.parse claimsText : Except String Claims) with
  | .error _ => false
  | .ok claims =>
    let headline := challenge #[{ proved with name := `Demo.double_eq }]
    let html := page { stats (some headline) with claims := some claims }
    let broken := page { stats Option.none with claims := some { error := some "expected an object" } }
    appearsBefore html "theorem main : P" "Theorem 2.2 of Finite lattices" &&
      appearsBefore html "data-bp-verdict=\"proved\"" "Author's claim" &&
      hasSubstr html "class=\"bp_stats_band bp_stats_claims\"" &&
      hasSubstr html "data-bp-claim-declaration=\"Demo.double\"" &&
      !hasSubstr html "data-bp-claim-declaration=\"Demo.double_eq\"" &&
      hasSubstr broken "informal-claims.json could not be read: expected an object"

/-! ## Informal text beside Lean code -/

-- The line under a statement names its source and says it was not checked.
/-- info: true -/
#guard_msgs in
#eval
  Meaning.sourceLine Option.none ==
      "Informal statement from the blueprint · not checked against the Lean statement" &&
    Meaning.sourceLine (some "docstring") ==
      "Informal statement from the docstring · not checked against the Lean statement" &&
    Meaning.sourceLine (some "tex") ==
      "Informal statement from the project's TeX blueprint · not checked against the Lean statement" &&
    Meaning.sourceLine (some "attribute") ==
      "Informal statement from a blueprint attribute · not checked against the Lean statement" &&
    hasSubstr (renderStatementSource (some "docstring")).asString
      "data-bp-statement-source=\"docstring\"" &&
    hasSubstr (renderSideBySideNode "n" (.text true "S") (some (.text true "L"))
      (renderStatementSource Option.none)).asString "class=\"bp_statement_source\"" &&
    -- a node without Lean code has nothing to be compared with: no line
    !hasSubstr (renderSideBySideNode "n" (.text true "S") Option.none
      (renderStatementSource Option.none)).asString "bp_statement_source" &&
    -- the generator shows the line for a written statement with Lean code, and only then
    (let data : BlockData := { kind := .theorem, label := `n, count := 1 }
     let html (note : Bool) : String := (renderInformalBlockModel {
        data, context := .forBlock data "1", statementSourceNote := note }).asString
     hasSubstr (html true) "bp_statement_source" && !hasSubstr (html false) "bp_statement_source")

private def nodeView : NodeView.NodeView := {
  label := "thm:x", title := "Theorem 1.2"
  status := (.proved, "Lean proof complete: no sorry in it or in what it uses")
  informal? := some (.text true "Every x is fine.")
  lean := #[.text true "theorem x : True"]
}

-- The node view: the source and the sentence under the statement, with the link; a claim in
-- the same column; neither without Lean code beside it.
/-- info: true -/
#guard_msgs in
#eval
  let claim : ClaimView.ClaimView := { reference := some "Theorem 2.2", statement := some "Claimed." }
  let both := ({ nodeView with informalSource := some "docstring", meaningHref? := some "Stats/#m"
                               claim? := some claim }).render.asString
  let leanOnly := ({ nodeView with informal? := Option.none, claim? := some claim }).render.asString
  let informalOnly := ({ nodeView with lean := #[], claim? := some claim }).render.asString
  hasSubstr both "Informal statement from the docstring. No tool has checked that this text says \
      the same as the Lean statement." &&
    hasSubstr both "<a href=\"Stats/#m\" class=\"bp_meaning_link\">What this means</a>" &&
    hasSubstr both "data-bp-statement-source=\"docstring\"" &&
    appearsBefore both "Every x is fine." "Author's claim" &&
    appearsBefore both "Author's claim" "class=\"bp_sbs_formal\"" &&
    -- a claim alone stands in the informal column, beside the Lean statement
    hasSubstr leanOnly "data-bp-node-view-layout=\"both\"" && hasSubstr leanOnly "Claimed." &&
    !hasSubstr leanOnly "Informal statement from" &&
    !hasSubstr informalOnly "Informal statement from" && !hasSubstr informalOnly "Author's claim"

/-! ## Numbers and titles -/

-- A README heading that names no project is no title.
/-- info: true -/
#guard_msgs in
#eval
  isGenericTitle "Readme" && isGenericTitle "README" && isGenericTitle " Read me! " &&
    isGenericTitle "Introduction" && !isGenericTitle "Finite congruence lattices" &&
    ({ title := some "Readme", name := some "pkg" } : ProjectIdentity).shownTitle? == Option.none &&
    ({ title := some "A project" } : ProjectIdentity).shownTitle? == some "A project" &&
    CodeSite.titleOf "/tmp/x" {} { title := some "Readme", name := some "OAI" } == "OAI"

-- A node shown without a number is titled by its kind and its label, without Lean's prefix for
-- private names.
/-- info: true -/
#guard_msgs in
#eval
  NumberingMode.parse? "none" == some .none &&
    ({ label := `Demo.double_eq, kind := .theorem, unnumbered := true } : NodeDisplay).title ==
      "Theorem Demo.double_eq" &&
    ({ label := Lean.mkPrivateNameCore `Demo.Basic `Demo.helper, kind := .theorem,
       unnumbered := true } : NodeDisplay).title == "Theorem Demo.helper" &&
    ({ label := `thm, kind := .theorem, number? := some "6.1" } : NodeDisplay).title == "Theorem 6.1"

/-! ## A site generated from code -/

-- No numbers anywhere a reader could take for a paper's; the statement's source under it; the
-- claim in the node view; the counts and the explanation on the stats page. The result is the
-- list of the checks that fail.
/-- info: #[] -/
#guard_msgs in
#eval show IO (Array String) from do
  let root := System.FilePath.mk s!"/tmp/vbp-meaning-test-{← IO.monoNanosNow}"
  IO.FS.createDirAll (root / "Demo")
  try
    IO.FS.writeFile (root / "Demo" / "Basic.lean") BlueprintCodeSite.basicSource
    IO.FS.writeFile (root / "Demo" / "Hard.lean") "theorem hard : False := sorry\n"
    IO.FS.writeFile (root / "code.json") (toJson statedFixture).compress
    IO.FS.writeFile (root / "README.md") "# Readme\n\nA small project.\n"
    IO.FS.writeFile (root / "lake-manifest.json") "{\"name\": \"demo\", \"packages\": []}"
    IO.FS.writeFile (root / claimsFile) claimsText
    let code ← CodeSite.generate (root / "code.json") root Option.none
      ["--output", (root / "_out").toString, "--reproducible"]
    let html := root / "_out" / "html-multi"
    let index ← IO.FS.readFile (html / "index.html")
    let chapter ← IO.FS.readFile (html / "Demo___Basic" / "index.html")
    let statsPage ← IO.FS.readFile (html / "Project-Stats" / "index.html")
    let views ← IO.FS.readFile (html / "-verso-data" / "blueprint-node-views.json")
    let entries := ((Json.parse views).toOption.bind
        (fun j => (j.getObjValAs? (Array Json) "entries").toOption)).getD #[]
    let viewOf (l : String) : String := (entries.findSome? fun e =>
      if (e.getObjValAs? String "label").toOption == some l then
        (e.getObjValAs? String "html").toOption
      else Option.none).getD ""
    let stated := viewOf "Demo.double_eq"
    let checks : Array (String × Bool) := #[
      ("the generator succeeds", code == 0),
      -- the title: the package's name, not the README's generic heading
      ("title is the package's name", hasSubstr index "<title>demo</title>"),
      ("no Readme title on the stats page", !hasSubstr statsPage ">Readme<"),
      ("front page says there are no numbers",
        hasSubstr index "Nodes are named by their declarations and carry no numbers"),
      -- titles by kind and name, never "Theorem 1.2"
      ("node view titled by kind and name", hasSubstr stated ">Theorem Demo.double_eq</a>"),
      ("uses are titled by kind and name", hasSubstr stated ">Definition Demo.double</a>"),
      ("no numbered title on the chapter page",
        hasSubstr chapter "Lean code for Theorem Demo.double_eq" &&
          -- the first chapter's nodes would be numbered 1.1, 1.2, …
          !hasSubstr chapter "Theorem 1" && !hasSubstr chapter "Definition 1"),
      ("claim on the chapter card, with the paper's own number",
        hasSubstr chapter "Theorem 2.2 of Finite lattices (A. Author; v2)" &&
          hasSubstr chapter "Attested by R. Reader, 2026-01-31: compared with v2"),
      -- the statement's source, on the chapter card and in the node view
      ("source attribute on the chapter card",
        hasSubstr chapter "data-bp-statement-source=\"tex\""),
      ("source line on the chapter card", hasSubstr chapter "Informal statement from the \
        project's TeX blueprint · not checked against the Lean statement"),
      ("source sentence in the node view", hasSubstr stated "Informal statement from the \
        project's TeX blueprint. No tool has checked that this text says the same as the Lean \
        statement."),
      ("link to the explanation in the node view",
        hasSubstr stated s!"Project-Stats/#{Informal.Meaning.anchor}"),
      -- the author's claim, in the node view and on the stats page
      ("claim in the node view",
        hasSubstr stated "Theorem 2.2 of Finite lattices (A. Author; v2)"),
      ("attestation in the node view",
        hasSubstr stated "Attested by R. Reader, 2026-01-31: compared with v2"),
      ("claim on the stats page",
        hasSubstr statsPage "Theorem 2.2 of Finite lattices (A. Author; v2)"),
      -- a node without a statement has no source line
      ("no source line without a statement", !hasSubstr (viewOf "Demo.ax") "Informal statement from"),
      -- the counts
      ("kind groups", hasSubstr statsPage "6 nodes: 4 theorems, 2 definitions</p>"),
      ("Lean complete counts", hasSubstr statsPage "2 of 4 theorems, 1 of 2 definitions."),
      ("informal statement count", hasSubstr statsPage "Informal statements: 2 of 6 nodes have \
        one. No tool has checked any of them against the Lean statements."),
      ("the explanation of the marks", hasSubstr statsPage s!"id=\"{Informal.Meaning.anchor}\""),
      ("no old wording", !hasSubstr statsPage "fully proved" && !hasSubstr stated "Proved in Lean")]
    return (checks.filter (!·.2)).map (·.1)
  finally IO.FS.removeDirAll root

end Verso.VersoBlueprintTests.BlueprintMeaning
