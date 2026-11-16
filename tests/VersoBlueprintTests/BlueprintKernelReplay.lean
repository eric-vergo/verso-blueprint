/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

import VersoBlueprintTests.Blueprint.Support
import VersoBlueprint.Stats.Comparator
import VersoBlueprint.PreviewManifest
import VersoBlueprint.ReplayView
import VersoBlueprintTests.ComparatorFixtures.Match.Solution
import VersoBlueprintTests.ComparatorFixtures.Forged.Solution
import VersoBlueprintTests.ReplayFixtures.Tree
import VersoBlueprintTests.ReplayFixtures.Nested

/-!
The kernel replay of a build, and the words that depend on it.

A page says "proved", and a node gets the check mark, only when the toolchain's `leanchecker`
accepted the compiled modules concerned. These tests run the real checker on the Comparator
fixtures and pin the four states a reader can meet:

* the replay accepts: "Lean statement proved", the check mark;
* a forged proof (`ComparatorFixtures.Forged.Solution`: no `sorry`, no axiom, same statement,
  and a constant no kernel saw): the comparison's conditions are met, the replay rejects the
  module, and the headline says so with the checker's message;
* no checker: what the compiled files report, with a mark that is not a check mark;
* the replay stopped at its time limit: the same, with the reason.

They also pin the parts: SHA-256 against the standard's test vectors, the record of accepted
modules, the checker's output as it is read, and how the replay is run: every module of the
project in a process of its own, exactly once, a root module apart from its children, under a
memory limit and a time limit.
-/

namespace Verso.VersoBlueprintTests.BlueprintKernelReplay

open Lean
open Informal
open Informal.Commands
open Informal.Stats
open Verso.VersoBlueprintTests.Blueprint.Support

/-! ## SHA-256 -/

-- The test vectors of FIPS 180-4: the empty message, one block, two blocks; and a message
-- whose padding takes a block of its own (56 bytes).
/-- info: true -/
#guard_msgs in
#eval
  Sha256.hexOfString "" ==
      "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855" &&
    Sha256.hexOfString "abc" ==
      "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad" &&
    Sha256.hexOfString "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq" ==
      "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1" &&
    Sha256.hex (ByteArray.mk (Array.replicate 1000000 97)) ==
      "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0"

/-! ## The checker's arguments and output -/

-- What `leanchecker -v` says it replayed, the memory `footprint` reports, and a `/proc` field.
/--
info: (#[`A.B, `C], some 1753088, some 1610612736, some 183500800, none, some 8)
-/
#guard_msgs in
#eval
  (parseReplayed "replaying A.B\nsomething\nreplaying C\n",
   parseFootprint "zsh [7431]: 64-bit    Footprint: 1712 KB (16384 bytes per page)\n",
   parseFootprint "leanchecker [1]: 64-bit    Footprint: 1.5 GB (16384 bytes per page)",
   parseFootprint "x: Footprint: 175 MB", parseFootprint "no footprint here",
   procField? "Name:\tx\nRssAnon:\t       8 kB\n" "RssAnon:")

-- The default number of checker processes, and the memory limit of each: the processes run at
-- once share a quarter of the physical memory.
/-- info: ([1, 1, 2, 4, 4], [17179869184, 4294967296, 1073741824]) -/
#guard_msgs in
#eval
  ([1, 4, 8, 16, 24].map defaultReplayJobs,
   [(68719476736, 1), (68719476736, 4), (17179869184, 4)].map fun (m, j) => defaultMemoryLimit m j)

-- A module comes after the modules it imports.
/-- info: [`C, `B, `A, `D] -/
#guard_msgs in
#eval
  let imports : Lean.NameMap (Array Name) :=
    ({} : Lean.NameMap (Array Name)).insert `A #[`B, `C] |>.insert `B #[`C] |>.insert `D #[`A]
  (importsFirst #[`A, `B, `C, `D] imports).toList

-- The module and the message of a rejection, as `leanchecker` prints them.
/-- info: (some `Comparator.Solution, "(kernel) declaration type mismatch", none, "something else") -/
#guard_msgs in
#eval
  let rejected := parseRejection
    "leanchecker found a problem in Comparator.Solution\nuncaught exception: (kernel) declaration type mismatch\n"
  let other := parseRejection "something else\n"
  (rejected.1, rejected.2, other.1, other.2)

/-! ## What a replay establishes -/

private def result (outcome : Replay.Outcome) : Replay.Result :=
  { outcome, version := some "4.35.0", modules := #[`P.Solution, `P.Basic]
    rejectedModule := if outcome == .rejected then some `P.Solution else none
    message := if outcome == .rejected then some "(kernel) declaration type mismatch" else none
    limitSeconds := if outcome == .timedOut then some 900 else none }

-- Only an accepted replay that covers the modules asked about is a standing of `accepted`.
/-- info: true -/
#guard_msgs in
#eval
  let needed := #[`P.Solution]
  Replay.standing (some (result .accepted)) needed == .accepted &&
    Replay.standing (some (result .accepted)) #[`Mathlib.Data.Nat.Basic] ==
      .notReplayed "not part of a replayed module: Mathlib.Data.Nat.Basic is not among the \
        project's modules that were replayed" &&
    Replay.standing (some (result .rejected)) needed == .rejected (some `P.Solution) &&
    Replay.standing none needed ==
      .notReplayed "this site was generated without a kernel replay" &&
    Replay.standing (some (result .noChecker)) needed ==
      .notReplayed "no kernel checker was found" &&
    Replay.standing (some (result .timedOut)) needed ==
      .notReplayed "leanchecker (Lean 4.35.0) did not finish within 900 s" &&
    Replay.standing (some (result .off)) needed ==
      .notReplayed "the kernel replay was switched off for this build" &&
    Replay.standing (some (result .failed)) needed ==
      .notReplayed "leanchecker (Lean 4.35.0) could not run to a verdict"

/-! ## The headline's verdict -/

private def met : HeadlineTheorem :=
  { name := `main, solution := .same, sorryFree := some true, conditionsMet := true }

-- The four states. "Proved" is said in one of them.
/--
info: [("proved", "Lean statement proved"),
 ("rejected", "Proof rejected by the kernel checker"),
 ("not-replayed",
  "Same Lean statement as the challenge; no sorry; permitted axioms: as the compiled files report, not replayed by a kernel"),
 ("not-replayed",
  "Same Lean statement as the challenge; no sorry; permitted axioms: as the compiled files report, not replayed by a kernel"),
 ("not-replayed",
  "Same Lean statement as the challenge; no sorry; permitted axioms: as the compiled files report, not replayed by a kernel")]
-/
#guard_msgs (whitespace := lax) in
#eval
  [some (result .accepted), some (result .rejected), some (result .noChecker),
   some (result .timedOut), none].map fun replay? =>
    headlineVerdict met (Replay.standing replay? #[`P.Solution])

-- Without a standing the verdict is the one without a replay; a theorem that does not meet the
-- comparison's conditions keeps its verdict whatever the replay says.
/-- info: true -/
#guard_msgs in
#eval
  (headlineVerdict met).1 == "not-replayed" &&
    (headlineVerdict { met with conditionsMet := false, sorryFree := some false } .accepted).1 ==
      "sorry"

-- The line under the verdict: the checker with its version, and for a rejection its message.
/--
info: ["Kernel replay: leanchecker (Lean 4.35.0) accepted the project module the solution rests on.",
 "Kernel replay: leanchecker (Lean 4.35.0) rejected module P.Solution: (kernel) declaration type mismatch",
 "No kernel replay: no kernel checker was found.",
 "No kernel replay: leanchecker (Lean 4.35.0) did not finish within 900 s.",
 "No kernel replay: this site was generated without a kernel replay."]
-/
#guard_msgs (whitespace := lax) in
#eval
  [some (result .accepted), some (result .rejected), some (result .noChecker),
   some (result .timedOut), none].map fun replay? => replayNoteText replay? #[`P.Solution]

/-! ## A node's mark -/

private def mark (modules : Array Name := #[`P.Basic]) : BlockStatusMark :=
  { status := .proved, title := "Lean statement: no sorry; Lean proof: no sorry", kind := .theorem
    modules }

-- The check mark needs an accepted replay of the node's module; the other states have marks of
-- their own, and their words say what was established.
/--
info: [("proved",
  "✓",
  "Lean proof complete: no sorry in it or in what it uses; checked again in Lean's kernel by leanchecker (Lean 4.35.0)"),
 ("rejected", "⊘", "Lean proof not accepted: leanchecker (Lean 4.35.0) rejected this build (module P.Solution)"),
 ("reported",
  "◇",
  "Lean proof without sorry, as the compiled files report; not replayed by a kernel (no kernel checker was found)"),
 ("reported",
  "◇",
  "Lean proof without sorry, as the compiled files report; not replayed by a kernel (leanchecker (Lean 4.35.0) did not finish within 900 s)"),
 ("reported",
  "◇",
  "Lean proof without sorry, as the compiled files report; not replayed by a kernel (this site was generated without a kernel replay)")]
-/
#guard_msgs (whitespace := lax) in
#eval
  [some (result .accepted), some (result .rejected), some (result .noChecker),
   some (result .timedOut), none].map fun replay? =>
    let (kind, text) := statusGlyph (some (mark)) replay?
    (kind.modifier, kind.glyph, text)

-- A node whose declaration is in a module outside the project is not covered by the replay.
/--
info: ("reported",
 "Lean proof without sorry, as the compiled files report; not replayed by a kernel (not part of a replayed module: Mathlib.Data.Nat.Basic is not among the project's modules that were replayed)")
-/
#guard_msgs (whitespace := lax) in
#eval
  let (kind, text) := statusGlyph (some (mark #[`Mathlib.Data.Nat.Basic])) (some (result .accepted))
  (kind.modifier, text)

-- A declaration whose module is not known (it is declared where the site's data was captured,
-- in a file that need not be compiled) is covered by no replay.
/-- info: true -/
#guard_msgs in
#eval
  let (kind, text) := statusGlyph (some { mark #[] with unplaced := some `Main.forged })
    (some (result .accepted))
  kind.modifier == "reported" && text == "Lean proof without sorry, as the compiled files \
    report; not replayed by a kernel (not part of a replayed module: the module of Main.forged \
    is not known)"

-- A headline whose solution module is not among the project's replayed modules is not called
-- proved, whatever the replay accepted.
/-- info: true -/
#guard_msgs in
#eval
  let h : Headline := { challengeModule := `P.Challenge, solutionModule := `P.Solution }
  let covered := { h with solutionModules := #[`P.Basic, `P.Solution] }
  headlineStanding (some (result .accepted)) covered == .accepted &&
    headlineStanding (some (result .accepted)) h == .notReplayed "the solution module \
      P.Solution is not among the project's compiled modules, so it was not replayed" &&
    headlineStanding (some (result .rejected)) h == .rejected (some `P.Solution) &&
    (headlineVerdict met (headlineStanding (some (result .accepted)) h)).1 == "not-replayed"

-- The marks that are not about a replay do not change with it: an axiom beyond the standard
-- three keeps the warning mark under an accepted replay.
/-- info: true -/
#guard_msgs in
#eval
  (statusGlyph (some { mark with extraAxioms := #[`Demo.ax] }) (some (result .accepted))).1.modifier
    == "problem"

/-! ## The Project Stats page -/

private def stats (replay? : Option Replay.Result) : ProjectStats := {
  identity := { name := some "demo", toolchain := some "leanprover/lean4:v4.35.0" }
  headline := some {
    challengeModule := `P.Challenge, solutionModule := `P.Solution
    solutionModules := #[`P.Basic, `P.Solution]
    theorems := #[{ met with statement := "theorem main : True" }] }
  hasComparatorChallenge := true
  replay := replay? }

private def page (replay? : Option Replay.Result) : String :=
  (statsPageHtml { stats := stats replay? }).asString

-- Accepted: the verdict, the line under it, and the band with the checker, the modules and
-- what a replay leaves trusted.
/-- info: true -/
#guard_msgs in
#eval
  let html := page (some (result .accepted))
  hasSubstr html "data-bp-verdict=\"proved\"" && hasSubstr html ">Lean statement proved</span>" &&
    hasSubstr html "Kernel replay: leanchecker (Lean 4.35.0) accepted the 2 project modules the \
      solution rests on." &&
    hasSubstr html "class=\"bp_stats_band bp_stats_replay\"" &&
    hasSubstr html "data-bp-replay=\"accepted\"" &&
    hasSubstr html "Accepted: leanchecker (Lean 4.35.0) checked every constant of this" &&
    hasSubstr html "Modules replayed (2)" && hasSubstr html "<code>P.Solution</code>" &&
    hasSubstr html "It leaves trusted: the checker and Lean" &&
    hasSubstr html "The comparison runs no kernel"

-- Rejected: no "proved" as a verdict, the checker's message, the error state.
/-- info: true -/
#guard_msgs in
#eval
  let html := page (some (result .rejected))
  hasSubstr html "data-bp-verdict=\"rejected\"" &&
    hasSubstr html ">Proof rejected by the kernel checker</span>" &&
    !hasSubstr html ">Lean statement proved</span>" &&
    hasSubstr html "data-bp-replay=\"rejected\"" &&
    hasSubstr html "Rejected: leanchecker (Lean 4.35.0) found a problem in module P.Solution." &&
    hasSubstr html "class=\"bp_stats_replay_message\">(kernel) declaration type mismatch</pre>" &&
    hasSubstr html "Modules to replay (2)"

-- No checker, a replay stopped at its limit, and no replay at all: what the compiled files
-- report, the reason, and never "proved" as a verdict.
/-- info: true -/
#guard_msgs in
#eval
  let states := [(some (result .noChecker), "no kernel checker was found"),
    (some (result .timedOut), "leanchecker (Lean 4.35.0) did not finish within 900 s"),
    (some (result .off), "the kernel replay was switched off for this build"),
    (none, "this site was generated without a kernel replay")]
  states.all fun (replay?, why) =>
    let html := page replay?
    hasSubstr html "data-bp-verdict=\"not-replayed\"" &&
      hasSubstr html s!">{conditionsMetText}</span>" &&
      !hasSubstr html ">Lean statement proved</span>" &&
      hasSubstr html s!"No kernel replay: {why}." &&
      hasSubstr html "data-bp-replay=\"none\"" &&
      hasSubstr html s!"Not replayed by a kernel: {why}. The marks on this site say what the \
        compiled files report."

/-! ## Colour follows the replay -/

-- Every success colour is declared with its neutral value, in both themes; its green value
-- lives under a name of its own, and only the scope rules bring it in.
/-- info: true -/
#guard_msgs in
#eval
  let light := Informal.Commands.blueprintLightTokensCss
  let dark := Informal.Commands.darkTokens
  !StatusColors.successColors.isEmpty &&
  StatusColors.successColors.all fun c =>
    hasSubstr light s!"  {c.name}: {c.reported.1};\n" &&
      hasSubstr light s!"  {c.name}-accepted: {c.accepted.1};\n" &&
      hasSubstr light s!"  {c.name}-reported: {c.reported.1};\n" &&
      (dark.filter (·.1 == c.name)) == [(c.name, c.reported.2)] &&
      dark.contains (s!"{c.name}-accepted", c.accepted.2) &&
      c.accepted != c.reported

-- The scope rules: green inside an element an accepted replay stands behind, neutral again
-- inside one it does not; the rules ship with every page's tokens.
/-- info: true -/
#guard_msgs in
#eval
  let css := StatusColors.replayScopeCss
  let accepted := ((css.splitOn ".bp_replay_none").head!)
  let neutral := ((css.splitOn ".bp_replay_none").getD 1 "")
  hasSubstr css ".bp_replay_accepted,\n[data-bp-replay-scope=\"accepted\"] {" &&
    hasSubstr css (".bp_replay_none,\n.bp_replay_rejected,\n" ++
      "[data-bp-replay-scope]:not([data-bp-replay-scope=\"accepted\"]) {") &&
    StatusColors.successColors.all (fun c =>
      hasSubstr accepted s!"  {c.name}: var({c.name}-accepted);\n" &&
        !hasSubstr accepted s!"var({c.name}-reported)" &&
        hasSubstr neutral s!"  {c.name}: var({c.name}-reported);\n" &&
        !hasSubstr neutral s!"var({c.name}-accepted)") &&
    hasSubstr Informal.Commands.blueprintTokensCss css

-- The state of a site: accepted only under an accepted replay that leaves no node uncovered.
/--
info: [("accepted", "bp_replay_accepted", none),
 ("none", "bp_replay_none", some "as the compiled files report, not replayed by a kernel"),
 ("rejected", "bp_replay_rejected", some "this build was rejected by the kernel checker"),
 ("none", "bp_replay_none", some "as the compiled files report, not replayed by a kernel"),
 ("none", "bp_replay_none", some "as the compiled files report, not replayed by a kernel"),
 ("none", "bp_replay_none", some "as the compiled files report, not replayed by a kernel")]
-/
#guard_msgs (whitespace := lax) in
#eval
  [Replay.siteState (some (result .accepted)),
   Replay.siteState (some (result .accepted)) #[`literate.node],
   Replay.siteState (some (result .rejected)) #[`literate.node],
   Replay.siteState (some (result .noChecker)),
   Replay.siteState (some (result .timedOut)),
   Replay.siteState none].map fun site => (site.token, site.scopeClass, site.note?)

/-- info: true -/
#guard_msgs in
#eval
  Replay.siteState (some (result .accepted)) #[`a, `b] ==
      .none "2 nodes with Lean code are not part of a replayed module" &&
    (Replay.siteState none).sentence == "The counts are as the compiled files report, not \
      replayed by a kernel: this site was generated without a kernel replay." &&
    (Replay.siteState (some (result .rejected))).sentence == "This build was rejected by the \
      kernel checker: the counts say what the compiled files report, and nothing here counts \
      as checked by a kernel." &&
    (Replay.siteState (some (result .accepted))).sentence == ""

-- The Project Stats page per state: the class of the page and of the headline card, the
-- sentence beside the counts, and the words of the legend entries a replay would turn green.
/-- info: true -/
#guard_msgs in
#eval
  let page (site : Replay.SiteState) (replay? : Option Replay.Result) : String :=
    (statsPageHtml { stats := { stats replay? with progress := { formalizedWithAncestors := 2 } },
                     site }).asString
  let accepted := page .accepted (some (result .accepted))
  let rejected := page .rejected (some (result .rejected))
  let none := page (.none "no kernel checker was found") (some (result .noChecker))
  let partly := page (Replay.siteState (some (result .accepted)) #[`literate.node])
    (some (result .accepted))
  hasSubstr accepted "class=\"bp_project_stats bp_replay_accepted\"" &&
    hasSubstr accepted "data-bp-replay-state=\"accepted\"" &&
    hasSubstr accepted "class=\"bp_stats_theorem bp_replay_accepted\"" &&
    !hasSubstr accepted "bp_stats_replay_counts" &&
    hasSubstr accepted "title=\"Lean complete, dependencies too: 2\"" &&
  hasSubstr rejected "class=\"bp_project_stats bp_replay_rejected\"" &&
    hasSubstr rejected "class=\"bp_stats_theorem bp_replay_rejected\"" &&
    !hasSubstr rejected "bp_replay_accepted" &&
    hasSubstr rejected "bp_stats_replay_counts bp_stats_replay_counts_rejected" &&
    hasSubstr rejected "This build was rejected by the kernel checker: the counts say" &&
    hasSubstr rejected "Lean complete, dependencies too (this build was rejected by the kernel \
      checker): 2" &&
  hasSubstr none "class=\"bp_project_stats bp_replay_none\"" &&
    hasSubstr none "class=\"bp_stats_theorem bp_replay_none\"" &&
    !hasSubstr none "bp_replay_accepted" &&
    hasSubstr none "The counts are as the compiled files report, not replayed by a kernel: no \
      kernel checker was found." &&
    hasSubstr none "Lean complete, dependencies too (as the compiled files report, not replayed \
      by a kernel): 2" &&
  -- a node the replay does not cover keeps the counts neutral; the headline it does cover and
  -- the sentence that the replay accepted the build stay positive
  hasSubstr partly "class=\"bp_project_stats bp_replay_none\"" &&
    hasSubstr partly "class=\"bp_stats_theorem bp_replay_accepted\"" &&
    hasSubstr partly "bp_stats_replay_accepted bp_replay_accepted" &&
    hasSubstr partly "1 node with Lean code is not part of a replayed module."

-- A view built with nothing said about a replay is neutral: the default is never green.
/-- info: true -/
#guard_msgs in
#eval
  let html := (statsPageHtml { stats := stats (some (result .accepted)) }).asString
  hasSubstr html "class=\"bp_project_stats bp_replay_none\"" &&
    (progressBuckets {}).any (·.label == "Lean complete, dependencies too (as the compiled \
      files report, not replayed by a kernel)") &&
    (progressBuckets {} .accepted).any (·.label == "Lean complete, dependencies too")

-- A node of the graph: the class that turns its fill and border green, and its own colours
-- for a drawing without the stylesheet, only under an accepted replay. Under a replay that
-- covers the node and not everything it depends on, it is drawn as complete on its own.
/--
info: [("bp_graph_status_formalized_with_ancestors bp_graph_statement_formalized", "#64748b", "#64748b", "#ffffff"),
 ("bp_graph_status_formalized bp_graph_statement_formalized bp_replay_accepted", "#dcfce7", "#16a34a", "#111827"),
 ("bp_graph_status_formalized_with_ancestors bp_graph_statement_formalized bp_replay_accepted",
  "#166534",
  "#16a34a",
  "#ffffff")]
-/
#guard_msgs (whitespace := lax) in
#eval
  let node : Graph.NodeData := {
    label := `n, title := "n", displayLabel := "n", kind := some .theorem
    statementStatus := .formalized, proofStatus := .formalizedWithAncestors
    visual := { fillcolor := Graph.proofStatusFillColor .theorem .formalizedWithAncestors } }
  [Graph.NodeReplay.none, .accepted, .acceptedWithDependencies].map fun replay =>
    let n := node.withReplay replay
    (Graph.nodeStatusClasses .theorem n.statementStatus n.proofStatus n.warnings n.replay,
      n.visual.fillcolor, n.visual.color, n.visual.fontcolor)

-- Statuses that are not about `sorry`-free code keep their colours whatever the replay says.
/-- info: true -/
#guard_msgs in
#eval
  let node : Graph.NodeData := {
    label := `n, title := "n", displayLabel := "n", kind := some .theorem
    statementStatus := .ready, proofStatus := .incomplete
    visual := { fillcolor := Graph.proofStatusFillColor .theorem .incomplete,
                color := Graph.statementStatusBorderColor .ready } }
  (node.withReplay .none).visual == node.visual &&
    Graph.nodeStatusClasses .theorem .ready .incomplete {} ==
      "bp_graph_status_incomplete bp_graph_statement_ready"

-- What the replay establishes for the nodes of a graph: a node is accepted with its
-- dependencies only when every node it depends on, directly or not, is accepted too; a node
-- without Lean code establishes nothing either way; a cycle ends.
/--
info: [(`top, Informal.Graph.NodeReplay.accepted),
 (`mid, Informal.Graph.NodeReplay.accepted),
 (`leaf, Informal.Graph.NodeReplay.none),
 (`side, Informal.Graph.NodeReplay.acceptedWithDependencies),
 (`text, Informal.Graph.NodeReplay.none),
 (`loop, Informal.Graph.NodeReplay.acceptedWithDependencies)]
-/
#guard_msgs (whitespace := lax) in
#eval
  let replay? := some (result .accepted)
  let index : ReplayView.Index := {
    replay?
    standings := Std.HashMap.ofList [
      (`top, .accepted), (`mid, .accepted), (`side, .accepted), (`loop, .accepted),
      (`leaf, Replay.standing replay? #[`Script])]
    uses := Std.HashMap.ofList [
      (`top, #[`mid, `side]), (`mid, #[`leaf]), (`leaf, #[]), (`side, #[`text]), (`text, #[]),
      (`loop, #[`loop, `side])] }
  [`top, `mid, `leaf, `side, `text, `loop].map fun label => (label, index.nodeReplay label)

-- The nodes an accepted replay leaves uncovered keep the site neutral; without an accepted
-- replay the site is neutral as a whole and no node is singled out.
/-- info: true -/
#guard_msgs in
#eval
  let standings : Std.HashMap Name Replay.Standing := Std.HashMap.ofList [
    (`covered, .accepted), (`script, .notReplayed "not part of a replayed module")]
  let accepted : ReplayView.Index := { replay? := some (result .accepted), standings }
  let rejected : ReplayView.Index := { replay? := some (result .rejected), standings }
  accepted.uncovered == #[`script] && accepted.siteState.token == "none" &&
    rejected.uncovered == #[] && rejected.siteState == .rejected &&
    ({ replay? := some (result .accepted) } : ReplayView.Index).siteState == .accepted

/-! ## A code block in a module that was not replayed -/

-- A code block written in the Blueprint's own text records the module it was elaborated in. A
-- kernel replay covers the node only when that module is among the replayed ones.
#docs (Genre.Manual) literateDoc "Literate" :=
:::::::
:::theorem "replay.literate"
A statement.
:::

```lean "replay.literate"
theorem replay_literate_fact : True := by
  trivial
```
:::::::

/-- The module this file is. -/
private def thisModule : Name := `VersoBlueprintTests.BlueprintKernelReplay

/-- The replay `result .accepted` with `modules` as the modules replayed. -/
private def acceptedFor (modules : Array Name) : Replay.Result :=
  { result .accepted with modules }

-- The declaration of the block knows its module, in the captured node and in the render model.
/-- info: true -/
#guard_msgs in
#eval
  show CoreM Bool from do
    let state := Informal.Environment.informalExt.getState (← getEnv)
    let some node := state.data.get? (Name.mkSimple "replay.literate") | pure false
    let captured := node.literateCodes.flatMap (·.definedTheorems.map (·.module))
    let model : RenderModel := blueprint_render_model%
    let some rendered := model.nodes.find? (·.label == Name.mkSimple "replay.literate") | pure false
    let code := rendered.toBlockData.codeData.getD {}
    pure (captured == #[some thisModule] && code.modules == #[thisModule] &&
      code.unplaced == none)

-- The mark of such a node: the check mark when the replay accepted its module, the neutral
-- mark with the reason when the module is not among the replayed ones (a file run as a script,
-- never compiled), and when the module is not known at all.
/--
info: [("proved",
  "Lean proof complete: no sorry in it or in what it uses; checked again in Lean's kernel by leanchecker (Lean 4.35.0)"),
 ("reported",
  "Lean proof without sorry, as the compiled files report; not replayed by a kernel (not part of a replayed module: VersoBlueprintTests.BlueprintKernelReplay is not among the project's modules that were replayed)"),
 ("reported",
  "Lean proof without sorry, as the compiled files report; not replayed by a kernel (not part of a replayed module: the module of replay_literate_fact is not known)")]
-/
#guard_msgs (whitespace := lax) in
#eval
  let decl (module : Option Name) : CodeDeclData :=
    { name := `replay_literate_fact, provedStatus := .proved, module }
  let code (module : Option Name) : BlockCodeData :=
    { literateDeclarations := { definedTheorems := #[decl module] } }
  let glyph (replay : Replay.Result) (module : Option Name) :=
    let (kind, text) := statusGlyph (CodeSummary.statusMark? .theorem (some (code module)))
      (some replay)
    (kind.modifier, text)
  [glyph (acceptedFor #[thisModule]) (some thisModule),
   glyph (acceptedFor #[`P.Basic]) (some thisModule),
   glyph (acceptedFor #[`P.Basic]) none]

-- On the rendered page: the block says what stands behind it, and the symbol of its Lean link
-- is the check mark only when the replay covers the module.
/-- info: true -/
#guard_msgs in
#eval
  show IO Bool from do
    let model : RenderModel := blueprint_render_model%
    let render (replay? : Option Replay.Result) : IO String :=
      renderManualDocHtmlString extension_impls% literateDoc
        (model := { model with stats := { model.stats with replay := replay? } })
    let covered ← render (some (acceptedFor #[thisModule]))
    let uncovered ← render (some (acceptedFor #[`P.Basic]))
    let unreplayed ← render none
    let symbol (html mark : String) : Bool :=
      hasSubstr html s!"class=\"bp_code_status_symbol\">{mark}</span>"
    pure (
      hasSubstr covered "data-bp-replay-scope=\"accepted\"" && symbol covered "✓" &&
      hasSubstr uncovered "data-bp-replay-scope=\"none\"" && symbol uncovered "◇" &&
        !symbol uncovered "✓" && !hasSubstr uncovered "data-bp-replay-scope=\"accepted\"" &&
      hasSubstr unreplayed "data-bp-replay-scope=\"none\"" && symbol unreplayed "◇" &&
        !symbol unreplayed "✓")

/-! ## The real checker on the fixtures -/

/-- The package root, three directories above this test file. -/
private def packageRoot : CoreM System.FilePath := do
  let file : System.FilePath := ← getFileName
  let file ← if file.isAbsolute then pure file else return (← IO.currentDir) / file
  return (file.parent.bind (·.parent) |>.bind (·.parent)).getD "."

private def fixtureModule (scenario role : String) : Name :=
  `VersoBlueprintTests.ComparatorFixtures ++ scenario.toName ++ role.toName

/-- A replay configuration for the fixtures: this package's compiled modules, the search path
of this build for everything else, the toolchain's checker, and a record of its own. -/
private def config (record : System.FilePath) : CoreM ReplayConfig := do
  let own ← IO.FS.realPath ((← packageRoot) / ".lake" / "build" / "lib" / "lean")
  let mut importDirs := #[]
  for dir in ← searchPathRef.get do
    if ← dir.isDir then
      let dir ← IO.FS.realPath dir
      unless dir == own || importDirs.contains dir do importDirs := importDirs.push dir
  return { checker? := ← findChecker?, projectDirs := #[own], importDirs
           record? := some record }

private def describe (r : Replay.Result) : String × List Name × Option Name :=
  (toString (repr r.outcome), r.modules.toList.map fun m => m.components.getLast!,
    r.rejectedModule.map fun m => m.components.getLast!)

-- An honest solution is accepted, with the toolchain's version; a second run finds it in the
-- record and does not start the checker (which a limit of no time would stop); a record of its
-- own and no time gives a replay that did not finish, and that is not recorded as accepted.
/--
info: [("Informal.Replay.Outcome.accepted", [`Solution], none),
 ("Informal.Replay.Outcome.accepted", [`Solution], none),
 ("Informal.Replay.Outcome.timedOut", [`Solution], none),
 ("Informal.Replay.Outcome.timedOut", [`Solution], none)]
true
-/
#guard_msgs (whitespace := lax) in
#eval show CoreM Unit from do
  let dir ← IO.FS.createTempDir
  let wanted := #[fixtureModule "Match" "Solution"]
  let base ← config (dir / "record.json")
  let first ← replayBuild base wanted
  let second ← replayBuild { base with limitSeconds := 0 } wanted
  let fresh := { base with record? := some (dir / "other.json"), limitSeconds := 0 }
  let third ← replayBuild fresh wanted
  let fourth ← replayBuild fresh wanted
  IO.FS.removeDirAll dir
  IO.println (repr [describe first, describe second, describe third, describe fourth])
  IO.println (first.version == some Lean.versionString && first.checker == "leanchecker" &&
    third.limitSeconds == some 0)

-- The forged solution meets every condition of the comparison: the same statement, no `sorry`,
-- no axiom.
/-- info: [("CmpForged.double_odd", true, some true, [], [`Solution])] -/
#guard_msgs in
#eval show CoreM _ from do
  let layout : WorkspaceLayout :=
    { sourceDirs := #["tests"], libraryDirs := #[".lake/build/lib/lean"] }
  let config : ChallengeConfig := {
    challengeModule := fixtureModule "Forged" "Challenge"
    solutionModule := fixtureModule "Forged" "Solution" }
  let h ← Headline.compute config (← packageRoot) layout (← searchPathRef.get)
  return h.theorems.toList.map fun t =>
    (t.name.toString, t.conditionsMet, t.sorryFree, t.axioms.toList,
      h.solutionModules.toList.map fun m => m.components.getLast!)

-- The kernel replay rejects it, naming the module and the constant; the headline then says
-- rejected, a node of the site gets no check mark, and nothing is recorded as accepted.
/--
info: ("Informal.Replay.Outcome.rejected", [`Solution], some `Solution)
(true, true)
("rejected", "Proof rejected by the kernel checker")
"rejected"
("Informal.Replay.Outcome.rejected", [`Solution], some `Solution)
-/
#guard_msgs (whitespace := lax) in
#eval show CoreM Unit from do
  let dir ← IO.FS.createTempDir
  let solution := fixtureModule "Forged" "Solution"
  let base ← config (dir / "record.json")
  let r ← replayBuild base #[solution]
  let again ← replayBuild base #[solution]
  IO.FS.removeDirAll dir
  let message := r.message.getD ""
  IO.println (repr (describe r))
  IO.println (repr (hasSubstr message "sneaky", hasSubstr message "(kernel)"))
  IO.println (repr (headlineVerdict met (Replay.standing (some r) #[solution])))
  IO.println (repr (statusGlyph (some (mark #[solution])) (some r)).1.modifier)
  IO.println (repr (describe again))

-- Without a checker, and with the replay switched off, nothing is replayed and the result says
-- which; the modules that would have been replayed are still named.
/--
info: [("Informal.Replay.Outcome.noChecker", [`Solution], none),
 ("Informal.Replay.Outcome.off", [`Solution], none),
 ("Informal.Replay.Outcome.failed", [], none)]
[`NoSuchModule]
-/
#guard_msgs (whitespace := lax) in
#eval show CoreM Unit from do
  let dir ← IO.FS.createTempDir
  let wanted := #[fixtureModule "Match" "Solution"]
  let base ← config (dir / "record.json")
  let missing ← replayBuild { base with checker? := none } wanted
  let off ← replayBuild { base with off := true } wanted
  -- a module that is not compiled in the project cannot be replayed
  let absent ← replayBuild base #[`NoSuchModule]
  IO.FS.removeDirAll dir
  IO.println (repr [describe missing, describe off, describe absent])
  IO.println (repr absent.notCompiled.toList)

/-! ## One module per process -/

private def treeModule (path : String) : Name :=
  `VersoBlueprintTests.ReplayFixtures ++ path.toName

private def short (m : Name) : String :=
  ".".intercalate ((m.components.drop 2).map (·.toString))

-- Every module of an honest tree is replayed once, in a process that replays that module and
-- nothing else: also the root and the middle module, whose names are prefixes of their
-- children's; with one process at a time and with two.
/--
info: [("Informal.Replay.Outcome.accepted",
  ["Tree.Mid.Leaf", "Tree.Mid", "Tree.Leaf", "Tree"],
  [["Tree.Mid.Leaf"], ["Tree.Mid"], ["Tree.Leaf"], ["Tree"]]),
 ("Informal.Replay.Outcome.accepted",
  ["Tree", "Tree.Leaf", "Tree.Mid", "Tree.Mid.Leaf"],
  [["Tree"], ["Tree.Leaf"], ["Tree.Mid"], ["Tree.Mid.Leaf"]])]
-/
#guard_msgs (whitespace := lax) in
#eval show CoreM Unit from do
  let dir ← IO.FS.createTempDir
  let base ← config (dir / "record.json")
  let one ← replayBuildRuns { base with record? := none } #[treeModule "Tree"]
  let two ← replayBuildRuns { base with record? := none, jobs := 2 } #[treeModule "Tree"]
  IO.FS.removeDirAll dir
  let describeRuns (r : ReplayRun) (sorted : Bool) :=
    let runs := if sorted then r.runs.qsort (·.module.toString < ·.module.toString) else r.runs
    (toString (repr r.result.outcome), runs.toList.map (short ·.module),
      runs.toList.map fun run => run.replayed.toList.map short)
  IO.println (repr [describeRuns one false, describeRuns two true])

-- A replay of the honest root `Nested` on its own accepts it: its process does not replay the
-- forged child. The project's replay still replays the child and rejects the build, naming it.
-- The checker named on the directory of compiled modules itself replays the child as well, and
-- rejects.
/--
info: (true, ["Nested"])
("Informal.Replay.Outcome.rejected", some "Nested.Forged", true)
(false, true)
-/
#guard_msgs (whitespace := lax) in
#eval show CoreM Unit from do
  let dir ← IO.FS.createTempDir
  let base ← config (dir / "record.json")
  let some checker := base.checker? | throwError "no checker"
  let some lib := base.projectDirs[0]? | throwError "no compiled modules"
  let run (path : System.FilePath) : CoreM (Bool × List String) := do
    let searchPath := System.SearchPath.toString (base.importDirs.push path).toList
    let sysroot := (checker.parent.bind (·.parent)).getD "."
    let out ← IO.Process.output {
      cmd := checker.toString, args := #["-v", (treeModule "Nested").toString]
      env := #[("LEAN_PATH", some searchPath), ("LEAN_SYSROOT", some sysroot.toString)] }
    return (out.exitCode == 0, (parseReplayed out.stdout).toList.map short)
  let shadow := dir / "path"
  let made ← buildShadow lib (treeModule "Nested") shadow
  let alone ← run shadow
  let r ← replayBuild { base with record? := none } #[treeModule "Nested"]
  let plain ← run lib
  IO.FS.removeDirAll dir
  IO.println (repr (made && alone.1, alone.2))
  IO.println (repr (toString (repr r.outcome), r.rejectedModule.map short,
    hasSubstr (r.message.getD "") "ghost"))
  IO.println (repr (plain.1, plain.2.contains "Nested.Forged"))

-- Removing the directory made for a module leaves the project's compiled files as they were.
/-- info: true -/
#guard_msgs in
#eval show CoreM Bool from do
  let dir ← IO.FS.createTempDir
  let base ← config (dir / "record.json")
  let some lib := base.projectDirs[0]? | throwError "no compiled modules"
  let count := do return (← (lib / "VersoBlueprintTests" / "ReplayFixtures").walkDir).size
  let before ← count
  let made ← buildShadow lib (treeModule "Tree.Mid") (dir / "path")
  IO.FS.removeDirAll dir
  return made && before > 0 && (← count) == before

/-! ## The limits -/

/-- A stand-in for the checker: a script `bin/checker` in `dir` that runs `command`. -/
private def standIn (dir : System.FilePath) (command : String) : IO System.FilePath := do
  IO.FS.createDirAll (dir / "bin")
  let script := dir / "bin" / "checker"
  IO.FS.writeFile script s!"#!/bin/sh\nexec {command}\n"
  IO.setAccessRights script
    { user := { read := true, write := true, execution := true } }
  return script

-- A checker that holds more memory than its limit is stopped: no verdict, with the reason and
-- the module, and long before the time limit. Nothing is recorded as accepted.
/--
info: ("Informal.Replay.Outcome.overMemory", some "Tree.Leaf", true, true)
"the replay was stopped: leanchecker went over its memory limit of 64 MiB while it replayed module M"
"Informal.Replay.Outcome.overMemory"
-/
#guard_msgs (whitespace := lax) in
#eval show CoreM Unit from do
  let dir ← IO.FS.createTempDir
  -- `dd` keeps a buffer of its block size, written full of zeros, until it has copied `count`
  let checker ← standIn dir "dd if=/dev/zero of=/dev/null bs=268435456 count=1000000"
  let base ← config (dir / "record.json")
  let config := { base with checker? := some checker, memoryLimit? := some (64 * 1024 * 1024)
                            limitSeconds := 120 }
  let start ← IO.monoMsNow
  let r ← replayBuild config #[treeModule "Tree.Leaf"]
  let elapsed := (← IO.monoMsNow) - start
  let again ← replayBuild config #[treeModule "Tree.Leaf"]
  IO.FS.removeDirAll dir
  IO.println (repr (toString (repr r.outcome), r.stoppedModule.map short,
    r.memoryLimit == some (64 * 1024 * 1024), decide (elapsed < 60000)))
  IO.println (repr (r.whyNot.replace (toString (treeModule "Tree.Leaf")) "M"))
  IO.println (repr (toString (repr again.outcome)))

-- A checker that does not end is stopped at the time limit: no verdict, with the limit.
/-- info: ("Informal.Replay.Outcome.timedOut", some 1, true) -/
#guard_msgs in
#eval show CoreM Unit from do
  let dir ← IO.FS.createTempDir
  let checker ← standIn dir "sleep 60"
  let base ← config (dir / "record.json")
  let start ← IO.monoMsNow
  let r ← replayBuild { base with checker? := some checker, limitSeconds := 1 }
    #[treeModule "Tree.Leaf"]
  let elapsed := (← IO.monoMsNow) - start
  IO.FS.removeDirAll dir
  IO.println (repr (toString (repr r.outcome), r.limitSeconds, decide (elapsed < 30000)))

end Verso.VersoBlueprintTests.BlueprintKernelReplay
