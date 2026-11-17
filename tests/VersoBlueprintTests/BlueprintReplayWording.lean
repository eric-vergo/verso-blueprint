/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

import VersoBlueprint
import VersoBlueprintTests.Blueprint.Support

/-!
Every sentence a site prints about the kernel replay, for every state it can print it in.

A site says what was proved, checked or replayed in a node's mark, in the headline's verdict and
the line under it, beside counts and legend entries, above the counts, and in the replay band.
These tests enumerate the combinations a reader can meet and pin the words of each:

* the replay: accepted, rejected, stopped without a verdict (at the time or memory limit, or on
  an error), nothing replayed (no checker, the export over its limit, switched off, not run);
* the node: covered by the replay or not (a declaration it did not check, a module that is not
  known); its Lean code free of axioms, on Lean's standard axioms, on an axiom of the project,
  on the result of compiled code (`native_decide`), with a `sorry`;
* the headline: a Comparator challenge whose theorem meets the comparison's conditions, with
  and without an axiom the replay found under it; a site without a challenge.

Then, for every row, the words that would be false in its state are absent: "not replayed by a
kernel" after a replay that checked the code, "accepted" where nothing was, "checked again"
or "proved" where a replay did not stand behind the code.
-/

namespace Verso.VersoBlueprintTests.BlueprintReplayWording

open Lean
open Informal
open Informal.Commands
open Informal.Stats
open Verso.VersoBlueprintTests.Blueprint.Support

/-! ## The states -/

/-- The axiom `native_decide` adds for `P.native`, as Lean names it. -/
private def nativeAxiom : Name := `P.native._native.native_decide.ax_1_1

/-- A replay that ended with `outcome`, of the declarations of the nodes below: the replay found
`Demo.ax` under `P.ax`, the compiled-code axiom under `P.native` and `sorryAx` under `P.sorry`. -/
private def result (outcome : Replay.Outcome) : Replay.Result :=
  { outcome, version := some "4.35.0"
    declarations := replayOrder #[`P.clean, `P.std, `P.ax, `P.native, `P.sorry, `P.main,
      `P.assumed]
    axioms := #[(`P.ax, #[`Demo.ax]), (`P.native, #[nativeAxiom]), (`P.sorry, #[``sorryAx]),
      (`P.assumed, #[`Demo.ax])]
    constants := 120
    message := match outcome with
      | .rejected => some "(kernel) declaration type mismatch"
      | .failed => some "no export was written"
      | _ => none
    limitSeconds := if outcome == .timedOut then some 900 else none
    memoryLimit := if outcome == .overMemory then some (64 * 1024 * 1024) else none
    exportLimit := if outcome == .overExport then some (8 * 1024 * 1024) else none }

/-- Every state of a replay, by name. -/
private def replays : List (String × Option Replay.Result) := [
  ("accepted", some (result .accepted)),
  ("rejected", some (result .rejected)),
  ("timed out", some (result .timedOut)),
  ("over memory", some (result .overMemory)),
  ("failed", some (result .failed)),
  ("no checker", some (result .noChecker)),
  ("export over its limit", some (result .overExport)),
  ("switched off", some (result .off)),
  ("not run", none)]

/-- Whether a replay in this state checked the code it covers and accepted it. -/
private def acceptedState (replay? : Option Replay.Result) : Bool :=
  replay?.any (·.outcome == .accepted)

/-- Whether a replay in this state was started and stopped without a verdict. -/
private def stoppedState (replay? : Option Replay.Result) : Bool :=
  replay?.any (·.outcome.stoppedWithoutVerdict)

private def directSorry : Data.ProvedStatus :=
  .incomplete { knownSorry := #[{ location := .proof, origin := .direct }] }

/-- A theorem's mark with these declarations, axioms as the compiled files report them, and
status. -/
private def mark (declarations : Array Name) (extraAxioms : Array Name := #[])
    (status : Data.ProvedStatus := .proved) (unplaced : Option Name := none) : BlockStatusMark :=
  { status, title := "Lean statement: no sorry; Lean proof: no sorry", kind := .theorem
    declarations, extraAxioms, unplaced }

/-- The nodes, by name: whether a replay that accepted the build covers each, and its Lean
code. -/
private def nodes : List (String × Bool × BlockStatusMark) := [
  ("no axiom", true, mark #[`P.clean]),
  ("standard axioms only", true, mark #[`P.std]),
  ("an axiom of the project", true, mark #[`P.ax] #[`Demo.ax]),
  ("an axiom only the replay found", true, mark #[`P.assumed]),
  ("native_decide", true, mark #[`P.native] #[nativeAxiom]),
  ("a sorry", true, { mark #[`P.sorry] (status := directSorry) with
      title := "Lean statement: no sorry; Lean proof: sorry" }),
  ("not checked by the replay", false, mark #[`P.other]),
  ("module not known", false, mark #[] (unplaced := some `Main.local))]

/-! ## A node's mark -/

/-- The mark of every node in every state: the state, the node, the glyph and its text. -/
private def markRows : List (String × String × String × String) :=
  replays.flatMap fun (state, replay?) => nodes.map fun (node, _, m) =>
    let (kind, text) := statusGlyph (some m) replay?
    (state, node, kind.glyph, text)

/-- One row of a table, its cells separated by ` | `. -/
private def row (cells : List String) : String := " | ".intercalate cells

-- Every node in every state: the state, the node, the glyph, the glyph's text.
/--
info: accepted | no axiom | ✓ | Lean proof complete: no sorry in it or in what it uses; checked again in Lean's kernel by leanchecker (Lean 4.35.0), with everything it depends on
accepted | standard axioms only | ✓ | Lean proof complete: no sorry in it or in what it uses; checked again in Lean's kernel by leanchecker (Lean 4.35.0), with everything it depends on
accepted | an axiom of the project | ⚠ | Lean proof without sorry, as the compiled files report; replayed and accepted by leanchecker (Lean 4.35.0), with everything it depends on; it rests on an axiom outside Lean's standard three (Demo.ax), which a kernel accepts without a proof, so it is not shown as proved
accepted | an axiom only the replay found | ⚠ | Lean proof without sorry, as the compiled files report; replayed and accepted by leanchecker (Lean 4.35.0), with everything it depends on; it rests on an axiom outside Lean's standard three (Demo.ax), which a kernel accepts without a proof, so it is not shown as proved (the replay found it in the terms; the compiled files report none)
accepted | native_decide | ⚠ | Lean proof without sorry, as the compiled files report; replayed and accepted by leanchecker (Lean 4.35.0), with everything it depends on; it rests on the result of compiled code (P.native._native.native_decide.ax_1_1), which a kernel accepts without a proof, so it is not shown as proved
accepted | a sorry | ◐ | Lean code incomplete: a sorry in the proof or in what it uses (Lean statement: no sorry; Lean proof: sorry)
accepted | not checked by the replay | ◇ | Lean proof without sorry, as the compiled files report; not replayed by a kernel (not part of the replay: P.other is not among the declarations that were checked)
accepted | module not known | ◇ | Lean proof without sorry, as the compiled files report; not replayed by a kernel (not part of the replay: the module of Main.local is not known)
rejected | no axiom | ⊘ | Lean proof not accepted: leanchecker (Lean 4.35.0) rejected this build
rejected | standard axioms only | ⊘ | Lean proof not accepted: leanchecker (Lean 4.35.0) rejected this build
rejected | an axiom of the project | ⚠ | Lean proof without sorry, as the compiled files report, resting on an axiom outside Lean's standard three (Demo.ax); not accepted: leanchecker (Lean 4.35.0) rejected this build
rejected | an axiom only the replay found | ⊘ | Lean proof not accepted: leanchecker (Lean 4.35.0) rejected this build
rejected | native_decide | ⚠ | Lean proof without sorry, as the compiled files report, resting on the result of compiled code (P.native._native.native_decide.ax_1_1); not accepted: leanchecker (Lean 4.35.0) rejected this build
rejected | a sorry | ◐ | Lean code incomplete: a sorry in the proof or in what it uses (Lean statement: no sorry; Lean proof: sorry)
rejected | not checked by the replay | ⊘ | Lean proof not accepted: leanchecker (Lean 4.35.0) rejected this build
rejected | module not known | ⊘ | Lean proof not accepted: leanchecker (Lean 4.35.0) rejected this build
timed out | no axiom | ◇ | Lean proof without sorry, as the compiled files report; no verdict of a kernel replay (the replay with leanchecker (Lean 4.35.0) did not finish within 900 s)
timed out | standard axioms only | ◇ | Lean proof without sorry, as the compiled files report; no verdict of a kernel replay (the replay with leanchecker (Lean 4.35.0) did not finish within 900 s)
timed out | an axiom of the project | ⚠ | Lean proof without sorry, as the compiled files report, resting on an axiom outside Lean's standard three (Demo.ax); no verdict of a kernel replay (the replay with leanchecker (Lean 4.35.0) did not finish within 900 s)
timed out | an axiom only the replay found | ◇ | Lean proof without sorry, as the compiled files report; no verdict of a kernel replay (the replay with leanchecker (Lean 4.35.0) did not finish within 900 s)
timed out | native_decide | ⚠ | Lean proof without sorry, as the compiled files report, resting on the result of compiled code (P.native._native.native_decide.ax_1_1); no verdict of a kernel replay (the replay with leanchecker (Lean 4.35.0) did not finish within 900 s)
timed out | a sorry | ◐ | Lean code incomplete: a sorry in the proof or in what it uses (Lean statement: no sorry; Lean proof: sorry)
timed out | not checked by the replay | ◇ | Lean proof without sorry, as the compiled files report; no verdict of a kernel replay (the replay with leanchecker (Lean 4.35.0) did not finish within 900 s)
timed out | module not known | ◇ | Lean proof without sorry, as the compiled files report; no verdict of a kernel replay (the replay with leanchecker (Lean 4.35.0) did not finish within 900 s)
over memory | no axiom | ◇ | Lean proof without sorry, as the compiled files report; no verdict of a kernel replay (the replay was stopped: leanchecker (Lean 4.35.0) went over its memory limit of 64 MiB)
over memory | standard axioms only | ◇ | Lean proof without sorry, as the compiled files report; no verdict of a kernel replay (the replay was stopped: leanchecker (Lean 4.35.0) went over its memory limit of 64 MiB)
over memory | an axiom of the project | ⚠ | Lean proof without sorry, as the compiled files report, resting on an axiom outside Lean's standard three (Demo.ax); no verdict of a kernel replay (the replay was stopped: leanchecker (Lean 4.35.0) went over its memory limit of 64 MiB)
over memory | an axiom only the replay found | ◇ | Lean proof without sorry, as the compiled files report; no verdict of a kernel replay (the replay was stopped: leanchecker (Lean 4.35.0) went over its memory limit of 64 MiB)
over memory | native_decide | ⚠ | Lean proof without sorry, as the compiled files report, resting on the result of compiled code (P.native._native.native_decide.ax_1_1); no verdict of a kernel replay (the replay was stopped: leanchecker (Lean 4.35.0) went over its memory limit of 64 MiB)
over memory | a sorry | ◐ | Lean code incomplete: a sorry in the proof or in what it uses (Lean statement: no sorry; Lean proof: sorry)
over memory | not checked by the replay | ◇ | Lean proof without sorry, as the compiled files report; no verdict of a kernel replay (the replay was stopped: leanchecker (Lean 4.35.0) went over its memory limit of 64 MiB)
over memory | module not known | ◇ | Lean proof without sorry, as the compiled files report; no verdict of a kernel replay (the replay was stopped: leanchecker (Lean 4.35.0) went over its memory limit of 64 MiB)
failed | no axiom | ◇ | Lean proof without sorry, as the compiled files report; no verdict of a kernel replay (the replay could not run to a verdict: no export was written)
failed | standard axioms only | ◇ | Lean proof without sorry, as the compiled files report; no verdict of a kernel replay (the replay could not run to a verdict: no export was written)
failed | an axiom of the project | ⚠ | Lean proof without sorry, as the compiled files report, resting on an axiom outside Lean's standard three (Demo.ax); no verdict of a kernel replay (the replay could not run to a verdict: no export was written)
failed | an axiom only the replay found | ◇ | Lean proof without sorry, as the compiled files report; no verdict of a kernel replay (the replay could not run to a verdict: no export was written)
failed | native_decide | ⚠ | Lean proof without sorry, as the compiled files report, resting on the result of compiled code (P.native._native.native_decide.ax_1_1); no verdict of a kernel replay (the replay could not run to a verdict: no export was written)
failed | a sorry | ◐ | Lean code incomplete: a sorry in the proof or in what it uses (Lean statement: no sorry; Lean proof: sorry)
failed | not checked by the replay | ◇ | Lean proof without sorry, as the compiled files report; no verdict of a kernel replay (the replay could not run to a verdict: no export was written)
failed | module not known | ◇ | Lean proof without sorry, as the compiled files report; no verdict of a kernel replay (the replay could not run to a verdict: no export was written)
no checker | no axiom | ◇ | Lean proof without sorry, as the compiled files report; not replayed by a kernel (no kernel checker was found)
no checker | standard axioms only | ◇ | Lean proof without sorry, as the compiled files report; not replayed by a kernel (no kernel checker was found)
no checker | an axiom of the project | ⚠ | Lean proof without sorry, as the compiled files report, resting on an axiom outside Lean's standard three (Demo.ax); not replayed by a kernel (no kernel checker was found)
no checker | an axiom only the replay found | ◇ | Lean proof without sorry, as the compiled files report; not replayed by a kernel (no kernel checker was found)
no checker | native_decide | ⚠ | Lean proof without sorry, as the compiled files report, resting on the result of compiled code (P.native._native.native_decide.ax_1_1); not replayed by a kernel (no kernel checker was found)
no checker | a sorry | ◐ | Lean code incomplete: a sorry in the proof or in what it uses (Lean statement: no sorry; Lean proof: sorry)
no checker | not checked by the replay | ◇ | Lean proof without sorry, as the compiled files report; not replayed by a kernel (no kernel checker was found)
no checker | module not known | ◇ | Lean proof without sorry, as the compiled files report; not replayed by a kernel (no kernel checker was found)
export over its limit | no axiom | ◇ | Lean proof without sorry, as the compiled files report; not replayed by a kernel (the export of what the site's declarations depend on went over its size limit of 8 MiB, so the checker was not run)
export over its limit | standard axioms only | ◇ | Lean proof without sorry, as the compiled files report; not replayed by a kernel (the export of what the site's declarations depend on went over its size limit of 8 MiB, so the checker was not run)
export over its limit | an axiom of the project | ⚠ | Lean proof without sorry, as the compiled files report, resting on an axiom outside Lean's standard three (Demo.ax); not replayed by a kernel (the export of what the site's declarations depend on went over its size limit of 8 MiB, so the checker was not run)
export over its limit | an axiom only the replay found | ◇ | Lean proof without sorry, as the compiled files report; not replayed by a kernel (the export of what the site's declarations depend on went over its size limit of 8 MiB, so the checker was not run)
export over its limit | native_decide | ⚠ | Lean proof without sorry, as the compiled files report, resting on the result of compiled code (P.native._native.native_decide.ax_1_1); not replayed by a kernel (the export of what the site's declarations depend on went over its size limit of 8 MiB, so the checker was not run)
export over its limit | a sorry | ◐ | Lean code incomplete: a sorry in the proof or in what it uses (Lean statement: no sorry; Lean proof: sorry)
export over its limit | not checked by the replay | ◇ | Lean proof without sorry, as the compiled files report; not replayed by a kernel (the export of what the site's declarations depend on went over its size limit of 8 MiB, so the checker was not run)
export over its limit | module not known | ◇ | Lean proof without sorry, as the compiled files report; not replayed by a kernel (the export of what the site's declarations depend on went over its size limit of 8 MiB, so the checker was not run)
switched off | no axiom | ◇ | Lean proof without sorry, as the compiled files report; not replayed by a kernel (the kernel replay was switched off for this build)
switched off | standard axioms only | ◇ | Lean proof without sorry, as the compiled files report; not replayed by a kernel (the kernel replay was switched off for this build)
switched off | an axiom of the project | ⚠ | Lean proof without sorry, as the compiled files report, resting on an axiom outside Lean's standard three (Demo.ax); not replayed by a kernel (the kernel replay was switched off for this build)
switched off | an axiom only the replay found | ◇ | Lean proof without sorry, as the compiled files report; not replayed by a kernel (the kernel replay was switched off for this build)
switched off | native_decide | ⚠ | Lean proof without sorry, as the compiled files report, resting on the result of compiled code (P.native._native.native_decide.ax_1_1); not replayed by a kernel (the kernel replay was switched off for this build)
switched off | a sorry | ◐ | Lean code incomplete: a sorry in the proof or in what it uses (Lean statement: no sorry; Lean proof: sorry)
switched off | not checked by the replay | ◇ | Lean proof without sorry, as the compiled files report; not replayed by a kernel (the kernel replay was switched off for this build)
switched off | module not known | ◇ | Lean proof without sorry, as the compiled files report; not replayed by a kernel (the kernel replay was switched off for this build)
not run | no axiom | ◇ | Lean proof without sorry, as the compiled files report; not replayed by a kernel (this site was generated without a kernel replay)
not run | standard axioms only | ◇ | Lean proof without sorry, as the compiled files report; not replayed by a kernel (this site was generated without a kernel replay)
not run | an axiom of the project | ⚠ | Lean proof without sorry, as the compiled files report, resting on an axiom outside Lean's standard three (Demo.ax); not replayed by a kernel (this site was generated without a kernel replay)
not run | an axiom only the replay found | ◇ | Lean proof without sorry, as the compiled files report; not replayed by a kernel (this site was generated without a kernel replay)
not run | native_decide | ⚠ | Lean proof without sorry, as the compiled files report, resting on the result of compiled code (P.native._native.native_decide.ax_1_1); not replayed by a kernel (this site was generated without a kernel replay)
not run | a sorry | ◐ | Lean code incomplete: a sorry in the proof or in what it uses (Lean statement: no sorry; Lean proof: sorry)
not run | not checked by the replay | ◇ | Lean proof without sorry, as the compiled files report; not replayed by a kernel (this site was generated without a kernel replay)
not run | module not known | ◇ | Lean proof without sorry, as the compiled files report; not replayed by a kernel (this site was generated without a kernel replay)
-/
#guard_msgs in
#eval for (state, node, glyph, text) in markRows do IO.println (row [state, node, glyph, text])

/-! ## The site as a whole -/

/-- Every state of a site, by name: the replay, the nodes with Lean code it does not cover, the
nodes without `sorry` that rest on an axiom outside the standard three, and those axioms. -/
private def sites : List (String × Replay.SiteState) :=
  [("accepted, every node", Replay.siteState (some (result .accepted))),
   ("accepted, a node not covered", Replay.siteState (some (result .accepted)) #[`n]),
   ("accepted, a node on an axiom",
     Replay.siteState (some (result .accepted)) #[] #[`n] #[`Demo.ax]),
   ("accepted, two nodes on axioms",
     Replay.siteState (some (result .accepted)) #[] #[`n, `m] #[nativeAxiom, `Demo.ax]),
   ("accepted, both", Replay.siteState (some (result .accepted)) #[`a, `b] #[`n] #[`Demo.ax])] ++
  (replays.drop 1).map fun (state, replay?) => (state, Replay.siteState replay? #[`n] #[`m])

-- Every state of a site: its token, the words beside a legend entry or a count of `sorry`-free
-- code, the sentence after a card's description, the sentence above the counts.
/--
info: accepted, every node | accepted | - | - | -
accepted, a node not covered | none | the kernel replay accepted the build; on this site 1 node with Lean code is not part of the replay | Counted as the compiled files report: the kernel replay accepted the build, and on this site 1 node with Lean code is not part of the replay. | The kernel replay accepted the build, and the counts are as the compiled files report: 1 node with Lean code is not part of the replay.
accepted, a node on an axiom | none | the kernel replay accepted the build; on this site 1 node without sorry rests on the axiom Demo.ax | Counted as the compiled files report: the kernel replay accepted the build, and on this site 1 node without sorry rests on the axiom Demo.ax, which a kernel accepts without a proof, so it is not shown as proved. | The kernel replay accepted the build, and the counts are as the compiled files report: 1 node without sorry rests on the axiom Demo.ax, which a kernel accepts without a proof, so it is not shown as proved.
accepted, two nodes on axioms | none | the kernel replay accepted the build; on this site 2 nodes without sorry rest on the axioms Demo.ax, P.native._native.native_decide.ax_1_1 (the result of compiled code) | Counted as the compiled files report: the kernel replay accepted the build, and on this site 2 nodes without sorry rest on the axioms Demo.ax, P.native._native.native_decide.ax_1_1 (the result of compiled code), which a kernel accepts without a proof, so they are not shown as proved. | The kernel replay accepted the build, and the counts are as the compiled files report: 2 nodes without sorry rest on the axioms Demo.ax, P.native._native.native_decide.ax_1_1 (the result of compiled code), which a kernel accepts without a proof, so they are not shown as proved.
accepted, both | none | the kernel replay accepted the build; on this site 2 nodes with Lean code are not part of the replay, and 1 node without sorry rests on the axiom Demo.ax | Counted as the compiled files report: the kernel replay accepted the build, and on this site 2 nodes with Lean code are not part of the replay; 1 node without sorry rests on the axiom Demo.ax, which a kernel accepts without a proof, so it is not shown as proved. | The kernel replay accepted the build, and the counts are as the compiled files report: 2 nodes with Lean code are not part of the replay; 1 node without sorry rests on the axiom Demo.ax, which a kernel accepts without a proof, so it is not shown as proved.
rejected | rejected | this build was rejected by the kernel checker | The kernel checker rejected this build. | This build was rejected by the kernel checker: the counts say what the compiled files report, and nothing here counts as checked by a kernel.
timed out | none | as the compiled files report, with no verdict of a kernel replay | Counted as the compiled files report, with no verdict of a kernel replay. | The counts are as the compiled files report, with no verdict of a kernel replay: the replay with leanchecker (Lean 4.35.0) did not finish within 900 s.
over memory | none | as the compiled files report, with no verdict of a kernel replay | Counted as the compiled files report, with no verdict of a kernel replay. | The counts are as the compiled files report, with no verdict of a kernel replay: the replay was stopped: leanchecker (Lean 4.35.0) went over its memory limit of 64 MiB.
failed | none | as the compiled files report, with no verdict of a kernel replay | Counted as the compiled files report, with no verdict of a kernel replay. | The counts are as the compiled files report, with no verdict of a kernel replay: the replay could not run to a verdict: no export was written.
no checker | none | as the compiled files report, not replayed by a kernel | Counted as the compiled files report, not replayed by a kernel. | The counts are as the compiled files report, not replayed by a kernel: no kernel checker was found.
export over its limit | none | as the compiled files report, not replayed by a kernel | Counted as the compiled files report, not replayed by a kernel. | The counts are as the compiled files report, not replayed by a kernel: the export of what the site's declarations depend on went over its size limit of 8 MiB, so the checker was not run.
switched off | none | as the compiled files report, not replayed by a kernel | Counted as the compiled files report, not replayed by a kernel. | The counts are as the compiled files report, not replayed by a kernel: the kernel replay was switched off for this build.
not run | none | as the compiled files report, not replayed by a kernel | Counted as the compiled files report, not replayed by a kernel. | The counts are as the compiled files report, not replayed by a kernel: this site was generated without a kernel replay.
-/
#guard_msgs in
#eval for (name, site) in sites do
  IO.println (row [name, site.token, site.note?.getD "-", site.countSentence?.getD "-",
    if site.sentence.isEmpty then "-" else site.sentence])

-- The replay band's first sentence, per state.
/--
info: accepted | Accepted: leanchecker (Lean 4.35.0) checked 7 declarations and everything they depend on, 120 constants in all again in Lean's kernel, starting from an empty environment.
rejected | Rejected: leanchecker (Lean 4.35.0) found a problem in what this site's declarations depend on. Nothing on this site counts as checked by a kernel.
timed out | No verdict of a kernel replay: the replay with leanchecker (Lean 4.35.0) did not finish within 900 s. The marks on this site say what the compiled files report.
over memory | No verdict of a kernel replay: the replay was stopped: leanchecker (Lean 4.35.0) went over its memory limit of 64 MiB. The marks on this site say what the compiled files report.
failed | No verdict of a kernel replay: the replay could not run to a verdict: no export was written. The marks on this site say what the compiled files report.
no checker | Not replayed by a kernel: no kernel checker was found. The marks on this site say what the compiled files report.
export over its limit | Not replayed by a kernel: the export of what the site's declarations depend on went over its size limit of 8 MiB, so the checker was not run. The marks on this site say what the compiled files report.
switched off | Not replayed by a kernel: the kernel replay was switched off for this build. The marks on this site say what the compiled files report.
not run | Not replayed by a kernel: this site was generated without a kernel replay. The marks on this site say what the compiled files report.
-/
#guard_msgs in
#eval for (state, replay?) in replays do
  IO.println (row [state, (replay?.map Replay.Result.summary).getD noReplaySummary])

/-! ## The headline -/

/-- A theorem of the challenge that meets the comparison's conditions. -/
private def met (name : Name) : HeadlineTheorem :=
  { name, solution := .same, sorryFree := some true, conditionsMet := true }

private def headline : Headline :=
  { challengeModule := `P.Challenge, solutionModule := `P.Solution }

/-- The verdict and the line under it for a theorem in every state. -/
private def headlineRows (h : Headline) (t : HeadlineTheorem) : List String :=
  replays.map fun (state, replay?) =>
    let standing := headlineStanding replay? h t
    let (token, verdict) := headlineVerdict t standing
    row [state, token, verdict, replayNoteText replay? standing]

-- A theorem that meets the comparison's conditions and that the replay checks: the state, the
-- verdict's token, the verdict, the line under it.
/--
info: accepted | proved | Lean statement proved | Kernel replay: leanchecker (Lean 4.35.0) accepted this theorem and every constant it depends on, in this project, in its dependencies and in Lean's own library, starting from an empty environment.
rejected | rejected | Not accepted: the kernel checker rejected this build | Kernel replay: leanchecker (Lean 4.35.0) rejected this build: (kernel) declaration type mismatch
timed out | not-replayed | Same Lean statement as the challenge; no sorry; permitted axioms: as the compiled files report, with no verdict of a kernel replay | No verdict of a kernel replay: the replay with leanchecker (Lean 4.35.0) did not finish within 900 s.
over memory | not-replayed | Same Lean statement as the challenge; no sorry; permitted axioms: as the compiled files report, with no verdict of a kernel replay | No verdict of a kernel replay: the replay was stopped: leanchecker (Lean 4.35.0) went over its memory limit of 64 MiB.
failed | not-replayed | Same Lean statement as the challenge; no sorry; permitted axioms: as the compiled files report, with no verdict of a kernel replay | No verdict of a kernel replay: the replay could not run to a verdict: no export was written.
no checker | not-replayed | Same Lean statement as the challenge; no sorry; permitted axioms: as the compiled files report, not replayed by a kernel | No kernel replay: no kernel checker was found.
export over its limit | not-replayed | Same Lean statement as the challenge; no sorry; permitted axioms: as the compiled files report, not replayed by a kernel | No kernel replay: the export of what the site's declarations depend on went over its size limit of 8 MiB, so the checker was not run.
switched off | not-replayed | Same Lean statement as the challenge; no sorry; permitted axioms: as the compiled files report, not replayed by a kernel | No kernel replay: the kernel replay was switched off for this build.
not run | not-replayed | Same Lean statement as the challenge; no sorry; permitted axioms: as the compiled files report, not replayed by a kernel | No kernel replay: this site was generated without a kernel replay.
-/
#guard_msgs in
#eval for r in headlineRows headline (met `P.main) do IO.println r

-- The same for a theorem under which the replay found an axiom the verdict does not allow.
/--
info: accepted | axioms | Same Lean statement as the challenge; replayed and accepted by a kernel; it rests on an axiom outside Lean's standard three (Demo.ax), which a kernel accepts without a proof, so it is not shown as proved | Kernel replay: leanchecker (Lean 4.35.0) accepted this theorem and every constant it depends on, in this project, in its dependencies and in Lean's own library, starting from an empty environment; the replay found under it an axiom the verdict does not allow (Demo.ax), which a kernel accepts without a proof.
rejected | rejected | Not accepted: the kernel checker rejected this build | Kernel replay: leanchecker (Lean 4.35.0) rejected this build: (kernel) declaration type mismatch
timed out | not-replayed | Same Lean statement as the challenge; no sorry; permitted axioms: as the compiled files report, with no verdict of a kernel replay | No verdict of a kernel replay: the replay with leanchecker (Lean 4.35.0) did not finish within 900 s.
over memory | not-replayed | Same Lean statement as the challenge; no sorry; permitted axioms: as the compiled files report, with no verdict of a kernel replay | No verdict of a kernel replay: the replay was stopped: leanchecker (Lean 4.35.0) went over its memory limit of 64 MiB.
failed | not-replayed | Same Lean statement as the challenge; no sorry; permitted axioms: as the compiled files report, with no verdict of a kernel replay | No verdict of a kernel replay: the replay could not run to a verdict: no export was written.
no checker | not-replayed | Same Lean statement as the challenge; no sorry; permitted axioms: as the compiled files report, not replayed by a kernel | No kernel replay: no kernel checker was found.
export over its limit | not-replayed | Same Lean statement as the challenge; no sorry; permitted axioms: as the compiled files report, not replayed by a kernel | No kernel replay: the export of what the site's declarations depend on went over its size limit of 8 MiB, so the checker was not run.
switched off | not-replayed | Same Lean statement as the challenge; no sorry; permitted axioms: as the compiled files report, not replayed by a kernel | No kernel replay: the kernel replay was switched off for this build.
not run | not-replayed | Same Lean statement as the challenge; no sorry; permitted axioms: as the compiled files report, not replayed by a kernel | No kernel replay: this site was generated without a kernel replay.
-/
#guard_msgs in
#eval for r in headlineRows headline (met `P.assumed) do IO.println r

-- A challenge that permits the axiom: the same theorem is proved.
/-- info: true -/
#guard_msgs in
#eval
  let h := { headline with permittedAxioms := some #[`Demo.ax] }
  let t := { met `P.assumed with axiomsPermitted := some true }
  headlineVerdict t (headlineStanding (some (result .accepted)) h t) ==
    ("proved", "Lean statement proved")

/-! ## No sentence is false in its state -/

/-- The words that would be false in a state, as the reasons a row fails. -/
private def falseWords (replay? : Option Replay.Result) (covered : Bool) (text : String) :
    List String :=
  let says (w : String) := if hasSubstr text w then [w] else []
  if acceptedState replay? && covered then
    -- the replay checked this code: it was replayed, and a verdict was reached
    says "not replayed" ++ says "no verdict" ++ says "as the compiled files report, not"
  else if acceptedState replay? then
    says "accepted by" ++ says "checked again" ++ says "proof complete"
  else if replay?.any (·.outcome == .rejected) then
    says "accepted by" ++ says "checked again" ++ says "proof complete" ++ says "not replayed" ++
      says "no verdict"
  else if stoppedState replay? then
    -- a replay was started: "not replayed" would say that nothing was
    says "accepted" ++ says "checked again" ++ says "proof complete" ++ says "not replayed"
  else
    says "accepted" ++ says "checked again" ++ says "proof complete" ++ says "no verdict"

-- A node's mark: no false words, and the check mark exactly where an accepted replay covers
-- Lean code without `sorry` and without an axiom outside the standard three.
/-- info: [] -/
#guard_msgs in
#eval
  replays.flatMap fun (state, replay?) => nodes.filterMap fun (node, covered, m) =>
    let (kind, text) := statusGlyph (some m) replay?
    let clean := m.status.isProved && m.extraAxioms.isEmpty &&
      !(m.declarations.any fun d => (result .accepted).axioms.any (·.1 == d))
    let tick := acceptedState replay? && covered && clean
    let wrong := falseWords replay? covered text ++
      (if (kind.glyph == "✓") != tick then ["the check mark"] else [])
    if wrong.isEmpty then none else some (state, node, wrong)

-- The headline: the same for both theorems.
/-- info: [] -/
#guard_msgs in
#eval
  replays.flatMap fun (state, replay?) => [`P.main, `P.assumed].filterMap fun name =>
    let standing := headlineStanding replay? headline (met name)
    let (token, verdict) := headlineVerdict (met name) standing
    let text := verdict ++ " " ++ replayNoteText replay? standing
    let wrong := falseWords replay? true text ++
      (if (token == "proved") != (acceptedState replay? && name == `P.main) then ["proved"] else [])
    if wrong.isEmpty then none else some (state, name, wrong)

-- The site: after an accepted replay no sentence says that nothing was replayed; without one,
-- none says that anything was accepted.
/-- info: [] -/
#guard_msgs in
#eval
  sites.filterMap fun (name, site) =>
    let texts := [site.note?.getD "", site.countSentence?.getD "", site.sentence]
    let accepted := (name.splitOn "accepted").length > 1
    let wrong := texts.flatMap fun text =>
      if accepted then
        (if hasSubstr text "not replayed" || hasSubstr text "no verdict" then [text] else []) ++
          (if site != .accepted && !hasSubstr text "accepted the build" then [text] else [])
      else if hasSubstr text "accepted" then [text] else []
    if wrong.isEmpty then none else some (name, wrong)

/-! ## On the page -/

-- The Project Stats page shows the sentence and the legend words of its state, and the counts
-- are neutral in every state but an accepted replay of every node.
/-- info: [] -/
#guard_msgs in
#eval
  sites.filterMap fun (name, site) =>
    let html := (statsPageHtml { stats := { progress := { formalizedWithAncestors := 2 } }, site
      }).asString
    let checks := [
      ("sentence", site.sentence.isEmpty || hasSubstr html site.sentence),
      ("legend", hasSubstr html s!"Lean complete, dependencies too{(site.note?.map (s!" ({·})")).getD ""}"),
      ("scope", hasSubstr html s!"class=\"bp_project_stats {site.scopeClass}\""),
      ("neutral", (site == .accepted) == hasSubstr html "bp_project_stats bp_replay_accepted")]
    let failed := checks.filter (!·.2) |>.map (·.1)
    if failed.isEmpty then none else some (name, failed)

end Verso.VersoBlueprintTests.BlueprintReplayWording
