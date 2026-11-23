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
import VersoBlueprintTests.ReplayFixtures.Nested
import VersoBlueprintTests.ReplayFixtures.Reach
import VersoBlueprintTests.ReplayFixtures.Mixed

/-!
The kernel replay of a build, and the words that depend on it.

A page says "proved", and a node gets the check mark, only for a declaration that both checkers
of the toolchain, `con-leche` and `con-ron`, accepted together with every constant it depends on,
in the project, in its dependencies and in Lean's own library. These tests run the real checkers
on fixtures, and stand-ins for every answer a checker can give, and pin the states a reader can
meet:

* the replay accepts: "Lean statement proved", the check mark;
* a forged proof (`ComparatorFixtures.Forged.Solution`: no `sorry`, no axiom, same statement,
  and a constant no kernel saw): the comparison's conditions are met, the replay rejects the
  build, and the headline says so with the checker's message;
* a forged constant in a dependency (`ReplayFixtures.Reach` over
  `VersoBlueprintReplayDependency.Lemmas`): rejected just the same, while a declaration that does
  not depend on it is accepted;
* a module whose compiled file exists in two directories of the search path: no verdict, in
  either order of the path;
* a declaration that rests on an axiom of the project, or on `sorry`: not exported and not
  checked, while the rest of the project is checked;
* the checkers disagree, one declines, one gives no answer, one says it accepted too few
  declarations or an empty file: never accepted;
* no checker in the toolchain, a replay stopped at a limit (time, memory, the size of the
  export): what the compiled files report, with the reason, and a mark that is not a check mark.

They also pin the parts: SHA-256 against the standard's test vectors, each checker's output as it
is read, the export's census, the record of accepted exports, and the worker process that loads
the modules.
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

/-! ## The machine, and the checker's output -/

-- The memory `footprint` reports, a `/proc` field, and the default memory limit of the checker:
-- a quarter of the physical memory.
/-- info: (some 1753088, some 1610612736, some 183500800, none, some 8, 17179869184) -/
#guard_msgs in
#eval
  (parseFootprint "zsh [7431]: 64-bit    Footprint: 1712 KB (16384 bytes per page)\n",
   parseFootprint "leanchecker [1]: 64-bit    Footprint: 1.5 GB (16384 bytes per page)",
   parseFootprint "x: Footprint: 175 MB", parseFootprint "no footprint here",
   procField? "Name:\tx\nRssAnon:\t       8 kB\n" "RssAnon:",
   defaultMemoryLimit 68719476736)

-- Each checker's answer: by its exit status first and its words second. An acceptance needs
-- status 0, its line and a count of at least the export's declaration records (23 here): both
-- checkers accept an empty or cut-off file with status 0. Status 1 is a rejection only with the
-- words of one (con-leche's `invalid:`, con-ron's `rejected:`), an error with an uncaught
-- exception; 2 is a decline (in the words of Lean 4.35 and of 4.36); 3 and any other status are
-- no answer. The run times a checker adds to its lines are dropped.
/--
info: [(Informal.Replay.Answer.accepted, some 23, none),
 (Informal.Replay.Answer.accepted, some 23, none),
 (Informal.Replay.Answer.accepted, some 23, none),
 (Informal.Replay.Answer.noAnswer,
  some 0,
  some "status 0, and it said it accepted 0 declarations, but the export holds 23"),
 (Informal.Replay.Answer.noAnswer,
  some 10,
  some "status 0, and it said it accepted 10 declarations, but the export holds 23"),
 (Informal.Replay.Answer.noAnswer,
  none,
  some "status 0 without its line that it accepted the export: it wrote nothing"),
 (Informal.Replay.Answer.rejected,
  none,
  some "invalid: type mismatch in theorem clean [at theorem clean, fold position 31] (--verified)"),
 (Informal.Replay.Answer.rejected,
  none,
  some "rejected: type mismatch in theorem [at theorem clean, fold position 31] (--verified)"),
 (Informal.Replay.Answer.error, none, some "con-leche: uncaught exception: out of bounds"),
 (Informal.Replay.Answer.noAnswer,
  none,
  some "status 1 without its words of rejection: con-leche: something else"),
 (Informal.Replay.Answer.declined,
  none,
  some "con-leche: not implemented yet: use of the sorryAx axiom in value of bad [at theorem bad, fold position 302] (--verified)"),
 (Informal.Replay.Answer.declined,
  some 296,
  some "con-ron: declined (296 declarations checked, 1 skipped for tolerated axioms) (--verified): 1 via sorryAx; first skipped: bad"),
 (Informal.Replay.Answer.noAnswer, none, some "status 3: con-leche: fuel exhausted at Nat.rec"),
 (Informal.Replay.Answer.noAnswer,
  none,
  some "status 3: con-ron: trunc.ndjson:332: expected a key (byte 1)"),
 (Informal.Replay.Answer.noAnswer, none, some "status 134: memory allocation of 8 bytes failed")]
-/
#guard_msgs (whitespace := lax) in
#eval
  [parseAnswer 0 "con-leche: accepted 23 declarations (--verified)\n" "" 23,
   parseAnswer 0 "con-ron: accepted 23 declarations (--verified)\n" "" 23,
   -- Lean 4.36 adds a line on the standard error when it accepts
   parseAnswer 0 "con-leche: accepted 23 declarations (--verified)\n" "con-leche: note\n" 23,
   parseAnswer 0 "con-leche: accepted 0 declarations (--verified)\n" "" 23,
   parseAnswer 0 "con-ron: accepted 10 declarations (--verified)\n" "" 23,
   parseAnswer 0 "" "" 23,
   parseAnswer 1 "" "con-leche: invalid: type mismatch in theorem clean [at theorem clean, fold position 31] (--verified) t=0.0s\n" 23,
   parseAnswer 1 "" "con-ron: rejected: type mismatch in theorem [at theorem clean, fold position 31] (--verified) t=0.021s\n" 23,
   parseAnswer 1 "" "con-leche: uncaught exception: out of bounds\n" 23,
   parseAnswer 1 "" "con-leche: something else\n" 23,
   parseAnswer 2 "" "con-leche: not implemented yet: use of the sorryAx axiom in value of bad [at theorem bad, fold position 302] (--verified) t=0.0s\n" 23,
   parseAnswer 2 "" "con-ron: declined (296 declarations checked, 1 skipped for tolerated axioms) (--verified): 1 via sorryAx; first skipped: bad\n" 23,
   parseAnswer 3 "" "con-leche: fuel exhausted at Nat.rec\n" 23,
   parseAnswer 3 "" "con-ron: trunc.ndjson:332: expected a key (byte 1)\n" 23,
   parseAnswer 134 "" "memory allocation of 8 bytes failed\n" 23]

-- The verdict of the two: accepted only when both accept; a rejection with an acceptance is a
-- disagreement; a rejection wins over a decline or no answer; a stop at a limit, a decline and
-- no answer give no verdict, naming the checker.
/--
info: [(Informal.Replay.Outcome.accepted, none),
 (Informal.Replay.Outcome.disagreed, some "rejected: bad"),
 (Informal.Replay.Outcome.disagreed, some "rejected: bad"),
 (Informal.Replay.Outcome.rejected, some "rejected: bad"),
 (Informal.Replay.Outcome.declined, some "declined: sorryAx"),
 (Informal.Replay.Outcome.failed, some "con-ron (Lean 4.35.0) gave no answer (fuel exhausted)"),
 (Informal.Replay.Outcome.failed,
  some "con-leche (Lean 4.35.0) ended with an error (uncaught exception)"),
 (Informal.Replay.Outcome.timedOut, some "con-ron (Lean 4.35.0)"),
 (Informal.Replay.Outcome.overMemory, some "con-leche (Lean 4.35.0)"),
 (Informal.Replay.Outcome.failed, some "no checker ran")]
-/
#guard_msgs (whitespace := lax) in
#eval
  let run (name : String) (answer : Replay.Answer) (message : Option String := none) :
      Replay.CheckerRun := { name, version := some "4.35.0", answer, message }
  let ok (name : String) := run name .accepted
  [combineRuns #[ok "con-leche", ok "con-ron"],
   combineRuns #[ok "con-leche", run "con-ron" .rejected (some "rejected: bad")],
   combineRuns #[run "con-leche" .rejected (some "rejected: bad"), ok "con-ron"],
   combineRuns #[run "con-leche" .rejected (some "rejected: bad"),
     run "con-ron" .declined (some "declined: sorryAx")],
   combineRuns #[ok "con-leche", run "con-ron" .declined (some "declined: sorryAx")],
   combineRuns #[ok "con-leche", run "con-ron" .noAnswer (some "fuel exhausted")],
   combineRuns #[run "con-leche" .error (some "uncaught exception"), ok "con-ron"],
   combineRuns #[ok "con-leche", run "con-ron" .timedOut],
   combineRuns #[run "con-leche" .overMemory, ok "con-ron"],
   combineRuns #[]]

-- The census of an export: its declaration records and whether its last line is complete, also
-- when a piece of the file ends inside a line. A `quot` record is not counted.
/--
info: [{ bytes := 0, records := 0, endsWithNewline := false },
 { bytes := 68, records := 2, endsWithNewline := true },
 { bytes := 67, records := 2, endsWithNewline := false }]
-/
#guard_msgs (whitespace := lax) in
#eval
  let text := "{\"meta\":1}\n{\"in\":1}\n{\"thm\":{}}\n{\"quot\":{}}\n{\"inductive\":{}}\n{\"x\":0}\n"
  [censusOf ByteArray.empty, censusOf text.toUTF8, censusOf (text.dropEnd 1).copy.toUTF8]

-- Each checker runs with half the machine's threads, at most 8 and at least 2.
/-- info: [2, 2, 4, 8, 8] -/
#guard_msgs in
#eval [jobsFor 0, jobsFor 4, jobsFor 8, jobsFor 16, jobsFor 24]

-- The record of accepted exports is in the user's cache directory, never in a project.
/--
info: [some "/Users/a/Library/Caches/verso-blueprint/kernel-replay-checkers.json",
 some "/x/cache/verso-blueprint/kernel-replay-checkers.json",
 some "/home/a/.cache/verso-blueprint/kernel-replay-checkers.json",
 none,
 none]
-/
#guard_msgs (whitespace := lax) in
#eval
  [recordFileIn (some "/Users/a") (some "/x/cache") none (macOS := true) (windows := false),
   recordFileIn (some "/home/a") (some "/x/cache") none (macOS := false) (windows := false),
   recordFileIn (some "/home/a") (some " ") none (macOS := false) (windows := false),
   recordFileIn none none none (macOS := true) (windows := false),
   recordFileIn (some "/home/a") none none (macOS := false) (windows := true)].map
    (·.map (·.toString))

-- The worker an environment names: its program, what comes before the generator's own
-- arguments, then the worker's flag.
/-- info: (none, some ("/app/launcher", #["/tc/lib/lean", "/app/libgen.dylib", "--kernel-replay-worker"]), some ("/bin/vbp", #["--kernel-replay-worker"])) -/
#guard_msgs (whitespace := lax) in
#eval
  let shown (w : Option (System.FilePath × Array String)) := w.map fun (p, args) => (p.toString, args)
  (shown (workerOfLines " \n"), shown (workerOfLines "/app/launcher\n/tc/lib/lean\n/app/libgen.dylib\n"),
   shown (workerOfLines "/bin/vbp"))

/-! ## What a replay establishes -/

/-- The run of the checker `name` in a made-up replay. -/
private def run (name : String) (answer : Replay.Answer) (message : Option String := none) :
    Replay.CheckerRun :=
  { name, version := some "4.35.0", answer, message
    declarations := if answer == .accepted then some 3402 else none }

private def result (outcome : Replay.Outcome) : Replay.Result :=
  { outcome, version := some "4.35.0"
    declarations := replayOrder #[`P.main, `P.lemma]
    axioms := #[(`P.assumed, #[`P.ax]), (`P.unfinished, #[``sorryAx])]
    checkers := match outcome with
      | .accepted => #[run "con-leche" .accepted, run "con-ron" .accepted]
      | .rejected => #[run "con-leche" .rejected (some "invalid: type mismatch"),
          run "con-ron" .rejected (some "rejected: type mismatch")]
      | .disagreed => #[run "con-leche" .accepted,
          run "con-ron" .rejected (some "rejected: type mismatch")]
      | _ => #[]
    notCovered := #[(`P.script, "is not in the compiled modules that were loaded")]
    constants := 3409
    origins := #[{ kind := .project, name := "P", constants := 87 },
                 { kind := .dependency, name := "Mathlib", constants := 860 },
                 { kind := .toolchain, name := "Init, Std", constants := 2462 }]
    message := if outcome.isRejection then some "rejected: type mismatch"
      else if outcome == .noChecker then some "this project's Lean (v4.34.0) ships no con-leche or con-ron"
      else none
    limitSeconds := if outcome == .timedOut then some 900 else none }

-- Only an accepted replay that covers the declarations asked about is a standing of
-- `accepted`; a declaration the replay left out says why.
/-- info: true -/
#guard_msgs in
#eval
  let needed := #[`P.main]
  Replay.standing (some (result .accepted)) needed == .accepted &&
    Replay.standing (some (result .accepted)) #[`P.main, `Mathlib.other] ==
      .notReplayed "not part of the replay: Mathlib.other is not among the declarations that \
        were checked" &&
    Replay.standing (some (result .accepted)) #[`P.script] ==
      .notReplayed "not part of the replay: P.script is not in the compiled modules that were \
        loaded" &&
    Replay.standing (some (result .rejected)) needed == .rejected &&
    Replay.standing none needed ==
      .notReplayed "this site was generated without a kernel replay" &&
    Replay.standing (some (result .noChecker)) needed ==
      .notReplayed "this project's Lean (v4.34.0) ships no con-leche or con-ron" &&
    Replay.standing (some (result .timedOut)) needed ==
      .noVerdict "the replay with con-leche and con-ron (Lean 4.35.0) did not finish within 900 s" &&
    Replay.standing (some (result .disagreed)) needed == .rejected &&
    Replay.standing (some { result .declined with message := some "con-ron: declined: x" })
        needed ==
      .noVerdict "con-leche and con-ron (Lean 4.35.0) declined to check the export: con-ron: \
        declined: x" &&
    Replay.standing (some (result .off)) needed ==
      .notReplayed "the kernel replay was switched off for this build" &&
    Replay.standing (some { result .failed with message := some "no export was written" })
        needed ==
      .noVerdict "the replay could not run to a verdict: no export was written" &&
    Replay.standing (some { result .overMemory with memoryLimit := some (64 * 1024 * 1024) })
        needed ==
      .noVerdict "the replay was stopped: con-leche and con-ron (Lean 4.35.0) went over its memory \
        limit of 64 MiB" &&
    Replay.standing (some { result .overExport with exportLimit := some (8 * 1024 * 1024) })
        needed ==
      .notReplayed "the export of what the site's declarations depend on went over its size \
        limit of 8 MiB, so the checker was not run"

-- A declaration that rests on an axiom outside Lean's standard three is not exported, and so not
-- checked: both checkers decline an export that uses such an axiom. A `sorry` is such an axiom.
-- No list of permitted axioms makes it checked.
/-- info: true -/
#guard_msgs in
#eval
  let replay? := some (result .accepted)
  Replay.provedStanding replay? #[`P.main] == .accepted &&
    Replay.standing replay? #[`P.assumed] == .notChecked #[`P.ax] &&
    Replay.provedStanding replay? #[`P.assumed] == .notChecked #[`P.ax] &&
    Replay.provedStanding replay? #[`P.main, `P.unfinished] == .notChecked #[``sorryAx] &&
    Replay.provedStanding replay? #[`P.main] (unplaced := some `Main.forged) ==
      .notReplayed "not part of the replay: the module of Main.forged is not known" &&
    (Replay.Standing.notChecked #[`P.ax]).token == "none" &&
    (Replay.Standing.notChecked #[`P.ax]).why == "not checked: it rests on an axiom outside \
      Lean's standard three (P.ax), and a replay checks only what rests on the standard three \
      alone" &&
    !(Replay.provedStanding (some (result .disagreed)) #[`P.main]).isAccepted

/-! ## The headline's verdict -/

private def met : HeadlineTheorem :=
  { name := `P.main, solution := .same, sorryFree := some true, conditionsMet := true }

private def headline : Headline := { challengeModule := `P.Challenge, solutionModule := `P.Solution }

-- The states. "Proved" is said in one of them.
/--
info: [("proved", "Lean statement proved"),
 ("rejected", "Not accepted: a kernel checker rejected this build"),
 ("rejected", "Not accepted: the two kernel checkers disagree on this build"),
 ("not-replayed",
  "Same Lean statement as the challenge; no sorry; permitted axioms: as the compiled files report, not replayed by a kernel"),
 ("not-replayed",
  "Same Lean statement as the challenge; no sorry; permitted axioms: as the compiled files report, with no verdict of a kernel replay"),
 ("not-replayed",
  "Same Lean statement as the challenge; no sorry; permitted axioms: as the compiled files report, with no verdict of a kernel replay"),
 ("not-replayed",
  "Same Lean statement as the challenge; no sorry; permitted axioms: as the compiled files report, not replayed by a kernel")]
-/
#guard_msgs (whitespace := lax) in
#eval
  [some (result .accepted), some (result .rejected), some (result .disagreed),
   some (result .noChecker), some (result .timedOut), some (result .declined), none].map
    fun replay? => headlineVerdict met (headlineStanding replay? headline met) replay?

-- Without a standing the verdict is the one without a replay; a theorem that does not meet the
-- comparison's conditions keeps its verdict whatever the replay says; a theorem the replay did
-- not check, or that rests on an axiom outside the standard three, is not called proved, also
-- when the challenge permits that axiom.
/-- info: true -/
#guard_msgs in
#eval
  let replay? := some (result .accepted)
  (headlineVerdict met).1 == "not-replayed" &&
    (headlineVerdict { met with conditionsMet := false, sorryFree := some false } .accepted).1 ==
      "sorry" &&
    headlineStanding replay? headline { met with name := `P.other } ==
      .notReplayed "not part of the replay: P.other is not among the declarations that were \
        checked" &&
    headlineStanding replay? headline { met with name := `P.assumed } == .notChecked #[`P.ax] &&
    (headlineVerdict met (headlineStanding replay? headline { met with name := `P.assumed })).1
      == "axioms" &&
    headlineStanding replay? { headline with permittedAxioms := some #[`P.ax] }
      { met with name := `P.assumed } == .notChecked #[`P.ax]

-- The line under the verdict: the checkers with their version, and for a rejection which one
-- and its message.
/--
info: ["Kernel replay: con-leche and con-ron (Lean 4.35.0) each checked this theorem and every constant it depends on, in this project, in its dependencies and in Lean's own library, starting from its own built-in prelude, and both accepted it.",
 "Kernel replay: con-leche and con-ron (Lean 4.35.0) each checked this theorem and every constant it depends on, in this project, in its dependencies and in Lean's own library, starting from its own built-in prelude, and both accepted it (in an earlier run, for an export identical to this build's).",
 "Kernel replay: con-leche and con-ron (Lean 4.35.0) each checked this theorem and every constant it depends on, in this project, in its dependencies and in Lean's own library, starting from its own built-in prelude, and both accepted it (in this run, or in an earlier one for an export identical to this build's).",
 "Kernel replay: con-leche (Lean 4.35.0) and con-ron (Lean 4.35.0) rejected this build: rejected: type mismatch",
 "Kernel replay: the two checkers disagree on this build: con-leche (Lean 4.35.0) accepted it and con-ron (Lean 4.35.0) rejected it: rejected: type mismatch",
 "No kernel replay: this project's Lean (v4.34.0) ships no con-leche or con-ron.",
 "No verdict of a kernel replay: the replay with con-leche and con-ron (Lean 4.35.0) did not finish within 900 s.",
 "No kernel replay: this site was generated without a kernel replay.",
 "Kernel replay: not checked: it rests on an axiom outside Lean's standard three (P.ax), and a replay checks only what rests on the standard three alone."]
-/
#guard_msgs (whitespace := lax) in
#eval
  ([some (result .accepted), some { result .accepted with recorded := true },
    some (result .accepted).forReproducible, some (result .rejected), some (result .disagreed),
    some (result .noChecker), some (result .timedOut), none].map
    fun replay? => replayNoteText replay? (headlineStanding replay? headline met)) ++
  [replayNoteText (some (result .accepted)) (.notChecked #[`P.ax])]

/-! ## A node's mark -/

private def mark (declarations : Array Name := #[`P.lemma]) : BlockStatusMark :=
  { status := .proved, title := "Lean statement: no sorry; Lean proof: no sorry", kind := .theorem
    declarations }

-- The check mark needs an accepted replay of the node's declarations; the other states have
-- marks of their own, and their words say what was established.
/--
info: [("proved",
  "✓",
  "Lean proof complete: no sorry in it or in what it uses; checked again by con-leche and con-ron (Lean 4.35.0), with everything it depends on, and both accepted it"),
 ("rejected",
  "⊘",
  "Lean proof not accepted: con-leche (Lean 4.35.0) and con-ron (Lean 4.35.0) rejected this build"),
 ("rejected",
  "⊘",
  "Lean proof not accepted: the two checkers disagree on this build: con-leche (Lean 4.35.0) accepted it and con-ron (Lean 4.35.0) rejected it"),
 ("reported",
  "◇",
  "Lean proof without sorry, as the compiled files report; not replayed by a kernel (this project's Lean (v4.34.0) ships no con-leche or con-ron)"),
 ("reported",
  "◇",
  "Lean proof without sorry, as the compiled files report; no verdict of a kernel replay (the replay with con-leche and con-ron (Lean 4.35.0) did not finish within 900 s)"),
 ("reported",
  "◇",
  "Lean proof without sorry, as the compiled files report; not replayed by a kernel (this site was generated without a kernel replay)")]
-/
#guard_msgs (whitespace := lax) in
#eval
  [some (result .accepted), some (result .rejected), some (result .disagreed),
   some (result .noChecker), some (result .timedOut), none].map fun replay? =>
    let (kind, text) := statusGlyph (some (mark)) replay?
    (kind.modifier, kind.glyph, text)

-- A node with a declaration the replay did not check is not covered by it.
/--
info: ("reported",
 "Lean proof without sorry, as the compiled files report; not replayed by a kernel (not part of the replay: Mathlib.other is not among the declarations that were checked)")
-/
#guard_msgs (whitespace := lax) in
#eval
  let (kind, text) := statusGlyph (some (mark #[`P.lemma, `Mathlib.other])) (some (result .accepted))
  (kind.modifier, text)

-- A declaration whose module is not known (it is declared where the site's data was captured,
-- in a file that need not be compiled) is covered by no replay.
/-- info: true -/
#guard_msgs in
#eval
  let (kind, text) := statusGlyph (some { mark #[] with unplaced := some `Main.forged })
    (some (result .accepted))
  kind.modifier == "reported" && text == "Lean proof without sorry, as the compiled files \
    report; not replayed by a kernel (not part of the replay: the module of Main.forged is not \
    known)"

-- The marks that are not about a replay do not change with it: an axiom beyond the standard
-- three keeps the warning mark under an accepted replay. And an axiom that only the replay
-- found, in the terms, takes the check mark away as well: such a declaration is not checked.
/--
info: ("problem",
 "problem",
 "Lean proof without sorry, as the compiled files report; not checked by the kernel replay: it rests on an axiom outside Lean's standard three (P.ax), and a replay checks only what rests on Lean's standard three axioms alone, so it is not shown as proved (the replay found it in the terms; the compiled files report none)")
-/
#guard_msgs (whitespace := lax) in
#eval
  let reported := statusGlyph (some { mark with extraAxioms := #[`Demo.ax] })
    (some (result .accepted))
  let found := statusGlyph (some (mark #[`P.assumed])) (some (result .accepted))
  (reported.1.modifier, found.1.modifier, found.2)

/-! ## The Project Stats page -/

private def stats (replay? : Option Replay.Result) : ProjectStats := {
  identity := { name := some "demo", toolchain := some "leanprover/lean4:v4.35.0" }
  headline := some { headline with theorems := #[{ met with statement := "theorem main : True" }] }
  hasComparatorChallenge := true
  replay := replay? }

private def page (replay? : Option Replay.Result) : String :=
  (statsPageHtml { stats := stats replay? }).render

-- Accepted: the verdict, the line under it, and the band with the checker, what was checked,
-- where it comes from, what was left out, and what a replay leaves trusted.
/-- info: true -/
#guard_msgs in
#eval
  let html := page (some (result .accepted))
  hasSubstr html "data-bp-verdict=\"proved\"" && hasSubstr html ">Lean statement proved</span>" &&
    hasSubstr html "Kernel replay: con-leche and con-ron (Lean 4.35.0) each checked this \
      theorem and every constant it depends on" &&
    hasSubstr html "class=\"bp_stats_band bp_stats_replay\"" &&
    hasSubstr html "data-bp-replay=\"accepted\"" &&
    hasSubstr html "Accepted: con-leche and con-ron (Lean 4.35.0) each checked 2 declarations \
      and everything they depend on, 3,409 constants in all (87 of this project, 860 of Mathlib \
      and 2,462 of Lean's own library (Init, Std)), starting from its own built-in prelude, and \
      both accepted them." &&
    hasSubstr html "con-leche (Lean 4.35.0) accepted the export (3,402 declaration records)" &&
    hasSubstr html "con-ron (Lean 4.35.0) accepted the export (3,402 declaration records)" &&
    hasSubstr html "Declarations checked, each with everything it depends on (2)" &&
    hasSubstr html "<code>P.main</code>" &&
    hasSubstr html "Declarations of the site that the replay does not cover (1)" &&
    hasSubstr html "<code>P.script</code> is not in the compiled modules that were loaded" &&
    hasSubstr html "Declarations not checked: each rests on an axiom outside Lean's \
      standard three, as the replay found by walking the terms (2)" &&
    hasSubstr html "<code>P.assumed</code>: P.ax" &&
    hasSubstr html "It leaves trusted: the export" &&
    hasSubstr html "con-ron, a checker written in Rust" &&
    hasSubstr html "The comparison runs no kernel"

-- An export the checker accepted in an earlier run: the band says so.
/-- info: true -/
#guard_msgs in
#eval
  let html := page (some { result .accepted with recorded := true })
  hasSubstr html "Accepted: con-leche and con-ron (Lean 4.35.0) both accepted an export \
    identical to this build's in an earlier run: 2 declarations and everything they depend \
    on, 3,409 constants in all (87 of this project, 860 of Mathlib and 2,462 of Lean's own \
    library (Init, Std))."

-- Rejected: no "proved" as a verdict, the checker's message, the error state.
/-- info: true -/
#guard_msgs in
#eval
  let html := page (some (result .rejected))
  hasSubstr html "data-bp-verdict=\"rejected\"" &&
    hasSubstr html s!">{rejectedVerdictText}</span>" &&
    !hasSubstr html ">Lean statement proved</span>" &&
    hasSubstr html "data-bp-replay=\"rejected\"" &&
    hasSubstr html "Rejected: con-leche (Lean 4.35.0) and con-ron (Lean 4.35.0) rejected this \
      build (the export of this site's declarations and what they depend on)." &&
    hasSubstr html "class=\"bp_stats_replay_message\">rejected: type mismatch</pre>" &&
    hasSubstr html "Declarations to check (2)"

-- The checkers disagree: no "proved", the disagreement said plainly, which accepted and which
-- rejected, the error state.
/-- info: true -/
#guard_msgs in
#eval
  let html := page (some (result .disagreed))
  hasSubstr html "data-bp-verdict=\"rejected\"" &&
    hasSubstr html s!">{disagreedVerdictText}</span>" &&
    !hasSubstr html ">Lean statement proved</span>" &&
    hasSubstr html "data-bp-replay=\"rejected\"" &&
    hasSubstr html "Rejected: the two checkers disagree on this build: con-leche (Lean 4.35.0) \
      accepted it and con-ron (Lean 4.35.0) rejected it. Nothing on this site counts as checked \
      by a kernel." &&
    hasSubstr html "con-ron (Lean 4.35.0) rejected the export: rejected: type mismatch"

-- No checker, a replay stopped at its limit, and no replay at all: what the compiled files
-- report, the reason, and never "proved" as a verdict.
/-- info: true -/
#guard_msgs in
#eval
  let states := [(some (result .noChecker), "this project's Lean (v4.34.0) ships no con-leche or con-ron"),
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

-- A replay stopped at its limit: no verdict, and never "not replayed".
/-- info: true -/
#guard_msgs in
#eval
  let why := "the replay with con-leche and con-ron (Lean 4.35.0) did not finish within 900 s"
  let html := page (some (result .timedOut))
  hasSubstr html "data-bp-verdict=\"not-replayed\"" &&
    hasSubstr html s!">{conditionsMetNoVerdictText}</span>" &&
    hasSubstr html s!"No verdict of a kernel replay: {why}." &&
    hasSubstr html s!"No verdict of a kernel replay: {why}. The marks on this site say what \
      the compiled files report." &&
    !hasSubstr html "Not replayed by a kernel"

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

-- The state of a site: accepted only under an accepted replay that leaves no node uncovered
-- and no node without `sorry` resting on an axiom outside the standard three.
/--
info: [("accepted", "bp_replay_accepted", none),
 ("none",
  "bp_replay_none",
  some "the kernel replay accepted the build; on this site 1 node with Lean code is not part of the replay"),
 ("none",
  "bp_replay_none",
  some "the kernel replay accepted the build; on this site 1 node without sorry rests on an axiom outside Lean's standard three"),
 ("rejected", "bp_replay_rejected", some "this build was rejected by a kernel checker"),
 ("rejected", "bp_replay_rejected", some "this build was rejected by a kernel checker"),
 ("none", "bp_replay_none", some "as the compiled files report, not replayed by a kernel"),
 ("none", "bp_replay_none", some "as the compiled files report, with no verdict of a kernel replay"),
 ("none", "bp_replay_none", some "as the compiled files report, not replayed by a kernel")]
-/
#guard_msgs (whitespace := lax) in
#eval
  [Replay.siteState (some (result .accepted)),
   Replay.siteState (some (result .accepted)) #[`literate.node],
   Replay.siteState (some (result .accepted)) #[] #[`axiom.node],
   Replay.siteState (some (result .rejected)) #[`literate.node],
   Replay.siteState (some (result .disagreed)),
   Replay.siteState (some (result .noChecker)),
   Replay.siteState (some (result .timedOut)),
   Replay.siteState none].map fun site => (site.token, site.scopeClass, site.note?)

/-- info: true -/
#guard_msgs in
#eval
  Replay.siteState (some (result .accepted)) #[`a, `b] == .acceptedExcept 2 0 #[] &&
    Replay.siteState (some (result .accepted)) #[] #[`a] #[`P.ax] == .acceptedExcept 0 1 #[`P.ax] &&
    (Replay.siteState (some (result .accepted)) #[] #[`a] #[`P.ax]).sentence == "The kernel \
      replay accepted the build, and the counts are as the compiled files report: 1 node \
      without sorry rests on the axiom P.ax, so it was not checked and is not shown as \
      proved." &&
    (Replay.siteState none).sentence == "The counts are as the compiled files report, not \
      replayed by a kernel: this site was generated without a kernel replay." &&
    (Replay.siteState (some (result .rejected))).sentence == "This build was rejected by a \
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
                     site }).render
  let accepted := page .accepted (some (result .accepted))
  let rejected := page .rejected (some (result .rejected))
  let none := page (.none "this project's Lean (v4.34.0) ships no con-leche or con-ron")
    (some (result .noChecker))
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
    hasSubstr rejected "This build was rejected by a kernel checker: the counts say" &&
    hasSubstr rejected "Lean complete, dependencies too (this build was rejected by a kernel \
      checker): 2" &&
  hasSubstr none "class=\"bp_project_stats bp_replay_none\"" &&
    hasSubstr none "class=\"bp_stats_theorem bp_replay_none\"" &&
    !hasSubstr none "bp_replay_accepted" &&
    hasSubstr none "The counts are as the compiled files report, not replayed by a kernel: this \
      project's Lean (v4.34.0) ships no con-leche or con-ron." &&
    hasSubstr none "Lean complete, dependencies too (as the compiled files report, not replayed \
      by a kernel): 2" &&
  -- a node the replay does not cover keeps the counts neutral; the headline it does cover and
  -- the sentence that the replay accepted the build stay positive
  hasSubstr partly "class=\"bp_project_stats bp_replay_none\"" &&
    hasSubstr partly "class=\"bp_stats_theorem bp_replay_accepted\"" &&
    hasSubstr partly "bp_stats_replay_accepted bp_replay_accepted" &&
    hasSubstr partly "1 node with Lean code is not part of the replay."

-- A view built with nothing said about a replay is neutral: the default is never green.
/-- info: true -/
#guard_msgs in
#eval
  let html := (statsPageHtml { stats := stats (some (result .accepted)) }).render
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
      (`leaf, Replay.standing replay? #[`Script.decl])]
    uses := Std.HashMap.ofList [
      (`top, #[`mid, `side]), (`mid, #[`leaf]), (`leaf, #[]), (`side, #[`text]), (`text, #[]),
      (`loop, #[`loop, `side])] }
  [`top, `mid, `leaf, `side, `text, `loop].map fun label => (label, index.nodeReplay label)

-- The nodes an accepted replay leaves uncovered keep the site neutral, and so does a node
-- without `sorry` that rests on an axiom; a node with a `sorry` is not counted as complete, so
-- it does not. Without an accepted replay the site is neutral as a whole and no node is
-- singled out.
/-- info: true -/
#guard_msgs in
#eval
  let standings : Std.HashMap Name Replay.Standing := Std.HashMap.ofList [
    (`covered, .accepted), (`script, .notReplayed "not part of the replay")]
  let accepted : ReplayView.Index := { replay? := some (result .accepted), standings }
  let rejected : ReplayView.Index := { replay? := some (result .rejected), standings }
  let withAxioms : Std.HashMap Name Replay.Standing := Std.HashMap.ofList [
    (`covered, .accepted), (`assumed, .notChecked #[`P.ax]),
    (`unfinished, .notChecked #[``sorryAx])]
  let resting : ReplayView.Index := { replay? := some (result .accepted), standings := withAxioms }
  accepted.uncovered == #[`script] && accepted.siteState.token == "none" &&
    rejected.uncovered == #[] && rejected.siteState == .rejected &&
    resting.uncovered == #[] && resting.resting == #[`assumed] &&
    resting.siteState.token == "none" && !resting.accepted `assumed &&
    ({ replay? := some (result .accepted) } : ReplayView.Index).siteState == .accepted

-- A node whose data says its code has no `sorry`, while the replay found `sorryAx` under it, is
-- counted as complete: it keeps the site's counts neutral and is named. A node reported with its
-- `sorry` is not counted as complete, and does not.
/-- info: true -/
#guard_msgs in
#eval
  let standings : Std.HashMap Name Replay.Standing := Std.HashMap.ofList [
    (`covered, .accepted), (`claimed, .notChecked #[``sorryAx]), (`honest, .notChecked #[``sorryAx])]
  let index : ReplayView.Index := { replay? := some (result .accepted), standings
                                    reportedProved := ({} : NameHashSet).insert `claimed }
  index.resting == #[`claimed] && index.siteState.token == "none" &&
    index.restingAxioms == #[``sorryAx]

/-! ## A code block in a module that was not replayed -/

-- A code block written in the Blueprint's own text records the module it was elaborated in. A
-- kernel replay covers the node only when it checked the block's declaration.
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

/-- The replay `result .accepted` with `declarations` as the declarations checked. -/
private def acceptedFor (declarations : Array Name) : Replay.Result :=
  { result .accepted with declarations := replayOrder declarations }

-- The declaration of the block knows its module, in the captured node and in the render model,
-- and the render model asks a replay for it there.
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
    pure (captured == #[some thisModule] && code.declarations.size == 1 &&
      code.declarations.all (·.toString.endsWith "replay_literate_fact") &&
      code.placedDeclarations == code.declarations.map (·, thisModule) &&
      code.unplaced == none &&
      code.declarations.all fun d =>
        model.replayTargets.contains { name := d, module? := some thisModule })

-- The mark of such a node: the check mark when the replay checked its declaration, the neutral
-- mark with the reason when it did not (a file run as a script, never compiled), and when the
-- module is not known at all.
/--
info: [("proved",
  "Lean proof complete: no sorry in it or in what it uses; checked again by con-leche and con-ron (Lean 4.35.0), with everything it depends on, and both accepted it"),
 ("reported",
  "Lean proof without sorry, as the compiled files report; not replayed by a kernel (not part of the replay: replay_literate_fact is not among the declarations that were checked)"),
 ("reported",
  "Lean proof without sorry, as the compiled files report; not replayed by a kernel (not part of the replay: the module of replay_literate_fact is not known)")]
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
  [glyph (acceptedFor #[`replay_literate_fact]) (some thisModule),
   glyph (acceptedFor #[`P.main]) (some thisModule),
   glyph (acceptedFor #[`replay_literate_fact]) none]

-- On the rendered page: the block says what stands behind it, and the symbol of its Lean link
-- is the check mark only when the replay covers the declaration.
/-- info: true -/
#guard_msgs in
#eval
  show IO Bool from do
    let model : RenderModel := blueprint_render_model%
    let render (replay? : Option Replay.Result) : IO String :=
      renderManualDocHtmlString extension_impls% literateDoc
        (model := { model with stats := { model.stats with replay := replay? } })
    let declared := (model.nodes.find? (·.label == Name.mkSimple "replay.literate")).map
      (·.literateDeclarations.declarations.map (·.name)) |>.getD #[]
    let covered ← render (some (acceptedFor declared))
    let uncovered ← render (some (acceptedFor #[`P.main]))
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

/-- The compiled modules of this package. -/
private def ownLibrary : CoreM System.FilePath := do
  IO.FS.realPath ((← packageRoot) / ".lake" / "build" / "lib" / "lean")

private def comparatorFixture (scenario role : String) : Name :=
  `VersoBlueprintTests.ComparatorFixtures ++ scenario.toName ++ role.toName

private def reachModule : Name := `VersoBlueprintTests.ReplayFixtures.Reach
private def dependencyModule : Name := `VersoBlueprintReplayDependency.Lemmas
private def nestedModule : Name := `VersoBlueprintTests.ReplayFixtures.Nested
private def forgedChild : Name := `VersoBlueprintTests.ReplayFixtures.Nested.Forged

/-- A replay configuration for the fixtures: the search path `path` (this package's compiled
modules when none is given), the toolchain's checkers, a record of its own, and as the worker the
interpreter on `tests/KernelReplayWorkerMain.lean`, so that the modules are loaded in a process
that has not loaded them already. -/
private def config (record : System.FilePath) (path : Array System.FilePath := #[])
    (project : Array System.FilePath := #[]) : CoreM ReplayConfig := do
  let own ← ownLibrary
  let worker := (← packageRoot) / "tests" / "KernelReplayWorkerMain.lean"
  let lean ← IO.appPath
  return {
    checkers := ← findCheckers, jobs := 2, record? := some record
    sysroot? := lean.parent.bind (·.parent)
    searchPath := if path.isEmpty then #[own] else path
    projectDirs := if path.isEmpty then #[own] else project
    worker? := some (lean, #["--run", worker.toString]) }

/-- The replay of `targets` as a site's generator runs it (`ProjectStats.withKernelReplayAt`),
without a Comparator challenge. -/
private def replay (config : ReplayConfig) (targets : Array ReplayTarget) : IO Replay.Result := do
  let stats ← ({} : ProjectStats).withKernelReplayAt "." targets (config? := some config)
    (compare := false)
  return stats.replay.getD { outcome := .off }

private def target (module name : Name) : ReplayTarget := { name, module? := some module }

/-- Copy the compiled files of `module` from this package's build to `dir`, as the module `as`. -/
private def place (dir : System.FilePath) (module : Name) (as : Option Name := none) :
    CoreM Unit := do
  let own ← ownLibrary
  for ext in ["olean", "olean.server", "olean.private"] do
    let source := modToFilePath own module ext
    if ← source.pathExists then
      let file := modToFilePath dir (as.getD module) ext
      if let some parent := file.parent then IO.FS.createDirAll parent
      IO.FS.writeBinFile file (← IO.FS.readBinFile source)

private def describe (r : Replay.Result) : String × List Name × Bool :=
  (toString (repr r.outcome), (r.declarations.qsort (·.toString < ·.toString)).toList, r.recorded)

-- An honest solution is accepted, with the toolchain's version and what was checked. A second
-- run finds the identical export in the record and does not run the checker; with a record of
-- its own the checker runs again.
/--
info: [("Informal.Replay.Outcome.accepted", [`CmpMatch.double_cases, `CmpMatch.double_eq], false),
 ("Informal.Replay.Outcome.accepted", [`CmpMatch.double_cases, `CmpMatch.double_eq], true),
 ("Informal.Replay.Outcome.accepted", [`CmpMatch.double_cases, `CmpMatch.double_eq], false)]
(true, true, true, true)
-/
#guard_msgs (whitespace := lax) in
#eval show CoreM Unit from do
  let dir ← IO.FS.createTempDir
  let solution := comparatorFixture "Match" "Solution"
  let targets := #[target solution `CmpMatch.double_eq, target solution `CmpMatch.double_cases]
  let base ← config (dir / "record.json")
  let first ← replay base targets
  let second ← replay base targets
  let third ← replay { base with record? := some (dir / "other.json") } targets
  IO.FS.removeDirAll dir
  IO.println (repr [describe first, describe second, describe third])
  -- neither theorem rests on an axiom outside the standard three, and their constants come
  -- from this package and from Lean's own library
  IO.println (repr (first.version == some Lean.versionString &&
      first.checker == "con-leche and con-ron" &&
      first.checkers.map (·.answer) == #[.accepted, .accepted] &&
      first.checkers.all (·.declarations == some first.records),
    first.axioms.isEmpty && first.notCovered.isEmpty,
    first.constants > 2 && second.constants == first.constants,
    first.origins.map (·.kind) == #[.project, .toolchain] ||
      first.origins.map (·.kind) == #[.toolchain, .project]))

-- The forged solution: the replay rejects it, naming the constant; nothing is recorded as
-- accepted, so a second run rejects it again; the headline then says rejected and a node of
-- the site gets no check mark.
/--
info: ("Informal.Replay.Outcome.rejected", [`CmpForged.double_odd], false)
(true, true)
("rejected", "Not accepted: a kernel checker rejected this build")
"rejected"
("Informal.Replay.Outcome.rejected", [`CmpForged.double_odd], false)
-/
#guard_msgs (whitespace := lax) in
#eval show CoreM Unit from do
  let dir ← IO.FS.createTempDir
  let targets := #[target (comparatorFixture "Forged" "Solution") `CmpForged.double_odd]
  let base ← config (dir / "record.json")
  let r ← replay base targets
  let again ← replay base targets
  IO.FS.removeDirAll dir
  let message := r.message.getD ""
  IO.println (repr (describe r))
  IO.println (repr (hasSubstr message "sneaky",
    r.checkers.map (·.answer) == #[.rejected, .rejected]))
  let judged := { met with name := `CmpForged.double_odd }
  IO.println (repr (headlineVerdict judged (headlineStanding (some r) headline judged)))
  IO.println (repr (statusGlyph (some (mark #[`CmpForged.double_odd])) (some r)).1.modifier)
  IO.println (repr (describe again))

-- A record entry stands for one export, byte for byte: with the honest solution's export
-- recorded as accepted, the forged solution is still checked and rejected against the same
-- record, and so is the honest module once another declaration is asked for with it.
/--
info: [("Informal.Replay.Outcome.accepted", false),
 ("Informal.Replay.Outcome.rejected", false),
 ("Informal.Replay.Outcome.accepted", false),
 ("Informal.Replay.Outcome.accepted", true)]
-/
#guard_msgs (whitespace := lax) in
#eval show CoreM Unit from do
  let dir ← IO.FS.createTempDir
  let honest := comparatorFixture "Match" "Solution"
  let base ← config (dir / "record.json")
  let one ← replay base #[target honest `CmpMatch.double_eq]
  let forged ← replay base #[target (comparatorFixture "Forged" "Solution") `CmpForged.double_odd]
  let two ← replay base #[target honest `CmpMatch.double_eq, target honest `CmpMatch.double_cases]
  let again ← replay base #[target honest `CmpMatch.double_eq]
  IO.FS.removeDirAll dir
  IO.println (repr ([one, forged, two, again].map fun r => (toString (repr r.outcome), r.recorded)))

-- What a declaration depends on decides. The honest root over a forged child: its own theorem
-- depends on nothing of the child and is accepted, although the child's module is loaded with
-- it; a replay that is also asked for the child's constant rejects the build.
/--
info: ("Informal.Replay.Outcome.accepted", [`ReplayNested.root_true], false)
("Informal.Replay.Outcome.rejected", true)
-/
#guard_msgs (whitespace := lax) in
#eval show CoreM Unit from do
  let dir ← IO.FS.createTempDir
  let base ← config (dir / "record.json")
  let root ← replay base #[target nestedModule `ReplayNested.root_true]
  let both ← replay base #[target nestedModule `ReplayNested.root_true,
    target forgedChild `ReplayNested.ghost]
  IO.FS.removeDirAll dir
  IO.println (repr (describe root))
  IO.println (repr (toString (repr both.outcome), hasSubstr (both.message.getD "") "ghost"))

/-! ## A dependency -/

/-- A project and a dependency in directories of their own: `proj` holds `ReplayFixtures.Reach`,
`dep` the module it imports. -/
private def projectOverDependency (dir : System.FilePath) :
    CoreM (System.FilePath × System.FilePath) := do
  let proj := dir / "proj"
  let dep := dir / "dep"
  place proj reachModule
  place dep dependencyModule
  return (← IO.FS.realPath proj, ← IO.FS.realPath dep)

-- A theorem of the project whose proof rests on a constant of a dependency that no kernel
-- accepts: every constant of the project's own module is sound, and the replay still rejects
-- the build, because it checks what the theorem depends on wherever that is. It names the
-- dependency's constant. Both checkers reject it.
/--
info: ("Informal.Replay.Outcome.rejected", [`ReplayReach.double_odd], false)
(true, true)
("rejected", "Not accepted: a kernel checker rejected this build")
-/
#guard_msgs (whitespace := lax) in
#eval show CoreM Unit from do
  let dir ← IO.FS.createTempDir
  let (proj, dep) ← projectOverDependency dir
  let base ← config (dir / "record.json") #[proj, dep] #[proj]
  let r ← replay base #[target reachModule `ReplayReach.double_odd]
  IO.FS.removeDirAll dir
  IO.println (repr (describe r))
  IO.println (repr (hasSubstr (r.message.getD "") "ReplayDependency.helper",
    r.checkers.map (·.answer) == #[.rejected, .rejected]))
  let judged := { met with name := `ReplayReach.double_odd }
  IO.println (repr (headlineVerdict judged (headlineStanding (some r) headline judged)))

-- Declarations of the same project that do not depend on the forged constant are accepted,
-- one of them through a sound lemma of the dependency; the band's counts say where the checked
-- constants come from. A declaration that rests on an axiom of the project is not checked: the
-- replay finds the axiom in the terms and leaves it out of the export. Unsafe code, a declaration that is
-- not there, and one the site's data places in another module are left out, each with its
-- reason.
/--
info: ("Informal.Replay.Outcome.accepted", [`ReplayReach.double_zero, `ReplayReach.uses_fine], false)
[("ReplayReach.from_axiom", ["ReplayReach.assumed"])]
[("ReplayReach.double_zero", "accepted"),
 ("ReplayReach.uses_fine", "accepted"),
 ("ReplayReach.from_axiom", "not checked"),
 ("ReplayReach.unsafeValue", "none"),
 ("ReplayReach.nothing", "none"),
 ("ReplayReach.double", "none")]
[("ReplayReach.double",
  "is in module VersoBlueprintTests.ReplayFixtures.Reach in the compiled modules that were loaded, not in Other.Module"),
 ("ReplayReach.nothing", "is not in the compiled modules that were loaded"),
 ("ReplayReach.unsafeValue", "is unsafe code, which a kernel does not check")]
[(Informal.Replay.OriginKind.dependency, "VersoBlueprintReplayDependency", true),
 (Informal.Replay.OriginKind.project, "VersoBlueprintTests", true),
 (Informal.Replay.OriginKind.toolchain, "Init", true)]
-/
#guard_msgs (whitespace := lax) in
#eval show CoreM Unit from do
  let dir ← IO.FS.createTempDir
  let (proj, dep) ← projectOverDependency dir
  let base ← config (dir / "record.json") #[proj, dep] #[proj]
  let names := #[`ReplayReach.double_zero, `ReplayReach.uses_fine, `ReplayReach.from_axiom,
    `ReplayReach.unsafeValue, `ReplayReach.nothing]
  let r ← replay base (names.map (target reachModule) ++ #[target `Other.Module `ReplayReach.double])
  IO.FS.removeDirAll dir
  IO.println (repr (describe r))
  IO.println (repr (r.axioms.toList.map fun ((d, axioms) : Name × Array Name) =>
    (d.toString, axioms.toList.map fun (a : Name) => a.toString)))
  let standingOf (d : Name) : String :=
    match Replay.provedStanding (some r) #[d] with
    | .accepted => "accepted"
    | .notChecked _ => "not checked"
    | .rejected => "rejected"
    | .notReplayed _ | .noVerdict _ => "none"
  IO.println (repr ((names.push `ReplayReach.double).toList.map fun (d : Name) =>
    (d.toString, standingOf d)))
  IO.println (repr (r.notCovered.toList.map fun ((d, why) : Name × String) => (d.toString, why)))
  IO.println (repr ((r.origins.qsort (fun a b => toString (repr a.kind) < toString (repr b.kind))
    |>.map fun o => (o.kind, o.name, decide (o.constants > 0))).toList))

/-! ## One module, two files -/

-- The compiled file of the forged solution in the project's directory, and a harmless file of
-- the same module name in a dependency's. Which of them a build means depends on the order of
-- the search path, so the replay gives no verdict in either order, names the module, and the
-- headline is not compared. Nothing is accepted.
/--
info: #[("Informal.Replay.Outcome.failed", true, true), ("Informal.Replay.Outcome.failed", true, true)]
-/
#guard_msgs (whitespace := lax) in
#eval show CoreM Unit from do
  let dir ← IO.FS.createTempDir
  let forged := comparatorFixture "Forged" "Solution"
  place (dir / "proj") forged
  place (dir / "dep") (comparatorFixture "Match" "Solution") (as := some forged)
  let proj ← IO.FS.realPath (dir / "proj")
  let dep ← IO.FS.realPath (dir / "dep")
  let targets := #[target forged `CmpForged.double_odd]
  let mut out := #[]
  for path in [#[proj, dep], #[dep, proj]] do
    let base ← config (dir / "record.json") path #[proj]
    let r ← replay base targets
    out := out.push (toString (repr r.outcome),
      hasSubstr (r.message.getD "") s!"module {forged} has a compiled file in more than one \
        directory of the search path",
      !(Replay.provedStanding (some r) #[`CmpForged.double_odd]).isAccepted)
  IO.FS.removeDirAll dir
  IO.println (repr out)

-- A second name for the same file is not a second file: with a symbolic link to the project's
-- compiled file in the other directory the module is loaded, and the forged proof is rejected.
-- A hard link is a file of its own by its path, and gives no verdict.
/-- info: ("Informal.Replay.Outcome.rejected", "Informal.Replay.Outcome.failed") -/
#guard_msgs (whitespace := lax) in
#eval show CoreM Unit from do
  let dir ← IO.FS.createTempDir
  let forged := comparatorFixture "Forged" "Solution"
  place (dir / "proj") forged
  let proj ← IO.FS.realPath (dir / "proj")
  let targets := #[target forged `CmpForged.double_odd]
  let other (name : String) (link : System.FilePath → System.FilePath → IO Unit) :
      CoreM Replay.Result := do
    let file := modToFilePath (dir / name) forged "olean"
    if let some parent := file.parent then IO.FS.createDirAll parent
    link (modToFilePath proj forged "olean") file
    let base ← config (dir / s!"{name}.json") #[proj, ← IO.FS.realPath (dir / name)] #[proj]
    replay base targets
  let symbolic ← other "symbolic" fun source file => do
    discard <| IO.Process.output { cmd := "ln", args := #["-s", source.toString, file.toString] }
  let hard ← other "hard" IO.FS.hardLink
  IO.FS.removeDirAll dir
  IO.println (repr (toString (repr symbolic.outcome), toString (repr hard.outcome)))

/-! ## Without a verdict -/

-- Without the checkers, and with the replay switched off, nothing is checked and the result says
-- which; the declarations that would have been checked are still named. A toolchain that lacks
-- one checker is named with what it lacks. A declaration whose module is not compiled is left
-- out with that reason, and a site none of whose modules is compiled gets no verdict. A setting
-- of the old single-checker variable gives no verdict either, and says why.
/--
info: [("Informal.Replay.Outcome.noChecker", [`CmpMatch.double_eq], false),
 ("Informal.Replay.Outcome.noChecker", [`CmpMatch.double_eq], false),
 ("Informal.Replay.Outcome.off", [`CmpMatch.double_eq], false),
 ("Informal.Replay.Outcome.failed", [`CmpMatch.double_eq], false),
 ("Informal.Replay.Outcome.accepted", [`CmpMatch.double_eq], false),
 ("Informal.Replay.Outcome.failed", [`Script.fact], false)]
[true, true, true]
[("Script.fact", "is not compiled: module NoSuchModule has no compiled file on the search path")]
"the replay could not run to a verdict: none of the site's modules has a compiled file on the search path"
-/
#guard_msgs (whitespace := lax) in
#eval show CoreM Unit from do
  let dir ← IO.FS.createTempDir
  let honest := target (comparatorFixture "Match" "Solution") `CmpMatch.double_eq
  let script := target `NoSuchModule `Script.fact
  let base ← config (dir / "record.json")
  let missing ← replay { base with checkers := #[("con-leche", none), ("con-ron", none)] } #[honest]
  let oneMissing ← replay { base with checkers := base.checkers.modify 1 fun (n, _) => (n, none) }
    #[honest]
  let off ← replay { base with off := true } #[honest]
  let setting ← replay { base with setting? := some "set to a program" } #[honest]
  let mixed ← replay base #[honest, script]
  let absent ← replay base #[script]
  IO.FS.removeDirAll dir
  IO.println (repr [describe missing, describe oneMissing, describe off, describe setting,
    describe mixed, describe absent])
  let version := Lean.versionString
  IO.println (repr [missing.whyNot == s!"this project's Lean (v{version}) ships no con-leche or \
      con-ron",
    oneMissing.whyNot == s!"this project's Lean (v{version}) ships no con-ron",
    setting.whyNot == "the replay could not run to a verdict: set to a program"])
  IO.println (repr (mixed.notCovered.toList.map fun ((d, why) : Name × String) =>
    (d.toString, why)))
  IO.println (repr absent.whyNot)

/-! ## A project with an open proof -/

-- One `sorry` in the export would make both checkers decline it whole. So what rests on an
-- axiom outside Lean's standard three is left out of the export, with the axiom: the proved
-- theorem is checked and accepted by both; the open step and what uses it are marked as not
-- checked, with the reason; neither is shown as proved, and the site's counts stay neutral.
/--
info: ("Informal.Replay.Outcome.accepted", [`ReplayMixed.sound], false)
[("ReplayMixed.open_step", ["sorryAx"]), ("ReplayMixed.uses_open", ["sorryAx"])]
[("ReplayMixed.sound", "accepted"), ("ReplayMixed.open_step", "not checked"), ("ReplayMixed.uses_open", "not checked")]
("problem",
 "Lean proof without sorry, as the compiled files report; not checked by the kernel replay: it rests on an axiom outside Lean's standard three (sorryAx), and a replay checks only what rests on Lean's standard three axioms alone, so it is not shown as proved (the replay found it in the terms; the compiled files report none)")
#[Informal.Replay.Answer.accepted, Informal.Replay.Answer.accepted]
-/
#guard_msgs (whitespace := lax) in
#eval show CoreM Unit from do
  let dir ← IO.FS.createTempDir
  let base ← config (dir / "record.json")
  let mixed := `VersoBlueprintTests.ReplayFixtures.Mixed
  let names := #[`ReplayMixed.sound, `ReplayMixed.open_step, `ReplayMixed.uses_open]
  let r ← replay base (names.map (target mixed))
  IO.FS.removeDirAll dir
  IO.println (repr (describe r))
  IO.println (repr (r.axioms.toList.map fun ((d, axioms) : Name × Array Name) =>
    (d.toString, axioms.toList.map fun (a : Name) => a.toString)))
  IO.println (repr (names.toList.map fun (d : Name) =>
    (d.toString, match Replay.provedStanding (some r) #[d] with
      | .accepted => "accepted"
      | .notChecked _ => "not checked"
      | _ => "other")))
  -- the dependant's own Lean code has no sorry in the compiled files' report
  let (kind, text) := statusGlyph (some (mark #[`ReplayMixed.uses_open])) (some r)
  IO.println (repr (kind.modifier, text))
  IO.println (repr (r.checkers.map (·.answer)))

/-! ## Stand-ins for the checkers -/

/-- A stand-in for the checker `name`: a script `bin/<name>` in `dir` that runs `command`. -/
private def standIn (dir : System.FilePath) (name command : String) : IO System.FilePath := do
  IO.FS.createDirAll (dir / "bin")
  let script := dir / "bin" / name
  IO.FS.writeFile script s!"#!/bin/sh\n{command}\n"
  IO.setAccessRights script
    { user := { read := true, write := true, execution := true } }
  return script

/-- An export of `records` declaration records, with the key the worker would give it. -/
private def madeUpExport (dir : System.FilePath) (records : Nat) : IO Prepared := do
  let file := dir / "export.ndjson"
  let text := "{\"meta\":{}}\n" ++ String.join (List.replicate records "{\"thm\":{}}\n")
  IO.FS.writeFile file text
  return { declarations := #[`P.main], constants := 1
           key? := some { bytes := text.utf8ByteSize, hash := "0" } }

/-- The checking half of a replay on a made-up export of `records` declaration records, with
stand-ins for both checkers that run `leche` and `ron`, and the limits of `config`. -/
private def checkWith (dir : System.FilePath) (leche ron : String) (config : ReplayConfig := {})
    (records : Nat := 2) : IO Replay.Result := do
  let prepared ← madeUpExport dir records
  let checkers := #[("con-leche", ← standIn dir "con-leche" leche),
    ("con-ron", ← standIn dir "con-ron" ron)]
  checkExport config { checkers, sysroot := dir, version := some "4.35.0" } prepared
    (dir / "export.ndjson") ((← IO.monoMsNow) + config.limitSeconds * 1000)

private def accepts (name : String) (n : Nat := 2) : String :=
  s!"echo '{name}: accepted {n} declarations (--verified)'"

private def says (code : Nat) (text : String) : String :=
  s!"echo '{text}' >&2; exit {code}"

-- Every answer a checker can give, from stand-ins, against an export of two declaration records:
-- only two acceptances with a full count are an acceptance, and only that is recorded.
/--
info: [("accepted", ["accepted", "accepted"], true),
 ("disagreed", ["accepted", "rejected"], false),
 ("disagreed", ["rejected", "accepted"], false),
 ("rejected", ["rejected", "rejected"], false),
 ("declined", ["accepted", "declined"], false),
 ("declined", ["declined", "accepted"], false),
 ("failed", ["error", "accepted"], false),
 ("failed", ["accepted", "noAnswer"], false),
 ("failed", ["noAnswer", "accepted"], false),
 ("failed", ["noAnswer", "accepted"], false),
 ("failed", ["accepted", "noAnswer"], false),
 ("failed", ["accepted", "noAnswer"], false),
 ("failed", ["noAnswer", "noAnswer"], false)]
-/
#guard_msgs (whitespace := lax) in
#eval show IO Unit from do
  let cases : List (String × String) := [
    (accepts "con-leche", accepts "con-ron"),
    (accepts "con-leche", says 1 "con-ron: rejected: type mismatch in theorem [at thm t]"),
    (says 1 "con-leche: invalid: type mismatch in theorem t [at theorem t]", accepts "con-ron"),
    (says 1 "con-leche: invalid: bad", says 1 "con-ron: rejected: bad"),
    (accepts "con-leche", says 2 "con-ron: declined: use of the sorryAx axiom [at theorem t]"),
    (says 2 "con-leche: declined (1 declarations checked, 1 skipped for tolerated axioms)",
      accepts "con-ron"),
    (says 1 "con-leche: uncaught exception: index out of bounds", accepts "con-ron"),
    (accepts "con-leche", says 3 "con-ron: fuel exhausted"),
    (accepts "con-leche" 0, accepts "con-ron"),
    (accepts "con-leche" 1, accepts "con-ron"),
    (accepts "con-leche", "echo 'all fine'"),
    (accepts "con-leche", says 3 "usage: con-ron [--verified|--trusted] FILE.ndjson"),
    ("kill -9 $$", "kill -9 $$")]
  let mut out := #[]
  for (leche, ron) in cases do
    let dir ← IO.FS.createTempDir
    let r ← checkWith dir leche ron { record? := some (dir / "record.json") }
    let recorded ← (dir / "record.json").pathExists
    IO.FS.removeDirAll dir
    let token (a : Replay.Answer) := (toString (repr a)).drop "Informal.Replay.Answer.".length
    out := out.push ((toString (repr r.outcome)).drop "Informal.Replay.Outcome.".length |>.copy,
      r.checkers.toList.map fun c => (token c.answer).copy, recorded)
  IO.println (repr out.toList)

-- An empty export, and a cut-off one: both checkers accept them with status 0, so the census
-- decides. An export that is not the file the worker wrote, or whose last line is cut, is not
-- checked at all.
/--
info: ["failed", "failed", "failed"]
[true, true, true]
-/
#guard_msgs (whitespace := lax) in
#eval show IO Unit from do
  let dir ← IO.FS.createTempDir
  let empty ← checkWith dir (accepts "con-leche" 0) (accepts "con-ron" 0) (records := 0)
  -- the worker said 37 bytes; the file now holds fewer, and its last line is cut
  let prepared ← madeUpExport dir 2
  IO.FS.writeFile (dir / "export.ndjson") "{\"meta\":{}}\n{\"thm\":{}}\n{\"thm\""
  let checkers := #[("con-leche", ← standIn dir "con-leche" (accepts "con-leche" 1)),
    ("con-ron", ← standIn dir "con-ron" (accepts "con-ron" 1))]
  let cut ← checkExport {} { checkers, sysroot := dir, version := none } prepared
    (dir / "export.ndjson") ((← IO.monoMsNow) + 60000)
  let lineCut ← checkExport {} { checkers, sysroot := dir, version := none }
    { prepared with key? := some { bytes := 34, hash := "0" } } (dir / "export.ndjson")
    ((← IO.monoMsNow) + 60000)
  IO.FS.removeDirAll dir
  IO.println (repr ([empty, cut, lineCut].map fun r =>
    ((toString (repr r.outcome)).drop "Informal.Replay.Outcome.".length).copy))
  IO.println (repr [hasSubstr empty.whyNot "the export holds no declaration record",
    hasSubstr cut.whyNot "is not the one that was written",
    hasSubstr lineCut.whyNot "its last line is not complete"])

-- The record holds an acceptance for exactly the two programs that gave it: the same export with
-- one checker's file changed (same name, same size) is checked again.
/-- info: [false, true, false] -/
#guard_msgs in
#eval show IO Unit from do
  let dir ← IO.FS.createTempDir
  let config : ReplayConfig := { record? := some (dir / "record.json") }
  let first ← checkWith dir (accepts "con-leche") (accepts "con-ron") config
  let second ← checkWith dir (accepts "con-leche") (accepts "con-ron") config
  let changed ← checkWith dir (accepts "con-leche") (accepts "con-ron" ++ " ") config
  IO.FS.removeDirAll dir
  IO.println (repr [first.recorded, second.recorded, changed.recorded])

/-! ## The limits -/

-- An export larger than its limit is not checked: nothing replayed, with the reason.
/--
info: ("Informal.Replay.Outcome.overExport", some 1000)
"the export of what the site's declarations depend on went over its size limit of 0 MiB, so the checker was not run"
-/
#guard_msgs (whitespace := lax) in
#eval show CoreM Unit from do
  let dir ← IO.FS.createTempDir
  let base ← config (dir / "record.json")
  let r ← replay { base with exportLimit? := some 1000 }
    #[target (comparatorFixture "Match" "Solution") `CmpMatch.double_eq]
  IO.FS.removeDirAll dir
  IO.println (repr (toString (repr r.outcome), r.exportLimit))
  IO.println (repr r.whyNot)

-- A checker that holds more memory than its limit is stopped: no verdict, naming it, and long
-- before the time limit. Nothing is recorded as accepted.
/--
info: ("Informal.Replay.Outcome.overMemory", true, true)
"the replay was stopped: con-ron (Lean 4.35.0) went over its memory limit of 64 MiB"
"Informal.Replay.Outcome.overMemory"
-/
#guard_msgs (whitespace := lax) in
#eval show CoreM Unit from do
  let dir ← IO.FS.createTempDir
  -- `dd` keeps a buffer of its block size, written full of zeros, until it has copied `count`
  let hog := "exec dd if=/dev/zero of=/dev/null bs=268435456 count=1000000"
  let limit := 64 * 1024 * 1024
  let config : ReplayConfig := { memoryLimit? := some limit, limitSeconds := 120
                                 record? := some (dir / "record.json") }
  let start ← IO.monoMsNow
  let r ← checkWith dir (accepts "con-leche") hog config
  let elapsed := (← IO.monoMsNow) - start
  let again ← checkWith dir (accepts "con-leche") hog config
  IO.FS.removeDirAll dir
  IO.println (repr (toString (repr r.outcome), r.memoryLimit == some limit,
    decide (elapsed < 60000)))
  IO.println (repr r.whyNot)
  IO.println (repr (toString (repr again.outcome)))

-- A checker that does not end is stopped at the time limit: no verdict, with the limit.
/-- info: ("Informal.Replay.Outcome.timedOut", some 1, true) -/
#guard_msgs in
#eval show CoreM Unit from do
  let dir ← IO.FS.createTempDir
  let start ← IO.monoMsNow
  let r ← checkWith dir "exec sleep 60" (accepts "con-ron") { limitSeconds := 1 }
  let elapsed := (← IO.monoMsNow) - start
  IO.FS.removeDirAll dir
  IO.println (repr (toString (repr r.outcome), r.limitSeconds, decide (elapsed < 30000)))

-- A checker that writes far more than a message is not held up, and what is kept is bounded.
/-- info: ("Informal.Replay.Outcome.failed", true) -/
#guard_msgs in
#eval show CoreM Unit from do
  let dir ← IO.FS.createTempDir
  let r ← checkWith dir "head -c 20000000 /dev/zero | tr '\\0' 'x'; exit 3" (accepts "con-ron")
    { limitSeconds := 60 }
  IO.FS.removeDirAll dir
  IO.println (repr (toString (repr r.outcome), decide ((r.message.getD "").length < 4000)))

-- The whole replay has the time limit too: with no time, the worker is not even started.
/-- info: ("Informal.Replay.Outcome.timedOut", some 0) -/
#guard_msgs in
#eval show CoreM Unit from do
  let dir ← IO.FS.createTempDir
  let base ← config (dir / "record.json")
  let r ← replay { base with limitSeconds := 0 }
    #[target (comparatorFixture "Match" "Solution") `CmpMatch.double_eq]
  IO.FS.removeDirAll dir
  IO.println (repr (toString (repr r.outcome), r.limitSeconds))

/-! ## The headline, compared where the replay exports -/

/-- A project root with a `comparator.json` for the Comparator fixture `scenario`. -/
private def challengeRoot (dir : System.FilePath) (scenario : String) (theorems : Array Name) :
    IO System.FilePath := do
  let root := dir / scenario
  IO.FS.createDirAll root
  IO.FS.writeFile (root / "comparator.json") (Json.mkObj [
    ("challenge_module", toJson (comparatorFixture scenario "Challenge")),
    ("solution_module", toJson (comparatorFixture scenario "Solution")),
    ("theorem_names", toJson theorems),
    ("permitted_axioms", toJson #[``propext, ``Quot.sound, ``Classical.choice])]).compress
  return root

-- A site's generator with a Comparator challenge: the solution is loaded once, the headline is
-- computed in that environment with the axioms walked from its terms, and the judged theorems
-- are exported from it and checked. The honest solution is called proved; the forged one meets
-- every condition of the comparison and is rejected.
/--
info: [("CmpMatch.double_eq", true, [], "proved"),
 ("CmpMatch.double_cases", true, ["Classical.choice", "Quot.sound", "propext"], "proved")]
[("CmpForged.double_odd", true, [], "rejected")]
-/
#guard_msgs (whitespace := lax) in
#eval show CoreM Unit from do
  let dir ← IO.FS.createTempDir
  let base ← config (dir / "record.json")
  let judge (scenario : String) (theorems : Array Name) : CoreM _ := do
    let root ← challengeRoot dir scenario theorems
    let stats ← ({} : ProjectStats).withKernelReplayAt root #[] (config? := some base)
    let some h := stats.headline | throwError "no headline"
    return h.theorems.toList.map fun t =>
      (t.name.toString, t.conditionsMet, t.axioms.toList.map (·.toString),
        (headlineVerdict t (headlineStanding stats.replay h t)).1)
  let honest ← judge "Match" #[`CmpMatch.double_eq, `CmpMatch.double_cases]
  let forged ← judge "Forged" #[`CmpForged.double_odd]
  IO.FS.removeDirAll dir
  IO.println (repr honest)
  IO.println (repr forged)

end Verso.VersoBlueprintTests.BlueprintKernelReplay
