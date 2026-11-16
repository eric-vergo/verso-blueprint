/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

import VersoBlueprintTests.Blueprint.Support
import VersoBlueprint.Stats.Comparator
import VersoBlueprint.PreviewManifest
import VersoBlueprintTests.ComparatorFixtures.Match.Solution
import VersoBlueprintTests.ComparatorFixtures.Forged.Solution

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

They also pin the parts: SHA-256 against the standard's test vectors, the prefixes the checker
is given, the record of accepted modules, and the checker's error output as it is read.
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

-- A prefix names every module below it, so it is used only when nothing else is below it: the
-- solution is named in full beside its challenge, a library of its own by its root.
/-- info: [[`P.Solution], [`Lib], [`Lib, `P.Solution], [`A]] -/
#guard_msgs in
#eval
  let all := #[`P.Challenge, `P.Solution, `Lib.A, `Lib.B.C, `Other.X, `A, `A.B]
  let allowed (names : List Name) : NameSet := names.foldl (·.insert ·) {}
  [targetsFor all (allowed [`P.Solution]) #[`P.Solution],
   targetsFor all (allowed [`Lib.A, `Lib.B.C]) #[`Lib.B.C, `Lib.A],
   targetsFor all (allowed [`Lib.A, `Lib.B.C, `P.Solution]) #[`Lib.A, `P.Solution],
   -- a module with another below it that is not wanted can only be named itself
   targetsFor all (allowed [`A]) #[`A]].map (·.toList)

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
      .notReplayed "Mathlib.Data.Nat.Basic is not among the project's modules that were replayed" &&
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
 "Lean proof without sorry, as the compiled files report; not replayed by a kernel (Mathlib.Data.Nat.Basic is not among the project's modules that were replayed)")
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
    report; not replayed by a kernel (the module of Main.forged is not known, so it was not \
    replayed)"

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

end Verso.VersoBlueprintTests.BlueprintKernelReplay
