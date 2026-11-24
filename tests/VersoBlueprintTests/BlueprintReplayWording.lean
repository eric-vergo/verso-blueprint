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

/-- The run of one checker. -/
private def run (name : String) (answer : Replay.Answer) (message : Option String := none) :
    Replay.CheckerRun :=
  { name, version := some "4.35.0", answer, message
    declarations := if answer == .accepted then some 118 else none }

/-- A replay that ended with `outcome`, of the declarations of the nodes below: the replay found
`Demo.ax` under `P.ax` and `P.assumed`, the compiled-code axiom under `P.native` and `sorryAx`
under `P.sorry`, so those four were left out of the export and not checked. -/
private def result (outcome : Replay.Outcome) : Replay.Result :=
  { outcome, version := some "4.35.0"
    declarations := replayOrder #[`P.clean, `P.std, `P.main]
    axioms := #[(`P.ax, #[`Demo.ax]), (`P.native, #[nativeAxiom]), (`P.sorry, #[``sorryAx]),
      (`P.assumed, #[`Demo.ax])]
    constants := 120
    records := 118
    checkers := match outcome with
      | .accepted => #[run "con-leche" .accepted, run "con-ron" .accepted]
      | .rejected => #[run "con-leche" .rejected (some "invalid: type mismatch in theorem P.bad"),
          run "con-ron" .rejected (some "rejected: type mismatch in theorem")]
      | .disagreed => #[run "con-leche" .accepted,
          run "con-ron" .rejected (some "rejected: type mismatch in theorem")]
      | .declined => #[run "con-leche" .accepted,
          run "con-ron" .declined (some "con-ron: declined: non-standard axiom [at axiom P.ax]")]
      | .failed => #[run "con-leche" .accepted,
          run "con-ron" .noAnswer (some "status 3: con-ron: fuel exhausted")]
      | _ => #[]
    message := match outcome with
      | .rejected => some "invalid: type mismatch in theorem P.bad"
      | .disagreed => some "rejected: type mismatch in theorem"
      | .declined => some "con-ron: declined: non-standard axiom [at axiom P.ax]"
      | .failed => some "con-ron (Lean 4.35.0) gave no answer (status 3: con-ron: fuel exhausted)"
      | .noChecker => some "this project's Lean (v4.34.0) ships no con-leche or con-ron"
      | .overMemory => some "con-ron (Lean 4.35.0)"
      | _ => none
    limitSeconds := if outcome == .timedOut then some 900 else none
    memoryLimit := if outcome == .overMemory then some (64 * 1024 * 1024) else none
    exportLimit := if outcome == .overExport then some (8 * 1024 * 1024) else none }

/-- Every state of a replay, by name. -/
private def replays : List (String × Option Replay.Result) := [
  ("accepted", some (result .accepted)),
  ("accepted (reproducible)", some (result .accepted).forReproducible),
  ("rejected", some (result .rejected)),
  ("disagreed", some (result .disagreed)),
  ("declined", some (result .declined)),
  ("no answer", some (result .failed)),
  ("timed out", some (result .timedOut)),
  ("over memory", some (result .overMemory)),
  ("no checker shipped", some (result .noChecker)),
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
  ("module not known", false, mark #[] (unplaced := some `Main.local)),
  ("source changed since the build", true,
    { mark #[`P.clean] (status := .ofSourceChange `P.clean true) with
      sourceChange? := some "the source of P (P.lean) changed since the build" }),
  ("source not known to match the build", true,
    { mark #[`P.clean] (status := .ofSourceChange `P.clean false) with
      sourceChange? := some "the source of P (P.lean) is not known to match the build: Lake's \
        build record P.trace of the compiled module P is missing or cannot be read" })]

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
info: accepted | no axiom | ✓ | Lean proof complete: no sorry in it or in what it uses; checked again by con-leche and con-ron (Lean 4.35.0), with everything it depends on, and both accepted it
accepted | standard axioms only | ✓ | Lean proof complete: no sorry in it or in what it uses; checked again by con-leche and con-ron (Lean 4.35.0), with everything it depends on, and both accepted it
accepted | an axiom of the project | ⚠ | Lean proof without sorry, as the compiled files report; not checked by the kernel replay: it rests on an axiom outside Lean's standard three (Demo.ax), and a replay checks only what rests on Lean's standard three axioms alone, so it is not shown as proved
accepted | an axiom only the replay found | ⚠ | Lean proof without sorry, as the compiled files report; not checked by the kernel replay: it rests on an axiom outside Lean's standard three (Demo.ax), and a replay checks only what rests on Lean's standard three axioms alone, so it is not shown as proved (the replay found it in the terms; the compiled files report none)
accepted | native_decide | ⚠ | Lean proof without sorry, as the compiled files report; not checked by the kernel replay: it rests on the result of compiled code (P.native._native.native_decide.ax_1_1), and a replay checks only what rests on Lean's standard three axioms alone, so it is not shown as proved
accepted | a sorry | ◐ | Lean code incomplete: a sorry in the proof or in what it uses (Lean statement: no sorry; Lean proof: sorry)
accepted | not checked by the replay | ◇ | Lean proof without sorry, as the compiled files report; not replayed by a kernel (not part of the replay: P.other is not among the declarations that were checked)
accepted | module not known | ◇ | Lean proof without sorry, as the compiled files report; not replayed by a kernel (not part of the replay: the module of Main.local is not known)
accepted | source changed since the build | ◌ | Lean proof: the source of P (P.lean) changed since the build, so nothing is shown as checked: what the compiled files report and what a kernel replay found are about the compiled module, not the text shown
accepted | source not known to match the build | ◌ | Lean proof: the source of P (P.lean) is not known to match the build: Lake's build record P.trace of the compiled module P is missing or cannot be read, so nothing is shown as checked: what the compiled files report and what a kernel replay found are about the compiled module, not the text shown
accepted (reproducible) | no axiom | ✓ | Lean proof complete: no sorry in it or in what it uses; checked again by con-leche and con-ron (Lean 4.35.0), with everything it depends on, and both accepted it
accepted (reproducible) | standard axioms only | ✓ | Lean proof complete: no sorry in it or in what it uses; checked again by con-leche and con-ron (Lean 4.35.0), with everything it depends on, and both accepted it
accepted (reproducible) | an axiom of the project | ⚠ | Lean proof without sorry, as the compiled files report; not checked by the kernel replay: it rests on an axiom outside Lean's standard three (Demo.ax), and a replay checks only what rests on Lean's standard three axioms alone, so it is not shown as proved
accepted (reproducible) | an axiom only the replay found | ⚠ | Lean proof without sorry, as the compiled files report; not checked by the kernel replay: it rests on an axiom outside Lean's standard three (Demo.ax), and a replay checks only what rests on Lean's standard three axioms alone, so it is not shown as proved (the replay found it in the terms; the compiled files report none)
accepted (reproducible) | native_decide | ⚠ | Lean proof without sorry, as the compiled files report; not checked by the kernel replay: it rests on the result of compiled code (P.native._native.native_decide.ax_1_1), and a replay checks only what rests on Lean's standard three axioms alone, so it is not shown as proved
accepted (reproducible) | a sorry | ◐ | Lean code incomplete: a sorry in the proof or in what it uses (Lean statement: no sorry; Lean proof: sorry)
accepted (reproducible) | not checked by the replay | ◇ | Lean proof without sorry, as the compiled files report; not replayed by a kernel (not part of the replay: P.other is not among the declarations that were checked)
accepted (reproducible) | module not known | ◇ | Lean proof without sorry, as the compiled files report; not replayed by a kernel (not part of the replay: the module of Main.local is not known)
accepted (reproducible) | source changed since the build | ◌ | Lean proof: the source of P (P.lean) changed since the build, so nothing is shown as checked: what the compiled files report and what a kernel replay found are about the compiled module, not the text shown
accepted (reproducible) | source not known to match the build | ◌ | Lean proof: the source of P (P.lean) is not known to match the build: Lake's build record P.trace of the compiled module P is missing or cannot be read, so nothing is shown as checked: what the compiled files report and what a kernel replay found are about the compiled module, not the text shown
rejected | no axiom | ⊘ | Lean proof not accepted: con-leche (Lean 4.35.0) and con-ron (Lean 4.35.0) rejected this build
rejected | standard axioms only | ⊘ | Lean proof not accepted: con-leche (Lean 4.35.0) and con-ron (Lean 4.35.0) rejected this build
rejected | an axiom of the project | ⚠ | Lean proof without sorry, as the compiled files report, resting on an axiom outside Lean's standard three (Demo.ax); not accepted: con-leche (Lean 4.35.0) and con-ron (Lean 4.35.0) rejected this build
rejected | an axiom only the replay found | ⊘ | Lean proof not accepted: con-leche (Lean 4.35.0) and con-ron (Lean 4.35.0) rejected this build
rejected | native_decide | ⚠ | Lean proof without sorry, as the compiled files report, resting on the result of compiled code (P.native._native.native_decide.ax_1_1); not accepted: con-leche (Lean 4.35.0) and con-ron (Lean 4.35.0) rejected this build
rejected | a sorry | ◐ | Lean code incomplete: a sorry in the proof or in what it uses (Lean statement: no sorry; Lean proof: sorry)
rejected | not checked by the replay | ⊘ | Lean proof not accepted: con-leche (Lean 4.35.0) and con-ron (Lean 4.35.0) rejected this build
rejected | module not known | ⊘ | Lean proof not accepted: con-leche (Lean 4.35.0) and con-ron (Lean 4.35.0) rejected this build
rejected | source changed since the build | ◌ | Lean proof: the source of P (P.lean) changed since the build, so nothing is shown as checked: what the compiled files report and what a kernel replay found are about the compiled module, not the text shown
rejected | source not known to match the build | ◌ | Lean proof: the source of P (P.lean) is not known to match the build: Lake's build record P.trace of the compiled module P is missing or cannot be read, so nothing is shown as checked: what the compiled files report and what a kernel replay found are about the compiled module, not the text shown
disagreed | no axiom | ⊘ | Lean proof not accepted: the two checkers disagree on this build: con-leche (Lean 4.35.0) accepted it and con-ron (Lean 4.35.0) rejected it
disagreed | standard axioms only | ⊘ | Lean proof not accepted: the two checkers disagree on this build: con-leche (Lean 4.35.0) accepted it and con-ron (Lean 4.35.0) rejected it
disagreed | an axiom of the project | ⚠ | Lean proof without sorry, as the compiled files report, resting on an axiom outside Lean's standard three (Demo.ax); not accepted: the two checkers disagree on this build: con-leche (Lean 4.35.0) accepted it and con-ron (Lean 4.35.0) rejected it
disagreed | an axiom only the replay found | ⊘ | Lean proof not accepted: the two checkers disagree on this build: con-leche (Lean 4.35.0) accepted it and con-ron (Lean 4.35.0) rejected it
disagreed | native_decide | ⚠ | Lean proof without sorry, as the compiled files report, resting on the result of compiled code (P.native._native.native_decide.ax_1_1); not accepted: the two checkers disagree on this build: con-leche (Lean 4.35.0) accepted it and con-ron (Lean 4.35.0) rejected it
disagreed | a sorry | ◐ | Lean code incomplete: a sorry in the proof or in what it uses (Lean statement: no sorry; Lean proof: sorry)
disagreed | not checked by the replay | ⊘ | Lean proof not accepted: the two checkers disagree on this build: con-leche (Lean 4.35.0) accepted it and con-ron (Lean 4.35.0) rejected it
disagreed | module not known | ⊘ | Lean proof not accepted: the two checkers disagree on this build: con-leche (Lean 4.35.0) accepted it and con-ron (Lean 4.35.0) rejected it
disagreed | source changed since the build | ◌ | Lean proof: the source of P (P.lean) changed since the build, so nothing is shown as checked: what the compiled files report and what a kernel replay found are about the compiled module, not the text shown
disagreed | source not known to match the build | ◌ | Lean proof: the source of P (P.lean) is not known to match the build: Lake's build record P.trace of the compiled module P is missing or cannot be read, so nothing is shown as checked: what the compiled files report and what a kernel replay found are about the compiled module, not the text shown
declined | no axiom | ◇ | Lean proof without sorry, as the compiled files report; no verdict of a kernel replay (con-ron (Lean 4.35.0) declined to check the export: con-ron: declined: non-standard axiom [at axiom P.ax])
declined | standard axioms only | ◇ | Lean proof without sorry, as the compiled files report; no verdict of a kernel replay (con-ron (Lean 4.35.0) declined to check the export: con-ron: declined: non-standard axiom [at axiom P.ax])
declined | an axiom of the project | ⚠ | Lean proof without sorry, as the compiled files report, resting on an axiom outside Lean's standard three (Demo.ax); no verdict of a kernel replay (con-ron (Lean 4.35.0) declined to check the export: con-ron: declined: non-standard axiom [at axiom P.ax])
declined | an axiom only the replay found | ◇ | Lean proof without sorry, as the compiled files report; no verdict of a kernel replay (con-ron (Lean 4.35.0) declined to check the export: con-ron: declined: non-standard axiom [at axiom P.ax])
declined | native_decide | ⚠ | Lean proof without sorry, as the compiled files report, resting on the result of compiled code (P.native._native.native_decide.ax_1_1); no verdict of a kernel replay (con-ron (Lean 4.35.0) declined to check the export: con-ron: declined: non-standard axiom [at axiom P.ax])
declined | a sorry | ◐ | Lean code incomplete: a sorry in the proof or in what it uses (Lean statement: no sorry; Lean proof: sorry)
declined | not checked by the replay | ◇ | Lean proof without sorry, as the compiled files report; no verdict of a kernel replay (con-ron (Lean 4.35.0) declined to check the export: con-ron: declined: non-standard axiom [at axiom P.ax])
declined | module not known | ◇ | Lean proof without sorry, as the compiled files report; no verdict of a kernel replay (con-ron (Lean 4.35.0) declined to check the export: con-ron: declined: non-standard axiom [at axiom P.ax])
declined | source changed since the build | ◌ | Lean proof: the source of P (P.lean) changed since the build, so nothing is shown as checked: what the compiled files report and what a kernel replay found are about the compiled module, not the text shown
declined | source not known to match the build | ◌ | Lean proof: the source of P (P.lean) is not known to match the build: Lake's build record P.trace of the compiled module P is missing or cannot be read, so nothing is shown as checked: what the compiled files report and what a kernel replay found are about the compiled module, not the text shown
no answer | no axiom | ◇ | Lean proof without sorry, as the compiled files report; no verdict of a kernel replay (the replay could not run to a verdict: con-ron (Lean 4.35.0) gave no answer (status 3: con-ron: fuel exhausted))
no answer | standard axioms only | ◇ | Lean proof without sorry, as the compiled files report; no verdict of a kernel replay (the replay could not run to a verdict: con-ron (Lean 4.35.0) gave no answer (status 3: con-ron: fuel exhausted))
no answer | an axiom of the project | ⚠ | Lean proof without sorry, as the compiled files report, resting on an axiom outside Lean's standard three (Demo.ax); no verdict of a kernel replay (the replay could not run to a verdict: con-ron (Lean 4.35.0) gave no answer (status 3: con-ron: fuel exhausted))
no answer | an axiom only the replay found | ◇ | Lean proof without sorry, as the compiled files report; no verdict of a kernel replay (the replay could not run to a verdict: con-ron (Lean 4.35.0) gave no answer (status 3: con-ron: fuel exhausted))
no answer | native_decide | ⚠ | Lean proof without sorry, as the compiled files report, resting on the result of compiled code (P.native._native.native_decide.ax_1_1); no verdict of a kernel replay (the replay could not run to a verdict: con-ron (Lean 4.35.0) gave no answer (status 3: con-ron: fuel exhausted))
no answer | a sorry | ◐ | Lean code incomplete: a sorry in the proof or in what it uses (Lean statement: no sorry; Lean proof: sorry)
no answer | not checked by the replay | ◇ | Lean proof without sorry, as the compiled files report; no verdict of a kernel replay (the replay could not run to a verdict: con-ron (Lean 4.35.0) gave no answer (status 3: con-ron: fuel exhausted))
no answer | module not known | ◇ | Lean proof without sorry, as the compiled files report; no verdict of a kernel replay (the replay could not run to a verdict: con-ron (Lean 4.35.0) gave no answer (status 3: con-ron: fuel exhausted))
no answer | source changed since the build | ◌ | Lean proof: the source of P (P.lean) changed since the build, so nothing is shown as checked: what the compiled files report and what a kernel replay found are about the compiled module, not the text shown
no answer | source not known to match the build | ◌ | Lean proof: the source of P (P.lean) is not known to match the build: Lake's build record P.trace of the compiled module P is missing or cannot be read, so nothing is shown as checked: what the compiled files report and what a kernel replay found are about the compiled module, not the text shown
timed out | no axiom | ◇ | Lean proof without sorry, as the compiled files report; no verdict of a kernel replay (the replay with con-leche and con-ron (Lean 4.35.0) did not finish within 900 s)
timed out | standard axioms only | ◇ | Lean proof without sorry, as the compiled files report; no verdict of a kernel replay (the replay with con-leche and con-ron (Lean 4.35.0) did not finish within 900 s)
timed out | an axiom of the project | ⚠ | Lean proof without sorry, as the compiled files report, resting on an axiom outside Lean's standard three (Demo.ax); no verdict of a kernel replay (the replay with con-leche and con-ron (Lean 4.35.0) did not finish within 900 s)
timed out | an axiom only the replay found | ◇ | Lean proof without sorry, as the compiled files report; no verdict of a kernel replay (the replay with con-leche and con-ron (Lean 4.35.0) did not finish within 900 s)
timed out | native_decide | ⚠ | Lean proof without sorry, as the compiled files report, resting on the result of compiled code (P.native._native.native_decide.ax_1_1); no verdict of a kernel replay (the replay with con-leche and con-ron (Lean 4.35.0) did not finish within 900 s)
timed out | a sorry | ◐ | Lean code incomplete: a sorry in the proof or in what it uses (Lean statement: no sorry; Lean proof: sorry)
timed out | not checked by the replay | ◇ | Lean proof without sorry, as the compiled files report; no verdict of a kernel replay (the replay with con-leche and con-ron (Lean 4.35.0) did not finish within 900 s)
timed out | module not known | ◇ | Lean proof without sorry, as the compiled files report; no verdict of a kernel replay (the replay with con-leche and con-ron (Lean 4.35.0) did not finish within 900 s)
timed out | source changed since the build | ◌ | Lean proof: the source of P (P.lean) changed since the build, so nothing is shown as checked: what the compiled files report and what a kernel replay found are about the compiled module, not the text shown
timed out | source not known to match the build | ◌ | Lean proof: the source of P (P.lean) is not known to match the build: Lake's build record P.trace of the compiled module P is missing or cannot be read, so nothing is shown as checked: what the compiled files report and what a kernel replay found are about the compiled module, not the text shown
over memory | no axiom | ◇ | Lean proof without sorry, as the compiled files report; no verdict of a kernel replay (the replay was stopped: con-ron (Lean 4.35.0) went over its memory limit of 64 MiB)
over memory | standard axioms only | ◇ | Lean proof without sorry, as the compiled files report; no verdict of a kernel replay (the replay was stopped: con-ron (Lean 4.35.0) went over its memory limit of 64 MiB)
over memory | an axiom of the project | ⚠ | Lean proof without sorry, as the compiled files report, resting on an axiom outside Lean's standard three (Demo.ax); no verdict of a kernel replay (the replay was stopped: con-ron (Lean 4.35.0) went over its memory limit of 64 MiB)
over memory | an axiom only the replay found | ◇ | Lean proof without sorry, as the compiled files report; no verdict of a kernel replay (the replay was stopped: con-ron (Lean 4.35.0) went over its memory limit of 64 MiB)
over memory | native_decide | ⚠ | Lean proof without sorry, as the compiled files report, resting on the result of compiled code (P.native._native.native_decide.ax_1_1); no verdict of a kernel replay (the replay was stopped: con-ron (Lean 4.35.0) went over its memory limit of 64 MiB)
over memory | a sorry | ◐ | Lean code incomplete: a sorry in the proof or in what it uses (Lean statement: no sorry; Lean proof: sorry)
over memory | not checked by the replay | ◇ | Lean proof without sorry, as the compiled files report; no verdict of a kernel replay (the replay was stopped: con-ron (Lean 4.35.0) went over its memory limit of 64 MiB)
over memory | module not known | ◇ | Lean proof without sorry, as the compiled files report; no verdict of a kernel replay (the replay was stopped: con-ron (Lean 4.35.0) went over its memory limit of 64 MiB)
over memory | source changed since the build | ◌ | Lean proof: the source of P (P.lean) changed since the build, so nothing is shown as checked: what the compiled files report and what a kernel replay found are about the compiled module, not the text shown
over memory | source not known to match the build | ◌ | Lean proof: the source of P (P.lean) is not known to match the build: Lake's build record P.trace of the compiled module P is missing or cannot be read, so nothing is shown as checked: what the compiled files report and what a kernel replay found are about the compiled module, not the text shown
no checker shipped | no axiom | ◇ | Lean proof without sorry, as the compiled files report; not replayed by a kernel (this project's Lean (v4.34.0) ships no con-leche or con-ron)
no checker shipped | standard axioms only | ◇ | Lean proof without sorry, as the compiled files report; not replayed by a kernel (this project's Lean (v4.34.0) ships no con-leche or con-ron)
no checker shipped | an axiom of the project | ⚠ | Lean proof without sorry, as the compiled files report, resting on an axiom outside Lean's standard three (Demo.ax); not replayed by a kernel (this project's Lean (v4.34.0) ships no con-leche or con-ron)
no checker shipped | an axiom only the replay found | ◇ | Lean proof without sorry, as the compiled files report; not replayed by a kernel (this project's Lean (v4.34.0) ships no con-leche or con-ron)
no checker shipped | native_decide | ⚠ | Lean proof without sorry, as the compiled files report, resting on the result of compiled code (P.native._native.native_decide.ax_1_1); not replayed by a kernel (this project's Lean (v4.34.0) ships no con-leche or con-ron)
no checker shipped | a sorry | ◐ | Lean code incomplete: a sorry in the proof or in what it uses (Lean statement: no sorry; Lean proof: sorry)
no checker shipped | not checked by the replay | ◇ | Lean proof without sorry, as the compiled files report; not replayed by a kernel (this project's Lean (v4.34.0) ships no con-leche or con-ron)
no checker shipped | module not known | ◇ | Lean proof without sorry, as the compiled files report; not replayed by a kernel (this project's Lean (v4.34.0) ships no con-leche or con-ron)
no checker shipped | source changed since the build | ◌ | Lean proof: the source of P (P.lean) changed since the build, so nothing is shown as checked: what the compiled files report and what a kernel replay found are about the compiled module, not the text shown
no checker shipped | source not known to match the build | ◌ | Lean proof: the source of P (P.lean) is not known to match the build: Lake's build record P.trace of the compiled module P is missing or cannot be read, so nothing is shown as checked: what the compiled files report and what a kernel replay found are about the compiled module, not the text shown
export over its limit | no axiom | ◇ | Lean proof without sorry, as the compiled files report; not replayed by a kernel (the export of what the site's declarations depend on went over its size limit of 8 MiB, so the checker was not run)
export over its limit | standard axioms only | ◇ | Lean proof without sorry, as the compiled files report; not replayed by a kernel (the export of what the site's declarations depend on went over its size limit of 8 MiB, so the checker was not run)
export over its limit | an axiom of the project | ⚠ | Lean proof without sorry, as the compiled files report, resting on an axiom outside Lean's standard three (Demo.ax); not replayed by a kernel (the export of what the site's declarations depend on went over its size limit of 8 MiB, so the checker was not run)
export over its limit | an axiom only the replay found | ◇ | Lean proof without sorry, as the compiled files report; not replayed by a kernel (the export of what the site's declarations depend on went over its size limit of 8 MiB, so the checker was not run)
export over its limit | native_decide | ⚠ | Lean proof without sorry, as the compiled files report, resting on the result of compiled code (P.native._native.native_decide.ax_1_1); not replayed by a kernel (the export of what the site's declarations depend on went over its size limit of 8 MiB, so the checker was not run)
export over its limit | a sorry | ◐ | Lean code incomplete: a sorry in the proof or in what it uses (Lean statement: no sorry; Lean proof: sorry)
export over its limit | not checked by the replay | ◇ | Lean proof without sorry, as the compiled files report; not replayed by a kernel (the export of what the site's declarations depend on went over its size limit of 8 MiB, so the checker was not run)
export over its limit | module not known | ◇ | Lean proof without sorry, as the compiled files report; not replayed by a kernel (the export of what the site's declarations depend on went over its size limit of 8 MiB, so the checker was not run)
export over its limit | source changed since the build | ◌ | Lean proof: the source of P (P.lean) changed since the build, so nothing is shown as checked: what the compiled files report and what a kernel replay found are about the compiled module, not the text shown
export over its limit | source not known to match the build | ◌ | Lean proof: the source of P (P.lean) is not known to match the build: Lake's build record P.trace of the compiled module P is missing or cannot be read, so nothing is shown as checked: what the compiled files report and what a kernel replay found are about the compiled module, not the text shown
switched off | no axiom | ◇ | Lean proof without sorry, as the compiled files report; not replayed by a kernel (the kernel replay was switched off for this build)
switched off | standard axioms only | ◇ | Lean proof without sorry, as the compiled files report; not replayed by a kernel (the kernel replay was switched off for this build)
switched off | an axiom of the project | ⚠ | Lean proof without sorry, as the compiled files report, resting on an axiom outside Lean's standard three (Demo.ax); not replayed by a kernel (the kernel replay was switched off for this build)
switched off | an axiom only the replay found | ◇ | Lean proof without sorry, as the compiled files report; not replayed by a kernel (the kernel replay was switched off for this build)
switched off | native_decide | ⚠ | Lean proof without sorry, as the compiled files report, resting on the result of compiled code (P.native._native.native_decide.ax_1_1); not replayed by a kernel (the kernel replay was switched off for this build)
switched off | a sorry | ◐ | Lean code incomplete: a sorry in the proof or in what it uses (Lean statement: no sorry; Lean proof: sorry)
switched off | not checked by the replay | ◇ | Lean proof without sorry, as the compiled files report; not replayed by a kernel (the kernel replay was switched off for this build)
switched off | module not known | ◇ | Lean proof without sorry, as the compiled files report; not replayed by a kernel (the kernel replay was switched off for this build)
switched off | source changed since the build | ◌ | Lean proof: the source of P (P.lean) changed since the build, so nothing is shown as checked: what the compiled files report and what a kernel replay found are about the compiled module, not the text shown
switched off | source not known to match the build | ◌ | Lean proof: the source of P (P.lean) is not known to match the build: Lake's build record P.trace of the compiled module P is missing or cannot be read, so nothing is shown as checked: what the compiled files report and what a kernel replay found are about the compiled module, not the text shown
not run | no axiom | ◇ | Lean proof without sorry, as the compiled files report; not replayed by a kernel (this site was generated without a kernel replay)
not run | standard axioms only | ◇ | Lean proof without sorry, as the compiled files report; not replayed by a kernel (this site was generated without a kernel replay)
not run | an axiom of the project | ⚠ | Lean proof without sorry, as the compiled files report, resting on an axiom outside Lean's standard three (Demo.ax); not replayed by a kernel (this site was generated without a kernel replay)
not run | an axiom only the replay found | ◇ | Lean proof without sorry, as the compiled files report; not replayed by a kernel (this site was generated without a kernel replay)
not run | native_decide | ⚠ | Lean proof without sorry, as the compiled files report, resting on the result of compiled code (P.native._native.native_decide.ax_1_1); not replayed by a kernel (this site was generated without a kernel replay)
not run | a sorry | ◐ | Lean code incomplete: a sorry in the proof or in what it uses (Lean statement: no sorry; Lean proof: sorry)
not run | not checked by the replay | ◇ | Lean proof without sorry, as the compiled files report; not replayed by a kernel (this site was generated without a kernel replay)
not run | module not known | ◇ | Lean proof without sorry, as the compiled files report; not replayed by a kernel (this site was generated without a kernel replay)
not run | source changed since the build | ◌ | Lean proof: the source of P (P.lean) changed since the build, so nothing is shown as checked: what the compiled files report and what a kernel replay found are about the compiled module, not the text shown
not run | source not known to match the build | ◌ | Lean proof: the source of P (P.lean) is not known to match the build: Lake's build record P.trace of the compiled module P is missing or cannot be read, so nothing is shown as checked: what the compiled files report and what a kernel replay found are about the compiled module, not the text shown
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
   ("accepted, both", Replay.siteState (some (result .accepted)) #[`a, `b] #[`n] #[`Demo.ax]),
   ("accepted, a node with its source changed",
     Replay.siteState (some (result .accepted)) #[] #[] #[] #[`c])] ++
  (replays.drop 1).map fun (state, replay?) => (state, Replay.siteState replay? #[`n] #[`m])

-- Every state of a site: its token, the words beside a legend entry or a count of `sorry`-free
-- code, the sentence after a card's description, the sentence above the counts.
/--
info: accepted, every node | accepted | - | - | -
accepted, a node not covered | none | the kernel replay accepted the build; on this site 1 node with Lean code is not part of the replay | Counted as the compiled files report: the kernel replay accepted the build, and on this site 1 node with Lean code is not part of the replay. | The kernel replay accepted the build, and the counts are as the compiled files report: 1 node with Lean code is not part of the replay.
accepted, a node on an axiom | none | the kernel replay accepted the build; on this site 1 node without sorry rests on the axiom Demo.ax | Counted as the compiled files report: the kernel replay accepted the build, and on this site 1 node without sorry rests on the axiom Demo.ax, so it was not checked and is not shown as proved. | The kernel replay accepted the build, and the counts are as the compiled files report: 1 node without sorry rests on the axiom Demo.ax, so it was not checked and is not shown as proved.
accepted, two nodes on axioms | none | the kernel replay accepted the build; on this site 2 nodes without sorry rest on the axioms Demo.ax, P.native._native.native_decide.ax_1_1 (the result of compiled code) | Counted as the compiled files report: the kernel replay accepted the build, and on this site 2 nodes without sorry rest on the axioms Demo.ax, P.native._native.native_decide.ax_1_1 (the result of compiled code), so they were not checked and are not shown as proved. | The kernel replay accepted the build, and the counts are as the compiled files report: 2 nodes without sorry rest on the axioms Demo.ax, P.native._native.native_decide.ax_1_1 (the result of compiled code), so they were not checked and are not shown as proved.
accepted, both | none | the kernel replay accepted the build; on this site 2 nodes with Lean code are not part of the replay, and 1 node without sorry rests on the axiom Demo.ax | Counted as the compiled files report: the kernel replay accepted the build, and on this site 2 nodes with Lean code are not part of the replay; 1 node without sorry rests on the axiom Demo.ax, so it was not checked and is not shown as proved. | The kernel replay accepted the build, and the counts are as the compiled files report: 2 nodes with Lean code are not part of the replay; 1 node without sorry rests on the axiom Demo.ax, so it was not checked and is not shown as proved.
accepted, a node with its source changed | none | the kernel replay accepted the build; on this site the Lean source of 1 node changed since the build or is not known to match it | Counted as the compiled files report: the kernel replay accepted the build, and on this site the Lean source of 1 node changed since the build or is not known to match it. | The kernel replay accepted the build, and the counts are as the compiled files report: the Lean source of 1 node changed since the build or is not known to match it.
accepted (reproducible) | none | the kernel replay accepted the build; on this site 1 node with Lean code is not part of the replay, and 1 node without sorry rests on an axiom outside Lean's standard three | Counted as the compiled files report: the kernel replay accepted the build, and on this site 1 node with Lean code is not part of the replay; 1 node without sorry rests on an axiom outside Lean's standard three, so it was not checked and is not shown as proved. | The kernel replay accepted the build, and the counts are as the compiled files report: 1 node with Lean code is not part of the replay; 1 node without sorry rests on an axiom outside Lean's standard three, so it was not checked and is not shown as proved.
rejected | rejected | this build was rejected by a kernel checker | A kernel checker rejected this build. | This build was rejected by a kernel checker: the counts say what the compiled files report, and nothing here counts as checked by a kernel.
disagreed | rejected | this build was rejected by a kernel checker | A kernel checker rejected this build. | This build was rejected by a kernel checker: the counts say what the compiled files report, and nothing here counts as checked by a kernel.
declined | none | as the compiled files report, with no verdict of a kernel replay | Counted as the compiled files report, with no verdict of a kernel replay. | The counts are as the compiled files report, with no verdict of a kernel replay: con-ron (Lean 4.35.0) declined to check the export: con-ron: declined: non-standard axiom [at axiom P.ax].
no answer | none | as the compiled files report, with no verdict of a kernel replay | Counted as the compiled files report, with no verdict of a kernel replay. | The counts are as the compiled files report, with no verdict of a kernel replay: the replay could not run to a verdict: con-ron (Lean 4.35.0) gave no answer (status 3: con-ron: fuel exhausted).
timed out | none | as the compiled files report, with no verdict of a kernel replay | Counted as the compiled files report, with no verdict of a kernel replay. | The counts are as the compiled files report, with no verdict of a kernel replay: the replay with con-leche and con-ron (Lean 4.35.0) did not finish within 900 s.
over memory | none | as the compiled files report, with no verdict of a kernel replay | Counted as the compiled files report, with no verdict of a kernel replay. | The counts are as the compiled files report, with no verdict of a kernel replay: the replay was stopped: con-ron (Lean 4.35.0) went over its memory limit of 64 MiB.
no checker shipped | none | as the compiled files report, not replayed by a kernel | Counted as the compiled files report, not replayed by a kernel. | The counts are as the compiled files report, not replayed by a kernel: this project's Lean (v4.34.0) ships no con-leche or con-ron.
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
info: accepted | Accepted: con-leche and con-ron (Lean 4.35.0) each checked 3 declarations and everything they depend on, 120 constants in all, starting from its own built-in prelude, and both accepted them.
accepted (reproducible) | Accepted: con-leche and con-ron (Lean 4.35.0) both accepted this build's export, in this run or, for an identical export, in an earlier one: 3 declarations and everything they depend on, 120 constants in all, each starting from its own built-in prelude.
rejected | Rejected: con-leche (Lean 4.35.0) and con-ron (Lean 4.35.0) rejected this build (the export of this site's declarations and what they depend on). Nothing on this site counts as checked by a kernel.
disagreed | Rejected: the two checkers disagree on this build: con-leche (Lean 4.35.0) accepted it and con-ron (Lean 4.35.0) rejected it. Nothing on this site counts as checked by a kernel.
declined | No verdict of a kernel replay: con-ron (Lean 4.35.0) declined to check the export: con-ron: declined: non-standard axiom [at axiom P.ax]. The marks on this site say what the compiled files report.
no answer | No verdict of a kernel replay: the replay could not run to a verdict: con-ron (Lean 4.35.0) gave no answer (status 3: con-ron: fuel exhausted). The marks on this site say what the compiled files report.
timed out | No verdict of a kernel replay: the replay with con-leche and con-ron (Lean 4.35.0) did not finish within 900 s. The marks on this site say what the compiled files report.
over memory | No verdict of a kernel replay: the replay was stopped: con-ron (Lean 4.35.0) went over its memory limit of 64 MiB. The marks on this site say what the compiled files report.
no checker shipped | Not replayed by a kernel: this project's Lean (v4.34.0) ships no con-leche or con-ron. The marks on this site say what the compiled files report.
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
    let (token, verdict) := headlineVerdict t standing replay?
    row [state, token, verdict, replayNoteText replay? standing]

-- A theorem that meets the comparison's conditions and that the replay checks: the state, the
-- verdict's token, the verdict, the line under it.
/--
info: accepted | proved | Lean statement proved | Kernel replay: con-leche and con-ron (Lean 4.35.0) each checked this theorem and every constant it depends on, in this project, in its dependencies and in Lean's own library, starting from its own built-in prelude, and both accepted it.
accepted (reproducible) | proved | Lean statement proved | Kernel replay: con-leche and con-ron (Lean 4.35.0) each checked this theorem and every constant it depends on, in this project, in its dependencies and in Lean's own library, starting from its own built-in prelude, and both accepted it (in this run, or in an earlier one for an export identical to this build's).
rejected | rejected | Not accepted: a kernel checker rejected this build | Kernel replay: con-leche (Lean 4.35.0) and con-ron (Lean 4.35.0) rejected this build: invalid: type mismatch in theorem P.bad
disagreed | rejected | Not accepted: the two kernel checkers disagree on this build | Kernel replay: the two checkers disagree on this build: con-leche (Lean 4.35.0) accepted it and con-ron (Lean 4.35.0) rejected it: rejected: type mismatch in theorem
declined | not-replayed | Same Lean statement as the challenge; no sorry; permitted axioms: as the compiled files report, with no verdict of a kernel replay | No verdict of a kernel replay: con-ron (Lean 4.35.0) declined to check the export: con-ron: declined: non-standard axiom [at axiom P.ax].
no answer | not-replayed | Same Lean statement as the challenge; no sorry; permitted axioms: as the compiled files report, with no verdict of a kernel replay | No verdict of a kernel replay: the replay could not run to a verdict: con-ron (Lean 4.35.0) gave no answer (status 3: con-ron: fuel exhausted).
timed out | not-replayed | Same Lean statement as the challenge; no sorry; permitted axioms: as the compiled files report, with no verdict of a kernel replay | No verdict of a kernel replay: the replay with con-leche and con-ron (Lean 4.35.0) did not finish within 900 s.
over memory | not-replayed | Same Lean statement as the challenge; no sorry; permitted axioms: as the compiled files report, with no verdict of a kernel replay | No verdict of a kernel replay: the replay was stopped: con-ron (Lean 4.35.0) went over its memory limit of 64 MiB.
no checker shipped | not-replayed | Same Lean statement as the challenge; no sorry; permitted axioms: as the compiled files report, not replayed by a kernel | No kernel replay: this project's Lean (v4.34.0) ships no con-leche or con-ron.
export over its limit | not-replayed | Same Lean statement as the challenge; no sorry; permitted axioms: as the compiled files report, not replayed by a kernel | No kernel replay: the export of what the site's declarations depend on went over its size limit of 8 MiB, so the checker was not run.
switched off | not-replayed | Same Lean statement as the challenge; no sorry; permitted axioms: as the compiled files report, not replayed by a kernel | No kernel replay: the kernel replay was switched off for this build.
not run | not-replayed | Same Lean statement as the challenge; no sorry; permitted axioms: as the compiled files report, not replayed by a kernel | No kernel replay: this site was generated without a kernel replay.
-/
#guard_msgs in
#eval for r in headlineRows headline (met `P.main) do IO.println r

-- The same for a theorem under which the replay found an axiom the verdict does not allow.
/--
info: accepted | axioms | Same Lean statement as the challenge; not checked by the kernel replay: it rests on an axiom outside Lean's standard three (Demo.ax), and a replay checks only what rests on the standard three alone, so it is not shown as proved | Kernel replay: not checked: it rests on an axiom outside Lean's standard three (Demo.ax), and a replay checks only what rests on the standard three alone.
accepted (reproducible) | axioms | Same Lean statement as the challenge; not checked by the kernel replay: it rests on an axiom outside Lean's standard three (Demo.ax), and a replay checks only what rests on the standard three alone, so it is not shown as proved | Kernel replay: not checked: it rests on an axiom outside Lean's standard three (Demo.ax), and a replay checks only what rests on the standard three alone.
rejected | rejected | Not accepted: a kernel checker rejected this build | Kernel replay: con-leche (Lean 4.35.0) and con-ron (Lean 4.35.0) rejected this build: invalid: type mismatch in theorem P.bad
disagreed | rejected | Not accepted: the two kernel checkers disagree on this build | Kernel replay: the two checkers disagree on this build: con-leche (Lean 4.35.0) accepted it and con-ron (Lean 4.35.0) rejected it: rejected: type mismatch in theorem
declined | not-replayed | Same Lean statement as the challenge; no sorry; permitted axioms: as the compiled files report, with no verdict of a kernel replay | No verdict of a kernel replay: con-ron (Lean 4.35.0) declined to check the export: con-ron: declined: non-standard axiom [at axiom P.ax].
no answer | not-replayed | Same Lean statement as the challenge; no sorry; permitted axioms: as the compiled files report, with no verdict of a kernel replay | No verdict of a kernel replay: the replay could not run to a verdict: con-ron (Lean 4.35.0) gave no answer (status 3: con-ron: fuel exhausted).
timed out | not-replayed | Same Lean statement as the challenge; no sorry; permitted axioms: as the compiled files report, with no verdict of a kernel replay | No verdict of a kernel replay: the replay with con-leche and con-ron (Lean 4.35.0) did not finish within 900 s.
over memory | not-replayed | Same Lean statement as the challenge; no sorry; permitted axioms: as the compiled files report, with no verdict of a kernel replay | No verdict of a kernel replay: the replay was stopped: con-ron (Lean 4.35.0) went over its memory limit of 64 MiB.
no checker shipped | not-replayed | Same Lean statement as the challenge; no sorry; permitted axioms: as the compiled files report, not replayed by a kernel | No kernel replay: this project's Lean (v4.34.0) ships no con-leche or con-ron.
export over its limit | not-replayed | Same Lean statement as the challenge; no sorry; permitted axioms: as the compiled files report, not replayed by a kernel | No kernel replay: the export of what the site's declarations depend on went over its size limit of 8 MiB, so the checker was not run.
switched off | not-replayed | Same Lean statement as the challenge; no sorry; permitted axioms: as the compiled files report, not replayed by a kernel | No kernel replay: the kernel replay was switched off for this build.
not run | not-replayed | Same Lean statement as the challenge; no sorry; permitted axioms: as the compiled files report, not replayed by a kernel | No kernel replay: this site was generated without a kernel replay.
-/
#guard_msgs in
#eval for r in headlineRows headline (met `P.assumed) do IO.println r

-- A challenge that permits the axiom: the theorem is still not checked, and not proved, since
-- both checkers decline an export that uses an axiom outside the standard three.
/-- info: true -/
#guard_msgs in
#eval
  let h := { headline with permittedAxioms := some #[`Demo.ax] }
  let t := { met `P.assumed with axiomsPermitted := some true }
  (headlineVerdict t (headlineStanding (some (result .accepted)) h t)).1 == "axioms"

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
  else if replay?.any (·.outcome.isRejection) then
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
    let (token, verdict) := headlineVerdict (met name) standing replay?
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
      }).render
    let checks := [
      ("sentence", site.sentence.isEmpty || hasSubstr html site.sentence),
      ("legend", hasSubstr html s!"Lean complete, dependencies too{(site.note?.map (s!" ({·})")).getD ""}"),
      ("scope", hasSubstr html s!"class=\"bp_project_stats {site.scopeClass}\""),
      ("neutral", (site == .accepted) == hasSubstr html "bp_project_stats bp_replay_accepted")]
    let failed := checks.filter (!·.2) |>.map (·.1)
    if failed.isEmpty then none else some (name, failed)


/-! ## The Comparator pages -/

-- The Comparator index gives every theorem the verdict of the Project Stats page, from the same
-- statistics, in every state: the same token and words, and the same scope of success colours.
/-- info: [] -/
#guard_msgs in
#eval
  replays.flatMap fun (state, replay?) => [`P.main, `P.assumed].filterMap fun name =>
    let h := { headline with name := "P", theorems := #[met name] }
    let stats : ProjectStats := { challenges := #[h], hasComparatorChallenge := true, replay := replay? }
    let index := (comparatorIndexHtml { stats }).render
    let band := (statsPageHtml { stats }).render
    let standing := headlineStanding replay? h (met name)
    let (token, verdict) := headlineVerdict (met name) standing replay?
    let checks := [
      ("index verdict", hasSubstr index s!"data-bp-verdict=\"{token}\"" && hasSubstr index verdict),
      ("index scope", hasSubstr index s!"bp_comparator_verdict {standing.scopeClass}"),
      ("band verdict", hasSubstr band verdict),
      ("index words", (falseWords replay? true (verdict ++ " " ++ replayNoteText replay? standing)).isEmpty)]
    let failed := checks.filter (!·.2) |>.map (·.1)
    if failed.isEmpty then none else some (state, name, failed)

-- The Comparator pages' own sentences, and why a challenge was not compared, for every reason.
/--
info: The Comparator challenge P: the challenge file states the theorems with sorry as their proofs, the solution file proves them, and comparator.json says which theorems are judged and which axioms a proof may use. The verdict is the one the Project Stats page shows for this challenge, from the same comparison and the same kernel replay.
The project's Comparator challenges. Each states theorems in a challenge file and proves them in a solution file; lake comparator, run from the project root with --config Comparator/<Name>/comparator.json, judges a solution against its challenge. The verdicts below are the ones the Project Stats page shows, from the same comparison and the same kernel replay.
What a verdict of the kernel replay leaves trusted
Shown with syntax colours only: no highlighted build of this module matches the file.
Not compared: the site's statistics hold no result for this challenge.
The continuous-integration run that built this site
source at the commit this site is built from
configInvalid | comparator.json could not be read or lacks the fields lake comparator needs.
challengeNotBuilt | The challenge module has not been built.
challengeOutOfDate | The compiled challenge module does not match its source: build it again after an edit.
challengeProvenanceUnknown | It is not known that the compiled challenge module was compiled from its source as shown.
challengeUnreadable | The compiled challenge module could not be read.
solutionNotImported | The Blueprint does not import the solution module.
importsNotAvailable | The challenge imports a module the Blueprint does not import.
modulesNotLoaded | The compiled modules were not loaded for the comparison.
solutionOutOfDate | The solution's source differs from the one its compiled module was compiled from: build it again after an edit.
solutionProvenanceUnknown | It is not known that the compiled solution module was compiled from its source as shown.
-/
#guard_msgs in
#eval do
  for line in [challengePageIntroText "P", comparatorIndexIntroText, challengeTrustedCaption,
      plainHighlightText, challengeWithoutResultText, ciRunText, sourceLinkText] do
    IO.println line
  for u in [Unavailable.configInvalid, .challengeNotBuilt, .challengeOutOfDate,
      .challengeProvenanceUnknown, .challengeUnreadable, .solutionNotImported,
      .importsNotAvailable, .modulesNotLoaded, .solutionOutOfDate, .solutionProvenanceUnknown] do
    IO.println (row [(toJson u).compress.replace "\"" "", unavailableText u])

end Verso.VersoBlueprintTests.BlueprintReplayWording
