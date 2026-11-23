/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

import Lean.Data.Json
import VersoBlueprint.Axioms

/-!
The kernel replay of a build, as a site reports it.

A site is generated from compiled modules. What they say (a statement, the absence of `sorry`, a
list of axioms) is what Lean's elaborator recorded, and a file can keep the kernel from seeing a
declaration at all (`set_option debug.skipKernelTC true`), in the project or in anything it
depends on. So a site says "proved", and draws a check mark in the success colour, only for a
declaration that a kernel replay covers: the generator loads the compiled modules, exports the
declaration together with every constant it depends on, in the project, in its dependencies and
in Lean's own library, and two checkers that ship with the Lean toolchain, `con-leche` and
`con-ron`, each check all of them again, starting from its own built-in prelude
(`Informal.Stats.ProjectStats.withKernelReplayAt` runs it when the site is generated). The
replay accepts only when both accept. A declaration that rests on an axiom outside Lean's
standard three (`sorryAx` among them) is not exported and not checked: both checkers decline an
export that uses one. Everywhere else the words are what the compiled files report, with a mark
that is not a check mark.

This module holds the result of a replay and the words for it; nothing here runs anything.

What a replay leaves trusted is said on the page (`trustedText`): the exporter, which the
generator runs on the modules it loaded; each checker with the compiler and runtime it is built
with; and Lean's elaborator for the step from the source text to the compiled module. No replay
says anything about what a statement means.
-/

namespace Informal.Replay

open Lean

/-- How a kernel replay ended. -/
inductive Outcome where
  /-- Both checkers accepted the export: every declaration of `Result.declarations` and every
  constant it depends on. -/
  | accepted
  /-- A checker rejected the export, and neither accepted it (`Result.checkers` says which, and
  `Result.message` what it said). -/
  | rejected
  /-- One checker accepted the export and the other rejected it. -/
  | disagreed
  /-- A checker declined to check the export (`Result.message`), and neither rejected it. -/
  | declined
  /-- The project's Lean toolchain ships no checker (`Result.message` says which it lacks):
  nothing was replayed. -/
  | noChecker
  /-- The replay was stopped at the time limit (`Result.limitSeconds`) without a verdict. -/
  | timedOut
  /-- A process of the replay was stopped because it went over its memory limit
  (`Result.memoryLimit`), without a verdict. -/
  | overMemory
  /-- The export went over its size limit (`Result.exportLimit`); the checker was not run. -/
  | overExport
  /-- The replay could not run to a verdict (`Result.message`). -/
  | failed
  /-- The replay was switched off for this build. -/
  | off
deriving Repr, Inhabited, DecidableEq, ToJson, FromJson

/-- Whether a replay that ended this way was started and stopped without a verdict (at a limit,
or on an error), as opposed to never checking anything (no checker, an export over its limit,
switched off). The words differ: "not replayed by a kernel" is said only when nothing was. -/
def Outcome.stoppedWithoutVerdict : Outcome → Bool
  | .timedOut | .overMemory | .failed | .declined => true
  | _ => false

/-- Whether a checker rejected the build: alone (`rejected`) or against the other's acceptance
(`disagreed`). Nothing is counted as checked then. -/
def Outcome.isRejection : Outcome → Bool
  | .rejected | .disagreed => true
  | _ => false

/-- What one checker answered, by its exit status first and its words second. -/
inductive Answer where
  /-- Exit status 0 with its line `accepted N declarations`, `N` at least the declaration
  records of the export. -/
  | accepted
  /-- Exit status 1 with its words of rejection. -/
  | rejected
  /-- Exit status 2: it declined to check the export. -/
  | declined
  /-- Exit status 1 with an uncaught exception: an error of the checker. -/
  | error
  /-- Any other ending: a usage or parse error, a reduction that ran out of fuel, an exit
  status 0 without its line or with too short a count, another status or a signal. -/
  | noAnswer
  /-- It was stopped at the time limit. -/
  | timedOut
  /-- It was stopped over its memory limit. -/
  | overMemory
  /-- It could not be started. -/
  | notStarted
deriving Repr, Inhabited, DecidableEq, ToJson, FromJson

/-- The run of one checker on an export. -/
structure CheckerRun where
  /-- The program's name: `con-leche` or `con-ron`. -/
  name : String
  /-- The Lean version of the toolchain the program ships with. -/
  version : Option String := none
  /-- The SHA-256 of the program's file, in hexadecimal. -/
  sha256 : Option String := none
  answer : Answer
  /-- The declaration records it said it accepted, or checked before it declined. -/
  declarations : Option Nat := none
  /-- What it said, when it did not accept. -/
  message : Option String := none
  /-- How long it ran, in milliseconds; `none` when not measured or left out of a reproducible
  build. -/
  ms : Option Nat := none
  /-- The most memory it was seen to hold, in bytes; `none` when never read or left out of a
  reproducible build. -/
  peakBytes : Option Nat := none
deriving Repr, Inhabited, DecidableEq, ToJson, FromJson

/-- The checker with its toolchain: `con-ron (Lean 4.35.0)`. -/
def CheckerRun.label (c : CheckerRun) : String :=
  match c.version with
  | some v => s!"{c.name} (Lean {v})"
  | none => c.name

/-- The two checkers of a replay, in the order they run. -/
def checkerNames : Array String := #["con-leche", "con-ron"]

/-- Where the constants of an export come from. -/
inductive OriginKind where
  /-- The project's own compiled modules. -/
  | project
  /-- A dependency of the project. -/
  | dependency
  /-- Lean's own library, which ships with the toolchain. -/
  | toolchain
deriving Repr, Inhabited, DecidableEq, ToJson, FromJson

/-- The constants of an export that come from one place. -/
structure Origin where
  kind : OriginKind
  /-- The first component of the names of the modules they are in (`Mathlib`); for the
  project and for Lean's own library, every such component joined by commas. -/
  name : String
  /-- How many constants. -/
  constants : Nat
deriving Repr, Inhabited, DecidableEq, ToJson, FromJson

/-- The kernel replay of one build. -/
structure Result where
  outcome : Outcome
  /-- The checkers' names, for a sentence. -/
  checker : String := "con-leche and con-ron"
  /-- The Lean version of the toolchain the checkers belong to. -/
  version : Option String := none
  /-- The declarations the replay covers, in `Name.quickLt` order: with `accepted`, each was
  exported with every constant it depends on, and both checkers accepted them all; otherwise the
  declarations that were to be checked. -/
  declarations : Array Name := #[]
  /-- Declarations the replay was asked for and does not cover, each with the reason (it is not
  in the compiled modules that were loaded, it is in another module there, it is unsafe). -/
  notCovered : Array (Name × String) := #[]
  /-- Declarations the replay was asked for that rest on an axiom outside Lean's standard three,
  with those axioms, sorted, as found by walking the terms of the loaded modules (`sorryAx` among
  them). They are not exported and not checked: both checkers decline an export that uses such
  an axiom. -/
  axioms : Array (Name × Array Name) := #[]
  /-- What each checker answered, in the order they ran; empty when none ran. -/
  checkers : Array CheckerRun := #[]
  /-- The declaration records of the export (`def`, `thm`, `opaque`, `axiom`, `inductive`; not
  the quotient package's `quot` records, which the checkers do not count), as the generator
  counted them in the file. -/
  records : Nat := 0
  /-- The number of constants in the export. -/
  constants : Nat := 0
  /-- Where the exported constants come from, the largest group first. -/
  origins : Array Origin := #[]
  /-- With `accepted`: both checkers accepted an identical export in an earlier run and were not
  run again. -/
  recorded : Bool := false
  /-- The site is built to be reproducible: whether an acceptance comes from this run or from
the record is not said, and the checkers' times and memory are left out
(`Result.forReproducible`). -/
  reproducible : Bool := false
  /-- With `rejected`, `disagreed`, `declined` or `failed`: what the checker, or the generator,
  said. With `overMemory`: what went over the limit. With `noChecker`: what the toolchain lacks. -/
  message : Option String := none
  /-- With `timedOut`: the limit. -/
  limitSeconds : Option Nat := none
  /-- With `overMemory`: the memory limit of the checker process, in bytes. -/
  memoryLimit : Option Nat := none
  /-- With `overExport`: the size limit of the export, in bytes. -/
  exportLimit : Option Nat := none
deriving Repr, Inhabited, DecidableEq, ToJson, FromJson

/-- `r` as a reproducible build shows it: two builds of the same project with the same checkers
give the same words whether the record held the export or not, so the acceptance's source and
the checkers' times and memory are left out. -/
def Result.forReproducible (r : Result) : Result :=
  { r with reproducible := true, recorded := false
           checkers := r.checkers.map fun c =>
             { c with ms := none, peakBytes := none
                      declarations := if c.answer == .accepted then none else c.declarations } }

/-- The checkers with their toolchain: `con-leche and con-ron (Lean 4.35.0)`. -/
def Result.checkerName (r : Result) : String :=
  match r.version with
  | some v => s!"{r.checker} (Lean {v})"
  | none => r.checker

/-- The checkers that gave `answer`, by `CheckerRun.label`, joined with "and". -/
def Result.answeredBy (r : Result) (answer : Answer) : String :=
  " and ".intercalate ((r.checkers.filter (·.answer == answer)).map (·.label)).toList

/-- What the checkers did with a build they did not both accept: "con-ron (Lean 4.35.0)
rejected this build", or that they disagree. -/
def Result.rejectionText (r : Result) : String :=
  let rejected := r.answeredBy .rejected
  let rejected := if rejected.isEmpty then r.checkerName else rejected
  if r.outcome == .disagreed then
    s!"the two checkers disagree on this build: {r.answeredBy .accepted} accepted it and \
      {rejected} rejected it"
  else s!"{rejected} rejected this build"

/-- Whether `declaration` is one of `Result.declarations`. -/
def Result.covers (r : Result) (declaration : Name) : Bool :=
  r.declarations.binSearchContains declaration Name.quickLt

/-- What a replay establishes for a set of declarations. -/
inductive Standing where
  /-- Every one of the declarations, with everything it depends on, was checked and accepted by
  both checkers. -/
  | accepted
  /-- A checker rejected the build (alone, or against the other's acceptance). -/
  | rejected
  /-- Nothing was replayed for the declarations: no replay was run, nothing was checked, or an
  accepted replay does not cover them. `why` is a clause that completes "not replayed by a
  kernel: …". -/
  | notReplayed (why : String)
  /-- A replay was started and stopped without a verdict (`Outcome.stoppedWithoutVerdict`).
  `why` is a clause that completes "no verdict of a kernel replay: …". -/
  | noVerdict (why : String)
  /-- The declarations rest on these axioms outside Lean's standard three, so they were not
  exported and not checked. -/
  | notChecked (axioms : Array Name)
deriving Repr, Inhabited, DecidableEq

private def nameList (names : Array Name) : String :=
  ", ".intercalate (names.toList.map (·.toString))

private def mib (bytes : Nat) : Nat := bytes / (1024 * 1024)

/-- Why nothing was established, when the outcome is not a verdict. -/
def Result.whyNot (r : Result) : String :=
  match r.outcome with
  | .accepted | .rejected | .disagreed => ""
  | .noChecker => r.message.getD "this project's Lean toolchain ships no con-leche or con-ron"
  | .declined =>
    let who := r.answeredBy .declined
    let who := if who.isEmpty then r.checkerName else who
    let detail := r.message.map (s!": {·}") |>.getD ""
    s!"{who} declined to check the export{detail}"
  | .timedOut =>
    let limit := r.limitSeconds.map (s!" within {·} s") |>.getD ""
    s!"the replay with {r.checkerName} did not finish{limit}"
  | .overMemory =>
    let limit := r.memoryLimit.map (s!" of {mib ·} MiB") |>.getD ""
    s!"the replay was stopped: {r.message.getD r.checkerName} went over its memory limit{limit}"
  | .overExport =>
    let limit := r.exportLimit.map (s!" of {mib ·} MiB") |>.getD ""
    s!"the export of what the site's declarations depend on went over its size limit{limit}, \
      so the checker was not run"
  | .failed =>
    let detail := r.message.map (s!": {·}") |>.getD ""
    s!"the replay could not run to a verdict{detail}"
  | .off => "the kernel replay was switched off for this build"

/-- What no replay at all is called. -/
def noReplayText : String := "this site was generated without a kernel replay"

/-- Why the replay does not cover `declaration`, as it recorded it. -/
def Result.notCoveredWhy (r : Result) (declaration : Name) : String :=
  match r.notCovered.find? (·.1 == declaration) with
  | some (_, why) => s!"{declaration} {why}"
  | none => s!"{declaration} is not among the declarations that were checked"

/-- The axioms outside `permitted` that the declarations `needed` rest on, as the replay found
them (`Result.axioms`), each once, sorted. -/
def Result.restingOn (r : Result) (needed : Array Name)
    (permitted : Array Name := Data.standardAxioms) : Array Name :=
  let all := r.axioms.foldl (init := #[]) fun acc (declaration, axioms) =>
    if needed.contains declaration then
      axioms.foldl (init := acc) fun acc a =>
        if permitted.contains a || acc.contains a then acc else acc.push a
    else acc
  Data.sortAxioms all

/-- What the replay `r?` establishes for the declarations `needed`: whether both checkers
checked each of them with everything it depends on. A rejection anywhere stands against every
declaration: a checker stops at its first problem, and what else it would have rejected is not
known. A declaration that rests on an axiom outside Lean's standard three was not checked
(`notChecked`), whatever the checkers said of the rest. -/
def standing (r? : Option Result) (needed : Array Name) : Standing :=
  match r? with
  | none => .notReplayed noReplayText
  | some r =>
    match r.outcome with
    | .rejected | .disagreed => .rejected
    | .accepted =>
      let resting := r.restingOn needed
      if !resting.isEmpty then .notChecked resting else
      -- an accepted replay stands behind declarations, never behind none
      if needed.isEmpty then
        .notReplayed "not part of the replay: no Lean declaration is recorded for it"
      else match needed.find? (!r.covers ·) with
        | none => .accepted
        | some missing => .notReplayed s!"not part of the replay: {r.notCoveredWhy missing}"
    | o => if o.stoppedWithoutVerdict then .noVerdict r.whyNot else .notReplayed r.whyNot

/-- `standing` for a node: `unplaced` is a declaration of it whose module is not known, which no
replay is known to cover. -/
def standingOf (r? : Option Result) (needed : Array Name) (unplaced : Option Name) : Standing :=
  match r?.map (·.outcome), unplaced with
  | some Outcome.accepted, some d =>
    .notReplayed s!"not part of the replay: the module of {d} is not known"
  | _, _ => standing r? needed

/-- What the replay establishes for the declarations `needed` as proved: `standingOf`. A
declaration that rests on an axiom outside Lean's standard three is never accepted: it was not
exported, since both checkers decline an export that uses such an axiom (`notChecked`). So
the axioms a challenge permits cannot widen what is accepted: an accepted standing always means
the standard three at most. -/
def provedStanding (r? : Option Result) (needed : Array Name) (unplaced : Option Name := none) :
    Standing :=
  standingOf r? needed unplaced

/-- The clause for declarations left out because they rest on `axioms`: "it rests on the axiom
sorryAx, and a replay checks only what rests on Lean's standard three axioms alone". -/
def notCheckedClause (axioms : Array Name) : String :=
  let noun := if axioms.size == 1 then "an axiom" else "axioms"
  s!"it rests on {noun} outside Lean's standard three ({nameList axioms}), and a replay checks \
    only what rests on the standard three alone"

/-- Why a standing is not an accepted replay, as a clause; empty for `accepted`. -/
def Standing.why : Standing → String
  | .accepted => ""
  | .rejected => rejectedClause
  | .notReplayed why | .noVerdict why => why
  | .notChecked axioms => s!"not checked: {notCheckedClause axioms}"
where
  rejectedClause := "a kernel checker rejected this build"

/-- Whether the standing is an accepted replay. -/
def Standing.isAccepted : Standing → Bool
  | .accepted => true
  | _ => false

/-- The standing as a token for markup: `accepted`, `rejected` or `none`. -/
def Standing.token : Standing → String
  | .accepted => "accepted"
  | .rejected => "rejected"
  | .notReplayed _ | .noVerdict _ | .notChecked _ => "none"

/-- The words for Lean code that no verdict of a replay covers, with the reason: "not replayed
by a kernel (…)" when nothing was replayed for it, "no verdict of a kernel replay (…)" when a
replay stopped without one, "not checked by the kernel replay (…)" when it rests on an axiom
outside the standard three; `none` for the other standings. -/
def Standing.unreplayed? : Standing → Option String
  | .notReplayed why => some s!"not replayed by a kernel ({why})"
  | .noVerdict why => some s!"no verdict of a kernel replay ({why})"
  | .notChecked axioms => some s!"not checked by the kernel replay ({notCheckedClause axioms})"
  | _ => none

/-- The class that tells the stylesheets what stands behind an element (`Standing.token`).
Success colours are drawn only inside `bp_replay_accepted`; a colour is a statement too. -/
def Standing.scopeClass (s : Standing) : String := s!"bp_replay_{s.token}"

/-- What a site as a whole may show in the success colour: the standing behind its counts,
bars and legends, which are about every node at once. -/
inductive SiteState where
  /-- Both checkers accepted the build, the replay covers the Lean code of every node, and no
  node counted as complete rests on an axiom outside Lean's standard three. -/
  | accepted
  /-- A checker rejected the build. -/
  | rejected
  /-- Nothing was replayed: no replay was run, the toolchain ships no checker, the export went
  over its limit, or the replay was switched off. `why` completes "not replayed by a kernel:
  …". -/
  | none (why : String)
  /-- A replay was started and stopped without a verdict. `why` completes "no verdict of a
  kernel replay: …". -/
  | noVerdict (why : String)
  /-- Both checkers accepted the build, but not for every node: `uncovered` nodes with Lean code
  are not part of it, and `resting` nodes without `sorry` rest on an axiom outside Lean's
  standard three (`axioms`, sorted), so they were not checked. One of the two counts is
  positive. -/
  | acceptedExcept (uncovered resting : Nat) (axioms : Array Name)
deriving Repr, Inhabited, DecidableEq

/-- The state of a site: `uncovered` are the nodes with Lean code that an accepted replay does
not cover (`standingOf` is not accepted for them), `resting` the nodes whose Lean code has no
`sorry` and depends on an axiom outside Lean's standard three, `axioms` those axioms. One such
node keeps the counts neutral: a count in the success colour would include it. -/
def siteState (r? : Option Result) (uncovered : Array Name := #[])
    (resting : Array Name := #[]) (axioms : Array Name := #[]) : SiteState :=
  match r? with
  | Option.none => .none noReplayText
  | some r =>
    match r.outcome with
    | .rejected | .disagreed => .rejected
    | .accepted =>
      if uncovered.isEmpty && resting.isEmpty then .accepted
      else .acceptedExcept uncovered.size resting.size (Data.sortAxioms axioms)
    | o => if o.stoppedWithoutVerdict then .noVerdict r.whyNot else .none r.whyNot

/-- The state as a token for markup: `accepted`, `rejected` or `none`. -/
def SiteState.token : SiteState → String
  | .accepted => "accepted"
  | .rejected => "rejected"
  | .none _ | .noVerdict _ | .acceptedExcept .. => "none"

/-- The class that tells the stylesheets what stands behind a page section (`SiteState.token`). -/
def SiteState.scopeClass (s : SiteState) : String := s!"bp_replay_{s.token}"

/-- A number with its thousands separated by commas. -/
def groupedNumber (n : Nat) : String :=
  let digits := (toString n).toList
  let len := digits.length
  String.ofList <| (digits.zipIdx.foldl (init := []) fun acc (c, i) =>
    if i > 0 && (len - i) % 3 == 0 then c :: ',' :: acc else c :: acc).reverse

/-- The words beside a count or a legend entry that an accepted replay would show in the success
colour, when nothing was replayed. -/
def reportedNote : String := "as the compiled files report, not replayed by a kernel"

/-- The words beside such a count when a replay stopped without a verdict. -/
def noVerdictNote : String := "as the compiled files report, with no verdict of a kernel replay"

/-- The words beside such a count when a checker rejected the build. -/
def rejectedNote : String := "this build was rejected by a kernel checker"

/-- `n` nodes, with what is said of them in the singular and in the plural. -/
private def nodesWith (n : Nat) (what one many : String) : String :=
  if n == 1 then s!"1 node {what} {one}" else s!"{groupedNumber n} nodes {what} {many}"

/-- Axioms by name, for a sentence: "the axiom Demo.ax", "the axioms A, B"; an axiom that
asserts the result of compiled code says so. -/
def axiomsPhrase (axioms : Array Name) : String :=
  let named := axioms.toList.map fun a =>
    if Data.AxiomClass.ofName a == .compilerTrusted then s!"{a} (the result of compiled code)"
    else a.toString
  match named with
  | [] => "an axiom outside Lean's standard three"
  | [one] => s!"the axiom {one}"
  | _ => s!"the axioms {", ".intercalate named}"

/-- What keeps a replay that accepted the build from standing behind every node, as clauses
about the site: the nodes it does not cover, and the nodes without `sorry` that rest on an
axiom outside the standard three. `long` adds what follows from such an axiom. -/
def exceptionsText (uncovered resting : Nat) (axioms : Array Name) (long : Bool) : String :=
  let notPart := if uncovered == 0 then [] else
    [nodesWith uncovered "with Lean code" "is not part of the replay" "are not part of the replay"]
  let tail := if !long then "" else
    s!", so {if resting == 1 then "it was" else "they were"} not checked and \
      {if resting == 1 then "is" else "are"} not shown as proved"
  let rests := if resting == 0 then [] else
    [nodesWith resting "without sorry" s!"rests on {axiomsPhrase axioms}{tail}"
      s!"rest on {axiomsPhrase axioms}{tail}"]
  (if long then "; " else ", and ").intercalate (notPart ++ rests)

/-- The qualification of a count or a legend entry about `sorry`-free Lean code: nothing under
an accepted replay of every node, else what the count rests on. Each is true of the site as a
whole, whichever nodes the count includes. -/
def SiteState.note? : SiteState → Option String
  | .accepted => Option.none
  | .rejected => some rejectedNote
  | .none _ => some reportedNote
  | .noVerdict _ => some noVerdictNote
  | .acceptedExcept u r axioms =>
    some s!"the kernel replay accepted the build; on this site \
      {exceptionsText u r axioms (long := false)}"

/-- A sentence after a count's description that says what the count rests on; nothing under an
accepted replay of every node. -/
def SiteState.countSentence? : SiteState → Option String
  | .accepted => Option.none
  | .rejected => some "A kernel checker rejected this build."
  | .none _ => some "Counted as the compiled files report, not replayed by a kernel."
  | .noVerdict _ => some "Counted as the compiled files report, with no verdict of a kernel replay."
  | .acceptedExcept u r axioms =>
    some s!"Counted as the compiled files report: the kernel replay accepted the build, and on \
      this site {exceptionsText u r axioms (long := true)}."

/-- One sentence for a page that shows counts: what stands behind them. Empty under an accepted
replay of every node. -/
def SiteState.sentence : SiteState → String
  | .accepted => ""
  | .rejected =>
    "This build was rejected by a kernel checker: the counts say what the compiled files \
      report, and nothing here counts as checked by a kernel."
  | .none why => s!"The counts are as the compiled files report, not replayed by a kernel: {why}."
  | .noVerdict why =>
    s!"The counts are as the compiled files report, with no verdict of a kernel replay: {why}."
  | .acceptedExcept u r axioms =>
    s!"The kernel replay accepted the build, and the counts are as the compiled files report: \
      {exceptionsText u r axioms (long := true)}."

/-- `n` things: "1 constant", "3,409 constants". -/
def counted (n : Nat) (noun : String) : String :=
  s!"{groupedNumber n} {noun}{if n == 1 then "" else "s"}"

/-- Where the exported constants come from, in words: "135 of this project, 51,402 of Mathlib
and 7,807 of Lean's own library (Init, Std)". -/
def Result.originsText (r : Result) : String :=
  let part (o : Origin) : String :=
    match o.kind with
    | .project => s!"{groupedNumber o.constants} of this project"
    | .dependency => s!"{groupedNumber o.constants} of {o.name}"
    | .toolchain => s!"{groupedNumber o.constants} of Lean's own library ({o.name})"
  match r.origins.toList.map part with
  | [] => ""
  | [one] => one
  | parts => ", ".intercalate parts.dropLast ++ " and " ++ parts.getLast!

/-- What an accepted replay checked: "3 declarations and everything they depend on, 3,409
constants in all". -/
def Result.checkedText (r : Result) : String :=
  let them := if r.declarations.size == 1 then "it depends" else "they depend"
  s!"{counted r.declarations.size "declaration"} and everything {them} on, \
    {counted r.constants "constant"} in all"

/-- One sentence on what the replay did, for the Project Stats page. -/
def Result.summary (r : Result) : String :=
  match r.outcome with
  | .accepted =>
    let origins := if r.origins.isEmpty then "" else s!" ({r.originsText})"
    if r.reproducible then
      s!"Accepted: {r.checkerName} both accepted this build's export, in this run or, for an \
        identical export, in an earlier one: {r.checkedText}{origins}, each starting from its \
        own built-in prelude."
    else if r.recorded then
      s!"Accepted: {r.checkerName} both accepted an export identical to this build's in an \
        earlier run: {r.checkedText}{origins}."
    else
      s!"Accepted: {r.checkerName} each checked {r.checkedText}{origins}, starting from its \
        own built-in prelude, and both accepted them."
  | .rejected =>
    s!"Rejected: {r.rejectionText} (the export of this site's declarations and what they \
      depend on). Nothing on this site counts as checked by a kernel."
  | .disagreed =>
    s!"Rejected: {r.rejectionText}. Nothing on this site counts as checked by a kernel."
  | o =>
    let lead := if o.stoppedWithoutVerdict then "No verdict of a kernel replay"
      else "Not replayed by a kernel"
    s!"{lead}: {r.whyNot}. The marks on this site say what the compiled files report."

/-- What a replay is, and what it leaves trusted. -/
def trustedText : String :=
  "A replay takes the Lean declarations of this site's nodes and the theorems its headline \
    judges from the compiled modules, as the generator loaded them when the site was generated. \
    Each of them that rests on no axiom beyond Lean's standard three is exported together with \
    every constant it depends on, whether that is in this project, in one of its dependencies \
    or in Lean's own library, and two checkers that ship with the Lean toolchain, con-leche and \
    con-ron, each check the whole export, starting from its own built-in prelude; a declaration \
    counts as checked only when both accept (an export identical to one both accepted before is \
    not checked twice). A declaration that rests on another axiom, sorry among them, is not \
    exported and not checked: both checkers decline an export that uses such an axiom. \
    Constants that no exported declaration depends on are not checked. It leaves trusted: the \
    export, which the generator writes from the modules it loaded with the toolchain's \
    exporter; con-leche, a checker written in Lean, with the Lean compiler and runtime it is \
    built with; con-ron, a checker written in Rust, with the Rust compiler and the memory \
    allocator it is built with; and Lean's elaborator, for the step from the source text to the \
    compiled module. A replay says nothing about what a statement means."

end Informal.Replay
