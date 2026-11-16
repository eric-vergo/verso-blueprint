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
in Lean's own library, and Lean's `leanchecker`, the toolchain's own program, checks all of them
again in Lean's kernel, starting from an empty environment (`Informal.Stats.ProjectStats.withKernelReplayAt` runs
it when the site is generated). Everywhere else the words are what the compiled files report,
with a mark that is not a check mark.

This module holds the result of a replay and the words for it; nothing here runs anything.

What a replay leaves trusted is said on the page (`trustedText`): the checker and Lean's kernel
in it; the export, which the generator writes from the modules it loaded with the toolchain's
exporter; and Lean's elaborator for the step from the source text to the compiled module. No
replay says anything about what a statement means.
-/

namespace Informal.Replay

open Lean

/-- How a kernel replay ended. -/
inductive Outcome where
  /-- The checker accepted the export: every declaration of `Result.declarations` and every
  constant it depends on. -/
  | accepted
  /-- The checker rejected the export (`Result.message`). -/
  | rejected
  /-- No checker was found: nothing was replayed. -/
  | noChecker
  /-- The replay was stopped at the time limit (`Result.limitSeconds`) without a verdict. -/
  | timedOut
  /-- The checker was stopped because it went over its memory limit (`Result.memoryLimit`),
  without a verdict. -/
  | overMemory
  /-- The export went over its size limit (`Result.exportLimit`); the checker was not run. -/
  | overExport
  /-- The replay could not run to a verdict (`Result.message`). -/
  | failed
  /-- The replay was switched off for this build. -/
  | off
deriving Repr, Inhabited, DecidableEq, ToJson, FromJson

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
  /-- The checker's name. -/
  checker : String := "leanchecker"
  /-- The Lean version of the toolchain the checker belongs to. -/
  version : Option String := none
  /-- The declarations the replay covers, in `Name.quickLt` order: with `accepted`, each was
  exported with every constant it depends on, and the checker accepted them all; otherwise the
  declarations that were to be checked. -/
  declarations : Array Name := #[]
  /-- Declarations the replay was asked for and does not cover, each with the reason (it is not
  in the compiled modules that were loaded, it is in another module there, it is unsafe). -/
  notCovered : Array (Name × String) := #[]
  /-- For each declaration of `declarations` that depends on an axiom outside Lean's standard
  three: those axioms, sorted, as found by walking the terms of the loaded modules (`sorryAx`
  among them). A kernel accepts an axiom without a proof, so an accepted replay proves such a
  declaration only from them. -/
  axioms : Array (Name × Array Name) := #[]
  /-- The number of constants in the export. -/
  constants : Nat := 0
  /-- Where the exported constants come from, the largest group first. -/
  origins : Array Origin := #[]
  /-- With `accepted`: the checker accepted an identical export in an earlier run and was not
  run again. -/
  recorded : Bool := false
  /-- With `rejected` or `failed`: what the checker, or the generator, said. With `overMemory`:
  what went over the limit, when it was not the checker. -/
  message : Option String := none
  /-- With `timedOut`: the limit. -/
  limitSeconds : Option Nat := none
  /-- With `overMemory`: the memory limit of the checker process, in bytes. -/
  memoryLimit : Option Nat := none
  /-- With `overExport`: the size limit of the export, in bytes. -/
  exportLimit : Option Nat := none
deriving Repr, Inhabited, DecidableEq, ToJson, FromJson

/-- The checker with its toolchain: `leanchecker (Lean 4.35.0)`. -/
def Result.checkerName (r : Result) : String :=
  match r.version with
  | some v => s!"{r.checker} (Lean {v})"
  | none => r.checker

/-- Whether `declaration` is one of `Result.declarations`. -/
def Result.covers (r : Result) (declaration : Name) : Bool :=
  r.declarations.binSearchContains declaration Name.quickLt

/-- The axioms outside `permitted` that the declarations `needed` depend on, as the replay
found them (`Result.axioms`), each once, sorted. -/
def Result.restingOn (r : Result) (needed : Array Name)
    (permitted : Array Name := Data.standardAxioms) : Array Name :=
  let all := r.axioms.foldl (init := #[]) fun acc (declaration, axioms) =>
    if needed.contains declaration then
      axioms.foldl (init := acc) fun acc a =>
        if permitted.contains a || acc.contains a then acc else acc.push a
    else acc
  Data.sortAxioms all

/-- What a replay establishes for a set of declarations. -/
inductive Standing where
  /-- Every one of the declarations, with everything it depends on, was checked and
  accepted. -/
  | accepted
  /-- The checker rejected the build. -/
  | rejected
  /-- Nothing was established: no replay was run, it did not end with a verdict, or it does
  not cover the declarations. `why` is a clause that completes "not replayed by a kernel: …". -/
  | notReplayed (why : String)
  /-- The checker accepted the declarations, and the replay found these axioms under them that
  are not permitted: a kernel accepts an axiom without a proof, so they are proved only from
  the axioms. -/
  | assumed (axioms : Array Name)
deriving Repr, Inhabited, DecidableEq

private def nameList (names : Array Name) : String :=
  ", ".intercalate (names.toList.map (·.toString))

private def mib (bytes : Nat) : Nat := bytes / (1024 * 1024)

/-- Why nothing was established, when the outcome is not a verdict. -/
def Result.whyNot (r : Result) : String :=
  match r.outcome with
  | .accepted | .rejected => ""
  | .noChecker => "no kernel checker was found"
  | .timedOut =>
    let limit := r.limitSeconds.map (s!" within {·} s") |>.getD ""
    s!"the replay with {r.checkerName} did not finish{limit}"
  | .overMemory =>
    let limit := r.memoryLimit.map (s!" of {mib ·} MiB") |>.getD ""
    s!"the replay was stopped: {r.message.getD r.checkerName} went over its memory limit{limit}"
  | .overExport =>
    let limit := r.exportLimit.map (s!" of {mib ·} MiB") |>.getD ""
    s!"the replay was stopped: the export of what the site's declarations depend on went over \
      its size limit{limit}"
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

/-- What the replay `r?` establishes for the declarations `needed`: whether it checked each of
them with everything it depends on. A rejection anywhere stands against every declaration: the
checker stops at its first problem, and what else it would have rejected is not known. The
axioms a declaration depends on are a separate matter (`provedStanding`). -/
def standing (r? : Option Result) (needed : Array Name) : Standing :=
  match r? with
  | none => .notReplayed noReplayText
  | some r =>
    match r.outcome with
    | .rejected => .rejected
    | .accepted =>
      -- an accepted replay stands behind declarations, never behind none
      if needed.isEmpty then
        .notReplayed "not part of the replay: no Lean declaration is recorded for it"
      else match needed.find? (!r.covers ·) with
        | none => .accepted
        | some missing => .notReplayed s!"not part of the replay: {r.notCoveredWhy missing}"
    | _ => .notReplayed r.whyNot

/-- `standing` for a node: `unplaced` is a declaration of it whose module is not known, which no
replay is known to cover. -/
def standingOf (r? : Option Result) (needed : Array Name) (unplaced : Option Name) : Standing :=
  match r?.map (·.outcome), unplaced with
  | some Outcome.accepted, some d =>
    .notReplayed s!"not part of the replay: the module of {d} is not known"
  | _, _ => standing r? needed

/-- What the replay establishes for the declarations `needed` as proved: `standingOf`, and
accepted only when the replay also found no axiom outside `permitted` under them (Lean's
standard three unless a list is given). A kernel accepts an axiom, `sorryAx` included, without
a proof. -/
def provedStanding (r? : Option Result) (needed : Array Name) (unplaced : Option Name := none)
    (permitted : Array Name := Data.standardAxioms) : Standing :=
  match standingOf r? needed unplaced, r? with
  | .accepted, some r =>
    let axioms := r.restingOn needed permitted
    if axioms.isEmpty then .accepted else .assumed axioms
  | s, _ => s

/-- Why a standing is not an accepted replay, as a clause; empty for `accepted`. -/
def Standing.why : Standing → String
  | .accepted => ""
  | .rejected => rejectedClause
  | .notReplayed why => why
  | .assumed axioms =>
    let noun := if axioms.size == 1 then "an axiom" else "axioms"
    s!"the replay found {noun} under it that a kernel accepts without a proof \
      ({nameList axioms})"
where
  rejectedClause := "the kernel checker rejected this build"

/-- Whether the standing is an accepted replay. -/
def Standing.isAccepted : Standing → Bool
  | .accepted => true
  | _ => false

/-- The standing as a token for markup: `accepted`, `rejected` or `none`. -/
def Standing.token : Standing → String
  | .accepted => "accepted"
  | .rejected => "rejected"
  | .notReplayed _ | .assumed _ => "none"

/-- The class that tells the stylesheets what stands behind an element (`Standing.token`).
Success colours are drawn only inside `bp_replay_accepted`; a colour is a statement too. -/
def Standing.scopeClass (s : Standing) : String := s!"bp_replay_{s.token}"

/-- What a site as a whole may show in the success colour: the standing behind its counts,
bars and legends, which are about every node at once. -/
inductive SiteState where
  /-- The replay accepted the build, covers the Lean code of every node, and found no axiom
  outside Lean's standard three under a node counted as complete. -/
  | accepted
  /-- The checker rejected the build. -/
  | rejected
  /-- No verdict of a replay stands behind every node. `why` completes "not replayed by a
  kernel: …". -/
  | none (why : String)
deriving Repr, Inhabited, DecidableEq

/-- The state of a site: `uncovered` are the nodes with Lean code that an accepted replay does
not cover (`standingOf` is not accepted for them), `resting` the nodes whose Lean code has no
`sorry` and depends on an axiom outside Lean's standard three. One such node keeps the counts
neutral: a count in the success colour would include it. -/
def siteState (r? : Option Result) (uncovered : Array Name := #[])
    (resting : Array Name := #[]) : SiteState :=
  match r? with
  | Option.none => .none noReplayText
  | some r =>
    match r.outcome with
    | .rejected => .rejected
    | .accepted =>
      let nodes (n : Nat) (one many : String) : String :=
        if n == 1 then s!"1 node with Lean code {one}" else s!"{n} nodes with Lean code {many}"
      if !uncovered.isEmpty then
        .none (nodes uncovered.size "is" "are" ++ " not part of the replay")
      else if !resting.isEmpty then
        .none (nodes resting.size "rests" "rest" ++ " on an axiom outside Lean's standard \
          three, which a kernel accepts without a proof")
      else .accepted
    | _ => .none r.whyNot

/-- The state as a token for markup: `accepted`, `rejected` or `none`. -/
def SiteState.token : SiteState → String
  | .accepted => "accepted"
  | .rejected => "rejected"
  | .none _ => "none"

/-- The class that tells the stylesheets what stands behind a page section (`SiteState.token`). -/
def SiteState.scopeClass (s : SiteState) : String := s!"bp_replay_{s.token}"

/-- The words beside a count or a legend entry that an accepted replay would show in the success
colour, when none stands behind it. -/
def reportedNote : String := "as the compiled files report, not replayed by a kernel"

/-- The words beside such a count when the checker rejected the build. -/
def rejectedNote : String := "this build was rejected by the kernel checker"

/-- The qualification of a count or a legend entry about `sorry`-free Lean code: nothing under
an accepted replay, else what the count rests on. -/
def SiteState.note? : SiteState → Option String
  | .accepted => Option.none
  | .rejected => some rejectedNote
  | .none _ => some reportedNote

/-- A sentence after a count's description that says what the count rests on; nothing under an
accepted replay. -/
def SiteState.countSentence? : SiteState → Option String
  | .accepted => Option.none
  | .rejected => some "The kernel checker rejected this build."
  | .none _ => some "Counted as the compiled files report, not replayed by a kernel."

/-- One sentence for a page that shows counts: what stands behind them. Empty under an accepted
replay. -/
def SiteState.sentence : SiteState → String
  | .accepted => ""
  | .rejected =>
    "This build was rejected by the kernel checker: the counts say what the compiled files \
      report, and nothing here counts as checked by a kernel."
  | .none why => s!"The counts are as the compiled files report, not replayed by a kernel: {why}."

/-- A number with its thousands separated by commas. -/
def groupedNumber (n : Nat) : String :=
  let digits := (toString n).toList
  let len := digits.length
  String.ofList <| (digits.zipIdx.foldl (init := []) fun acc (c, i) =>
    if i > 0 && (len - i) % 3 == 0 then c :: ',' :: acc else c :: acc).reverse

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
    let how := if r.recorded then
        s!"{r.checkerName} accepted an export identical to this build's in an earlier run: "
      else s!"{r.checkerName} checked "
    let tail := if r.recorded then "" else
      " again in Lean's kernel, starting from an empty environment"
    s!"Accepted: {how}{r.checkedText}{origins}{tail}."
  | .rejected =>
    s!"Rejected: {r.checkerName} found a problem in what this site's declarations depend on. \
      Nothing on this site counts as checked by a kernel."
  | _ => s!"Not replayed by a kernel: {r.whyNot}. The marks on this site say what the compiled \
      files report."

/-- What a replay is, and what it leaves trusted. -/
def trustedText : String :=
  "A replay takes the Lean declarations of this site's nodes and the theorems its headline \
    judges from the compiled modules, as the generator loaded them when the site was generated. \
    It exports each of them together with every constant it depends on, whether that is in \
    this project, in one of its dependencies or in Lean's own library, and the checker checks \
    all of them again in Lean's kernel, starting from an empty environment (an export identical \
    to one a replay accepted before is not checked twice). Constants that no such declaration \
    depends on are not checked. It leaves trusted: the checker and Lean's kernel in it; the \
    export, which the generator writes from the modules it loaded with the exporter of the \
    Lean toolchain; and Lean's elaborator, for the step from the source text to the compiled \
    module. A kernel accepts an axiom without a proof, so the axioms a declaration depends on \
    are found by walking the same terms, and a declaration that depends on one outside Lean's \
    standard three is not shown as checked. A replay says nothing about what a statement means."

end Informal.Replay
