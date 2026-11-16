/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

import Lean.Data.Json

/-!
The kernel replay of a build, as a site reports it.

A site is generated from compiled modules. What they say (a statement, the absence of `sorry`, a
list of axioms) is what Lean's elaborator recorded, and a file can keep the kernel from seeing a
declaration at all (`set_option debug.skipKernelTC true`). So a site says "proved", and draws a
check mark in the success colour, only where a kernel replay accepted the compiled modules
concerned: Lean's `leanchecker`, the toolchain's own program, checks every constant a module adds
again in Lean's kernel, in a process of its own (`Informal.Stats.replayBuild` runs it when the
site is generated). Everywhere else the words are what the compiled files report, with a mark
that is not a check mark.

This module holds the result of a replay and the words for it; nothing here runs anything.

What a replay leaves trusted is said on the page (`trustedText`): the checker and Lean's kernel
in it; the compiled modules of everything outside the project, which are loaded and not
replayed; and Lean's elaborator for the step from the source text to the compiled module. No
replay says anything about what a statement means.
-/

namespace Informal.Replay

open Lean

/-- How a kernel replay ended. -/
inductive Outcome where
  /-- The checker replayed every module of `Result.modules` and accepted them. -/
  | accepted
  /-- The checker rejected a module (`Result.rejectedModule`, `Result.message`). -/
  | rejected
  /-- No checker was found: nothing was replayed. -/
  | noChecker
  /-- The checker was stopped at the time limit (`Result.limitSeconds`) without a verdict. -/
  | timedOut
  /-- The checker could not run to a verdict (`Result.message`). -/
  | failed
  /-- The replay was switched off for this build. -/
  | off
deriving Repr, Inhabited, DecidableEq, ToJson, FromJson

/-- The kernel replay of one build. -/
structure Result where
  outcome : Outcome
  /-- The checker's name. -/
  checker : String := "leanchecker"
  /-- The Lean version of the toolchain the checker belongs to. -/
  version : Option String := none
  /-- The project's modules the replay covers, sorted: with `accepted`, each was replayed and
  accepted; otherwise the modules that were to be replayed. -/
  modules : Array Name := #[]
  /-- Modules of the site that have no compiled module among the project's own, so that nothing
  could be replayed for them (a file run as a script, for example), sorted. -/
  notCompiled : Array Name := #[]
  /-- With `rejected`: the module the checker rejected. -/
  rejectedModule : Option Name := none
  /-- With `rejected` or `failed`: what the checker said. -/
  message : Option String := none
  /-- With `timedOut`: the limit. -/
  limitSeconds : Option Nat := none
deriving Repr, Inhabited, DecidableEq, ToJson, FromJson

/-- The checker with its toolchain: `leanchecker (Lean 4.35.0)`. -/
def Result.checkerName (r : Result) : String :=
  match r.version with
  | some v => s!"{r.checker} (Lean {v})"
  | none => r.checker

/-- What a replay establishes for a set of modules. -/
inductive Standing where
  /-- Every one of the modules was replayed and accepted. -/
  | accepted
  /-- The checker rejected the build; `module` is the module it stopped on. -/
  | rejected (module : Option Name)
  /-- Nothing was established: no replay was run, it did not end with a verdict, or it did not
  cover the modules. `why` is a clause that completes "not replayed by a kernel: …". -/
  | notReplayed (why : String)
deriving Repr, Inhabited, DecidableEq

private def nameList (names : Array Name) : String :=
  ", ".intercalate (names.toList.map (·.toString))

/-- Why nothing was established, when the outcome is not a verdict. -/
def Result.whyNot (r : Result) : String :=
  match r.outcome with
  | .accepted | .rejected => ""
  | .noChecker => "no kernel checker was found"
  | .timedOut =>
    let limit := r.limitSeconds.map (s!" within {·} s") |>.getD ""
    s!"{r.checkerName} did not finish{limit}"
  | .failed => s!"{r.checkerName} could not run to a verdict"
  | .off => "the kernel replay was switched off for this build"

/-- What no replay at all is called. -/
def noReplayText : String := "this site was generated without a kernel replay"

/-- What the replay `r?` establishes for the modules `needed`. A rejection anywhere stands
against every module: which declarations rest on the rejected one is not known. -/
def standing (r? : Option Result) (needed : Array Name) : Standing :=
  match r? with
  | none => .notReplayed noReplayText
  | some r =>
    match r.outcome with
    | .rejected => .rejected r.rejectedModule
    | .accepted =>
      let missing := needed.filter (!r.modules.contains ·)
      if missing.isEmpty then .accepted
      else
        let be := if missing.size == 1 then "is" else "are"
        .notReplayed s!"not part of a replayed module: {nameList missing} {be} not among the \
          project's modules that were replayed"
    | _ => .notReplayed r.whyNot

/-- `standing` for a node: `unplaced` is a declaration of it whose module is not known, which no
accepted replay is known to cover. -/
def standingOf (r? : Option Result) (needed : Array Name) (unplaced : Option Name) : Standing :=
  match standing r? needed, unplaced with
  | .accepted, some d =>
    .notReplayed s!"not part of a replayed module: the module of {d} is not known"
  | s, _ => s

/-- Whether the standing is an accepted replay. -/
def Standing.isAccepted : Standing → Bool
  | .accepted => true
  | _ => false

/-- The standing as a token for markup: `accepted`, `rejected` or `none`. -/
def Standing.token : Standing → String
  | .accepted => "accepted"
  | .rejected _ => "rejected"
  | .notReplayed _ => "none"

/-- The class that tells the stylesheets what stands behind an element (`Standing.token`).
Success colours are drawn only inside `bp_replay_accepted`; a colour is a statement too. -/
def Standing.scopeClass (s : Standing) : String := s!"bp_replay_{s.token}"

/-- What a site as a whole may show in the success colour: the standing behind its counts,
bars and legends, which are about every node at once. -/
inductive SiteState where
  /-- The replay accepted the build and covers the Lean code of every node. -/
  | accepted
  /-- The checker rejected the build. -/
  | rejected
  /-- No verdict of a replay stands behind every node. `why` completes "not replayed by a
  kernel: …". -/
  | none (why : String)
deriving Repr, Inhabited, DecidableEq

/-- The state of a site: `uncovered` are the nodes with Lean code that an accepted replay does
not cover (`standingOf` is not accepted for them). One such node keeps the counts neutral: a
count in the success colour would include it. -/
def siteState (r? : Option Result) (uncovered : Array Name := #[]) : SiteState :=
  match r? with
  | Option.none => .none noReplayText
  | some r =>
    match r.outcome with
    | .rejected => .rejected
    | .accepted =>
      if uncovered.isEmpty then .accepted
      else
        let nodes := if uncovered.size == 1 then "1 node with Lean code is"
          else s!"{uncovered.size} nodes with Lean code are"
        .none s!"{nodes} not part of a replayed module"
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

/-- One sentence on what the replay did, for the Project Stats page. -/
def Result.summary (r : Result) : String :=
  let n := r.modules.size
  let modules := if n == 1 then "1 compiled module" else s!"{n} compiled modules"
  match r.outcome with
  | .accepted =>
    s!"Accepted: {r.checkerName} checked every constant of this project's {modules} again in \
      Lean's kernel, in a process of its own."
  | .rejected =>
    let where_ := r.rejectedModule.map (s!" in module {·}") |>.getD ""
    s!"Rejected: {r.checkerName} found a problem{where_}. Nothing on this site counts as checked \
      by a kernel."
  | _ => s!"Not replayed by a kernel: {r.whyNot}. The marks on this site say what the compiled \
      files report."

/-- What a replay is, and what it leaves trusted. -/
def trustedText : String :=
  "A replay checks each constant that a module of this project adds again in Lean's kernel, on \
    top of the module's imports, reading the compiled modules as they were when the site was \
    generated (a module whose compiled file is identical to one a replay accepted before, with \
    identical imports, is not replayed twice). It leaves trusted: the checker and Lean's kernel \
    in it; the compiled modules of everything outside this project (Lean's own library and the \
    project's dependencies), which are loaded and not replayed; and Lean's elaborator, for the \
    step from the source text to the compiled module. It says nothing about what a statement \
    means."

end Informal.Replay
