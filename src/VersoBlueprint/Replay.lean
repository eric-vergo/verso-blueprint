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
        .notReplayed s!"{nameList missing} {be} not among the project's modules that were replayed"
    | _ => .notReplayed r.whyNot

/-- Whether the standing is an accepted replay. -/
def Standing.isAccepted : Standing → Bool
  | .accepted => true
  | _ => false

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
