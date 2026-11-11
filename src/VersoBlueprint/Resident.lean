/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

import VersoManual
import VersoBlueprint.RenderModel

/-!
Document substitution for a resident build session (`vbp build --resident`).

A resident session keeps the generator's environment loaded. When only included chapters changed,
it elaborates those chapters again in-process instead of rebuilding their `.olean` files, and then
runs the generator's `main` once more. The generator still evaluates the document it was compiled
with; `blueprintMain` and `blueprintMainWithPreviewData` call `apply`, which replaces the included
parts of the rebuilt chapters and the render model captured from the old Blueprint state. Outside a
session nothing is installed and `apply` returns its arguments.
-/

namespace Informal.Resident

open Lean
open Verso Doc
open Verso.Genre (Manual)

/-- A chapter elaborated again: the part the compiled document includes and its replacement. -/
structure ChapterUpdate where
  /-- The chapter's module. -/
  module : Name
  /-- The part as the compiled document includes it (`VersoDoc.toPart` of the old constant). -/
  previous : Part Manual
  /-- The part of the chapter as elaborated now. -/
  replacement : Part Manual

/-- What the next generator run substitutes. -/
structure Substitution where
  chapters : Array ChapterUpdate := #[]
  /-- The render model of the Blueprint state with the rebuilt chapters' entries. -/
  model : RenderModel

/-- Set by a resident session around one generator run. -/
initialize substitutionRef : IO.Ref (Option Substitution) ← IO.mkRef none

/-- Whether the generator applied the installed substitution (checked by the session). -/
initialize appliedRef : IO.Ref Bool ← IO.mkRef false

/-- Install a substitution for the next generator run. -/
def install (substitution : Substitution) : IO Unit := do
  appliedRef.set false
  substitutionRef.set (some substitution)

/-- Remove the substitution; whether the generator applied it. -/
def uninstall : IO Bool := do
  substitutionRef.set none
  appliedRef.modifyGet fun applied => (applied, false)

/--
Replace every subpart (at any depth) equal to one of the `previous` parts by its replacement.
Returns the new part and the modules whose part was found, once per occurrence. Titles are compared
before whole parts, so unrelated parts cost a string comparison.
-/
partial def replaceParts (updates : Array ChapterUpdate) (part : Part Manual) :
    Part Manual × Array Name :=
  let (subParts, found) := part.subParts.foldl (init := (#[], #[])) fun (subParts, found) sub =>
    match updates.find? fun update =>
        update.previous.titleString == sub.titleString && update.previous == sub with
    | some update => (subParts.push update.replacement, found.push update.module)
    | none =>
      let (sub, inner) := replaceParts updates sub
      (subParts.push sub, found ++ inner)
  ({ part with subParts }, found)

/--
The document and render model the generator renders: the installed substitution applied to
`text`, else both arguments unchanged. Fails when a rebuilt chapter is not included exactly once,
so that the session falls back to a full build instead of rendering a stale chapter.
-/
def apply (text : Part Manual) (model : RenderModel) : IO (Part Manual × RenderModel) := do
  let some substitution ← substitutionRef.get
    | return (text, model)
  let (text, found) := replaceParts substitution.chapters text
  for update in substitution.chapters do
    let count := (found.filter (· == update.module)).size
    unless count == 1 do
      throw <| IO.userError
        s!"resident build: chapter {update.module} is included {count} times in the document; expected once"
  appliedRef.set true
  return (text, substitution.model)

end Informal.Resident
