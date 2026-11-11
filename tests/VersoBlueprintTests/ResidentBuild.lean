/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

import VersoBlueprint.PreviewManifest
import VersoBlueprint.VbpResident

/-!
Resident builds (`vbp build --resident`): the document substitution the generator applies, the
session's plan and request parsing, chapter detection, and the shared inspection cache.
-/

namespace Verso.VersoBlueprintTests.ResidentBuild

open Lean
open Verso Genre Manual
open Informal.Resident
open VersoBlueprint.Vbp.Resident

#docs (Manual) rootDoc "Root" :=
:::::::
The root.
:::::::

#docs (Manual) chapterA "Chapter A" :=
:::::::
First chapter.
:::::::

#docs (Manual) chapterAEdited "Chapter A" :=
:::::::
First chapter, edited.
:::::::

#docs (Manual) chapterB "Chapter B" :=
:::::::
Second chapter.
:::::::

private def document : Verso.Doc.Part Manual :=
  { rootDoc.toPart with subParts := #[chapterA.toPart, chapterB.toPart] }

private def updateA : ChapterUpdate :=
  { module := `A, previous := chapterA.toPart, replacement := chapterAEdited.toPart }

/-- info: true -/
#guard_msgs in
#eval
  let (part, found) := replaceParts #[updateA] document
  found == #[`A] && part.subParts.size == 2 &&
    part.subParts[0]! == chapterAEdited.toPart && part.subParts[1]! == chapterB.toPart

-- a nested chapter is found too
/-- info: true -/
#guard_msgs in
#eval
  let nested := { rootDoc.toPart with subParts := #[document] }
  let (part, found) := replaceParts #[updateA] nested
  found == #[`A] && part.subParts[0]!.subParts[0]! == chapterAEdited.toPart

-- without a substitution, `apply` changes nothing
/-- info: true -/
#guard_msgs in
#eval show IO Bool from do
  let (part, model) ← apply document {}
  return part == document && model.nodes.isEmpty

-- an installed substitution is applied once and reported
/-- info: (true, true, false) -/
#guard_msgs in
#eval show IO (Bool × Bool × Bool) from do
  install { chapters := #[updateA], model := {} }
  let (part, _) ← apply document {}
  let applied ← uninstall
  let (again, _) ← apply document {}
  return (part.subParts[0]! == chapterAEdited.toPart, applied, again != document)

-- a chapter the document does not include is an error (the session falls back to Lake)
/-- info: "resident build: chapter B is included 0 times in the document; expected once" -/
#guard_msgs in
#eval show IO String from do
  install { chapters := #[{ updateA with module := `B, previous := chapterAEdited.toPart }], model := {} }
  try
    discard <| apply document {}
    discard uninstall
    return "applied"
  catch err =>
    discard uninstall
    return toString err

/-! ## The plan -/

private def mod (name : Name) (imports : Array Name) (hash : UInt64) (isModule := false) : SourceModule :=
  { name, file := s!"{name}.lean", imports, isModule, hash }

private def sources (modules : Array SourceModule) (generatorHash : UInt64 := 1)
    (config : Array (System.FilePath × Option UInt64) := #[("lakefile.lean", some 7)]) : Sources :=
  { generatorHash, modules, config }

private def closure (a b : UInt64) (libHash : UInt64 := 3) (aImports := #[`Lib]) : Array SourceModule :=
  #[mod `Lib #[] libHash, mod `A aImports a, mod `B #[`Lib] b, mod `Root #[`A, `B] 9]

private def chapters : NameSet := chaptersOf (closure 1 2) #[`Root] `Root

/-- info: [`A, `B] -/
#guard_msgs in
#eval chapters.toList.mergeSort (·.toString < ·.toString)

/-- info: true -/
#guard_msgs in
#eval
  let base := sources (closure 1 2)
  plan base base chapters == .unchanged &&
    plan base (sources (closure 5 2)) chapters == .chapters #[`A] &&
    plan base (sources (closure 5 6)) chapters == .chapters #[`A, `B] &&
    plan base (sources (closure 1 2 (libHash := 4))) chapters ==
      .lake "Lib changed and is not an included chapter" &&
    plan base (sources (closure 1 2 |>.push (mod `New #[] 1))) chapters ==
      .lake "the set of imported workspace modules changed"

/-- info: true -/
#guard_msgs in
#eval
  let base := sources (closure 1 2)
  -- the same modules, but `A` now imports another dependency
  let reordered := sources #[mod `Lib #[] 3, mod `A #[`Lib, `Other] 5, mod `B #[`Lib] 2, mod `Root #[`A, `B] 9]
  plan base reordered chapters == .lake "the imports of A changed" &&
    plan base (sources (closure 1 2) (generatorHash := 2)) chapters == .lake "the generator file changed" &&
    plan base (sources (closure 1 2) (config := #[("lakefile.lean", some 8)])) chapters ==
      .restart "lakefile.lean"

-- a module imported by another chapter, the generator, or in the module system is not a chapter
/-- info: [`B] -/
#guard_msgs in
#eval
  let modules := #[mod `Lib #[] 3, mod `A #[`Lib] 1, mod `C #[`A] 4, mod `B #[`Lib] 2,
    mod `D #[] 5 (isModule := true), mod `Root #[`A, `B, `C, `D] 9]
  (chaptersOf modules #[`Root, `C] `Root).toList

/-- info: true -/
#guard_msgs in
#eval
  let parsed (line : String) := (parseRequest line).toOption
  parsed "build" == some (.build false) && parsed "" == some (.build false) &&
    parsed "  build --full " == some (.build true) &&
    parsed "prepare blueprint/Chapter.lean" == some (.prepare "blueprint/Chapter.lean") &&
    parsed "quit" == some .quit && (parsed "rebuild").isNone

/-- info: [some `Contents, some `RokickiBlueprint, none] -/
#guard_msgs in
#eval [docModuleOf? "def main :=\n  blueprintMain (%doc Contents) args",
  docModuleOf? "  Informal.PreviewManifest.blueprintMainWithPreviewData\n    (%doc RokickiBlueprint)\n",
  docModuleOf? "def main : IO Unit := pure ()"]

/-! ## The shared inspection cache -/

-- the second analysis of imported declarations reads the environment's cache: same results
/-- info: true -/
#guard_msgs in
#eval show CoreM Bool from do
  let names := #[``Nat.add_comm, ``List.length_append, ``Array.size_push]
  let first ← names.mapM Informal.Data.analyzeDeclaration
  let cached ← match Informal.Data.importedInspectionCache.getState (← getEnv) with
    | some ref => ref.get
    | none => pure {}
  let second ← names.mapM Informal.Data.analyzeDeclaration
  let render (statuses : Array Informal.Data.ProvedStatus) := statuses.map fun s => toString (repr s)
  return cached.size > 0 && render first == render second

end Verso.VersoBlueprintTests.ResidentBuild
