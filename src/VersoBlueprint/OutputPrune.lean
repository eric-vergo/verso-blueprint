/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

import Lean.Data.Json

/-!
Removing what an earlier build left in an output folder.

A site is written into a folder that may hold an earlier build of it. A page the current build
does not write (a chapter that was removed, a drawing of a graph that changed) would otherwise
stay at its address, with whatever marks it had then. So each build of a folder records the files
it wrote (`manifestName`), and the next build removes every file of that record that it did not
write again (`finish`). A file the generator never wrote is never on a record, so it is never
removed: files a person put into the folder stay.

A file counts as written by this build when it was modified after the build began (`begin`
writes a marker file and takes its modification time). Every file of a site is written whole on
every build, so a file left at an older time is one this build did not write.
-/

namespace Informal.OutputPrune

open Lean System

/-- The record of the files a build wrote into a folder, relative to it, inside that folder. -/
def manifestName : String := ".vbp-generated.json"

/-- The marker whose modification time is when a build of a folder began. -/
def markerName : String := ".vbp-build-started"

/-- The files below `dir`, relative to it with `/` separators, every symbolic link left as a
file (never followed); the record and the marker are left out. -/
partial def filesBelow (dir : FilePath) : IO (Array String) := do
  let rec go (sub : String) (acc : Array String) : IO (Array String) := do
    let here := if sub.isEmpty then dir else dir / sub
    let entries ← try here.readDir catch _ => return acc
    let mut acc := acc
    for e in entries.qsort (·.fileName < ·.fileName) do
      let rel := if sub.isEmpty then e.fileName else sub ++ "/" ++ e.fileName
      if rel == manifestName || rel == markerName then continue
      let md ← try e.path.symlinkMetadata catch _ => continue
      if md.type == .dir then acc ← go rel acc else acc := acc.push rel
    return acc
  go "" #[]

/-- Begin a build of `dir`: write the marker and give its modification time. -/
def begin (dir : FilePath) : IO IO.FS.SystemTime := do
  IO.FS.createDirAll dir
  let marker := dir / markerName
  IO.FS.writeFile marker ""
  return (← marker.metadata).modified

private def readRecord (dir : FilePath) : IO (Array String) := do
  try
    let json ← IO.ofExcept (Json.parse (← IO.FS.readFile (dir / manifestName)))
    IO.ofExcept (json.getObjValAs? (Array String) "files")
  catch _ => return #[]

/-- Whether `rel` is a path inside the folder: relative, without `..` or empty components. -/
private def inside (rel : String) : Bool :=
  !rel.isEmpty && !rel.startsWith "/" && (rel.splitOn "/").all fun p => p != ".." && p != ""

/-- Finish the build of `dir` that began at `start`: remove the files of the earlier build's
record that this build did not write, then the folders left empty by that, and record the files
this build wrote. Gives the paths removed, sorted. -/
def finish (dir : FilePath) (start : IO.FS.SystemTime) : IO (Array String) := do
  let earlier ← readRecord dir
  let mut written : Array String := #[]
  for rel in ← filesBelow dir do
    let md ← try (dir / rel).symlinkMetadata catch _ => continue
    if md.modified ≥ start then written := written.push rel
  let writtenSet : Std.HashSet String := written.foldl (·.insert ·) {}
  let mut removed := #[]
  for rel in earlier do
    unless inside rel do continue
    if writtenSet.contains rel then continue
    let path := dir / rel
    let some md ← (try some <$> path.symlinkMetadata catch _ => pure none) | continue
    if md.type == .dir then continue
    try IO.FS.removeFile path; removed := removed.push rel catch _ => pure ()
    -- the folders above it, while they are empty
    let mut parts := (rel.splitOn "/").dropLast
    while !parts.isEmpty do
      let folder := dir / "/".intercalate parts
      let empty ← try pure (← folder.readDir).isEmpty catch _ => pure false
      unless empty do break
      try IO.FS.removeDirAll folder catch _ => break
      parts := parts.dropLast
  IO.FS.writeFile (dir / manifestName)
    (Json.mkObj [("version", toJson (1 : Nat)), ("files", toJson written)]).compress
  try IO.FS.removeFile (dir / markerName) catch _ => pure ()
  return removed.qsort (· < ·)

end Informal.OutputPrune
