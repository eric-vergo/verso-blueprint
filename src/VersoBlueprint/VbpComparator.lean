/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

import Lake.Build.Module
import Lake.Build.Run
import Lake.Load.Workspace
import VersoBlueprint.Stats.Comparator

/-!
What `vbp` does with a project's Comparator challenges (`Informal.Stats.ComparatorLayout`):

* `checkLayout` checks the layout and, given the project's Lake workspace, that it can build
  every challenge's two modules (rule `K1`); `vbp build` checks both and stops when they do not
  hold, and `vbp comparator-check` reports the files' rules with an exit code for continuous
  integration (without loading the workspace, which could make Lake fetch missing packages);
* `buildComparatorChallenges` builds each challenge module before the generator runs, so that
  the statistics' headlines compare up-to-date challenges with their solutions. Nothing imports a
  challenge (it declares the same names as its solution), so building the generator's imports
  does not build it;
* `migrate` (`vbp comparator-migrate`) moves the single-challenge layout into a challenge folder.
-/

namespace VersoBlueprint.Vbp

open System
open Informal.Stats
open Informal.Stats.ComparatorLayout

/-- The layout's violations of the project at `root`, with rule `K1` checked against `ws`: a
module the workspace cannot find cannot be built by `lake comparator` either. -/
def checkLayout (root : FilePath) (ws? : Option Lake.Workspace) : IO Report := do
  let report ← check root
  let some ws := ws? | return report
  let mut violations := report.violations
  for config in report.challenges do
    for (mod, file) in [(config.challengeModule, challengeFileName),
        (config.solutionModule, solutionFileName)] do
      if (ws.findModule? mod).isNone then
        violations := violations.push {
          file := s!"{folderOf config.name}/{file}", rule := .lakeModule
          message := s!"the project's Lake workspace has no library that holds {mod}, so \
            neither `lake build` nor `lake comparator` can build it; add a library for the \
            challenges, in lakefile.toml `[[lean_lib]]` with `name = \"Comparator\"` and \
            `globs = [\"Comparator.+\"]` (in lakefile.lean `lean_lib Comparator where globs := \
            #[.submodules `Comparator]`)" }
  return { report with violations }

/-- Build every Comparator challenge module of the workspace rooted at the working directory.
Only errors are reported (a challenge's `sorry` warnings are expected); a challenge that fails to
build is reported and its headline says it was not built. -/
def buildComparatorChallenges (ws : Lake.Workspace) (challenges : Array ChallengeConfig) :
    IO Unit := do
  for config in challenges do
    let some mod := ws.findModule? config.challengeModule | continue
    try
      let _ ← ws.runBuild mod.leanArts.fetch { outLv := .error }
    catch err =>
      IO.eprintln s!"vbp build: the Comparator challenge {config.challengeModule} did not build: \
        {err}"

/-- `vbp comparator-check [--root <dir>]`: the layout's violations, one per line, and exit code 1
when there are any; 0 when the project follows the layout or has no Comparator files. -/
def comparatorCheck (root : FilePath) (ws? : Option Lake.Workspace) : IO UInt32 := do
  let report ← checkLayout root ws?
  if report.violations.isEmpty then
    if report.challenges.isEmpty then
      IO.println "vbp comparator-check: no Comparator challenge"
    else
      IO.println s!"vbp comparator-check: {report.challenges.size} \
        {if report.challenges.size == 1 then "challenge follows" else "challenges follow"} the \
        layout: {", ".intercalate (report.challenges.map (·.name)).toList}"
    return 0
  IO.eprintln s!"vbp comparator-check: {report.errorText}"
  return 1

/-! ## Moving the single-challenge layout -/

/-- One change of a migration. -/
inductive Change where
  /-- Create a folder. -/
  | mkdir (dir : String)
  /-- Move a file (`git mv` in a Git checkout). -/
  | move (src dst : String)
  /-- Write a file. -/
  | write (file text : String)
  /-- Replace every whole-word occurrence of `old` by `new` in `file` (`count` of them). -/
  | rename (file old new : String) (count : Nat)

/-- The change as a line a reader can run or check. -/
def Change.describe : Change → String
  | .mkdir dir => s!"mkdir -p {dir}"
  | .move src dst => s!"git mv {src} {dst}"
  | .write file _ => s!"write {file}"
  | .rename file old new count => s!"in {file}: {old} -> {new} ({count}×)"

/-- Whether `c` can continue a Lean name before a match (so the match is not a whole word). -/
private def continuesName (c : Char) : Bool := c.isAlphanum || c == '_' || c == '\'' || c == '.'

/-- `text` with every whole-word occurrence of `old` replaced by `new`, and how many there were.
A match is whole when the character before it cannot continue a Lean name and the one after it
is not a letter, digit, `_` or `'`. -/
def replaceWord (text old new : String) : String × Nat := Id.run do
  let parts := text.splitOn old
  match parts with
  | [] | [_] => return (text, 0)
  | first :: rest =>
    let mut out := first
    let mut count := 0
    for piece in rest do
      let before := out.toList.getLast?
      let after := piece.toList.head?
      let whole := !(before.any continuesName) &&
        !(after.any fun c => c.isAlphanum || c == '_' || c == '\'')
      out := out ++ (if whole then new else old) ++ piece
      if whole then count := count + 1
    return (out, count)

/-- The files of the project whose text may name the challenge's modules or files: its Lean
files, `lakefile.toml` and Markdown files of at most 4 MiB, outside Lake's and Git's folders,
build outputs and other Lake projects inside it, looking at most at `walkLimit` entries. -/
partial def textFiles (root : FilePath) : IO (Array String) := do
  let mut out := #[]
  let mut todo : Array (FilePath × String) := #[(root, "")]
  let mut seen := 0
  while h : todo.size > 0 do
    let (dir, rel) := todo[todo.size - 1]
    todo := todo.pop
    for name in ← namesIn dir do
      seen := seen + 1
      if seen > walkLimit then return out
      let relPath := if rel.isEmpty then name else s!"{rel}/{name}"
      match ← entryAt (dir / name) with
      | .dir =>
        let otherProject := (← entryAt (dir / name / "lakefile.toml")) != .missing ||
          (← entryAt (dir / name / "lakefile.lean")) != .missing
        if !skippedFolder name && !otherProject then todo := todo.push (dir / name, relPath)
      | .file size =>
        if size ≤ 4 * 1024 * 1024 && (name.endsWith ".lean" || name.endsWith ".md" ||
            name == "lakefile.toml") then
          out := out.push relPath
      | _ => pure ()
  return out.qsort (· < ·)

/-- The theorems a challenge file declares, as `theorem_names` lists them. -/
def declaredTheorems (text : String) : Array Lean.Name := theoremsOf (codeOnly text)

/-- The changes that move the single-challenge layout of the project at `root` into
`Comparator/<name>/`: the two files moved, the root's `comparator.json` moved and given the new
module names (or written, judging every theorem the challenge declares and permitting Lean's
standard three axioms, as the single-challenge layout did without the file), and the module
names and file paths replaced in the project's Lean files, `lakefile.toml` and Markdown files.
An error when the project does not have that layout or the folder exists. -/
def migrationPlan (root : FilePath) (name : String) : IO (Except String (Array Change)) := do
  unless isChallengeName name do
    return .error s!"{name} is not a challenge name: an ASCII capital letter, then ASCII letters \
      and digits, at most {nameCharLimit} characters"
  let legacyChallenge := s!"{folder}/{challengeFileName}"
  let legacySolution := s!"{folder}/{solutionFileName}"
  unless (← entryAt (root / legacyChallenge)) matches .file _ do
    return .error s!"{legacyChallenge} is not a file here: this project does not have the \
      single-challenge layout"
  unless (← entryAt (root / legacySolution)) matches .file _ do
    return .error s!"{legacySolution} is not a file here: this project does not have the \
      single-challenge layout"
  let target := folderOf name
  if (← entryAt (root / target)) != .missing then
    return .error s!"{target} exists already; choose another name with --name"
  let mut changes : Array Change := #[.mkdir target,
    .move legacyChallenge s!"{target}/{challengeFileName}",
    .move legacySolution s!"{target}/{solutionFileName}"]
  let configPath := s!"{target}/{comparatorConfigFile}"
  let newChallenge := challengeModuleOf name
  let newSolution := solutionModuleOf name
  match ← readLimited (root / comparatorConfigFile) configLimit with
  | .ok text =>
    changes := changes.push (.move comparatorConfigFile configPath)
    let json ← match Lean.Json.parse text with
      | .ok (.obj fields) => pure (Lean.Json.obj fields)
      | _ => return .error s!"{comparatorConfigFile} is not a JSON object; correct it first"
    let json := (json.setObjVal! "challenge_module" (.str newChallenge.toString)).setObjVal!
      "solution_module" (.str newSolution.toString)
    changes := changes.push (.write configPath (json.pretty ++ "\n"))
  | .error _ =>
    let challengeText ← match ← readLimited (root / legacyChallenge) leanFileLimit with
      | .ok text => pure text
      | .error why => return .error s!"{legacyChallenge}: {why}"
    let theorems := declaredTheorems challengeText
    if theorems.isEmpty then
      return .error s!"{legacyChallenge} declares no theorem; there is nothing to judge"
    let str := fun (s : String) => (Lean.Json.str s).compress
    let list := fun (items : Array String) => s!"[{", ".intercalate (items.toList.map str)}]"
    let text := s!"\{\n  \"challenge_module\": {str newChallenge.toString},\n  \
      \"solution_module\": {str newSolution.toString},\n  \
      \"theorem_names\": {list (theorems.map (·.toString))},\n  \
      \"permitted_axioms\": {list #["propext", "Quot.sound", "Classical.choice"]}\n}\n"
    changes := changes.push (.write configPath text)
  let renames := #[("Comparator.Challenge", newChallenge.toString),
    ("Comparator.Solution", newSolution.toString),
    (legacyChallenge, s!"{target}/{challengeFileName}"),
    (legacySolution, s!"{target}/{solutionFileName}")]
  for file in ← textFiles root do
    let some text ← (try some <$> IO.FS.readFile (root / file) catch _ => pure none) | continue
    for (old, new) in renames do
      let (_, count) := replaceWord text old new
      if count > 0 then changes := changes.push (.rename file old new count)
  return .ok changes

/-- Carry out `changes` in the project at `root`; moves use `git mv` in a Git checkout (so the
history follows the files), and a written file is added with `git add`; outside a checkout, a
rename. A rename of text is applied to the file's
place after the moves. -/
def applyChanges (root : FilePath) (changes : Array Change) : IO Unit := do
  let git := (← entryAt (root / ".git")) != .missing
  let moved : Array (String × String) := changes.filterMap fun
    | .move src dst => some (src, dst) | _ => none
  let placeOf := fun (file : String) => ((moved.find? (·.1 == file)).map (·.2)).getD file
  for change in changes do
    match change with
    | .mkdir dir => IO.FS.createDirAll (root / dir)
    | .move src dst =>
      if git then
        let out ← IO.Process.output { cmd := "git", args := #["mv", "--", src, dst], cwd := root }
        unless out.exitCode == 0 do
          throw (IO.userError s!"git mv {src} {dst} failed: {out.stderr.trimAscii}")
      else IO.FS.rename (root / src) (root / dst)
    | .write file text =>
      IO.FS.writeFile (root / file) text
      -- a new file of the challenge is added to Git with the moved ones
      if git then
        let out ← IO.Process.output { cmd := "git", args := #["add", "--", file], cwd := root }
        unless out.exitCode == 0 do
          throw (IO.userError s!"git add {file} failed: {out.stderr.trimAscii}")
    | .rename file old new _ =>
      let path := root / placeOf file
      let text ← IO.FS.readFile path
      IO.FS.writeFile path (replaceWord text old new).1

/-- The options of `vbp comparator-migrate`. -/
structure MigrateOptions where
  name : String := "Main"
  dryRun : Bool := false
  root : FilePath := "."

/-- Parse the options of `vbp comparator-migrate`. -/
def parseMigrateOptions : List String → MigrateOptions → Except String MigrateOptions
  | [], opts => .ok opts
  | "--name" :: n :: rest, opts => parseMigrateOptions rest { opts with name := n }
  | "--dry-run" :: rest, opts => parseMigrateOptions rest { opts with dryRun := true }
  | "--root" :: dir :: rest, opts => parseMigrateOptions rest { opts with root := dir }
  | arg :: _, _ => .error s!"unknown comparator-migrate option '{arg}'"

/-- `vbp comparator-migrate [--name <Name>] [--dry-run] [--root <dir>]`: move the
single-challenge layout into `Comparator/<Name>/` (default `Main`), printing every change; with
`--dry-run` only print them. -/
def migrate (args : List String) : IO UInt32 := do
  match parseMigrateOptions args {} with
  | .error e =>
    IO.eprintln e
    IO.eprintln "usage: lake exe vbp comparator-migrate [--name <Name>] [--dry-run] [--root <dir>]"
    return 2
  | .ok { name, dryRun, root } =>
    match ← migrationPlan root name with
    | .error e => IO.eprintln s!"vbp comparator-migrate: {e}"; return 1
    | .ok changes =>
      for c in changes do IO.println c.describe
      if dryRun then
        IO.println "(dry run: nothing changed)"
        return 0
      try applyChanges root changes
      catch e => IO.eprintln s!"vbp comparator-migrate: {e}"; return 1
      let report ← check root
      if report.violations.isEmpty then
        IO.println s!"done: {folderOf name} follows the layout"
        return 0
      IO.eprintln s!"moved, but the project does not follow the layout yet: {report.errorText}"
      return 1

end VersoBlueprint.Vbp
