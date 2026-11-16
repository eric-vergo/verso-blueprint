/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

import Lean.Util.Path
import Lean.Environment
import VersoBlueprint.Lib.Sha256
import VersoBlueprint.Replay

/-!
Running the kernel replay of a build (`Informal.Replay`).

`replayBuild` runs the toolchain's `leanchecker` on the project's own compiled modules: for each
module named on its command line, `leanchecker` loads the module's imports and checks every
constant the module adds again in Lean's kernel. It runs in a process of its own, at a lower
priority, with a time limit; a run that is stopped at the limit is reported as such, never as
accepted.

## Which modules

The modules asked for (the project's modules in the environment the site is generated from, and
the modules a Comparator solution rests on), and every module of the project they import. A
module with no compiled file among the project's own cannot be replayed and is reported
(`Replay.Result.notCompiled`). Modules outside the project (Lean's library, dependencies) are
loaded as imports and not replayed.

`leanchecker` takes module name prefixes and looks for each one in every directory of the search
path, which costs seconds per prefix in a project that depends on Mathlib. So the modules are
named by as few prefixes as cover them and nothing else (`targetsFor`), and the search path is
ordered with the largest directory first.

## The record

A module is not replayed twice. After an accepted run each module's key is written to a record
(`blueprint-kernel-replay.json` in the project's build directory, or the file
`VERSO_BLUEPRINT_KERNEL_REPLAY_RECORD` names); a later run replays only the modules whose key is
not there. The key of a module is the SHA-256 of: its compiled files' contents; the keys of the
project's modules it imports; the checker (path, size, modification time, Lean version); and the
sizes and modification times of every compiled module outside the project on the search path.
So a module counts as accepted only while its own bytes, the bytes of everything in the project
below it, the checker and the files of its dependencies are what an accepted replay saw.

## Finding the checker

`VERSO_BLUEPRINT_KERNEL_CHECKER` names the program, or is `off`; otherwise `leanchecker` is
looked for in `LEAN_SYSROOT` (Lake sets it) and beside the running program (a generator run by
`lean --run`). No toolchain is asked for by name on the `PATH`. Without a checker the result
says so. `VERSO_BLUEPRINT_KERNEL_REPLAY_SECONDS` sets the time limit.
-/

namespace Informal.Stats

open Lean System
open Informal.Replay

/-- Names the checker program, or is `off`. -/
def replayCheckerVar : String := "VERSO_BLUEPRINT_KERNEL_CHECKER"

/-- The time limit of a replay, in seconds. -/
def replayLimitVar : String := "VERSO_BLUEPRINT_KERNEL_REPLAY_SECONDS"

/-- The file that records accepted modules; empty for none. -/
def replayRecordVar : String := "VERSO_BLUEPRINT_KERNEL_REPLAY_RECORD"

/-- The time limit when `replayLimitVar` sets none. -/
def defaultReplayLimit : Nat := 900

/-- The record's file name in the project's build directory. -/
def replayRecordFile : String := "blueprint-kernel-replay.json"

/-- How a replay is run. -/
structure ReplayConfig where
  /-- The checker program; `none` when none was found. -/
  checker? : Option FilePath := none
  /-- The replay is switched off. -/
  off : Bool := false
  limitSeconds : Nat := defaultReplayLimit
  /-- The directories of the project's own compiled modules. -/
  projectDirs : Array FilePath := #[]
  /-- The directories of the compiled modules of everything else, without the toolchain's own
  library (which is found from the checker). -/
  importDirs : Array FilePath := #[]
  /-- The file that records accepted modules. -/
  record? : Option FilePath := none
deriving Inhabited, Repr

private def checkerExe : String :=
  if Platform.isWindows then "leanchecker.exe" else "leanchecker"

/-- The toolchain's `leanchecker`: in `LEAN_SYSROOT`, else beside the running program. -/
def findChecker? : IO (Option FilePath) := do
  let mut candidates : Array FilePath := #[]
  if let some root ← IO.getEnv "LEAN_SYSROOT" then
    candidates := candidates.push (FilePath.mk root / "bin" / checkerExe)
  if let some dir := (← IO.appPath).parent then
    candidates := candidates.push (dir / checkerExe)
  for c in candidates do
    if ← c.pathExists then return some c
  return none

private def realOr (path : FilePath) : IO FilePath :=
  try IO.FS.realPath path catch _ => pure path

private def dedupDirs (dirs : Array FilePath) : IO (Array FilePath) := do
  let mut out := #[]
  for dir in dirs do
    unless ← dir.isDir do continue
    let real ← realOr dir
    unless out.contains real do out := out.push real
  return out

/-- The configuration for the project at `root`, whose own compiled modules are in
`libraryDirs` (relative to `root`), from the environment variables above. The other compiled
modules are looked for in the project's Lake packages and in `LEAN_PATH`. -/
def ReplayConfig.fromEnv (root : FilePath) (libraryDirs : Array String) : IO ReplayConfig := do
  let projectDirs ← dedupDirs (libraryDirs.map fun dir : String => root / dir)
  let mut others : Array FilePath := #[root / ".lake" / "build" / "lib" / "lean"]
  let packages := root / ".lake" / "packages"
  if ← packages.isDir then
    for entry in (← packages.readDir).qsort (·.fileName < ·.fileName) do
      others := others.push (entry.path / ".lake" / "build" / "lib" / "lean")
  if let some path ← IO.getEnv "LEAN_PATH" then
    others := others ++ (SearchPath.parse path).toArray
  let importDirs := (← dedupDirs others).filter (!projectDirs.contains ·)
  let choice := ((← IO.getEnv replayCheckerVar).map (·.trimAscii.copy)).filter (!·.isEmpty)
  let off := choice == some "off"
  let checker? ← match choice with
    | some path => if off then pure none else
        pure (if ← (FilePath.mk path).pathExists then some (FilePath.mk path) else none)
    | none => findChecker?
  let limitSeconds := ((← IO.getEnv replayLimitVar).bind (·.trimAscii.copy.toNat?)).getD
    defaultReplayLimit
  let record? ← match ← IO.getEnv replayRecordVar with
    | some path => pure (if path.trimAscii.isEmpty then none else some (FilePath.mk path))
    | none => pure (some (root / ".lake" / "build" / replayRecordFile))
  return { checker?, off, limitSeconds, projectDirs, importDirs, record? }

/-! ## Modules on disk -/

/-- The module of a compiled file below `dir`: `dir/A/B.olean` is `A.B`. -/
private def moduleOfFile? (dir file : FilePath) : Option Name := do
  let dir := dir.toString
  let file := file.toString
  guard (file.startsWith dir && file.endsWith ".olean")
  let rel := ((file.drop dir.length).copy.dropEnd ".olean".length).copy
  let parts := (rel.splitOn FilePath.pathSeparator.toString).filter (!·.isEmpty)
  guard !parts.isEmpty
  return parts.foldl Name.str .anonymous

/-- The compiled files below `dir` (`.olean`, and the `.olean.server` and `.olean.private` parts
the module system writes). -/
private def compiledFiles (dir : FilePath) : IO (Array FilePath) := do
  let all ← try dir.walkDir catch _ => pure #[]
  return all.filter fun f =>
    let s := f.toString
    s.endsWith ".olean" || s.endsWith ".olean.server" || s.endsWith ".olean.private"

/-- The parts of a compiled module, given its `.olean`. -/
private def moduleParts (olean : FilePath) : IO (Array FilePath) := do
  let mut parts := #[olean]
  for ext in ["server", "private"] do
    let part := olean.addExtension ext
    if ← part.pathExists then parts := parts.push part
  return parts

private def hexOfFile (file : FilePath) : IO String :=
  return Sha256.hex (← IO.FS.readBinFile file)

/-- The modules a compiled module imports. The file stays mapped for the rest of the process. -/
private def importsOf (olean : FilePath) : IO (Array Name) := do
  let (data, _) ← readModuleData olean
  return data.imports.map (·.module)

/-! ## Targets -/

/-- Module name prefixes for `leanchecker` that cover `todo`: for each module the shortest
prefix of its name under which every module of `all` is in `allowed`, or the module's own name
when there is none. `leanchecker` replays every module on its search path whose name starts
with one of its arguments, so a prefix must not reach outside `allowed`. -/
def targetsFor (all : Array Name) (allowed : NameSet) (todo : Array Name) : Array Name := Id.run do
  -- every prefix of a module that must not be replayed
  let mut barred : NameSet := {}
  for m in all do
    unless allowed.contains m do
      let mut p := m
      while !p.isAnonymous do
        barred := barred.insert p
        p := p.getPrefix
  let mut targets : Array Name := #[]
  for m in todo.qsort (·.toString < ·.toString) do
    if targets.any (·.isPrefixOf m) then continue
    let prefixes := Id.run do
      let mut ps := #[]
      let mut p := m
      while !p.isAnonymous do
        ps := ps.push p
        p := p.getPrefix
      return ps.reverse
    targets := targets.push ((prefixes.find? (!barred.contains ·)).getD m)
  return targets

/-! ## The record -/

private def readRecord (file? : Option FilePath) : IO (Array String) := do
  let some file := file? | return #[]
  try
    let json ← IO.ofExcept (Json.parse (← IO.FS.readFile file))
    IO.ofExcept (json.getObjValAs? (Array String) "accepted")
  catch _ => return #[]

private def writeRecord (file? : Option FilePath) (keys : Array String) : IO Unit := do
  let some file := file? | return
  try
    if let some dir := file.parent then IO.FS.createDirAll dir
    let tmp := file.addExtension s!"tmp{← IO.monoNanosNow}"
    IO.FS.writeFile tmp (Json.mkObj [("version", 1),
      ("accepted", toJson (keys.qsort (· < ·)))]).compress
    IO.FS.rename tmp file
  catch _ => return

/-! ## Running the checker -/

/-- The Lean version a toolchain's `lean --version` prints (`4.35.0`). -/
def leanVersionOf (lean : FilePath) : IO (Option String) := do
  try
    let out ← IO.Process.output { cmd := lean.toString, args := #["--version"] }
    let text := out.stdout
    let some rest := (text.splitOn "version ")[1]? | return none
    let version := (rest.takeWhile fun c => c != ',' && c != ')' && !c.isWhitespace).copy
    return if version.isEmpty then none else some version
  catch _ => return none

/-- What a run of the checker gave. -/
private inductive RunEnd where
  | exited (code : UInt32) (stdout stderr : String)
  | timedOut
  | notStarted (error : String)

/-- Run `cmd` with `args` and `env` at a lower priority (through `nice`, when there is one),
killing it and what it started after `limitSeconds`. -/
private def runLimited (cmd : String) (args : Array String)
    (env : Array (String × Option String)) (limitSeconds : Nat) : IO RunEnd := do
  let spawn (cmd : String) (args : Array String) :=
    IO.Process.spawn { cmd, args, env, stdin := .null, stdout := .piped, stderr := .piped,
                       setsid := true }
  let child ← try spawn "nice" (#["-n", "10", cmd] ++ args) catch _ =>
    try spawn cmd args catch e => return .notStarted (toString e)
  let stdout ← IO.asTask child.stdout.readToEnd Task.Priority.dedicated
  let stderr ← IO.asTask child.stderr.readToEnd Task.Priority.dedicated
  let deadline := (← IO.monoMsNow) + limitSeconds * 1000
  let mut code? : Option UInt32 := none
  while code?.isNone do
    code? ← child.tryWait
    if code?.isSome then break
    if (← IO.monoMsNow) ≥ deadline then
      try child.kill catch _ => pure ()
      discard <| child.wait
      return .timedOut
    IO.sleep 50
  let text (t : Task (Except IO.Error String)) : String :=
    match t.get with
    | .ok s => s
    | .error _ => ""
  return .exited (code?.getD 1) (text stdout) (text stderr)

/-- The longest message a result keeps. -/
private def messageLimit : Nat := 2000

private def clip (text : String) : String :=
  let text := text.trimAscii.copy
  if text.length ≤ messageLimit then text else (text.take messageLimit).copy ++ " …"

/-- The line `leanchecker` prints before the error of a module it rejects. -/
private def problemMarker : String := "leanchecker found a problem in "

/-- The module `leanchecker` rejected and what it said, from its error output. -/
def parseRejection (stderr : String) : Option Name × String :=
  let lines := stderr.splitOn "\n"
  let module := lines.findSome? fun line =>
    if line.startsWith problemMarker then
      some (line.drop problemMarker.length).trimAscii.copy.toName
    else none
  let rest := lines.filter (!·.startsWith problemMarker)
  let text := "\n".intercalate rest
  let text := if text.trimAscii.copy.startsWith "uncaught exception: " then
      (text.trimAscii.copy.drop "uncaught exception: ".length).copy else text
  (module.filter (!·.isAnonymous), clip text)

/-- Replay the modules `wanted` of a project, and the project's modules they import
(the module docstring says how). -/
def replayBuild (config : ReplayConfig) (wanted : Array Name) : IO Replay.Result := do
  -- the project's compiled modules, and everything else on the search path
  let mut own : NameMap FilePath := {}
  for dir in config.projectDirs do
    for file in ← compiledFiles dir do
      if let some m := moduleOfFile? dir file then
        unless own.contains m do own := own.insert m file
  -- the modules to cover: the wanted ones that are compiled, and the project's below them
  let mut imports : NameMap (Array Name) := {}
  let mut covered : NameSet := {}
  let mut notCompiled : Array Name := #[]
  let mut todo := wanted
  while h : todo.size > 0 do
    let m := todo[todo.size - 1]
    todo := todo.pop
    if covered.contains m then continue
    let some olean := own.find? m
      | if wanted.contains m && !notCompiled.contains m then notCompiled := notCompiled.push m
        continue
    covered := covered.insert m
    let deps ← try importsOf olean catch _ => pure #[]
    let deps := deps.filter own.contains
    imports := imports.insert m deps
    todo := todo ++ deps
  let modules := covered.toArray.qsort (·.toString < ·.toString)
  let base : Replay.Result :=
    { outcome := .off, modules, notCompiled := notCompiled.qsort (·.toString < ·.toString) }
  if config.off then return base
  let some checker := config.checker? | return { base with outcome := .noChecker }
  let checker ← realOr checker
  let some binDir := checker.parent | return { base with outcome := .noChecker }
  let sysroot := binDir.parent.getD binDir
  let version ← leanVersionOf (binDir / (if Platform.isWindows then "lean.exe" else "lean"))
  let base := { base with version }
  if modules.isEmpty then
    let message := "none of the site's modules has a compiled module among the project's own"
    return { base with outcome := .failed, message := some message }
  -- everything a module's acceptance rests on outside the project
  let mut all : Array Name := own.toArray.map (·.1)
  let mut counts : Array (FilePath × Nat) := config.projectDirs.map fun d => (d, 0)
  let mut outside := ""
  let sysLib := sysroot / "lib" / "lean"
  for dir in config.importDirs.push sysLib do
    let files ← compiledFiles dir
    counts := counts.push (dir, files.size)
    for file in files.qsort (·.toString < ·.toString) do
      if let some m := moduleOfFile? dir file then all := all.push m
      let (size, modified) ← try
          let md ← file.metadata
          pure (md.byteSize, s!"{md.modified.sec}.{md.modified.nsec}")
        catch _ => pure (0, "")
      outside := outside ++ s!"{file} {size} {modified}\n"
  let checkerId ← try
      let md ← checker.metadata
      pure s!"{checker} {md.byteSize} {md.modified.sec}.{md.modified.nsec} {version}"
    catch _ => pure s!"{checker} {version}"
  let outsideKey := Sha256.hexOfString (checkerId ++ "\n" ++ outside)
  -- the modules' keys, imports first
  let mut keys : NameMap String := {}
  let mut stack := modules.reverse
  while h : stack.size > 0 do
    let m := stack[stack.size - 1]
    if keys.contains m then stack := stack.pop; continue
    let deps := (imports.find? m).getD #[]
    let pending := deps.filter (!keys.contains ·)
    if !pending.isEmpty then stack := stack ++ pending; continue
    stack := stack.pop
    let some olean := own.find? m | continue
    let mut contents := ""
    for part in ← moduleParts olean do
      contents := contents ++ (← hexOfFile part) ++ "\n"
    let below := "\n".intercalate
      ((deps.filterMap keys.find?).qsort (· < ·)).toList
    keys := keys.insert m
      (Sha256.hexOfString s!"replay 1\n{outsideKey}\n{m}\n{contents}{below}")
  let recorded ← readRecord config.record?
  let keyOf (m : Name) : String := (keys.find? m).getD ""
  let pending := modules.filter fun m => !recorded.contains (keyOf m)
  if pending.isEmpty then return { base with outcome := .accepted }
  let targets := targetsFor all covered pending
  -- the largest directory first: the checker tries the directories in turn for every file
  let dirs := (counts.qsort (·.2 > ·.2)).map (·.1)
  let env : Array (String × Option String) := #[
    ("LEAN_PATH", some (SearchPath.toString dirs.toList)),
    ("LEAN_SYSROOT", some sysroot.toString)]
  let stillAccepted := (modules.filter (!pending.contains ·)).map keyOf
  match ← runLimited checker.toString (targets.map (·.toString)) env config.limitSeconds with
  | .notStarted error =>
    return { base with outcome := .failed, message := some (clip error) }
  | .timedOut =>
    writeRecord config.record? stillAccepted
    return { base with outcome := .timedOut, limitSeconds := some config.limitSeconds }
  | .exited code _ stderr =>
    if code == 0 then
      writeRecord config.record? (modules.map keyOf)
      return { base with outcome := .accepted }
    writeRecord config.record? stillAccepted
    let (module?, message) := parseRejection stderr
    match module? with
    | some m =>
      if covered.contains m then
        return { base with outcome := .rejected, rejectedModule := some m, message := some message }
      else
        let message := s!"it stopped on module {m}, which is not a module of this site: {message}"
        return { base with outcome := .failed, message := some message }
    | none => return { base with outcome := .failed, message := some message }

end Informal.Stats
