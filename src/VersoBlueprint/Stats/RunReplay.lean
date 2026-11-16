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
module, `leanchecker` loads the module's imports and checks every constant the module adds again
in Lean's kernel. Each module is replayed in a process of its own, at a lower priority, a few
processes at a time, with a memory limit per process and a time limit for the whole replay; a
run that is stopped at a limit is reported as such, never as accepted.

## Which modules

The modules asked for (the project's modules in the environment the site is generated from, and
the modules a Comparator solution rests on), and every module of the project they import. A
module with no compiled file among the project's own cannot be replayed and is reported
(`Replay.Result.notCompiled`). Modules outside the project (Lean's library, dependencies) are
loaded as imports and not replayed.

## One module per process

`leanchecker` takes module name prefixes: it replays every module on its search path whose name
starts with one of its arguments, all of them at once in one process. Each of those modules
loads its own copy of its imports, and only the first copy of a compiled file can be mapped from
the disk, so the memory of one process grows with every module it replays (a project that
imports Mathlib needs about one more gigabyte per module). One module alone needs a few hundred
megabytes, whatever the size of its imports.

So every module is replayed by a process of its own, which names exactly that module. A module
named `A.B` is a prefix of its children `A.B.C`, and `leanchecker` would replay those too; the
process is therefore given a search path on which `A.B` is the only module of the project that
`leanchecker` finds by name (`buildShadow`): a directory in place of the project's that holds a
link to `A/B.olean` and symbolic links to everything else. `leanchecker` lists modules by the
real paths of the files it finds, and these lie outside every directory of its search path, so
it finds the children by import and does not count them as modules to replay. The checker is
run with `-v`, and the module it says it replayed is checked against the one asked for. Where
the directory cannot be made (no `ln` program), the module is named on the project's own
directory, and the checker replays it with its children.

`leanchecker` also looks through every directory of its search path once per process, which costs
seconds in a project that depends on Mathlib; the processes therefore run a few at a time
(`replayJobsVar`), and the search path is ordered with the largest directory first.

## Limits

The whole replay has a time limit (`replayLimitVar`). Every checker process has a memory limit
(`replayMemoryVar`): its memory is sampled while it runs (its physical footprint on macOS, its
anonymous and swapped memory on Linux, its resident size elsewhere), and a process over the
limit is stopped; the result then says so (`Replay.Outcome.overMemory`). By default the
processes run at once share a quarter of the machine's physical memory (`defaultMemoryLimit`).

## The record

A module is not replayed twice. Each module a checker accepted has its key written to a record
(`blueprint-kernel-replay.json` in the build directory that holds the project's compiled
modules, or the file `VERSO_BLUEPRINT_KERNEL_REPLAY_RECORD` names; empty for none); a later run
replays only the modules whose key is not there. The key of a module is the SHA-256 of: its
compiled files' contents; the keys of the project's modules it imports; the checker (path,
size, modification time, Lean version); and the sizes and modification times of every compiled
module outside the project on the search path. So a module counts as accepted only while its own
bytes, the bytes of everything in the project below it, the checker and the files of its
dependencies are what an accepted replay saw.

## Finding the checker

`VERSO_BLUEPRINT_KERNEL_CHECKER` names the program, or is `off`; otherwise `leanchecker` is
looked for in `LEAN_SYSROOT` (Lake sets it) and beside the running program (a generator run by
`lean --run`). No toolchain is asked for by name on the `PATH`. Without a checker the result
says so.
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

/-- The number of checker processes run at once. -/
def replayJobsVar : String := "VERSO_BLUEPRINT_KERNEL_REPLAY_JOBS"

/-- The memory limit of one checker process, in MiB; `0` for none. -/
def replayMemoryVar : String := "VERSO_BLUEPRINT_KERNEL_REPLAY_MEMORY_MB"

/-- The time limit when `replayLimitVar` sets none. -/
def defaultReplayLimit : Nat := 900

/-- The record's file name in the project's build directory. -/
def replayRecordFile : String := "blueprint-kernel-replay.json"

/-- The checker processes run at once on a machine with `cores` processors, when `replayJobsVar`
sets none: a quarter of them, at least one and at most four. -/
def defaultReplayJobs (cores : Nat) : Nat := max 1 (min 4 (cores / 4))

/-- The memory limit of one checker process, in bytes, when `replayMemoryVar` sets none: the
`jobs` processes run at once share a quarter of the machine's physical memory `physical`. -/
def defaultMemoryLimit (physical jobs : Nat) : Nat := physical / 4 / max 1 jobs

/-- The memory limit of one checker process when the machine's physical memory is not known:
2 GiB. -/
def fallbackMemoryLimit : Nat := 2 * 1024 * 1024 * 1024

/-- How a replay is run. -/
structure ReplayConfig where
  /-- The checker program; `none` when none was found. -/
  checker? : Option FilePath := none
  /-- The replay is switched off. -/
  off : Bool := false
  /-- The time limit of the whole replay, in seconds. -/
  limitSeconds : Nat := defaultReplayLimit
  /-- The number of checker processes run at once. -/
  jobs : Nat := 1
  /-- The memory limit of one checker process, in bytes; `none` for no limit. -/
  memoryLimit? : Option Nat := none
  /-- The directories of the project's own compiled modules. -/
  projectDirs : Array FilePath := #[]
  /-- The directories of the compiled modules of everything else, without the toolchain's own
  library (which is found from the checker). -/
  importDirs : Array FilePath := #[]
  /-- The file that records accepted modules. -/
  record? : Option FilePath := none
  /-- Print a line on the standard error for every module and for the end of the replay. -/
  progress : Bool := false
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

/-! ## The machine -/

/-- The standard output of a command that exits with status 0. -/
private def commandOutput? (cmd : String) (args : Array String) : IO (Option String) := do
  try
    let out ← IO.Process.output { cmd, args, stdin := .null }
    return if out.exitCode == 0 then some out.stdout else none
  catch _ => return none

/-- `cmd` from the first of `dirs` that has it, else `cmd` itself (looked for on the `PATH`). -/
private def systemTool (cmd : String) (dirs : List String) : IO String := do
  for dir in dirs do
    let path := FilePath.mk dir / cmd
    if ← path.pathExists then return path.toString
  return cmd

/-- The number on the line of `text` that starts with `key` (`/proc` style: `MemTotal:  8 kB`). -/
def procField? (text key : String) : Option Nat :=
  (text.splitOn "\n").findSome? fun line =>
    if line.startsWith key then
      let rest := (line.drop key.length).trimAscii.copy
      (rest.splitOn " ")[0]?.bind (·.toNat?)
    else none

/-- The machine's physical memory, in bytes, when it can be found. -/
def physicalMemory? : IO (Option Nat) := do
  if Platform.isOSX then
    let sysctl ← systemTool "sysctl" ["/usr/sbin", "/sbin"]
    return (← commandOutput? sysctl #["-n", "hw.memsize"]).bind (·.trimAscii.copy.toNat?)
  try
    return (procField? (← IO.FS.readFile "/proc/meminfo") "MemTotal:").map (· * 1024)
  catch _ => return none

/-- The machine's number of processors, when it can be found. -/
def processorCount? : IO (Option Nat) := do
  if Platform.isOSX then
    let sysctl ← systemTool "sysctl" ["/usr/sbin", "/sbin"]
    return (← commandOutput? sysctl #["-n", "hw.ncpu"]).bind (·.trimAscii.copy.toNat?)
  try
    let text ← IO.FS.readFile "/proc/cpuinfo"
    let n := ((text.splitOn "\n").filter (·.startsWith "processor")).length
    return if n == 0 then none else some n
  catch _ => return none

/-- The physical footprint in the output of macOS's `footprint` (`Footprint: 175 MB`), in
bytes. -/
def parseFootprint (text : String) : Option Nat := do
  let rest ← (text.splitOn "Footprint: ")[1]?
  let words := (((rest.splitOn "\n")[0]?).getD "").splitOn " " |>.filter (!·.isEmpty)
  let number ← words[0]?
  let scale : Nat ← match words[1]? with
    | some "B" => some 1
    | some "KB" => some 1024
    | some "MB" => some (1024 * 1024)
    | some "GB" => some (1024 * 1024 * 1024)
    | some "TB" => some (1024 * 1024 * 1024 * 1024)
    | _ => none
  match number.splitOn "." with
  | [whole] => return (← whole.toNat?) * scale
  | [whole, frac] =>
    return (← whole.toNat?) * scale + (← frac.toNat?) * scale / 10 ^ frac.length
  | _ => none

/-- The memory the process `pid` holds that the system cannot take back by dropping pages of
files, in bytes: its physical footprint on macOS (`footprint`), its anonymous resident and
swapped memory on Linux, else its resident size (`ps`). Pages of compiled modules mapped from
the disk are not counted where the system says which pages those are. `none` when it cannot be
read. -/
def processMemory? (pid : UInt32) : IO (Option Nat) := do
  if Platform.isOSX then
    let tool : FilePath := "/usr/bin/footprint"
    if ← tool.pathExists then
      if let some out ← commandOutput? tool.toString #[toString pid] then
        if let some bytes := parseFootprint out then return some bytes
  else
    let status ← try some <$> IO.FS.readFile s!"/proc/{pid}/status" catch _ => pure none
    if let some text := status then
      if let some anon := procField? text "RssAnon:" then
        return some ((anon + (procField? text "VmSwap:").getD 0) * 1024)
  let ps ← systemTool "ps" ["/bin", "/usr/bin"]
  let some out ← commandOutput? ps #["-o", "rss=", "-p", toString pid] | return none
  return out.trimAscii.copy.toNat?.map (· * 1024)

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
  let number (var : String) : IO (Option Nat) :=
    return (← IO.getEnv var).bind (·.trimAscii.copy.toNat?)
  let limitSeconds := (← number replayLimitVar).getD defaultReplayLimit
  let jobs ← match ← number replayJobsVar with
    | some n => pure (max 1 n)
    | none => pure (defaultReplayJobs ((← processorCount?).getD 1))
  let memoryLimit? ← match ← number replayMemoryVar with
    | some 0 => pure none
    | some mib => pure (some (mib * 1024 * 1024))
    | none =>
      let physical? ← physicalMemory?
      pure (some ((physical?.map (defaultMemoryLimit · jobs)).getD fallbackMemoryLimit))
  let record? ← match ← IO.getEnv replayRecordVar with
    | some path => pure (if path.trimAscii.isEmpty then none else some (FilePath.mk path))
    | none =>
      -- beside the project's compiled modules: `<package>/.lake/build`, above `lib/lean`
      pure <| (projectDirs[0]?.bind fun dir => dir.parent.bind (·.parent)).map (· / replayRecordFile)
  return { checker?, off, limitSeconds, jobs, memoryLimit?, projectDirs, importDirs, record?,
           progress := true }

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

/-- The modules of `modules` in an order where every module comes after the modules of
`modules` it imports (`imports`). -/
def importsFirst (modules : Array Name) (imports : NameMap (Array Name)) : Array Name := Id.run do
  let mut done : NameSet := {}
  let mut out := #[]
  for root in modules do
    -- an explicit stack: `(module, its imports were pushed)`
    let mut stack := #[(root, false)]
    while h : stack.size > 0 do
      let (m, expanded) := stack[stack.size - 1]
      stack := stack.pop
      if done.contains m then continue
      if expanded then
        done := done.insert m
        out := out.push m
      else
        stack := stack.push (m, true)
        for d in (imports.find? m).getD #[] do
          if modules.contains d && !done.contains d then stack := stack.push (d, false)
  return out

/-! ## A search path with one module of the project -/

/-- The string components of a module name. -/
private def nameParts (module : Name) : Array String :=
  module.components.toArray.filterMap fun
    | .str _ s => some s
    | _ => none

/-- Make symbolic links in `dir` to each of `targets` (`ln -s`). -/
private def linkInto (dir : FilePath) (targets : Array FilePath) : IO Bool := do
  let mut rest := targets
  while !rest.isEmpty do
    let chunk := rest.extract 0 256
    rest := rest.extract 256 rest.size
    let args := #["-s", "--"] ++ chunk.map (·.toString) ++ #[dir.toString]
    let some _ ← commandOutput? "ln" args | return false
  return true

/-- Fill the empty directory `shadow` so that, put on a search path in place of the directory
`lib` of compiled modules, it shows `leanchecker` the module `module` and no other module of
`lib`, while every module of `lib` can still be imported. On the path from `shadow` to the module
each directory is a real one; the module's compiled files are hard links (copies where a link
cannot be made); everything else is a symbolic link into `lib`. `leanchecker` names the modules
it finds by the real paths of their files, which lie outside every directory of its search path
for everything but the module itself. `false` when the directory could not be made. -/
def buildShadow (lib : FilePath) (module : Name) (shadow : FilePath) : IO Bool := do
  let parts := nameParts module
  if parts.isEmpty then return false
  let lib ← realOr lib
  let own := #["olean", "olean.server", "olean.private"].map (parts.back! ++ "." ++ ·)
  let mut src := lib
  let mut dst := shadow
  IO.FS.createDirAll dst
  for h : i in [0:parts.size] do
    let next := parts[i]
    let last := i + 1 == parts.size
    unless ← src.isDir do return false
    let mut links := #[]
    for entry in ← src.readDir do
      if !last && entry.fileName == next then continue
      if last && own.contains entry.fileName then
        let target := dst / entry.fileName
        try IO.FS.hardLink entry.path target
        catch _ => IO.FS.writeBinFile target (← IO.FS.readBinFile entry.path)
        continue
      links := links.push entry.path
    unless ← linkInto dst links do return false
    unless last do
      src := src / next
      dst := dst / next
      IO.FS.createDir dst
  return true

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
  | overMemory
  | stopped
  | notStarted (error : String)

/-- How often a checker process's memory is looked at, in milliseconds. -/
private def sampleMs : Nat := 500

/-- Run `cmd` with `args` and `env` at a lower priority (through `nice`, when there is one),
killing it when the clock passes `deadline` (`IO.monoMsNow`), when its memory passes
`memoryLimit?` (`processMemory?`) or when `stop` is set. The process stays in this process's
process group, so that whatever stops the generator's group (an interrupt at the terminal, the
program that started the generator) stops the checker too. -/
private def runLimited (cmd : String) (args : Array String)
    (env : Array (String × Option String)) (deadline : Nat) (memoryLimit? : Option Nat)
    (stop : IO.Ref Bool) : IO RunEnd := do
  if (← IO.monoMsNow) ≥ deadline then return .timedOut
  let spawn (cmd : String) (args : Array String) :=
    IO.Process.spawn { cmd, args, env, stdin := .null, stdout := .piped, stderr := .piped }
  let child ← try spawn "nice" (#["-n", "10", cmd] ++ args) catch _ =>
    try spawn cmd args catch e => return .notStarted (toString e)
  let stdout ← IO.asTask child.stdout.readToEnd Task.Priority.dedicated
  let stderr ← IO.asTask child.stderr.readToEnd Task.Priority.dedicated
  let finish (r : RunEnd) : IO RunEnd := do
    try child.kill catch _ => pure ()
    discard <| child.wait
    return r
  let mut nextSample := (← IO.monoMsNow) + sampleMs
  let mut code? : Option UInt32 := none
  while code?.isNone do
    code? ← child.tryWait
    if code?.isSome then break
    let now ← IO.monoMsNow
    if now ≥ deadline then return ← finish .timedOut
    if ← stop.get then return ← finish .stopped
    if let some limit := memoryLimit? then
      if now ≥ nextSample then
        if let some used ← processMemory? child.pid then
          if used > limit then return ← finish .overMemory
        nextSample := (← IO.monoMsNow) + sampleMs
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

/-- The line `leanchecker -v` prints for each module it replays. -/
private def replayingMarker : String := "replaying "

/-- The modules `leanchecker -v` says it replayed, from its standard output. -/
def parseReplayed (stdout : String) : Array Name :=
  (stdout.splitOn "\n").toArray.filterMap fun line =>
    if line.startsWith replayingMarker then
      let m := (line.drop replayingMarker.length).trimAscii.copy.toName
      if m.isAnonymous then none else some m
    else none

/-- How the replay of one module ended. -/
inductive ModuleEnd where
  /-- The checker accepted the module. -/
  | accepted
  /-- The checker rejected the module `module` (the one asked for, or a child replayed with it)
  and said `message`. -/
  | rejected (module : Name) (message : String)
  /-- The checker was stopped at the time limit. -/
  | timedOut
  /-- The checker was stopped over the memory limit. -/
  | overMemory
  /-- The checker was stopped because another module was rejected. -/
  | stopped
  /-- The checker could not run to a verdict. -/
  | failed (message : String)
deriving Repr, Inhabited, DecidableEq

/-- What the replay of one module did: how it ended, and the modules the checker said it
replayed. -/
structure ModuleRun where
  module : Name
  ending : ModuleEnd
  replayed : Array Name := #[]
deriving Repr, Inhabited

/-- What a replay of a build did: the result, and one entry per module that was replayed. -/
structure ReplayRun where
  result : Replay.Result
  runs : Array ModuleRun := #[]
deriving Repr, Inhabited

private def mib (bytes : Nat) : Nat := bytes / (1024 * 1024)

/-- Replay the modules `wanted` of a project, and the project's modules they import (the module
docstring says how), with an entry for each module that was replayed. -/
def replayBuildRuns (config : ReplayConfig) (wanted : Array Name) : IO ReplayRun := do
  let say (line : String) : IO Unit := do
    if config.progress then IO.eprintln s!"Kernel replay: {line}"
  -- the project's compiled modules, and everything else on the search path
  let mut own : NameMap (FilePath × FilePath) := {}
  for dir in config.projectDirs do
    for file in ← compiledFiles dir do
      if let some m := moduleOfFile? dir file then
        unless own.contains m do own := own.insert m (dir, file)
  -- the modules to cover: the wanted ones that are compiled, and the project's below them
  let mut imports : NameMap (Array Name) := {}
  let mut covered : NameSet := {}
  let mut notCompiled : Array Name := #[]
  let mut todo := wanted
  while h : todo.size > 0 do
    let m := todo[todo.size - 1]
    todo := todo.pop
    if covered.contains m then continue
    let some (_, olean) := own.find? m
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
  if config.off then return { result := base }
  let some checker := config.checker? | return { result := { base with outcome := .noChecker } }
  let checker ← realOr checker
  let some binDir := checker.parent | return { result := { base with outcome := .noChecker } }
  let sysroot := binDir.parent.getD binDir
  let version ← leanVersionOf (binDir / (if Platform.isWindows then "lean.exe" else "lean"))
  let base := { base with version }
  if modules.isEmpty then
    let message := "none of the site's modules has a compiled module among the project's own"
    return { result := { base with outcome := .failed, message := some message } }
  -- everything a module's acceptance rests on outside the project
  let mut counts : Array (FilePath × Nat) := #[]
  for dir in config.projectDirs do
    counts := counts.push (dir, (← compiledFiles dir).size)
  let mut outside := ""
  let sysLib := sysroot / "lib" / "lean"
  for dir in config.importDirs.push sysLib do
    let files ← compiledFiles dir
    counts := counts.push (dir, files.size)
    for file in files.qsort (·.toString < ·.toString) do
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
  let order := importsFirst modules imports
  let mut keys : NameMap String := {}
  for m in order do
    let deps := (imports.find? m).getD #[]
    let some (_, olean) := own.find? m | continue
    let mut contents := ""
    for part in ← moduleParts olean do
      contents := contents ++ (← hexOfFile part) ++ "\n"
    let below := "\n".intercalate ((deps.filterMap keys.find?).qsort (· < ·)).toList
    keys := keys.insert m
      (Sha256.hexOfString s!"replay 1\n{outsideKey}\n{m}\n{contents}{below}")
  let recorded ← readRecord config.record?
  let keyOf (m : Name) : String := (keys.find? m).getD ""
  let pending := order.filter fun m => !recorded.contains (keyOf m)
  let stillAccepted := (modules.filter (!pending.contains ·)).map keyOf
  if pending.isEmpty then
    say s!"every one of the {modules.size} modules was accepted before"
    return { result := { base with outcome := .accepted } }
  -- the search path: the largest directory first, as the checker tries them in turn per file
  let dirs := (counts.qsort (·.2 > ·.2)).map (·.1)
  let jobs := max 1 (min config.jobs pending.size)
  let limitText := match config.memoryLimit? with
    | some limit => s!", at most {mib limit} MiB each"
    | none => ""
  say s!"{pending.size} of {modules.size} modules to replay with {checker.fileName.getD "the \
    checker"}, {jobs} at a time{limitText}"
  let deadline := (← IO.monoMsNow) + config.limitSeconds * 1000
  let work ← IO.FS.createTempDir
  let next ← IO.mkRef 0
  let stop ← IO.mkRef false
  let runs ← IO.mkRef (#[] : Array ModuleRun)
  let replayOne (slot : Nat) (m : Name) : IO ModuleRun := do
    let some (lib, _) := own.find? m | return { module := m, ending := .failed "not compiled" }
    let shadow := work / s!"path{slot}"
    if ← shadow.pathExists then IO.FS.removeDirAll shadow
    let isolated ← try buildShadow lib m shadow catch _ => pure false
    let path := dirs.map fun d => if isolated && d == lib then shadow else d
    let env : Array (String × Option String) := #[
      ("LEAN_PATH", some (SearchPath.toString path.toList)),
      ("LEAN_SYSROOT", some sysroot.toString)]
    let ending ← runLimited checker.toString #["-v", m.toString] env deadline
      config.memoryLimit? stop
    if ← shadow.pathExists then try IO.FS.removeDirAll shadow catch _ => pure ()
    match ending with
    | .notStarted error => return { module := m, ending := .failed (clip error) }
    | .timedOut => return { module := m, ending := .timedOut }
    | .overMemory => return { module := m, ending := .overMemory }
    | .stopped => return { module := m, ending := .stopped }
    | .exited code stdout stderr =>
      let replayed := parseReplayed stdout
      if code == 0 then
        if replayed.contains m then return { module := m, ending := .accepted, replayed }
        let message := s!"the checker did not report replaying {m}"
        return { module := m, ending := .failed message, replayed }
      let (module?, message) := parseRejection stderr
      match module? with
      | some r =>
        if covered.contains r then return { module := m, ending := .rejected r message, replayed }
        let message := s!"it stopped on module {r}, which is not a module of this site: {message}"
        return { module := m, ending := .failed message, replayed }
      | none => return { module := m, ending := .failed message, replayed }
  let worker (slot : Nat) : IO Unit := do
    repeat
      if ← stop.get then break
      let i ← next.modifyGet fun i => (i, i + 1)
      let some m := pending[i]? | break
      let run ← replayOne slot m
      if run.ending matches .rejected .. then stop.set true
      let done ← runs.modifyGet fun rs => (rs.size + 1, rs.push run)
      match run.ending with
      | .accepted => say s!"accepted {m} ({done} of {pending.size})"
      | .rejected r _ => say s!"rejected {r}"
      | .overMemory =>
        say s!"stopped over the memory limit in {m}"
      | .failed message => say s!"could not replay {m}: {message}"
      | _ => pure ()
  let tasks ← (List.range jobs).toArray.mapM fun slot =>
    IO.asTask (worker slot) Task.Priority.dedicated
  for t in tasks do
    discard <| IO.wait t
  try IO.FS.removeDirAll work catch _ => pure ()
  let runs ← runs.get
  let acceptedNow := (runs.filter (·.ending == .accepted)).map (keyOf ·.module)
  writeRecord config.record? (stillAccepted ++ acceptedNow)
  let ordered := order.filterMap fun m => runs.find? (·.module == m)
  let result : Replay.Result ←
    if let some (r, message) := ordered.findSome? fun run =>
        match run.ending with | .rejected r message => some (r, message) | _ => none then
      pure { base with outcome := .rejected, rejectedModule := some r, message := some message }
    else if let some run := ordered.find? (·.ending == .overMemory) then
      pure { base with outcome := .overMemory, stoppedModule := some run.module,
                       memoryLimit := config.memoryLimit? }
    else if ordered.size < pending.size || ordered.any (·.ending == .timedOut) then
      pure { base with outcome := .timedOut, limitSeconds := some config.limitSeconds }
    else if let some (m, message) := ordered.findSome? fun run =>
        match run.ending with | .failed message => some (run.module, message) | _ => none then
      pure { base with outcome := .failed, message := some s!"module {m}: {message}" }
    else
      pure { base with outcome := .accepted }
  say (match result.outcome with
    | .accepted => s!"accepted, {modules.size} modules"
    | .rejected => s!"rejected ({(result.rejectedModule.map toString).getD "a module"})"
    | _ => result.whyNot)
  return { result, runs := ordered }

/-- Replay the modules `wanted` of a project, and the project's modules they import
(`replayBuildRuns`). -/
def replayBuild (config : ReplayConfig) (wanted : Array Name) : IO Replay.Result :=
  return (← replayBuildRuns config wanted).result

end Informal.Stats
