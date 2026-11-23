/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

import Lean.Util.Path
import Lean.Environment
import LeanExport.Basic
import VersoBlueprint.Axioms
import VersoBlueprint.Lib.Sha256
import VersoBlueprint.Replay

/-!
Running the kernel replay of a build (`Informal.Replay`).

A replay checks the Lean declarations a site reports on, and everything they depend on, again
in Lean's kernel. It has two halves.

The first half (`prepareExport`, after `loadModules`) runs in a worker process:

1. It loads the compiled modules that hold the declarations into an environment, by the search
   path of the build.
2. It takes each declaration from that environment and walks the terms of everything it depends
   on, which gives the axioms under it (`restingAxioms`).
3. It writes the declarations and every constant they depend on to a file, with the exporter
   of the Lean toolchain (`LeanExport`). The dependencies are followed wherever they lead: into
   the project's other modules, its dependencies and Lean's own library.

Only declarations that rest on Lean's standard three axioms at most are exported: both checkers
decline a whole export that uses another axiom (`sorryAx` among them), so a declaration that
rests on one is left out, with its axioms (`Prepared.axioms`), and the others are still checked.

The second half (`checkExport`) runs the two checkers that ship with the Lean toolchain, first
`con-leche` and then `con-ron`, each as `--verified --jobs=N FILE`, at a lower priority, with a
memory limit and under one time limit for the whole replay. Each adds every declaration of the
file to an empty environment. Its answer is read from its exit status first and its words second
(`parseAnswer`): an acceptance needs status 0, its line `accepted N declarations` and `N` at
least the declaration records the generator counts in the file (`exportCensus`), which must also
be exactly the file the worker wrote and end with a complete line; both checkers accept an empty
or cut-off file with status 0. The replay accepts only when both checkers accept
(`combineRuns`); a run stopped at a limit is reported as such, never as accepted.

## The worker

A generator usually has the project's compiled modules loaded already (a generator that
`lean --run` runs has imported them), and a second copy of a compiled module in one process is
not mapped from the disk but read into memory. So the first half runs in a process of its own,
the worker: a compiled program whose `main` answers `replayWorkerFlag` with `replayWorkerMain`
(`Informal.Stats.Comparator`). `vbp` is one, and names itself to the generators it runs
(`replayWorkerProgramFlag`); a compiled generator is its own (`registerSelfAsReplayWorker`); a
generator that another program starts as a library is named with what comes before its own
arguments by `replayWorkerVar`. The
worker is given the request as a file and leaves its reply in another (`runWorker`); it is run
under the replay's time limit and memory limit, like the checker. Without a worker there is no
replay.

## One environment

Everything a positive statement of the site rests on is taken from the one environment the
worker loads: the declaration that is exported and checked, the axioms under it, and (in
`ReplayRequest.run`) the comparison of a judged theorem with its challenge. The
checker is given no module name and reads no compiled module: it reads the export. So the
constants it checks are the constants of the loaded environment, and no second lookup of a module
by its name can find another file.

The loaded environment itself is found by name, on the search path. A module whose compiled file
exists in more than one directory of the search path could be either file, depending on the order
of the path, so the replay then stops without a verdict and names the module and the
directories (`duplicateModule?`). Directories are compared by their real paths, and two files
that are one file by their real path count once. A name is looked up as the file system looks it
up: on a file system that ignores case, two files whose names differ only by case are two
candidates for one module and stop the replay as well.

## Limits

The whole replay has a time limit (`replayLimitVar`), the worker and the checker each a memory
limit (`replayMemoryVar`: a process's memory is sampled while it runs, as its physical footprint
on macOS, its anonymous and swapped memory on Linux, its resident size elsewhere), and the
export a size limit (`replayExportVar`). By default a process may use a quarter of the
machine's physical memory (`defaultMemoryLimit`). The limits are enforced by polling: a process's
memory is read every `sampleMs` from its process id, so a peak between two readings is not seen,
and a reading that cannot be made is skipped; a process over a limit is stopped (the immediate
child; a checker starts no process of its own). What a process writes is kept up to
`outputLimit` bytes per stream, the rest read and dropped.

## The record

An export is not checked twice. The key of an accepted export is written to a record: the file
`VERSO_BLUEPRINT_KERNEL_REPLAY_RECORD` names (empty for none), or else
`verso-blueprint/kernel-replay-checkers.json` in the user's cache directory
(`defaultRecordFile?`). The
record is never looked for inside the project by default: a record says that the checkers
accepted something, and a project must not be able to bring such a statement with it. A record
named by the environment variable is where that variable says; the environment is the user's.
The key is the SHA-256 of the export's contents (`ExportKey`) and of its count of declaration
records, together with both checkers (each program's name, the SHA-256 of its file and its Lean
version). The export is written and hashed on every run, from the environment in memory, so an
accepted key stands for exactly the constants that were checked, by exactly those programs. Two
generators that write the record at once can lose an entry, which only means a second check:
the record is read again and merged just before it is replaced.

## Finding the checkers

`VERSO_BLUEPRINT_CON_LECHE` and `VERSO_BLUEPRINT_CON_RON` name the programs; otherwise each is
looked for in `LEAN_SYSROOT`'s `bin` (Lake sets it) and beside the running program (a generator
run by `lean --run`). No toolchain is asked for by name on the `PATH`.
`VERSO_BLUEPRINT_KERNEL_CHECKER=off` switches the replay off; any other value of that variable
gives no verdict and says why. A toolchain that ships neither checker (Lean before 4.35) gives no
verdict either, and the result names the Lean version.
-/

namespace Informal.Stats

open Lean System
open Informal.Replay

/-- `off` switches the replay off. -/
def replayCheckerVar : String := "VERSO_BLUEPRINT_KERNEL_CHECKER"

/-- Names the `con-leche` program. -/
def conLecheVar : String := "VERSO_BLUEPRINT_CON_LECHE"

/-- Names the `con-ron` program. -/
def conRonVar : String := "VERSO_BLUEPRINT_CON_RON"

/-- The time limit of a replay, in seconds. -/
def replayLimitVar : String := "VERSO_BLUEPRINT_KERNEL_REPLAY_SECONDS"

/-- The file that records accepted exports; empty for none. -/
def replayRecordVar : String := "VERSO_BLUEPRINT_KERNEL_REPLAY_RECORD"

/-- The memory limit of the checker process, in MiB; `0` for none. -/
def replayMemoryVar : String := "VERSO_BLUEPRINT_KERNEL_REPLAY_MEMORY_MB"

/-- The size limit of the export, in MiB; `0` for none. -/
def replayExportVar : String := "VERSO_BLUEPRINT_KERNEL_REPLAY_EXPORT_MB"

/-- The worker's program and the arguments that come before `replayWorkerFlag`, one per line:
for a generator that is started through another program (a launcher that loads it as a
library), which is then not its own worker by its program's path alone. -/
def replayWorkerVar : String := "VERSO_BLUEPRINT_KERNEL_REPLAY_WORKER"

/-- The time limit when `replayLimitVar` sets none. -/
def defaultReplayLimit : Nat := 900

/-- The size limit of the export when `replayExportVar` sets none: 4 GiB. -/
def defaultExportLimit : Nat := 4 * 1024 * 1024 * 1024

/-- The record's file in the user's cache directory, from what the environment says: on macOS
`Library/Caches` in `home`, on Windows `localAppData`, elsewhere `xdgCache` or `.cache` in
`home`; then `verso-blueprint/kernel-replay-checkers.json`. `none` when the directory is not
known. -/
def recordFileIn (home xdgCache localAppData : Option String) (macOS windows : Bool) :
    Option FilePath :=
  let present (value : Option String) : Option FilePath :=
    (value.filter (!·.trimAscii.isEmpty)).map FilePath.mk
  let cache : Option FilePath :=
    if windows then present localAppData
    else if macOS then (present home).map (· / "Library" / "Caches")
    else present xdgCache <|> (present home).map (· / ".cache")
  cache.map (· / "verso-blueprint" / "kernel-replay-checkers.json")

/-- The record when `replayRecordVar` names none: `recordFileIn` of this process's
environment. -/
def defaultRecordFile? : IO (Option FilePath) :=
  return recordFileIn (← IO.getEnv "HOME") (← IO.getEnv "XDG_CACHE_HOME")
    (← IO.getEnv "LOCALAPPDATA") Platform.isOSX Platform.isWindows

/-- The memory limit of the checker process, in bytes, when `replayMemoryVar` sets none: a
quarter of the machine's physical memory `physical`. -/
def defaultMemoryLimit (physical : Nat) : Nat := physical / 4

/-- The memory limit of the checker process when the machine's physical memory is not known:
4 GiB. -/
def fallbackMemoryLimit : Nat := 4 * 1024 * 1024 * 1024

/-- The worker threads each checker runs with on a machine of `threads` hardware threads: half
of them, at most 8 and at least 2. -/
def jobsFor (threads : Nat) : Nat := max 2 (min 8 (threads / 2))

/-- `jobsFor` this machine. -/
def defaultJobs : IO Nat :=
  return jobsFor (System.Platform.Internal.getHardwareConcurrency ()).toNat

/-- How a replay is run. -/
structure ReplayConfig where
  /-- The checker programs by name, in the order they run (`Replay.checkerNames`); a name
  without a program is one that was not found. -/
  checkers : Array (String × Option FilePath) := #[]
  /-- Why the configuration of the checkers is not usable, when it is not (a value of
  `replayCheckerVar` other than `off`). -/
  setting? : Option String := none
  /-- The worker threads of each checker. -/
  jobs : Nat := 2
  /-- The root of the Lean toolchain the project was built with, whose own library the compiled
  modules are loaded on; `none` for the toolchain the checker is in. -/
  sysroot? : Option FilePath := none
  /-- The replay is switched off. -/
  off : Bool := false
  /-- The time limit of the whole replay, in seconds. -/
  limitSeconds : Nat := defaultReplayLimit
  /-- The memory limit of the checker process, in bytes; `none` for no limit. -/
  memoryLimit? : Option Nat := none
  /-- The size limit of the export, in bytes; `none` for no limit. -/
  exportLimit? : Option Nat := none
  /-- The directories compiled modules are loaded from, in the order they are searched, without
  the toolchain's own library (which is found from the checker and searched last). -/
  searchPath : Array FilePath := #[]
  /-- The directories of `searchPath` that hold the project's own compiled modules. -/
  projectDirs : Array FilePath := #[]
  /-- The file that records accepted exports. -/
  record? : Option FilePath := none
  /-- The program that loads the modules and writes the export in a process of its own
  (`registerReplayWorker`), with its leading arguments; `none` to do both in this process. -/
  worker? : Option (FilePath × Array String) := none
  /-- Print a line on the standard error for every step of the replay. -/
  progress : Bool := false
deriving Inhabited, Repr

/-- A declaration a replay is asked to check. -/
structure ReplayTarget where
  name : Name
  /-- The module the site's data places the declaration in; `none` when it names none. A
  declaration found in another module is not the one the site reports on. -/
  module? : Option Name := none
deriving Inhabited, Repr, BEq, ToJson, FromJson

/-! ## The worker -/

/-- The first argument of a program that is run as the replay's worker: the request file and
the reply file follow. -/
def replayWorkerFlag : String := "--kernel-replay-worker"

/-- The generator's flag that names the worker program (`vbp build` passes itself). -/
def replayWorkerProgramFlag : String := "--kernel-replay-with"

/-- The worker of this process (`ReplayConfig.worker?`), when one is known. -/
initialize replayWorkerRef : IO.Ref (Option (FilePath × Array String)) ← IO.mkRef none

/-- Name the program that loads the modules and writes the export for the replays of this
process: `program`, run with `replayWorkerFlag`, a request file and a reply file. -/
def registerReplayWorker (program : FilePath) : IO Unit :=
  replayWorkerRef.set (some (program, #[replayWorkerFlag]))

/-- `registerReplayWorker` with this program itself, for a compiled program whose `main` answers
`replayWorkerFlag`. A program run by `lean --run` is `lean`, which is no worker: nothing is
registered then, nor when a worker is registered already. -/
def registerSelfAsReplayWorker : IO Unit := do
  if (← replayWorkerRef.get).isSome then return
  let program ← IO.appPath
  if program.fileStem == some "lean" then return
  registerReplayWorker program

private def exeName (name : String) : String :=
  if Platform.isWindows then name ++ ".exe" else name

/-- The toolchain's program `name` (`con-leche`, `con-ron`): in `LEAN_SYSROOT`, else beside the
running program. -/
def findChecker? (name : String) : IO (Option FilePath) := do
  let mut candidates : Array FilePath := #[]
  if let some root ← IO.getEnv "LEAN_SYSROOT" then
    candidates := candidates.push (FilePath.mk root / "bin" / exeName name)
  if let some dir := (← IO.appPath).parent then
    candidates := candidates.push (dir / exeName name)
  for c in candidates do
    if ← c.pathExists then return some c
  return none

/-- Both checkers, each from its variable (`conLecheVar`, `conRonVar`) when it is set, else
`findChecker?`. A variable that names no file finds nothing. -/
def findCheckers : IO (Array (String × Option FilePath)) :=
  Replay.checkerNames.mapM fun name => do
    let var := if name == "con-leche" then conLecheVar else conRonVar
    match ((← IO.getEnv var).map (·.trimAscii.copy)).filter (!·.isEmpty) with
    | some path =>
      return (name, if ← (FilePath.mk path).pathExists then some (FilePath.mk path) else none)
    | none => return (name, ← findChecker? name)

private def realOr (path : FilePath) : IO FilePath :=
  try IO.FS.realPath path catch _ => pure path

/-- The directories of `dirs` that exist, by their real paths, each once, in order. -/
def dedupDirs (dirs : Array FilePath) : IO (Array FilePath) := do
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
swapped memory on Linux, else its resident size (`ps`). `none` when it cannot be read. -/
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

/-- The worker a value of `replayWorkerVar` names: the program on its first line, the arguments
before `replayWorkerFlag` on the lines after it, then that flag. `none` for an empty value. -/
def workerOfLines (value : String) : Option (FilePath × Array String) :=
  match (value.splitOn "\n").filter (!·.trimAscii.isEmpty) with
  | [] => none
  | program :: leading => some (FilePath.mk program, leading.toArray.push replayWorkerFlag)

/-- The configuration for the project at `root`, whose own compiled modules are in
`libraryDirs` (relative to `root`), from the environment variables above. Modules are searched
for in the directories of `LEAN_PATH`, in its order (Lake sets it for a program it runs), then in
the project's own directories and those of its Lake packages. -/
def ReplayConfig.fromEnv (root : FilePath) (libraryDirs : Array String) : IO ReplayConfig := do
  let projectDirs ← dedupDirs (libraryDirs.map fun dir : String => root / dir)
  let mut dirs : Array FilePath := #[]
  if let some path ← IO.getEnv "LEAN_PATH" then
    dirs := dirs ++ (SearchPath.parse path).toArray
  dirs := dirs ++ projectDirs
  dirs := dirs.push (root / ".lake" / "build" / "lib" / "lean")
  let packages := root / ".lake" / "packages"
  if ← packages.isDir then
    for entry in (← packages.readDir).qsort (·.fileName < ·.fileName) do
      dirs := dirs.push (entry.path / ".lake" / "build" / "lib" / "lean")
  let searchPath ← dedupDirs dirs
  let choice := ((← IO.getEnv replayCheckerVar).map (·.trimAscii.copy)).filter (!·.isEmpty)
  let off := choice == some "off"
  let setting? := choice.bind fun value => if value == "off" then none else
    some s!"{replayCheckerVar} is set to '{value}', and it takes only 'off': the checkers are \
      named by {conLecheVar} and {conRonVar}"
  let checkers ← findCheckers
  let jobs ← defaultJobs
  let number (var : String) : IO (Option Nat) :=
    return (← IO.getEnv var).bind (·.trimAscii.copy.toNat?)
  let limitSeconds := (← number replayLimitVar).getD defaultReplayLimit
  let megabytes (var : String) (otherwise : IO Nat) : IO (Option Nat) := do
    match ← number var with
    | some 0 => pure none
    | some mib => pure (some (mib * 1024 * 1024))
    | none => some <$> otherwise
  let memoryLimit? ← megabytes replayMemoryVar do
    return ((← physicalMemory?).map defaultMemoryLimit).getD fallbackMemoryLimit
  let exportLimit? ← megabytes replayExportVar (pure defaultExportLimit)
  let record? ← match ← IO.getEnv replayRecordVar with
    | some path => pure (if path.trimAscii.isEmpty then none else some (FilePath.mk path))
    | none => defaultRecordFile?
  let sysroot? := (← IO.getEnv "LEAN_SYSROOT").map FilePath.mk
  let worker? := (workerOfLines ((← IO.getEnv replayWorkerVar).getD "")) <|> (← replayWorkerRef.get)
  return { checkers, setting?, jobs, sysroot?, off, limitSeconds, memoryLimit?, exportLimit?,
           searchPath, projectDirs, record?, worker?, progress := true }

/-! ## Loading the compiled modules -/

/-- The top-level names in each directory of a search path, in lower case: a module can only
be in a directory that has its first name component, whatever the file system does with case. -/
private def topNames (path : Array FilePath) : IO (Array (Std.HashSet String)) :=
  path.mapM fun dir => do
    let entries ← try dir.readDir catch _ => pure #[]
    return entries.foldl (init := {}) fun set entry => set.insert entry.fileName.toLower

/-- The directories of `path` that hold a compiled file of `module`. -/
private def dirsOf (path : Array FilePath) (tops : Array (Std.HashSet String)) (module : Name) :
    IO (Array FilePath) := do
  let top := (module.getRoot.toString (escape := false)).toLower
  let mut out := #[]
  for dir in path, names in tops do
    unless names.contains top || names.contains (top ++ ".olean") do continue
    if ← (modToFilePath dir module "olean").pathExists then out := out.push dir
  return out

/-- The directories of `path` that hold different compiled files of `module`, when there is
more than one: the module could then be either, by the order of the path. Files that are one
file by their real path count once. -/
private def duplicateDirs (path : Array FilePath) (tops : Array (Std.HashSet String))
    (module : Name) : IO (Array FilePath × Bool) := do
  let dirs ← dirsOf path tops module
  if dirs.size ≤ 1 then return (dirs, false)
  let mut files : Array FilePath := #[]
  for dir in dirs do
    let real ← realOr (modToFilePath dir module "olean")
    unless files.contains real do files := files.push real
  return (dirs, files.size > 1)

/-- The message for a module with more than one compiled file on the search path. -/
def duplicateMessage (module : Name) (dirs : Array FilePath) : String :=
  s!"module {module} has a compiled file in more than one directory of the search path \
    ({", ".intercalate (dirs.toList.map (·.toString))}), so which of them a build means depends \
    on the order of the path"

/-- The compiled modules a replay loaded. -/
structure LoadedModules where
  env : Environment
  /-- The toolchain's own library directory. -/
  toolchainDir : FilePath
  /-- For each module of `env`, by its index: the directory of the search path it was loaded
  from. -/
  dirs : Array FilePath
  /-- The modules that were asked for and have no compiled file on the search path. -/
  notCompiled : Array Name := #[]

/-- The search path of a replay: the configuration's, then the toolchain's own library. -/
private def fullPath (config : ReplayConfig) (sysroot : FilePath) : IO (Array FilePath) :=
  dedupDirs (config.searchPath.push (sysroot / "lib" / "lean"))

/-- Whether `module` has more than one compiled file on the search path of `config`
(`duplicateMessage`); `none` when it has at most one. -/
def duplicateModule? (config : ReplayConfig) (sysroot : FilePath) (module : Name) :
    IO (Option String) := do
  let path ← fullPath config sysroot
  let (dirs, duplicate) ← duplicateDirs path (← topNames path) module
  return if duplicate then some (duplicateMessage module dirs) else none

/-- Load the modules `modules` that have a compiled file, and everything they import, into an
environment, by the search path of `config` and the toolchain's library in `sysroot`. Fails,
with the reason, when the modules cannot be imported together, or when a module of the
environment has more than one compiled file on the search path (`duplicateMessage`). The
process's search path is put back afterwards. -/
def loadModules (config : ReplayConfig) (sysroot : FilePath) (modules : Array Name) :
    IO (Except String LoadedModules) := do
  let path ← fullPath config sysroot
  let toolchainDir ← realOr (sysroot / "lib" / "lean")
  let tops ← topNames path
  let mut wanted := #[]
  let mut notCompiled := #[]
  for m in modules do
    if wanted.contains m || notCompiled.contains m then continue
    if (← dirsOf path tops m).isEmpty then notCompiled := notCompiled.push m
    else wanted := wanted.push m
  if wanted.isEmpty then
    return .error "none of the site's modules has a compiled file on the search path"
  let before ← searchPathRef.get
  let env ← try
      searchPathRef.set path.toList
      let env ← importModules (wanted.map ({ module := · })) {} (loadExts := false)
      searchPathRef.set before
      pure env
    catch e =>
      searchPathRef.set before
      return .error s!"the site's modules could not be loaded into one environment: {e}"
  let mut dirs := Array.mkEmpty env.header.moduleNames.size
  for m in env.header.moduleNames do
    let (found, duplicate) ← duplicateDirs path tops m
    if duplicate then return .error (duplicateMessage m found)
    let some dir := found[0]?
      | return .error s!"the compiled file of module {m} was not found again on the search path"
    dirs := dirs.push dir
  return .ok { env, toolchainDir, dirs, notCompiled }

/-! ## What a declaration depends on -/

/-- The recursors of each inductive type of `env`. -/
private def recursorsOf (env : Environment) : NameMap (Array Name) :=
  env.constants.fold (init := {}) fun map _ info =>
    match info with
    | .recInfo val => val.all.foldl (init := map) fun map type =>
      map.insert type (((map.find? type).getD #[]).push val.name)
    | _ => map

/-- The constant that stands for `name` in the walk: an inductive type, its constructors and its
recursors refer to each other and are checked as one block, as are the constants of `Quot`, so
each block is one node (the first type of the block, or `Quot`). -/
private def blockOf (env : Environment) (name : Name) : Name :=
  let ofType (type : Name) : Name :=
    match env.find? type with
    | some (.inductInfo val) => val.all.headD type
    | _ => type
  match env.find? name with
  | some (.inductInfo val) => val.all.headD name
  | some (.ctorInfo val) => ofType val.induct
  | some (.recInfo val) => ofType (val.all.headD name)
  | some (.quotInfo _) => `Quot
  | _ => name

/-- The constants the block of `block` refers to, as the exporter follows them: types and
values; for an inductive block the types of its types, constructors and recursors and the
recursors' rules; for `Quot` its four constants and `Eq`. -/
private def blockUses (env : Environment) (recursors : NameMap (Array Name)) (block : Name) :
    Array Name :=
  let ofInfo (info : ConstantInfo) : Array Name :=
    info.type.getUsedConstants ++
      ((info.value? (allowOpaque := true)).map (·.getUsedConstants)).getD #[]
  match env.find? block with
  | some (.inductInfo val) => Id.run do
    let mut out := #[]
    for type in val.all do
      let some (.inductInfo typeVal) := env.find? type | continue
      out := out ++ typeVal.type.getUsedConstants
      for ctor in typeVal.ctors do
        if let some info := env.find? ctor then out := out ++ info.type.getUsedConstants
      for recursor in (recursors.find? type).getD #[] do
        if let some (.recInfo recVal) := env.find? recursor then
          out := out ++ recVal.type.getUsedConstants
          for rule in recVal.rules do
            out := out ++ rule.rhs.getUsedConstants
    return out
  | some (.quotInfo _) =>
    #[``Eq] ++ #[`Quot, ``Quot.mk, ``Quot.lift, ``Quot.ind].flatMap fun c =>
      ((env.find? c).map (·.type.getUsedConstants)).getD #[]
  | some info => ofInfo info
  | none => #[]

/-- The axioms outside Lean's standard three under each of `roots` (with `standard`, those
three as well), found by walking the terms of `env` (types, values, the parts of inductive
types), sorted; a root with none is left out. The tables of axioms that compiled modules record
are not read. Fails when declarations depend on each other in a cycle, which no well-formed
environment has. -/
def restingAxioms (env : Environment) (roots : Array Name) (standard : Bool := false) :
    Except String (Array (Name × Array Name)) := Id.run do
  let recursors := recursorsOf env
  -- the axioms under each block that is done; a block on the stack has none yet
  let mut done : Std.HashMap Name (Array Name) := {}
  let mut open_ : Std.HashSet Name := {}
  for root in roots do
    -- `(block, what it uses)`; the uses are there once the block is open
    let mut stack : Array (Name × Option (Array Name)) := #[(blockOf env root, none)]
    while h : stack.size > 0 do
      let (block, uses?) := stack[stack.size - 1]
      stack := stack.pop
      if done.contains block then continue
      match uses? with
      | some uses =>
        let mut axioms : Array Name := #[]
        if let some (.axiomInfo _) := env.find? block then
          if standard || !Data.standardAxioms.contains block then axioms := axioms.push block
        for used in uses do
          for a in done.getD used #[] do
            unless axioms.contains a do axioms := axioms.push a
        done := done.insert block axioms
        open_ := open_.erase block
      | none =>
        let uses := (blockUses env recursors block).map (blockOf env) |>.filter (· != block)
        open_ := open_.insert block
        stack := stack.push (block, some uses)
        for used in uses do
          unless done.contains used do
            if open_.contains used then
              return .error s!"the loaded modules hold declarations that depend on each other \
                in a cycle (at {used})"
            stack := stack.push (used, none)
  let mut out := #[]
  for root in roots do
    let axioms := done.getD (blockOf env root) #[]
    unless axioms.isEmpty do out := out.push (root, Data.sortAxioms axioms)
  return .ok out

/-! ## The export -/

/-- The size of the pieces an export is hashed in. -/
private def pieceSize : Nat := 4 * 1024 * 1024

/-- Why an export was stopped. -/
private inductive ExportStop where
  | overExport
  | timedOut
deriving Inhabited, DecidableEq

/-- Where an export goes: a file, written in pieces that are hashed as they are written. -/
private structure Sink where
  handle : IO.FS.Handle
  buffer : IO.Ref ByteArray
  digests : IO.Ref (Array (Task ByteArray))
  bytes : IO.Ref Nat
  stopped : IO.Ref (Option ExportStop)
  limit? : Option Nat
  deadline : Nat

private def Sink.flush (sink : Sink) : IO Unit := do
  let piece ← sink.buffer.modifyGet fun b => (b, ByteArray.emptyWithCapacity 0)
  if piece.isEmpty then return
  sink.handle.write piece
  sink.digests.modify (·.push (Task.spawn fun _ => Sha256.digest piece))
  let bytes ← sink.bytes.modifyGet fun n => (n + piece.size, n + piece.size)
  if sink.limit?.any (bytes > ·) then
    sink.stopped.set (some .overExport)
    throw (IO.userError "the export went over its size limit")
  if (← IO.monoMsNow) ≥ sink.deadline then
    sink.stopped.set (some .timedOut)
    throw (IO.userError "the export went over the time limit")

private def Sink.put (sink : Sink) (bytes : ByteArray) : IO Unit := do
  let size ← sink.buffer.modifyGet fun b => let b := b ++ bytes; (b.size, b)
  if size ≥ pieceSize then sink.flush

/-- What names an export by its contents: its length and the SHA-256 of the SHA-256 digests of
its pieces (of `pieceSize` bytes, cut at the end of the line that fills one), in hexadecimal. -/
structure ExportKey where
  bytes : Nat
  hash : String
deriving Repr, Inhabited, DecidableEq, ToJson, FromJson

private def Sink.key (sink : Sink) : IO ExportKey := do
  let mut all := ByteArray.emptyWithCapacity 0
  for digest in ← sink.digests.get do
    all := all ++ digest.get
  let bytes ← sink.bytes.get
  return { bytes, hash := Sha256.hex (all ++ (toString bytes).toUTF8) }

/-- Write `roots` and every constant they depend on to `file`, in the export format of the Lean
toolchain, with its exporter. Gives the constants written and the export's key, or why the
export was stopped. The exporter prints to the standard output, which is redirected for this
thread while it runs. -/
private def writeExport (env : Environment) (roots : Array Name) (file : FilePath)
    (limit? : Option Nat) (deadline : Nat) :
    IO (Except ExportStop (Array Name × ExportKey)) := do
  let handle ← IO.FS.Handle.mk file .write
  let sink : Sink := {
    handle, limit?, deadline
    buffer := ← IO.mkRef (ByteArray.emptyWithCapacity 0)
    digests := ← IO.mkRef #[]
    bytes := ← IO.mkRef 0
    stopped := ← IO.mkRef none }
  let stream : IO.FS.Stream := {
    flush := pure ()
    read := fun _ => pure (ByteArray.emptyWithCapacity 0)
    write := sink.put
    getLine := pure ""
    putStr := fun text => sink.put text.toUTF8
    isTty := pure false }
  let state : LeanExport.State := {
    visitedNames := (Std.HashMap.emptyWithCapacity 65536).insert .anonymous 0
    visitedLevels := (Std.HashMap.emptyWithCapacity 1024).insert .zero 0
    visitedExprs := Std.HashMap.emptyWithCapacity 262144
    noMDataExprs := Std.HashMap.emptyWithCapacity 1024 }
  let action : LeanExport.M Unit := do
    LeanExport.initState env
    LeanExport.dumpMetadata
    for root in roots do
      modify fun st => { st with noMDataExprs := {} }
      LeanExport.dumpConstant root
  let before ← IO.setStdout stream
  let written ← try
      let (_, state) ← StateT.run (ReaderT.run action { env }) state
      sink.flush
      discard <| IO.setStdout before
      pure (some state.visitedConstants.toArray)
    catch e =>
      discard <| IO.setStdout before
      if (← sink.stopped.get).isNone then throw e
      pure none
  handle.flush
  match written, ← sink.stopped.get with
  | some constants, none => return .ok (constants, ← sink.key)
  | _, some stop => return .error stop
  | none, none => throw (IO.userError "the export was not written")

/-! ## The record -/

/-- How many accepted exports a record keeps: the newest. -/
private def recordSize : Nat := 256

/-- The version of a record's format; a record of another version holds nothing. -/
private def recordVersion : Nat := 3

private def readRecord (file? : Option FilePath) : IO (Array String) := do
  let some file := file? | return #[]
  try
    let json ← IO.ofExcept (Json.parse (← IO.FS.readFile file))
    let .ok v := json.getObjValAs? Nat "version" | return #[]
    if v != recordVersion then return #[]
    IO.ofExcept (json.getObjValAs? (Array String) "accepted")
  catch _ => return #[]

/-- Add `key` to the record, merged with what the record holds now (another generator may have
written it since it was read), and replace the file in one rename. -/
private def addToRecord (file? : Option FilePath) (key : String) : IO Unit := do
  let some file := file? | return
  try
    let now ← readRecord file?
    let keys := (now.filter (· != key)).push key
    if let some dir := file.parent then IO.FS.createDirAll dir
    let tmp := file.addExtension s!"tmp{← IO.monoNanosNow}"
    let keys := keys.extract (keys.size - recordSize) keys.size
    IO.FS.writeFile tmp
      (Json.mkObj [("version", toJson recordVersion), ("accepted", toJson keys)]).compress
    IO.FS.rename tmp file
  catch _ => return

/-! ## Running the checkers -/

/-- The Lean version a toolchain's `lean --version` prints (`4.35.0`). -/
def leanVersionOf (lean : FilePath) : IO (Option String) := do
  try
    let out ← IO.Process.output { cmd := lean.toString, args := #["--version"] }
    let text := out.stdout
    let some rest := (text.splitOn "version ")[1]? | return none
    let version := (rest.takeWhile fun c => c != ',' && c != ')' && !c.isWhitespace).copy
    return if version.isEmpty then none else some version
  catch _ => return none

/-- What a run of a process gave; `peak` is the most memory it was seen to hold
(`processMemory?`), in bytes. -/
private inductive RunEnd where
  | exited (code : UInt32) (stdout stderr : String) (peak : Nat)
  | timedOut
  | overMemory
  | notStarted (error : String)

/-- How often a process's memory is looked at, in milliseconds. -/
def sampleMs : Nat := 500

/-- The most bytes of each of a process's output streams that are kept; the rest is read and
dropped, so that the process is never held up by a full pipe. -/
def outputLimit : Nat := 1024 * 1024

/-- Read `stream` to its end, keeping its first `limit` bytes. -/
private partial def readCapped (stream : IO.FS.Handle) (limit : Nat) : IO String := do
  let rec go (acc : ByteArray) : IO ByteArray := do
    let chunk ← stream.read 65536
    if chunk.isEmpty then return acc
    if acc.size ≥ limit then go acc
    else go (acc ++ chunk.extract 0 (limit - acc.size))
  let bytes ← go (ByteArray.emptyWithCapacity 0)
  -- the cut may fall inside a character: drop its first bytes, else keep the ASCII only
  let valid := [0, 1, 2, 3].findSome? fun k =>
    if k ≤ bytes.size then String.fromUTF8? (bytes.extract 0 (bytes.size - k)) else none
  return valid.getD (String.ofList (bytes.toList.filterMap fun b =>
    if b < 128 then some (Char.ofNat b.toNat) else none))

/-- Run `cmd` with `args` and `env` at a lower priority (through `nice`, when there is one),
killing it when the clock passes `deadline` (`IO.monoMsNow`) or when its memory passes
`memoryLimit?` (`processMemory?`, looked at every `sampleMs`). The process stays in this
process's process group, so that
whatever stops the generator's group (an interrupt at the terminal, the program that started the
generator) stops it too. -/
private def runLimited (cmd : String) (args : Array String)
    (env : Array (String × Option String)) (deadline : Nat) (memoryLimit? : Option Nat) :
    IO RunEnd := do
  if (← IO.monoMsNow) ≥ deadline then return .timedOut
  let spawn (cmd : String) (args : Array String) :=
    IO.Process.spawn { cmd, args, env, stdin := .null, stdout := .piped, stderr := .piped }
  let child ← try spawn "nice" (#["-n", "10", cmd] ++ args) catch _ =>
    try spawn cmd args catch e => return .notStarted (toString e)
  let stdout ← IO.asTask (readCapped child.stdout outputLimit) Task.Priority.dedicated
  let stderr ← IO.asTask (readCapped child.stderr outputLimit) Task.Priority.dedicated
  let finish (r : RunEnd) : IO RunEnd := do
    try child.kill catch _ => pure ()
    discard <| child.wait
    return r
  let mut nextSample := (← IO.monoMsNow) + sampleMs
  let mut peak := 0
  let mut code? : Option UInt32 := none
  while code?.isNone do
    code? ← child.tryWait
    if code?.isSome then break
    let now ← IO.monoMsNow
    if now ≥ deadline then return ← finish .timedOut
    if now ≥ nextSample then
      if let some used ← processMemory? child.pid then
        peak := max peak used
        if memoryLimit?.any (used > ·) then return ← finish .overMemory
      nextSample := (← IO.monoMsNow) + sampleMs
    IO.sleep 50
  let text (t : Task (Except IO.Error String)) : String :=
    match t.get with
    | .ok s => s
    | .error _ => ""
  return .exited (code?.getD 1) (text stdout) (text stderr) peak

/-- The longest message a result keeps. -/
private def messageLimit : Nat := 2000

private def clip (text : String) : String :=
  let text := text.trimAscii.copy
  if text.length ≤ messageLimit then text else (text.take messageLimit).copy ++ " …"

/-- `text` without the run times a checker adds to its lines (` t=0.021s`), which differ from
run to run. -/
def withoutTimes (text : String) : String :=
  "\n".intercalate ((text.splitOn "\n").map fun line =>
    match line.splitOn " t=" with
    | [] | [_] => line
    | parts =>
      let last := parts.getLast!
      let isTime := !last.isEmpty && last.endsWith "s" &&
        (last.dropEnd 1).all fun c => c.isDigit || c == '.'
      if isTime then " t=".intercalate parts.dropLast else line)

/-- The number `N` of a line `<program>: accepted N declarations …`, when `text` has one. -/
def acceptedCount? (text : String) : Option Nat :=
  (text.splitOn "\n").findSome? fun line =>
    match line.splitOn ": accepted " with
    | [_, rest] =>
      match rest.splitOn " " with
      | n :: "declarations" :: _ | n :: "declaration" :: _ => n.toNat?
      | _ => none
    | _ => none

/-- The number `N` of a 4.36 decline `declined (N declarations checked, …)`, when there is one. -/
def declinedCount? (text : String) : Option Nat :=
  (text.splitOn "declined (")[1]? |>.bind fun rest => ((rest.splitOn " ")[0]?).bind (·.toNat?)

/-- The words with which a checker rejects: `con-leche` writes `invalid: …`, `con-ron`
`rejected: …`. -/
def rejectionMarkers : List String := [": invalid: ", ": rejected: "]

/-- A checker's answer from its exit status first and its words second, for an export of
`records` declaration records: 0 is an acceptance only with its line `accepted N declarations`
and `N ≥ records`; 1 is a rejection only with its words of rejection, and an error with an
uncaught exception; 2 is a decline; 3 (a usage or parse error, a reduction out of fuel) and any
other status are no answer. Gives the answer, the count it stated and what it said. -/
def parseAnswer (code : UInt32) (stdout stderr : String) (records : Nat) :
    Replay.Answer × Option Nat × Option String :=
  let said := clip (withoutTimes (if stderr.trimAscii.isEmpty then stdout else stderr))
  let all := withoutTimes (stdout ++ "\n" ++ stderr)
  let saidOr (fallback : String) := if said.isEmpty then fallback else said
  match code with
  | 0 =>
    match acceptedCount? stdout with
    | some n =>
      if n ≥ records then (.accepted, some n, none)
      else (.noAnswer, some n, some s!"status 0, and it said it accepted {n} declarations, but \
        the export holds {records}")
    | none => (.noAnswer, none, some s!"status 0 without its line that it accepted the export: \
        {saidOr "it wrote nothing"}")
  | 1 =>
    if (all.splitOn "uncaught exception").length > 1 then
      (.error, none, some (saidOr "an uncaught exception"))
    else
      let rejection := rejectionMarkers.findSome? fun marker =>
        match all.splitOn marker with
        | _ :: rest@(_ :: _) => some (clip ((marker.drop 2).copy ++ marker.intercalate rest))
        | _ => none
      match rejection with
      | some message => (.rejected, none, some message)
      | none => (.noAnswer, none, some s!"status 1 without its words of rejection: \
          {saidOr "it wrote nothing"}")
  | 2 => (.declined, declinedCount? all, some (saidOr "it declined without saying why"))
  | 3 => (.noAnswer, none, some s!"status 3: {saidOr "it wrote nothing"}")
  | n => (.noAnswer, none, some s!"status {n}: {saidOr "it wrote nothing"}")

/-- The verdict of a replay from its checkers' runs, in order: accepted only when every one
accepted (and there is one); disagreed when one accepted and another rejected; rejected when one
rejected; otherwise a stop at a limit, a decline, or no answer, with what the first such
checker said. -/
def combineRuns (runs : Array Replay.CheckerRun) : Replay.Outcome × Option String :=
  let first (a : Replay.Answer) := runs.find? (·.answer == a)
  if !runs.isEmpty && runs.all (·.answer == .accepted) then (.accepted, none)
  else match first .rejected with
  | some r => (if (first .accepted).isSome then .disagreed else .rejected, r.message)
  | none =>
    if let some c := first .timedOut then (.timedOut, some c.label)
    else if let some c := first .overMemory then (.overMemory, some c.label)
    else if let some c := first .declined then (.declined, c.message)
    else match runs.find? (·.answer != .accepted) with
      | some c =>
        let what := match c.answer with
          | .error => "ended with an error"
          | .notStarted => "could not be started"
          | _ => "gave no answer"
        (.failed, some s!"{c.label} {what}{(c.message.map (s!" ({·})")).getD ""}")
      | none => (.failed, some "no checker ran")

/-- What the generator finds in an export file: its size, its declaration records (lines that
start with `{"def":`, `{"thm":`, `{"opaque":`, `{"axiom":`, `{"inductive":` or `{"quot":`) and
whether its last line is complete. -/
structure ExportCensus where
  bytes : Nat
  records : Nat
  endsWithNewline : Bool
deriving Repr, Inhabited, DecidableEq

private def recordPrefixes : Array ByteArray :=
  #["{\"def\":", "{\"thm\":", "{\"opaque\":", "{\"axiom\":", "{\"inductive\":", "{\"quot\":"].map
    (·.toUTF8)

private def startsWithAt (bytes : ByteArray) (at_ : Nat) (pre : ByteArray) : Bool := Id.run do
  if at_ + pre.size > bytes.size then return false
  for i in [0:pre.size] do
    if bytes.get! (at_ + i) != pre.get! i then return false
  return true

/-- `ExportCensus` of the bytes `bytes`. -/
def censusOf (bytes : ByteArray) : ExportCensus := Id.run do
  let mut records := 0
  let mut lineStart := true
  for i in [0:bytes.size] do
    if lineStart then
      if recordPrefixes.any (startsWithAt bytes i ·) then records := records + 1
    lineStart := bytes.get! i == 10
  return { bytes := bytes.size, records, endsWithNewline := bytes.size > 0 && lineStart }

/-- `ExportCensus` of the file `file`, read in pieces (a line's start is never cut: a piece is
cut after a newline). -/
def exportCensus (file : FilePath) : IO ExportCensus := do
  let handle ← IO.FS.Handle.mk file .read
  let mut bytes := 0
  let mut records := 0
  let mut carry := ByteArray.emptyWithCapacity 0
  let mut last : Option UInt8 := none
  repeat
    let chunk ← handle.read (4 * 1024 * 1024)
    if chunk.isEmpty then break
    bytes := bytes + chunk.size
    last := some (chunk.get! (chunk.size - 1))
    let data := carry ++ chunk
    -- count the complete lines; keep the rest for the next piece
    let mut cut := data.size
    while cut > 0 && data.get! (cut - 1) != 10 do cut := cut - 1
    records := records + (censusOf (data.extract 0 cut)).records
    carry := data.extract cut data.size
  records := records + (censusOf carry).records
  return { bytes, records, endsWithNewline := last == some 10 }

/-! ## The replay -/

private def mebibytes (bytes : Nat) : Nat := (bytes + 1024 * 1024 - 1) / (1024 * 1024)

/-- A process's time and memory for a progress line: "47 s, at most 688 MiB of memory". The
memory is left out when it was never read. -/
private def usedText (ms peak : Nat) : String :=
  let memory := if peak == 0 then "" else s!", at most {mebibytes peak} MiB of memory"
  s!"{(ms + 500) / 1000} s{memory}"

/-- Where the constants `constants` of `loaded` come from: the project (`projectDirs`), Lean's
own library, and each dependency by the first component of its modules' names. -/
private def originsOf (loaded : LoadedModules) (projectDirs : Array FilePath)
    (constants : Array Name) : Array Origin := Id.run do
  let env := loaded.env
  -- per kind: the first name components seen, and for a dependency its own count
  let mut project : Nat := 0
  let mut projectNames : Array String := #[]
  let mut toolchain : Nat := 0
  let mut toolchainNames : Array String := #[]
  let mut dependencies : Std.HashMap String Nat := {}
  for c in constants do
    let some idx := env.getModuleIdxFor? c | continue
    let some module := env.header.moduleNames[idx.toNat]? | continue
    let some dir := loaded.dirs[idx.toNat]? | continue
    let top := module.getRoot.toString (escape := false)
    if projectDirs.contains dir then
      project := project + 1
      unless projectNames.contains top do projectNames := projectNames.push top
    else if dir == loaded.toolchainDir then
      toolchain := toolchain + 1
      unless toolchainNames.contains top do toolchainNames := toolchainNames.push top
    else
      dependencies := dependencies.insert top (dependencies.getD top 0 + 1)
  let joined (names : Array String) := ", ".intercalate (names.qsort (· < ·)).toList
  let mut out : Array Origin := #[]
  if project > 0 then
    out := out.push { kind := .project, name := joined projectNames, constants := project }
  for (name, n) in dependencies.toArray.qsort
      (fun a b => a.2 > b.2 || (a.2 == b.2 && a.1 < b.1)) do
    out := out.push { kind := .dependency, name, constants := n }
  if toolchain > 0 then
    out := out.push { kind := .toolchain, name := joined toolchainNames, constants := toolchain }
  return out

/-- The checkers of a replay: each program by name, the root of the Lean toolchain the modules
are loaded on (`ReplayConfig.sysroot?`, else the toolchain the first checker is in) and that
toolchain's Lean version. -/
structure Toolchain where
  checkers : Array (String × FilePath)
  sysroot : FilePath
  version : Option String

/-- The toolchain of `config`, or how the replay ends without one (`off`; `failed` for an
unusable setting; `noChecker` when a checker is missing, with the message that names the Lean
version and what it lacks). -/
def ReplayConfig.toolchain (config : ReplayConfig) :
    IO (Except (Replay.Outcome × Option String × Option String) Toolchain) := do
  if config.off then return .error (.off, none, none)
  if let some why := config.setting? then return .error (.failed, some why, none)
  let leanIn (root : FilePath) : FilePath :=
    root / "bin" / (if Platform.isWindows then "lean.exe" else "lean")
  let sysroot? := config.sysroot? <|> (← IO.getEnv "LEAN_SYSROOT").map FilePath.mk
  let missing := (config.checkers.filter (·.2.isNone)).map (·.1)
  let missing := if config.checkers.isEmpty then Replay.checkerNames else missing
  if !missing.isEmpty then
    let version ← match sysroot? with
      | some root => leanVersionOf (leanIn root)
      | none => pure none
    let lean := (version.map (s!"Lean (v{·})")).getD "Lean toolchain"
    let what := " or ".intercalate missing.toList
    return .error (.noChecker, some s!"this project's {lean} ships no {what}", version)
  let mut found := #[]
  for (name, path?) in config.checkers do
    if let some path := path? then found := found.push (name, ← realOr path)
  let some (_, first) := found[0]? | return .error (.noChecker, none, none)
  let some binDir := first.parent | return .error (.noChecker, none, none)
  let sysroot := sysroot?.getD (binDir.parent.getD binDir)
  let version ← leanVersionOf (binDir / (if Platform.isWindows then "lean.exe" else "lean"))
  return .ok { checkers := found, sysroot, version }

/-- `names`, each once, in the order `Replay.Result.declarations` keeps. -/
def replayOrder (names : Array Name) : Array Name :=
  let distinct : NameHashSet := names.foldl (init := {}) fun set n => set.insert n
  distinct.toArray.qsort Name.quickLt

/-- What the first half of a replay gives (`prepareExport`): the declarations that were exported
and the export's key, or why there is no export. It holds nothing of the loaded environment, so
it can come from another process. -/
structure Prepared where
  /-- The declarations exported, in `replayOrder`. -/
  declarations : Array Name := #[]
  /-- `Replay.Result.notCovered`. -/
  notCovered : Array (Name × String) := #[]
  /-- `Replay.Result.axioms`: the declarations left out of the export because they rest on an
  axiom outside Lean's standard three, with those axioms. -/
  axioms : Array (Name × Array Name) := #[]
  /-- The number of constants in the export. -/
  constants : Nat := 0
  origins : Array Origin := #[]
  /-- The export's key, when the export was written. -/
  key? : Option ExportKey := none
  /-- Without an export: how the replay ends (`overExport`, `timedOut`, `failed`). -/
  stop? : Option Replay.Outcome := none
  /-- With `stop?` of `failed`: why. -/
  message : Option String := none
deriving Inhabited, Repr, ToJson, FromJson

/-- The first half of a replay: take the declarations `targets` from the loaded modules
`loaded`, walk what they depend on for the axioms, and write those that rest on Lean's standard
three axioms at most, with everything they depend on, to `file` (the module docstring says how).
A declaration that rests on another axiom is left out of the export (`Prepared.axioms`): both
checkers decline a whole export that uses one. -/
def prepareExport (loaded : LoadedModules) (projectDirs : Array FilePath)
    (targets : Array ReplayTarget) (file : FilePath) (exportLimit? : Option Nat)
    (deadline : Nat) : IO Prepared := do
  let env := loaded.env
  -- the declarations the loaded modules have where the site's data places them
  let mut roots : Array Name := #[]
  let mut seen : NameHashSet := {}
  let mut notCovered : Array (Name × String) := #[]
  for target in targets do
    if seen.contains target.name then continue
    seen := seen.insert target.name
    let leaveOut (why : String) := notCovered.push (target.name, why)
    match env.find? target.name with
    | none =>
      let why := match target.module? with
        | some m => if loaded.notCompiled.contains m then
            s!"is not compiled: module {m} has no compiled file on the search path"
          else "is not in the compiled modules that were loaded"
        | none => "is not in the compiled modules that were loaded"
      notCovered := leaveOut why
    | some info =>
      let module? := (env.getModuleIdxFor? target.name).bind fun idx =>
        env.header.moduleNames[idx.toNat]?
      if info.isUnsafe then
        notCovered := leaveOut "is unsafe code, which a kernel does not check"
      else if target.module?.any (some · != module?) then
        notCovered := leaveOut s!"is in module {(module?.map toString).getD "?"} in the \
          compiled modules that were loaded, not in {(target.module?.map toString).getD "?"}"
      else roots := roots.push target.name
  let sorted := notCovered.qsort (·.1.toString < ·.1.toString)
  let failed (base : Prepared) (message : String) : Prepared :=
    { base with stop? := some .failed, message := some message }
  if roots.isEmpty then
    return failed { declarations := #[], notCovered := sorted }
      "none of the site's Lean declarations is \
      in the compiled modules that were loaded"
  let axioms ← match restingAxioms env roots with
    | .ok axioms => pure (axioms.qsort (·.1.toString < ·.1.toString))
    | .error message =>
      return failed { declarations := replayOrder roots, notCovered := sorted } message
  -- what rests on another axiom is not exported: the checkers would decline the whole export
  let resting : NameHashSet := axioms.foldl (init := {}) fun set (d, _) => set.insert d
  let checkable := roots.filter (!resting.contains ·)
  let base : Prepared := { declarations := replayOrder checkable, notCovered := sorted, axioms }
  if checkable.isEmpty then
    return failed base "every Lean declaration of the site that was found rests on an axiom \
      outside Lean's standard three, so none was exported"
  -- the export, written and hashed from the environment in memory
  let exported ← try writeExport env checkable file exportLimit? deadline
    catch e => return { base with stop? := some .failed, message := some s!"the export failed: {e}" }
  let (constants, key) ← match exported with
    | .ok written => pure written
    | .error .overExport => return { base with stop? := some .overExport }
    | .error .timedOut => return { base with stop? := some .timedOut }
  -- the exporter leaves out what it cannot export; a root it left out was not checked
  let exportedSet : NameHashSet := constants.foldl (init := {}) fun set c => set.insert c
  if let some missing := checkable.find? (!exportedSet.contains ·) then
    return failed base s!"the export does not hold {missing}"
  return { base with
    constants := constants.size, origins := originsOf loaded projectDirs constants
    key? := some key }

/-- The identity of a checker program in the record's key: its name, the SHA-256 of its file
and its Lean version. -/
def checkerIdentity (name : String) (program : FilePath) (version : Option String) :
    IO (String × Option String) := do
  let sha? ← try some <$> (Sha256.hex <$> IO.FS.readBinFile program) catch _ => pure none
  return (s!"{name} {sha?.getD "?"} {version.getD "?"}", sha?)

/-- The second half of a replay: have both checkers of `toolchain` check the export `file` that
`prepared` describes, one after the other, unless the record has it as accepted by both, and give
the replay's result. Before a checker runs, the file must be the one the worker wrote (its size)
and end with a complete line; its declaration records are counted (`exportCensus`) for the
checkers' counts to be held to. -/
def checkExport (config : ReplayConfig) (toolchain : Toolchain) (prepared : Prepared)
    (file : FilePath) (deadline : Nat) : IO Replay.Result := do
  let say (line : String) : IO Unit := do
    if config.progress then IO.eprintln s!"Kernel replay: {line}"
  let version := toolchain.version
  let base : Replay.Result := {
    outcome := .failed, version, declarations := prepared.declarations
    checker := " and ".intercalate (toolchain.checkers.map (·.1)).toList
    notCovered := prepared.notCovered, axioms := prepared.axioms
    constants := prepared.constants, origins := prepared.origins }
  let finish (result : Replay.Result) : IO Replay.Result := do
    say (match result.outcome with
      | .accepted => s!"accepted by both checkers, {counted result.constants "constant"}"
      | .rejected | .disagreed => result.rejectionText
      | _ => result.whyNot)
    return result
  let key ← match prepared.key?, prepared.stop? with
    | some key, none => pure key
    | _, some .overExport =>
      return ← finish { base with outcome := .overExport, exportLimit := config.exportLimit? }
    | _, some .timedOut =>
      return ← finish { base with outcome := .timedOut, limitSeconds := some config.limitSeconds }
    | _, _ =>
      return ← finish { base with message := prepared.message <|> some "no export was written" }
  let census ← try exportCensus file catch e =>
    return ← finish { base with message := some s!"the export could not be read: {e}" }
  if census.bytes != key.bytes || !census.endsWithNewline then
    return ← finish { base with message := some s!"the export file is not the one that was \
      written ({census.bytes} bytes, {key.bytes} written{if census.endsWithNewline then "" else
        ", and its last line is not complete"})" }
  -- both checkers accept an export without a declaration with status 0: that is no acceptance
  if census.records == 0 then
    return ← finish { base with message := some "the export holds no declaration record" }
  let base := { base with records := census.records }
  let mut ids := #[]
  let mut shas := #[]
  for (name, program) in toolchain.checkers do
    let (id, sha?) ← checkerIdentity name program version
    ids := ids.push id
    shas := shas.push sha?
  let recordKey := Sha256.hexOfString
    s!"export 2\n{"\n".intercalate ids.toList}\n{key.bytes}\n{key.hash}\n{census.records}"
  let recorded ← readRecord config.record?
  if recorded.contains recordKey then
    say s!"an identical export ({mebibytes key.bytes} MiB) was accepted by both checkers before"
    let checkers := (toolchain.checkers.zip shas).map fun ((name, _), sha256) =>
      ({ name, version, sha256, answer := .accepted } : Replay.CheckerRun)
    return ← finish { base with outcome := .accepted, recorded := true, checkers }
  let mut runs : Array Replay.CheckerRun := #[]
  for ((name, program), sha256) in toolchain.checkers.zip shas do
    say s!"checking {counted prepared.constants "constant"} ({mebibytes key.bytes} MiB, \
      {counted census.records "declaration record"}) with {name}"
    let start ← IO.monoMsNow
    let ending ← runLimited program.toString
      #["--verified", s!"--jobs={config.jobs}", file.toString] #[] deadline config.memoryLimit?
    let ms := (← IO.monoMsNow) - start
    let run : Replay.CheckerRun := { name, version, sha256, answer := .noAnswer, ms := some ms }
    let run ← match ending with
      | .notStarted error =>
        pure { run with answer := .notStarted, message := some (clip error) }
      | .timedOut => pure { run with answer := .timedOut }
      | .overMemory => pure { run with answer := .overMemory }
      | .exited code stdout stderr peak =>
        let (answer, declarations, message) := parseAnswer code stdout stderr census.records
        say s!"{name} ran for {usedText ms peak}"
        pure { run with answer, declarations, message
                        peakBytes := if peak == 0 then none else some peak }
    runs := runs.push run
  let (outcome, message) := combineRuns runs
  let result := { base with outcome, message, checkers := runs }
  let result := match outcome with
    | .timedOut => { result with limitSeconds := some config.limitSeconds }
    | .overMemory => { result with memoryLimit := config.memoryLimit? }
    | _ => result
  if outcome == .accepted then addToRecord config.record? recordKey
  finish result

/-- How a worker process ended (`runWorker`). -/
inductive WorkerEnd where
  /-- It exited with status 0; `used` says how long it ran and how much memory it held. -/
  | done (used : String)
  /-- It was stopped at the time limit. -/
  | timedOut
  /-- It was stopped over the memory limit. -/
  | overMemory
  /-- It could not be started, or exited with another status: what it said. -/
  | failed (message : String)
deriving Repr, Inhabited, DecidableEq

/-- Run the worker of `config` on the request file `request`, for the reply file `reply`, under
the time limit `deadline` and the memory limit of `config`, with `LEAN_SYSROOT` set to `sysroot`,
the toolchain whose library the modules are loaded on. -/
def runWorker (config : ReplayConfig) (sysroot : FilePath) (request reply : FilePath)
    (deadline : Nat) : IO WorkerEnd := do
  let some (program, args) := config.worker? | return .failed "no worker program is known"
  let start ← IO.monoMsNow
  -- the exporter's toolchain: without `LEAN_SYSROOT` Lean would look for one by running `lean`
  let env := #[("LEAN_SYSROOT", some sysroot.toString)]
  let ending ← runLimited program.toString (args ++ #[request.toString, reply.toString]) env
    deadline config.memoryLimit?
  match ending with
  | .timedOut => return .timedOut
  | .overMemory => return .overMemory
  | .notStarted error => return .failed s!"the export process could not be started: {clip error}"
  | .exited 0 _ _ peak => return .done (usedText ((← IO.monoMsNow) - start) peak)
  | .exited code _ stderr _ =>
    return .failed s!"the export process ended with status {code}: {clip stderr}"

end Informal.Stats
