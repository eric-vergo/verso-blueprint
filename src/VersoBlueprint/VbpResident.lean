/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

import Lean.Elab.Frontend
import Lean.Elab.Import
import Lean.Language.Lean
import Lake.Build.Module
import Lake.Build.Run
import Lake.Load.Workspace
import VersoBlueprint
import VersoBlueprint.PreviewManifest
import VersoBlueprint.Resident
import VersoBlueprint.VbpComparator

/-!
# Resident build session (`vbp build --resident`)

A session builds the site once, keeps the generator's environment, the evaluated document and the
highlighted sources in memory, and rebuilds whenever a request line arrives on standard input:

* `build`: rebuild what changed since the last build;
* `build --full`: let Lake build the generator's imports and load them again;
* `quit` (or the end of the input): end the session.

Each build ends with one line on standard output,
`vbp resident: done exit=<code> mode=<mode> ms=<wall time> chapters=<modules>`; `mode` is `full`
(Lake build and load), `chapters` (included chapters elaborated in-process) or `unchanged` (nothing
changed; the generator ran again). A change of the workspace configuration (lakefile, manifest,
toolchain, package overrides) ends the session with `vbp resident: restart (<file> changed)`
and exit code 3: the caller starts a new one.

**Chapters.** A module of the generator's import closure is a *chapter* when it is a Verso document
included by the document root (the `%doc` module of the generator), is imported by the root and by
nothing else in the closure. When only chapters changed (and none of their headers), each changed
chapter is elaborated on an environment of its own imports (imported once and kept), its new part
replaces the old one in the document, the Blueprint state is rebuilt with its new entries, and the
generator's `main` runs again with both (`Informal.Resident.apply`). The chapter's `.olean` is not
rewritten: until the next Lake build the session keeps substituting it. Any other change takes the
Lake path.

Native code comes from this executable: the precompiled libraries of packages linked into `vbp`
are not loaded again (loading a second copy of a module duplicates its global state); other
plugins listed by Lake are loaded as `lake lean` loads them.
-/

namespace VersoBlueprint.Vbp.Resident

open Lean Elab
open System
open Verso Doc
open Verso.Genre (Manual)

/-- The bytes of a file, hashed (`none` when it cannot be read). -/
def fileHash? (path : FilePath) : IO (Option UInt64) := do
  try
    return some (hash (← IO.FS.readBinFile path))
  catch _ =>
    return none

/-- One source module of the generator's import closure inside the workspace. -/
structure SourceModule where
  name : Name
  file : FilePath
  imports : Array Name
  /-- Whether the header says `module` (the module system). -/
  isModule : Bool := false
  hash : UInt64
deriving Inhabited

/-- Where the session's sources stood when they were last loaded or substituted. -/
structure Sources where
  generatorHash : UInt64
  /-- In import order: a module comes after the modules it imports. -/
  modules : Array SourceModule := #[]
  /-- Workspace configuration files and their hashes. -/
  config : Array (FilePath × Option UInt64) := #[]
deriving Inhabited

/-- Whether `file` is a source the user edits (not a checkout under `.lake`). -/
def isWorkspaceSource (file : FilePath) : Bool :=
  !((file.toString.splitOn "/.lake/").length > 1)

/-- The header of a Lean file. -/
def readHeader (file : FilePath) : IO ModuleHeader := do
  Lean.parseImports' (← IO.FS.readFile file) file.toString

/-- The imports of a Lean file's header. -/
def headerImports (file : FilePath) : IO (Array Name) := do
  return (← readHeader file).imports.map (·.module)

/--
The workspace source modules reachable from `roots` through imports, each after its imports.
Imports that resolve to no workspace source (dependencies) are not followed.
-/
partial def scanModules (ws : Lake.Workspace) (roots : Array Name) : IO (Array SourceModule) := do
  let (_, (_, out)) ← (roots.forM visit).run ({}, #[])
  return out
where
  visit (name : Name) : StateT (NameSet × Array SourceModule) IO Unit := do
    if (← get).1.contains name then return
    modify fun (seen, out) => (seen.insert name, out)
    let some mod := ws.findModule? name | return
    let file := mod.leanFile
    unless isWorkspaceSource file do return
    let some hash ← fileHash? file | return
    let header ← readHeader file
    let imports := header.imports.map (·.module)
    imports.forM visit
    modify fun (seen, out) => (seen, out.push { name, file, imports, isModule := header.isModule, hash })

/-- The configuration files whose change ends the session. -/
def configFiles (ws : Lake.Workspace) : Array FilePath := Id.run do
  let root := ws.root.dir
  let mut files : Array FilePath := #[root / "lean-toolchain", root / "lake-manifest.json",
    root / ".lake" / "package-overrides.json"]
  for pkg in ws.packages do
    if isWorkspaceSource pkg.dir then
      files := files.push (pkg.dir / pkg.configFile)
  return files

/-- The module of the generator's `%doc X`, if any. -/
def docModuleOf? (generatorText : String) : Option Name :=
  generatorText.splitOn "\n" |>.findSome? fun line =>
    match line.splitOn "%doc " with
    | _ :: after :: _ =>
      (after.replace ")" " ").trimAscii.toString.splitOn " " |>.filter (!·.isEmpty) |>.head?
        |>.map String.toName
    | _ => none

/--
The chapters of a closure: modules imported by `root` and by no other module of the closure
(the generator file included, through `generatorImports`), outside the module system.
-/
def chaptersOf (modules : Array SourceModule) (generatorImports : Array Name) (root : Name) :
    NameSet := Id.run do
  let some rootModule := modules.find? (·.name == root) | return {}
  let mut chapters : NameSet := {}
  for name in rootModule.imports do
    if !(modules.any fun m => m.name == name && !m.isModule) then continue
    if generatorImports.contains name then continue
    if modules.any fun m => m.name != root && m.imports.contains name then continue
    chapters := chapters.insert name
  return chapters

/-- What a request needs, from the sources as loaded and as they are now. -/
inductive Plan where
  | unchanged
  /-- Only these chapters changed (their headers did not). -/
  | chapters (modules : Array Name)
  /-- Something else changed: Lake builds and the session loads again. -/
  | lake (reason : String)
  /-- The workspace configuration changed. -/
  | restart (file : FilePath)
deriving Inhabited, Repr, BEq

/-- Decide the plan (pure; `now` re-scans the same closure). -/
def plan (loaded now : Sources) (chapters : NameSet) : Plan := Id.run do
  for (file, hash) in now.config do
    if (loaded.config.find? (·.1 == file) |>.map (·.2)) != some hash then
      return .restart file
  if loaded.generatorHash != now.generatorHash then
    return .lake "the generator file changed"
  if loaded.modules.map (·.name) != now.modules.map (·.name) then
    return .lake "the set of imported workspace modules changed"
  let mut changed := #[]
  for (old, new) in loaded.modules.zip now.modules do
    if old.hash == new.hash then continue
    if !chapters.contains new.name then
      return .lake s!"{new.name} changed and is not an included chapter"
    if old.imports != new.imports then
      return .lake s!"the imports of {new.name} changed"
    changed := changed.push new.name
  return if changed.isEmpty then .unchanged else .chapters changed

/-- A request read from standard input. -/
inductive Request where
  /-- Rebuild what changed (`full`: let Lake build and load again). -/
  | build (full : Bool)
  /-- Elaborate a chapter (module name or source path) so that its next rebuild reuses its imports. -/
  | prepare (target : String)
  | quit
deriving Inhabited, Repr, BEq

/-- Parse one request line. -/
def parseRequest (line : String) : Except String Request :=
  match line.trimAscii.toString.splitOn " " |>.filter (!·.isEmpty) with
  | [] | ["build"] => .ok (.build false)
  | ["build", "--full"] => .ok (.build true)
  | ["prepare", target] => .ok (.prepare target)
  | ["quit"] => .ok .quit
  | _ => .error s!"unknown request '{line.trimAscii}'; expected `build`, `build --full`, `prepare <chapter>` or `quit`"

/-! ## Loading -/

/-- The setup Lake prepares for `lake lean <file>` (building the file's imports). -/
def generatorSetup (ws : Lake.Workspace) (file : FilePath) : IO ModuleSetup := do
  let spawn ← ws.runBuild (Lake.prepareLeanCommand file)
  let rec find : List String → Option String
    | "--setup" :: path :: _ => some path
    | _ :: rest => find rest
    | [] => none
  let some path := find spawn.args.toList
    | throw <| IO.userError s!"Lake prepared no setup for {file}"
  let setup ← ModuleSetup.load path
  try IO.FS.removeFile path catch _ => pure ()
  return setup

/-- The setup of a workspace module (its imports built). -/
def moduleSetup (ws : Lake.Workspace) (name : Name) : IO ModuleSetup := do
  let some mod := ws.findModule? name
    | throw <| IO.userError s!"module {name} is not part of the workspace"
  ws.runBuild mod.setup.fetch

/-- The packages whose code is linked into this executable (VersoBlueprint and its dependencies). -/
partial def linkedPackageDirs (ws : Lake.Workspace) : Array FilePath := Id.run do
  let rec go (fuel : Nat) (todo : List Name) (seen : NameSet) (dirs : Array FilePath) :=
    match fuel, todo with
    | 0, _ | _, [] => dirs
    | fuel + 1, name :: todo =>
      if seen.contains name then go fuel todo seen dirs else
      match ws.findPackageByName? name with
      | none => go fuel todo (seen.insert name) dirs
      | some pkg =>
        go fuel (todo ++ (pkg.depConfigs.map (·.name)).toList) (seen.insert name) (dirs.push pkg.dir)
  go 1000 [`VersoBlueprint] {} #[]

/-- Load the plugins and dynamic libraries of a setup that are not linked into this executable. -/
def loadForeignNative (ws : Lake.Workspace) (setup : ModuleSetup) : IO Unit := do
  let sysroot ← findSysroot
  let linked := (linkedPackageDirs ws).map (·.toString)
  let isLinked (path : FilePath) : Bool :=
    path.toString.startsWith sysroot.toString || linked.any (path.toString.startsWith ·)
  for dynlib in setup.dynlibs do
    unless isLinked dynlib do Lean.loadDynlib dynlib
  for plugin in setup.plugins do
    unless isLinked plugin.path do Lean.loadPlugin plugin.path plugin.initFn?

/-- One elaboration of a file, as `lean --setup` elaborates it. -/
structure Elaborated where
  env : Environment
  /-- The options in effect at the end of the file. -/
  opts : Options
  hasErrors : Bool
  /-- Lets the next elaboration of the same file reuse its imports when its header is unchanged. -/
  snapshot : Lean.Language.Lean.InitialSnapshot

/--
Elaborate a file through Lean's own processing pipeline with the options and imports of `setup`,
exactly as `lean --setup` does (`Lean.Elab.runFrontend`), and print its messages as `lean`
prints them. `old?`, the snapshot of the previous elaboration of the same file, lets Lean reuse
the imported environment when the header did not change.
-/
def elaborateFile (file : FilePath) (setup : ModuleSetup)
    (old? : Option Lean.Language.Lean.InitialSnapshot := none) : IO Elaborated := do
  let input ← IO.FS.readFile file
  let inputCtx := Parser.mkInputContext input file.toString
  -- like `lean`, but keeping full snapshots (`cmdlineSnapshots` drops what reuse needs)
  let opts := Lean.internal.cmdlineSnapshots.setIfNotSet ({} : Options) false
  let opts := Elab.async.setIfNotSet opts true
  let setupImports (stx : HeaderSyntax) : Lean.Language.ProcessingT IO
      (Except Lean.Language.Lean.HeaderProcessedSnapshot Lean.Language.Lean.SetupImportsResult) := do
    return .ok {
      trustLevel := 1024
      package? := setup.package?
      mainModuleName := setup.name
      isModule := strictOr setup.isModule stx.isModule
      imports := setup.imports?.getD stx.imports
      importArts := setup.importArts
      opts := opts.mergeBy (fun _ _ setupValue => setupValue) setup.options.toOptions
    }
  -- importing resets the flag (`withImporting`), so set it before every elaboration
  unsafe enableInitializersExecution
  let snapshot ← Lean.Language.Lean.process setupImports old? { inputCtx with }
  let hasErrors ← (Lean.Language.toSnapshotTree snapshot).runAndReport opts
  let some cmdState := Lean.Language.Lean.waitForFinalCmdState? snapshot
    | throw <| IO.userError s!"importing the imports of {file} failed"
  return { env := cmdState.env, opts := cmdState.scopes[0]!.opts, hasErrors, snapshot }

/-- `VersoDoc.toPart` of a module's document constant. -/
unsafe def documentPartImpl (env : Environment) (opts : Options) (module : Name) :
    IO (Part Manual) := do
  let doc ← IO.ofExcept <| env.evalConst (VersoDoc Manual) opts (docName module) (checkMeta := false)
  return doc.toPart

@[implemented_by documentPartImpl]
opaque documentPart (env : Environment) (opts : Options) (module : Name) : IO (Part Manual)

/-- The generator's `main`, in either common signature. -/
unsafe def generatorMainImpl (env : Environment) (opts : Options) :
    IO (List String → IO UInt32) := do
  match env.evalConst (List String → IO UInt32) opts `main (checkMeta := false) with
  | .ok main => return main
  | .error _ =>
    let main ← IO.ofExcept <| env.evalConst (IO UInt32) opts `main (checkMeta := false)
    return fun _ => main

@[implemented_by generatorMainImpl]
opaque generatorMain (env : Environment) (opts : Options) : IO (List String → IO UInt32)

/-- The render model of `env`'s Blueprint state with some modules' entries replaced. -/
def modelReplacing (env : Environment) (opts : Options) (file : FilePath)
    (replacements : Lean.NameMap (Array Informal.Environment.Entry)) : IO Informal.RenderModel := do
  let state ← Informal.Environment.stateReplacingModules env opts replacements
  let env := Informal.Environment.informalExt.setState env state
  let (json, _) ← Informal.RenderModel.captureJson.toIO
    { fileName := file.toString, fileMap := default, options := opts } { env }
  return Informal.RenderModel.fromJsonString! json

/-! ## The session -/

/-- A chapter elaborated in-process since the last load. -/
structure Rebuilt where
  hash : UInt64
  update : Informal.Resident.ChapterUpdate
  entries : Array Informal.Environment.Entry

/-- The generator as loaded by the last Lake build. -/
structure Loaded where
  env : Environment
  opts : Options
  main : List String → IO UInt32
  sources : Sources
  generatorImports : Array Name
  chapters : NameSet

structure Session where
  ws : Lake.Workspace
  generatorFile : FilePath
  generatorArgs : List String
  loaded? : Option Loaded := none
  /--
  Per chapter: its setup and its last elaboration, whose imports the next one reuses. At most
  `keptChapterEnvs`, the most recently elaborated ones (`recentChapters`, newest last).
  -/
  chapterEnvs : Lean.NameMap (ModuleSetup × Lean.Language.Lean.InitialSnapshot) := {}
  recentChapters : Array Name := #[]
  /-- Chapters substituted since the last load. -/
  rebuilt : Lean.NameMap Rebuilt := {}

/--
How many chapter environments a session keeps. Each holds an import of the chapter's whole
closure (on Mathlib-based projects about 2 GB), so only the chapters edited last are kept.
-/
def keptChapterEnvs : Nat := 2

/-- Keep `module`'s elaboration, dropping the oldest beyond `keptChapterEnvs`. -/
def Session.keepChapterEnv (s : Session) (module : Name) (setup : ModuleSetup)
    (snapshot : Lean.Language.Lean.InitialSnapshot) : Session := Id.run do
  let recent := (s.recentChapters.filter (· != module)).push module
  let dropped := recent.extract 0 (recent.size - keptChapterEnvs)
  let recent := recent.extract (recent.size - keptChapterEnvs) recent.size
  let envs := dropped.foldl (init := s.chapterEnvs) fun envs name => envs.erase name
  return { s with chapterEnvs := envs.insert module (setup, snapshot), recentChapters := recent }

/-- The sources now, over the closure of the generator's imports. -/
def scan (ws : Lake.Workspace) (generatorFile : FilePath) (imports : Array Name) : IO Sources := do
  let some generatorHash ← fileHash? generatorFile
    | throw <| IO.userError s!"cannot read {generatorFile}"
  let modules ← scanModules ws imports
  let config ← (configFiles ws).mapM fun file => return (file, ← fileHash? file)
  return { generatorHash, modules, config }

/-- Lake builds the generator's imports and the Comparator challenge; load the imports and the
generator. -/
def load (s : Session) : IO Session := do
  VersoBlueprint.Vbp.buildComparatorChallenge s.ws
  let setup ← generatorSetup s.ws s.generatorFile
  loadForeignNative s.ws setup
  let generator ← elaborateFile s.generatorFile setup
  if generator.hasErrors then throw <| IO.userError s!"{s.generatorFile} has errors"
  let env := generator.env
  let main ← generatorMain env generator.opts
  let generatorImports ← headerImports s.generatorFile
  let sources ← scan s.ws s.generatorFile generatorImports
  let chapters := match docModuleOf? (← IO.FS.readFile s.generatorFile) with
    | some root => (chaptersOf sources.modules generatorImports root).filter fun c =>
      env.contains (docName c)
    | none => {}
  Informal.DeclarationSource.clear
  return { s with
    loaded? := some { env, opts := generator.opts, main, sources, generatorImports, chapters }
    chapterEnvs := {}, recentChapters := #[], rebuilt := {} }

/-- Run the generator's `main`, substituting the rebuilt chapters. -/
def runGenerator (s : Session) (loaded : Loaded) : IO UInt32 := do
  if s.rebuilt.isEmpty then
    return ← loaded.main s.generatorArgs
  let replacements := s.rebuilt.foldl (init := {}) fun acc name r => acc.insert name r.entries
  let model ← modelReplacing loaded.env loaded.opts s.generatorFile replacements
  Informal.Resident.install {
    chapters := s.rebuilt.foldl (init := #[]) fun acc _ r => acc.push r.update
    model }
  let code ← try loaded.main s.generatorArgs finally discard Informal.Resident.uninstall
  return code

/-- Elaborate a chapter in-process, reusing its imports when they are kept. -/
def elaborateChapter (s : Session) (module : SourceModule) : IO (Session × Elaborated) := do
  let t0 ← IO.monoMsNow
  let (setup, old?) ← match s.chapterEnvs.find? module.name with
    | some (setup, snapshot) => pure (setup, some snapshot)
    | none => pure (← moduleSetup s.ws module.name, none)
  let t1 ← IO.monoMsNow
  let chapter ← elaborateFile module.file setup old?
  let t2 ← IO.monoMsNow
  IO.println s!"vbp resident: {module.name}: setup {t1 - t0} ms, elaboration {t2 - t1} ms{if old?.isSome then " (imports reused)" else ""}"
  return (s.keepChapterEnv module.name setup chapter.snapshot, chapter)

/-- Elaborate one changed chapter in-process; `none` when it has errors. -/
def rebuildChapter (s : Session) (loaded : Loaded) (module : SourceModule) :
    IO (Session × Option Rebuilt) := do
  let (s, chapter) ← elaborateChapter s module
  if chapter.hasErrors then return (s, none)
  let previous ← match s.rebuilt.find? module.name with
    | some r => pure r.update.previous
    | none => documentPart loaded.env loaded.opts module.name
  let replacement ← documentPart chapter.env chapter.opts module.name
  let entries := Informal.Environment.localEntries chapter.env
  return (s, some { hash := module.hash, update := { module := module.name, previous, replacement }, entries })

/-- The outcome of one request. -/
structure Outcome where
  code : UInt32
  mode : String
  chapters : Array Name := #[]
  restart? : Option String := none

/-- Serve one build request. -/
def build (s : Session) (full : Bool) : IO (Session × Outcome) := do
  let lakePath (s : Session) : IO (Session × Outcome) := do
    let s ← load s
    let some loaded := s.loaded? | return (s, { code := 1, mode := "full" })
    return (s, { code := ← runGenerator s loaded, mode := "full" })
  let some loaded := s.loaded? | lakePath s
  if full then return ← lakePath s
  let now ← scan s.ws s.generatorFile loaded.generatorImports
  -- the reference for a substituted chapter is its last substituted text
  let reference := { loaded.sources with
    modules := loaded.sources.modules.map fun m =>
      match s.rebuilt.find? m.name with
      | some r => { m with hash := r.hash }
      | none => m }
  match plan reference now loaded.chapters with
  | .restart file => return (s, { code := 3, mode := "restart", restart? := some s!"{file} changed" })
  | .lake reason =>
    IO.println s!"vbp resident: {reason}; Lake builds the generator's imports"
    lakePath s
  | .unchanged => return (s, { code := ← runGenerator s loaded, mode := "unchanged" })
  | .chapters names =>
    let mut session := s
    for name in names do
      let some module := now.modules.find? (·.name == name) | continue
      IO.println s!"vbp resident: elaborating {name} in-process"
      (← IO.getStdout).flush
      let (next, rebuilt?) ← rebuildChapter session loaded module
      session := next
      let some rebuilt := rebuilt?
        | return (session, { code := 1, mode := "chapters", chapters := names })
      session := { session with rebuilt := session.rebuilt.insert name rebuilt }
    try
      return (session, { code := ← runGenerator session loaded, mode := "chapters", chapters := names })
    catch err =>
      IO.eprintln s!"vbp resident: {err}; Lake builds the generator's imports"
      let (after, outcome) ← lakePath session
      return (after, { outcome with chapters := names })

/-- Serve a `prepare` request: elaborate the chapter now, keep its imports for its next rebuild. -/
def prepareChapter (s : Session) (target : String) : IO (Session × Outcome) := do
  let some loaded := s.loaded? | return (s, { code := 1, mode := "prepare" })
  let isTarget (m : SourceModule) := m.name.toString == target || m.file.toString == target ||
    m.file.toString.endsWith ("/" ++ target)
  let some module := loaded.sources.modules.find? isTarget
    | return (s, { code := 0, mode := "prepare" })
  unless loaded.chapters.contains module.name do return (s, { code := 0, mode := "prepare" })
  -- already kept: its next rebuild reuses its imports anyway
  if s.chapterEnvs.contains module.name then
    return (s, { code := 0, mode := "prepare", chapters := #[module.name] })
  let some hash ← fileHash? module.file | return (s, { code := 1, mode := "prepare" })
  let (s, _) ← elaborateChapter s { module with hash }
  return (s, { code := 0, mode := "prepare", chapters := #[module.name] })

/-- The line that ends every build. -/
def doneLine (outcome : Outcome) (ms : Nat) : String :=
  let chapters := ",".intercalate (outcome.chapters.toList.map toString)
  s!"vbp resident: done exit={outcome.code} mode={outcome.mode} ms={ms} chapters={chapters}"

/-- Run a session: build once, then once per request line. -/
partial def run (ws : Lake.Workspace) (generatorFile : FilePath) (generatorArgs : List String) :
    IO UInt32 := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let rec serve (s : Session) (request : Request) : IO UInt32 := do
    let t0 ← IO.monoMsNow
    let (s, outcome) ← try
        match request with
        | .prepare target => prepareChapter s target
        | .build full => build s full
        | .quit => pure (s, { code := 0, mode := "quit" })
      catch err => do
        IO.eprintln s!"vbp resident: {err}"
        pure ({ s with loaded? := none }, { code := 1, mode := "full" })
    if let some why := outcome.restart? then
      IO.println s!"vbp resident: restart ({why})"
      stdout.flush
      return 3
    IO.println (doneLine outcome ((← IO.monoMsNow) - t0))
    stdout.flush
    let rec next : IO UInt32 := do
      let line ← stdin.getLine
      if line.isEmpty then return 0
      match parseRequest line with
      | .error err =>
        IO.eprintln s!"vbp resident: {err}"
        stdout.flush
        next
      | .ok .quit => return 0
      | .ok request => serve s request
    next
  serve { ws, generatorFile, generatorArgs } (.build false)

end VersoBlueprint.Vbp.Resident
