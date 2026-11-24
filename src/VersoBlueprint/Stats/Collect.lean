/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

import Lean.Meta.Instances
import Lean.Meta.Match.MatcherInfo
import VersoBlueprint.Axioms
import VersoBlueprint.Environment
import VersoBlueprint.Graph
import VersoBlueprint.Stats.Claims
import VersoBlueprint.Stats.Data
import VersoBlueprint.Stats.RunReplay

/-!
Collects `ProjectStats` from the checked environment, the Blueprint state, its dependency graph
and the files of the project.

The project root is the working directory, which is the workspace root when Lake builds or runs
the generator; a Blueprint that is a package of its own inside the project it describes names
the project's root with the option `verso.blueprint.projectRoot`, and its own folder is then left
out of the project's files. The project's modules are the modules of the environment whose source file lies
inside the project root and outside its `.lake` directory, in a source directory of one of the
workspace's packages there (`WorkspaceLayout.ofSearchPaths`). Every `.lean` file under the root
is scanned; a file that is not one of those modules counts as compiled when a library directory
of those packages holds its `.olean`.

The files at the root are read when the model is captured and again when the generator runs
(`ProjectStats.refreshWorkspace`), so README, license and source edits that no Lean module
depends on still reach the site.
-/

namespace Informal.Stats

open Lean
open Informal Data Environment

/-! ## Paths -/

/-- `path` relative to `root`, when it lies inside it (`"."` for the root itself). -/
def relativeTo? (root path : System.FilePath) : Option String :=
  let root := root.toString
  let path := path.toString
  let sep := System.FilePath.pathSeparator.toString
  let rootPrefix := if root.endsWith sep then root else root ++ sep
  if path == root then some "."
  else if path.startsWith rootPrefix then
    some ((path.drop rootPrefix.length).copy.replace sep "/")
  else none

/-- The relative path of a module's source or compiled file below a directory. -/
def modulePath (module : Name) (ext : String) : String :=
  "/".intercalate (module.components.map (·.toString (escape := false))) ++ "." ++ ext

/-- `dir/rel`, where `dir` is `"."` for the root itself. -/
private def joinRel (dir rel : String) : String :=
  if dir == "." then rel else dir ++ "/" ++ rel

private def components (rel : String) : List String := rel.splitOn "/"

/-- The suffix of a package's directory of compiled modules. -/
private def libraryDirSuffix : String := ".lake/build/lib/lean"

/-- The package directory of a library directory (`"Local/.lake/build/lib/lean"` gives
`"Local"`, `".lake/build/lib/lean"` gives `"."`). -/
private def packageDirOf? (libraryDir : String) : Option String :=
  if libraryDir == libraryDirSuffix then some "."
  else if libraryDir.endsWith ("/" ++ libraryDirSuffix) then
    some (libraryDir.dropEnd (libraryDirSuffix.length + 1)).copy
  else none

/-- The non-hidden subdirectories of `dir`, relative to the root. -/
private def subdirectories (root : System.FilePath) (dir : String) : IO (Array String) := do
  let entries ← try (root / dir).readDir catch _ => pure #[]
  let mut out := #[]
  for entry in entries do
    if entry.fileName.startsWith "." then continue
    let isDir ← try pure ((← entry.path.symlinkMetadata).type == .dir) catch _ => pure false
    if isDir then out := out.push (joinRel dir entry.fileName)
  return out

/-- Where to look for the project's sources and compiled modules inside `root`, from a source
search path and a library search path.

Library directories are those inside the project but not under `.lake/packages`, where Lake
keeps dependencies. Lake does not pass a source search path to the modules it compiles, so the
source directories are guessed: the entries of the source path inside the project and outside
`.lake`, the project root and every package directory inside it (the directory of a library
directory), and the subdirectories of those, where library source directories usually are.
`projectModules` keeps the ones that hold a module. -/
def WorkspaceLayout.ofSearchPaths (root : System.FilePath)
    (srcPath libPath : System.SearchPath) : IO WorkspaceLayout := do
  let inside (path : System.SearchPath) (keep : String → Bool) : IO (Array String) := do
    let mut out := #[]
    for dir in path do
      let some real ← (try some <$> IO.FS.realPath dir catch _ => pure none) | continue
      unless ← real.isDir do continue
      if let some rel := relativeTo? root real then
        if keep rel && !out.contains rel then out := out.push rel
    return out
  let libraryDirs ← inside libPath fun rel =>
    let cs := components rel
    !(cs.zip cs.tail).contains (".lake", "packages")
  let packageDirs := #["."] ++ libraryDirs.filterMap packageDirOf?
  let mut candidates ← inside srcPath fun rel => !(components rel).contains ".lake"
  for dir in packageDirs do
    candidates := candidates.push dir ++ (← subdirectories root dir)
  let sourceDirs := candidates.foldl (init := #[]) fun acc d =>
    if acc.contains d then acc else acc.push d
  return { sourceDirs := sourceDirs.qsort (· < ·), libraryDirs := libraryDirs.qsort (· < ·) }

/-- The working directory, with symbolic links resolved. -/
def workingDirectory : IO System.FilePath := do
  let cwd ← IO.currentDir
  try IO.FS.realPath cwd catch _ => pure cwd

register_option verso.blueprint.projectRoot : String := {
  defValue := ""
  descr := "The root of the project the Blueprint describes, relative to the working directory \
    (default: the working directory). A Blueprint that is a Lake package of its own inside the \
    project sets `..`, so that the Project Stats page reports on the project: its README, \
    license, sources and Comparator challenge."
}

/-- The project root: the working directory, or the folder `relative` names from there (the
option `verso.blueprint.projectRoot`), with symbolic links resolved. -/
def projectRoot (relative : Option String := none) : IO System.FilePath := do
  let cwd ← workingDirectory
  match relative.filter (!·.trimAscii.isEmpty) with
  | none => pure cwd
  | some rel =>
    let root := cwd / rel.trimAscii.copy
    try IO.FS.realPath root catch _ => pure root

/-- The Blueprint package's own folder relative to `root`, when the working directory is a
folder inside the project root and not the root itself: its files are the Blueprint's, not the
project's. -/
def blueprintFolder? (root : System.FilePath) : IO (Option String) := do
  let cwd ← workingDirectory
  return (relativeTo? root cwd).filter (· != ".")

/-- Whether the path `rel` (relative to the project root) is `folder` or inside it. -/
def insideFolder (folder : Option String) (rel : String) : Bool :=
  folder.any fun f => rel == f || rel.startsWith (f ++ "/")

/-- The layout of the running process's workspace, from `LEAN_SRC_PATH` and the library search
path (`LEAN_PATH` and the one Lean was initialised with). -/
def WorkspaceLayout.current (root : System.FilePath) : IO WorkspaceLayout := do
  let libPath := (← searchPathRef.get) ++
    ((← IO.getEnv "LEAN_PATH").map System.SearchPath.parse |>.getD [])
  let layout ← WorkspaceLayout.ofSearchPaths root (← getSrcSearchPath) libPath
  -- A Blueprint package inside the project is not part of the project it describes.
  let own ← blueprintFolder? root
  return { layout with
    sourceDirs := layout.sourceDirs.filter (!insideFolder own ·)
    libraryDirs := layout.libraryDirs.filter (!insideFolder own ·) }

/-! ## Declarations -/

/-- The kind a declaration is counted as, or `none` for declarations Lean generates (recursors,
constructors, `noConfusion`, matchers, projections, equation lemmas, internal names). -/
def declarationKind? (env : Environment) (info : ConstantInfo) : Option String := do
  let name := info.name
  if (privateToUserName name).isInternalDetail then none
  if isAuxRecursor env name || isNoConfusion env name || isRecCore env name ||
      Meta.isMatcherCore env name || isReservedName env name || env.isProjectionFn name then
    none
  -- Injectivity and size theorems generated for each constructor.
  if let .str parent last := name then
    if (last == "inj" || last == "injEq" || last == "sizeOf_spec") &&
        (env.find? parent).any (·.isCtor) then
      none
  if Meta.isInstanceCore env name then return "instances"
  match info with
  | .thmInfo _ => some "theorems"
  | .defnInfo _ => some "definitions"
  | .axiomInfo _ => some "axioms"
  | .opaqueInfo _ => some "opaques"
  | .inductInfo _ =>
    if isClass env name then some "classes"
    else if isStructure env name then some "structures"
    else some "inductives"
  | _ => none

/-- Add one declaration of the given kind. -/
def DeclarationCounts.add (c : DeclarationCounts) : String → DeclarationCounts
  | "theorems" => { c with theorems := c.theorems + 1 }
  | "definitions" => { c with definitions := c.definitions + 1 }
  | "instances" => { c with instances := c.instances + 1 }
  | "structures" => { c with structures := c.structures + 1 }
  | "classes" => { c with classes := c.classes + 1 }
  | "inductives" => { c with inductives := c.inductives + 1 }
  | "axioms" => { c with axioms := c.axioms + 1 }
  | "opaques" => { c with opaques := c.opaques + 1 }
  | _ => c

instance : Add DeclarationCounts where
  add a b := {
    theorems := a.theorems + b.theorems, definitions := a.definitions + b.definitions
    instances := a.instances + b.instances, structures := a.structures + b.structures
    classes := a.classes + b.classes, inductives := a.inductives + b.inductives
    axioms := a.axioms + b.axioms, opaques := a.opaques + b.opaques }

/-- Count the declarations among `infos`. -/
def countDeclarations (env : Environment) (infos : Array ConstantInfo) : DeclarationCounts :=
  infos.foldl (init := {}) fun c info =>
    match declarationKind? env info with
    | some kind => c.add kind
    | none => c

/-- The project's modules of `env` with their source paths and declaration counts, sorted by
name, and the source directories of `layout` that hold them, sorted. A module is the project's
when its source file is in one of the source directories. The module being elaborated counts
too, with the declarations it has so far; `currentFile?` is its source path relative to the
root, for a file elaborated without a module name. -/
def projectModules (env : Environment) (root : System.FilePath) (layout : WorkspaceLayout)
    (currentFile? : Option String := none) :
    IO (Array (ModuleStats × DeclarationCounts) × Array String) := do
  -- The top-level names in each source directory, so that most modules need no file check.
  let mut tops : Array (String × Array String) := #[]
  for dir in layout.sourceDirs do
    let entries ← try (root / dir).readDir catch _ => pure #[]
    tops := tops.push (dir, entries.map (·.fileName))
  let sourceOf? (module : Name) : IO (Option (String × String)) := do
    let first := module.getRoot.toString (escape := false)
    for (dir, names) in tops do
      unless names.contains first || names.contains (first ++ ".lean") do continue
      let rel := joinRel dir (modulePath module "lean")
      if ← (root / rel).pathExists then return some (dir, rel)
    return none
  let mut out := #[]
  let mut used : Array String := #[]
  for h : idx in [0:env.header.moduleNames.size] do
    let module := env.header.moduleNames[idx]
    let some (dir, path) ← sourceOf? module | continue
    if !used.contains dir then used := used.push dir
    let infos := (env.header.moduleData[idx]?.map (·.constants)).getD #[]
    let counts := countDeclarations env infos
    out := out.push ({ name := module, path, declarations := counts.total }, counts)
  -- The file being elaborated: found by its module name, or, when it runs as a script
  -- (`lean --run`, which names no module), by its file name.
  let main := env.mainModule
  if !env.header.moduleNames.contains main then
    let found ← match ← sourceOf? main with
      | some (dir, path) => pure (some (dir, path, main))
      | none => pure <| currentFile?.map fun path =>
        (".", path, (path.dropEnd ".lean".length).copy.splitOn "/" |>.foldl Name.str .anonymous)
    if let some (dir, path, name) := found then
      unless out.any (·.1.path == path) do
        if !used.contains dir then used := used.push dir
        let infos := env.constants.foldStage2
          (fun (acc : Array ConstantInfo) _ info => acc.push info) #[]
        let counts := countDeclarations env infos
        out := out.push ({ name, path, declarations := counts.total }, counts)
  return (out.qsort (·.1.name.toString < ·.1.name.toString), used.qsort (· < ·))

/-! ## Files -/

/-- Scan every `.lean` file under `root`. A file is imported when it is the source of one of
`modules`, compiled when some library directory of `layout` holds the `.olean` of a module it
would be from one of the source directories, and not built otherwise. -/
def SourceStats.read (root : System.FilePath) (layout : WorkspaceLayout)
    (modules : Array ModuleStats) : IO SourceStats := do
  let imported := modules.map (·.path)
  let own ← blueprintFolder? root
  let mut files := #[]
  let mut total : LineCounts := {}
  for path in ← leanFilesUnder root do
    if insideFolder own path then continue
    let lines := countLeanLines ((← try IO.FS.readFile (root / path) catch _ => pure ""))
    total := total + lines
    let status ←
      if imported.contains path then pure FileStatus.imported
      else if ← isCompiled path then pure .compiled
      else pure .notBuilt
    files := files.push { path, lines, status }
  return { files, lines := total }
where
  /-- Whether a library directory holds the `.olean` of `path` read as a module of a source
  directory. -/
  isCompiled (path : String) : IO Bool := do
    for dir in layout.sourceDirs do
      let rel? := if dir == "." then some path else
        if path.startsWith (dir ++ "/") then some (path.drop (dir.length + 1)).copy else none
      let some rel := rel? | continue
      let olean := (rel.dropEnd ".lean".length).copy ++ ".olean"
      for lib in layout.libraryDirs do
        if ← (root / joinRel lib olean).pathExists then return true
    return false

/-! ## The Blueprint graph -/

private def kindOrder : Array Data.NodeKind := #[.definition, .proposition, .lemma, .theorem, .corollary]

private def kindKey : Data.NodeKind → String
  | .definition => "definition"
  | .proposition => "proposition"
  | .lemma => "lemma"
  | .theorem => "theorem"
  | .corollary => "corollary"

/-- Progress over the graph's nodes, leaving out placeholders for unknown references. -/
def progressOf (graph : Graph.GraphModel) : ProgressCounts :=
  graph.nodes.foldl (init := {}) fun c node =>
    if node.warnings.unknownRef then c else c.add node.proofStatus

/-- The nodes by kind group, with what is known of their Lean code (from the graph's progress
status) and whether they have an informal statement (from the Blueprint state). A node without a
kind counts as theorem-like, as the graph draws it. -/
def leanProgressOf (state : Environment.State) (graph : Graph.GraphModel) : LeanProgress :=
  graph.nodes.foldl (init := {}) fun p node =>
    if node.warnings.unknownRef then p else
    let add (k : KindProgress) : KindProgress :=
      let complete := node.proofStatus == .formalized || node.proofStatus == .formalizedWithAncestors
      let informal := (state.data.get? node.label).any (·.toNode.hasStatementBody)
      { total := k.total + 1
        leanComplete := k.leanComplete + (if complete then 1 else 0)
        leanCompleteWithDependencies := k.leanCompleteWithDependencies +
          (if node.proofStatus == .formalizedWithAncestors then 1 else 0)
        informal := k.informal + (if informal then 1 else 0) }
    if (node.kind.map (·.isTheoremLike)).getD true then { p with theorems := add p.theorems }
    else { p with definitions := add p.definitions }

/-- `leanProgressOf` counted again from `graph`, keeping the counts of informal statements of
`captured`, which the graph does not hold. -/
def leanProgressWith (captured : LeanProgress) (graph : Graph.GraphModel) : LeanProgress :=
  let counted := leanProgressOf {} graph
  { theorems := { counted.theorems with informal := captured.theorems.informal }
    definitions := { counted.definitions with informal := captured.definitions.informal } }

/-- The size of the graph. Edges are counted from the uses of real nodes. -/
def graphSizeOf (graph : Graph.GraphModel) : GraphSize := Id.run do
  let nodes := graph.nodes.filter (!·.warnings.unknownRef)
  let mut statementEdges := 0
  let mut proofEdges := 0
  let mut edges := 0
  for node in nodes do
    let stmt := Data.UseRef.mergeByLabel #[] node.statementUses |>.map (·.label)
    let proof := Data.UseRef.mergeByLabel #[] node.proofUses |>.map (·.label)
    statementEdges := statementEdges + stmt.size
    proofEdges := proofEdges + proof.size
    edges := edges + stmt.size + (proof.filter (!stmt.contains ·)).size
  let byKind := kindOrder.filterMap fun kind =>
    let n := (nodes.filter (·.kind == some kind)).size
    if n == 0 then none else some (kindKey kind, n)
  let groups := (graph.groupMetadata.map (·.label)).foldl (init := (#[] : Array Name))
    fun acc label => if acc.contains label then acc else acc.push label
  return { nodes := nodes.size, statementEdges, proofEdges, edges, groups := groups.size, byKind }

/-! ## Trust -/

/-- One Lean declaration of a node, as the node recorded it. -/
private structure NodeDeclaration where
  name : Name
  axioms : Array Name
  status : ProvedStatus

/-- The Lean declarations of a node, each once: external references and declarations of its
inline code, with their axioms joined and statuses merged conservatively. Names a node refers
to that were not present come back separately. -/
private def nodeDeclarations (node : Data.Node) : Array NodeDeclaration × Array Name := Id.run do
  let mut decls : Array NodeDeclaration := #[]
  let mut missing : Array Name := #[]
  let observe (decls : Array NodeDeclaration) (name : Name) (axioms : Array Name)
      (status : ProvedStatus) : Array NodeDeclaration :=
    let name := name.eraseMacroScopes
    match decls.findIdx? (·.name == name) with
    | some i => decls.modify i fun d =>
      { d with axioms := sortAxioms (d.axioms ++ axioms), status := d.status.mergeConservative status }
    | none => decls.push { name, axioms := sortAxioms axioms, status }
  for ref in node.associatedExternalRefs do
    if ref.present then
      decls := observe decls ref.canonical ref.axioms ref.provedStatus
    else if !missing.contains ref.canonical then
      missing := missing.push ref.canonical
  for code in node.literateCodes do
    for d in code.definedDefs do
      decls := observe decls d.name d.axioms d.provedStatus
    for t in code.definedTheorems do
      decls := observe decls t.name t.axioms t.provedStatus
  return (decls, missing)

private def byLabelThenDeclaration (a b : TrustEntry) : Bool :=
  a.label.toString < b.label.toString ||
    (a.label == b.label && a.declaration.toString < b.declaration.toString)

/-- The trust ledger of the Blueprint state, with unknown references taken from its graph. -/
def trustLedgerOf (state : Environment.State) (graph : Graph.GraphModel) : TrustLedger := Id.run do
  let mut ledger : TrustLedger := {}
  for (label, registered) in state.data do
    let (decls, missing) := nodeDeclarations registered.toNode
    for name in missing do
      let entry : MissingDeclaration := { label, declaration := name }
      ledger := { ledger with missingDeclarations := ledger.missingDeclarations.push entry }
    for d in decls do
      let entry (cls : AxiomClass) : TrustEntry :=
        { label, declaration := d.name, axioms := d.axioms.filter (AxiomClass.ofName · == cls) }
      let sorries := entry .sorryAx
      if d.status.containsExplicitSorry then
        ledger := { ledger with sorryDirect := ledger.sorryDirect.push sorries }
      else if !sorries.axioms.isEmpty || !d.status.sorryEvidence.isEmpty then
        ledger := { ledger with sorryThroughDependency := ledger.sorryThroughDependency.push sorries }
      let extra := entry .other
      if !extra.axioms.isEmpty then
        ledger := { ledger with extraAxioms := ledger.extraAxioms.push extra }
      let compiled := entry .compilerTrusted
      if !compiled.axioms.isEmpty then
        ledger := { ledger with compilerTrusted := ledger.compilerTrusted.push compiled }
  let unknown := graph.nodes.filter (·.warnings.unknownRef) |>.map (·.label)
  let unknownReferences := unknown.map fun label =>
    let referencedBy := graph.nodes.filterMap fun node =>
      if !node.warnings.unknownRef &&
          (node.statementUses.any (·.label == label) || node.proofUses.any (·.label == label)) then
        some node.label
      else none
    ({ label, referencedBy := referencedBy.qsort (·.toString < ·.toString) } : UnknownReference)
  return { ledger with
    sorryDirect := ledger.sorryDirect.qsort byLabelThenDeclaration
    sorryThroughDependency := ledger.sorryThroughDependency.qsort byLabelThenDeclaration
    extraAxioms := ledger.extraAxioms.qsort byLabelThenDeclaration
    compilerTrusted := ledger.compilerTrusted.qsort byLabelThenDeclaration
    missingDeclarations := ledger.missingDeclarations.qsort fun a b =>
      a.label.toString < b.label.toString ||
        (a.label == b.label && a.declaration.toString < b.declaration.toString)
    unknownReferences := unknownReferences.qsort (·.label.toString < ·.label.toString) }

/-! ## Capture -/

/-- A file name as an absolute path with symbolic links resolved, relative to the working
directory. -/
private def resolve (file : String) : IO System.FilePath := do
  let path : System.FilePath := file
  let cwd ← IO.currentDir
  let path := if path.isAbsolute then path else cwd / path
  try IO.FS.realPath path catch _ => pure path

/-- The project modules whose declarations the nodes of `state` refer to, with each one's source
file relative to `root`, each once and sorted by name: the modules whose source a site can show
beside what it reports of them. A module checked out as a dependency (`.lake/packages`) is not
one of them. -/
def nodeSourceModules (state : Environment.State) (root : System.FilePath) :
    Array (Name × String) := Id.run do
  let mut out : Array (Name × String) := #[]
  for (_, registered) in state.data do
    for ref in registered.toNode.associatedExternalRefs do
      let .inWorkspace module path := ref.provenance | continue
      if Data.isPackageSource path || out.any (·.1 == module) then continue
      let file := (relativeTo? root path).getD path
      out := out.push (module, file)
  return out.qsort (·.1.toString < ·.1.toString)

/-- The source text each module of `nodeSourceModules` was compiled from, while the Blueprint is
elaborated against these compiled modules: by Lake's build record of an imported module
(`BuiltSource.read`), and for the module being elaborated, its own text. A module whose record
Lake wrote when it took the compiled files from its artifact cache names no source
(`syntheticRecord`); Lake checked that module against its source in the build that is elaborating
the Blueprint, so the file's text as it reads now is the one compiled, up to an edit made during
the build. -/
def builtSourcesOf (state : Environment.State) (root : System.FilePath) :
    CoreM (Array BuiltSource) := do
  let sp ← searchPathRef.get
  let main := (← getEnv).mainModule
  let text := (← getFileMap).source
  (nodeSourceModules state root).mapM fun (module, file) => do
    if module == main then return { module, file, hash := some (lakeTextHash text) }
    let olean? ← liftM (m := IO) <| findBuiltModule? sp module
    let built ← liftM <| BuiltSource.read module file olean?
    if built.hash.isSome then return built
    let some olean := olean? | return built
    unless ← liftM (m := IO) (syntheticRecord olean) do return built
    let some text ← liftM (m := IO) (try some <$> IO.FS.readFile (root / file) catch _ => pure none)
      | return built
    return { module, file, hash := some (lakeTextHash text) }

/-- The modules of `built` whose source, as it reads under `root` now, is not the one the
Blueprint was elaborated against: changed since, or not known to match it. -/
def sourceChangesNow (built : Array BuiltSource) (root : System.FilePath) :
    IO (Array SourceChange) :=
  built.filterMapM fun b => do
    let text? ← try some <$> IO.FS.readFile (root / b.file) catch _ => pure none
    return b.check text?

/-- The project statistics of the current environment, Blueprint state and graph, with the
project's files read from the working directory. -/
def ProjectStats.capture (graph : Graph.GraphModel) : CoreM ProjectStats := do
  let env ← getEnv
  let named := some (verso.blueprint.projectRoot.get (← getOptions)) |>.filter (!·.trimAscii.isEmpty)
  let root ← projectRoot named
  let layout ← WorkspaceLayout.current root
  let own ← blueprintFolder? root
  let currentFile? := (relativeTo? root (← resolve (← getFileName))).filter fun path =>
    path.endsWith ".lean" && !insideFolder own path
  let (modules, sourceDirs) ← projectModules env root layout currentFile?
  let layout := { layout with sourceDirs, projectRoot := named }
  let declarations := modules.foldl (init := {}) fun acc (_, counts) => acc + counts
  let modules := modules.map (·.1)
  let sources ← SourceStats.read root layout modules
  let identity ← ProjectIdentity.read root
  let state := informalExt.getState env
  return {
    identity, layout, modules, declarations, sources
    progress := progressOf graph
    leanProgress := leanProgressOf state graph
    graph := graphSizeOf graph
    trust := trustLedgerOf state graph
    claims := ← Claims.atRoot? root
    builtSources := ← builtSourcesOf state root
  }

/-- Read the project's files again from the working directory, keeping what was captured from
the environment. Nothing changes when the working directory is not the captured project (its
Lake manifest names another root package, or none while one was captured). -/
def ProjectStats.refreshWorkspace (stats : ProjectStats) : IO ProjectStats := do
  let root ← projectRoot stats.layout.projectRoot
  let identity ← ProjectIdentity.read root
  unless identity.name == stats.identity.name do
    return stats
  let sources ← SourceStats.read root stats.layout stats.modules
  return { stats with identity, sources, claims := ← Claims.atRoot? root }

end Informal.Stats
