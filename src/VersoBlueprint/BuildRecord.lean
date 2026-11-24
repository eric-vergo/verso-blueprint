/-
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

import Lean.Data.Json
import Lean.Elab.ParseImportsFast
import Lean.Util.Path

/-!
Whether a source file is the one its compiled module was compiled from, by the build record Lake
writes beside the compiled module (`<module>.trace`).

A site shows a module's source text beside what was established about the compiled module: a
mark, a colour, "no sorry", a verdict. The text is read from the disk when the site is generated,
the rest comes from the build, and nothing else holds the two together: a file edited after the
build would be shown beside a verdict about another text. So every module whose source a site
shows is checked against Lake's record (`provenanceOf`), and a module whose source differs from
the one its compiled module was compiled from, or is not known to be that one, is a
`SourceChange`: no positive mark is shown for its declarations.

The check reads the record (a small JSON file), hashes the compiled files the record names to
make sure the record describes them, and hashes the source text, both as Lake does
(`Lake.Hash.ofByteArray`, `Lake.Hash.ofText`).
-/

namespace Informal.Stats

open Lean

/-- Lake's content hash (`Lake.Hash`) of a value hashed with `h`, as Lake writes it: sixteen
lower-case hexadecimal digits. -/
def lakeHashHex (h : UInt64) : String :=
  let v := mixHash 1723 h
  let digits := (Nat.toDigits 16 v.toNat)
  String.ofList (List.replicate (16 - digits.length) '0' ++ digits)

/-- Lake's hash of a source file's text: line endings normalized (`Lake.Hash.ofText`). -/
def lakeTextHash (text : String) : String := lakeHashHex (hash text.crlfToLf)

/-- Lake's hash of a binary file's bytes (`Lake.Hash.ofByteArray`). -/
def lakeBytesHash (bytes : ByteArray) : String := lakeHashHex (hash bytes)

/-- Whether a compiled module was compiled from a source text, by Lake's build record of it. -/
inductive Provenance where
  /-- The record describes these compiled files and names this source text. -/
  | same
  /-- The record describes these compiled files and a different source text. -/
  | differs
  /-- Nothing is known: why. -/
  | unknown (why : String)
deriving Repr, Inhabited, DecidableEq

/-- Every `[path, hash]` pair of a Lake trace's `inputs`, at any depth. -/
private partial def tracePairs (j : Json) : Array (String × String) :=
  match j with
  | .arr #[.str path, .str h] => #[(path, h)]
  | .arr items => items.flatMap tracePairs
  | _ => #[]

/-- The file of Lake's artifact cache that holds the compiled output `output` (`HASH.olean`) of a
build record, when the cache is named (`LAKE_CACHE_DIR`). -/
def cachedArtifact? (output : String) : IO (Option System.FilePath) := do
  let some dir ← IO.getEnv "LAKE_CACHE_DIR" | return none
  if dir.isEmpty || output.isEmpty || output.contains '/' then return none
  return some (System.FilePath.mk dir / "artifacts" / output)

/-- The compiled module `module` on the search path `path`: the `.olean` file, or, for a module
whose compiled files Lake's artifact cache keeps elsewhere, where it would be beside its build
record (`<module>.trace`), which `provenanceOf` reads. -/
def findBuiltModule? (path : System.SearchPath) (module : Name) :
    IO (Option System.FilePath) := do
  for dir in path do
    let file := modToFilePath dir module "olean"
    if ← file.pathExists then return some file
  for dir in path do
    let trace := modToFilePath dir module "trace"
    if ← trace.pathExists then return some (trace.withExtension "olean")
  return none

/-- Lake's hash of the source text that the compiled module `olean` (with its `.server` and
`.private` parts) was compiled from, by the build record Lake writes beside it
(`<module>.trace`): the record's outputs must be these compiled files (by Lake's hash of their
bytes, beside the record or in Lake's artifact cache), and its input of `sourceFile` (relative to
the project root) is the hash. A record that is missing, unreadable, or describes other files says
nothing: the error says why. -/
def recordedSourceHash (olean : System.FilePath) (sourceFile : String)
    (what : String := "the compiled challenge") : IO (Except String String) := do
  let trace := olean.withExtension "trace"
  let some json ← (try some <$> (IO.ofExcept (Json.parse (← IO.FS.readFile trace)))
      catch _ => pure none)
    | return .error s!"Lake's build record {trace.fileName.getD "?"} of {what} is \
        missing or cannot be read"
  -- the outputs: `HASH.olean`, `HASH.olean.server`, `HASH.olean.private`
  let outputs : Array String := match json.getObjValD "outputs" |>.getObjValD "o" with
    | .str s => #[s]
    | .arr items => items.filterMap fun | .str s => some s | _ => none
    | _ => #[]
  if outputs.isEmpty then
    return .error s!"Lake's build record of {what} lists no compiled file"
  for output in outputs do
    let (h, ext) := match output.splitOn "." with
      | h :: rest => (h, ".".intercalate rest)
      | [] => ("", "")
    let file : System.FilePath := match ext with
      | "olean" => olean
      | "olean.server" => olean.addExtension "server"
      | "olean.private" => olean.addExtension "private"
      | _ => olean.withExtension ext
    -- Lake's artifact cache may keep the compiled files under their hashes instead of beside
    -- the record (`LAKE_CACHE_DIR`, artifacts restored or not)
    let read (f : System.FilePath) : IO (Option ByteArray) :=
      try some <$> IO.FS.readBinFile f catch _ => pure none
    let bytes? ← match ← read file with
      | some bytes => pure (some bytes)
      | none => match ← cachedArtifact? output with
        | some f => read f
        | none => pure none
    let some bytes := bytes?
      | return .error s!"the compiled file {file.fileName.getD "?"} that Lake's build record \
          lists is missing"
    unless lakeBytesHash bytes == h do
      return .error s!"Lake's build record of {what} describes other compiled files \
        than {file.fileName.getD "?"}"
  let suffix := "/" ++ sourceFile
  let inputs := (tracePairs (json.getObjValD "inputs")).filter fun (path, _) =>
    path == sourceFile || path.endsWith suffix
  let some (_, recorded) := inputs[0]?
    | return .error s!"Lake's build record of {what} does not name its source {sourceFile}"
  return .ok recorded

/-- Whether Lake's build record beside the compiled module `olean` is one Lake writes when it takes
the compiled files from its artifact cache (`"synthetic": true`): such a record names no input,
so it says nothing of the source text; Lake checked the module's inputs, source text included,
against the cache's key when it wrote it. -/
def syntheticRecord (olean : System.FilePath) : IO Bool := do
  let some json ← (try some <$> (IO.ofExcept (Json.parse
      (← IO.FS.readFile (olean.withExtension "trace")))) catch _ => pure none)
    | return false
  return json.getObjValD "synthetic" == .bool true

/-- Whether the compiled module `olean` was compiled from the source text `text` of the file
`sourceFile` (relative to the project root), by the build record Lake writes beside it
(`recordedSourceHash`). A source edited after the build differs; a record that is missing,
unreadable, or describes other files says nothing. -/
def provenanceOf (olean : System.FilePath) (sourceFile : String) (text : String)
    (what : String := "the compiled challenge") : IO Provenance := do
  return match ← recordedSourceHash olean sourceFile what with
    | .ok recorded => if recorded == lakeTextHash text then .same else .differs
    | .error why => .unknown why

/-- A module whose source text, as a site would show it, is not known to be the text its compiled
module was compiled from. -/
structure SourceChange where
  module : Name
  /-- The source file, relative to the project root. -/
  file : String
  /-- The source differs from the one Lake's build record names (`true`), or no record says which
  source it was (`false`, with `why`). -/
  changed : Bool
  /-- Why it is not known to match, when `changed` is `false`. -/
  why : String := ""
deriving Repr, Inhabited, DecidableEq, ToJson, FromJson

/-- How `why` begins for a module that is not known to match the build only because a project
module it imports, directly or not, is not (`SourceChange.imported`). -/
def SourceChange.importsLead : String := "it imports "

/-- Whether the module is not known to match the build only because of a module it imports. -/
def SourceChange.isImported (c : SourceChange) : Bool :=
  !c.changed && c.why.startsWith SourceChange.importsLead

/-- Where the module is, for a clause: "Demo.A in Demo/A.lean". -/
def SourceChange.place (c : SourceChange) : String := s!"{c.module} in {c.file}"

/-- What is wrong with the module's own source, as a clause after its name: "changed since the
build", or "is not known to match the build: why". -/
def SourceChange.state (c : SourceChange) : String :=
  if c.changed then "changed since the build"
  else s!"is not known to match the build: {c.why}"

/-- The modules `causes` (each one whose own source is not known to match the build), as a
clause: "Demo.A in Demo/A.lean, which changed since the build", and how many others there are. -/
def SourceChange.causesText (causes : Array SourceChange) : String :=
  match causes[0]? with
  | none => ""
  | some c =>
    let others := causes.size - 1
    let more := if others == 0 then ""
      else s!" (and {others} other {if others == 1 then "module" else "modules"} not known to \
        match the build)"
    s!"{c.place}, which {c.state}{more}"

/-- `module`, whose source `file` is the text its compiled module was compiled from, is still not
known to match the build: the project modules `causes`, which it imports directly or not, are
not (sorted by name, not empty). Lake rebuilds a module when one of its imports changes. -/
def SourceChange.imported (module : Name) (file : String) (causes : Array SourceChange) :
    SourceChange :=
  { module, file, changed := false
    why := s!"{SourceChange.importsLead}{SourceChange.causesText causes}" }

/-- The change as a clause: "the source of Demo.A (Demo/A.lean) changed since the build", "the
source of Demo.A (Demo/A.lean) is not known to match the build: why", or "Demo.B (Demo/B.lean)
imports Demo.A in Demo/A.lean, which changed since the build". -/
def SourceChange.text (c : SourceChange) : String :=
  if c.changed then s!"the source of {c.module} ({c.file}) changed since the build"
  else if c.isImported then
    s!"{c.module} ({c.file}) imports {c.why.drop SourceChange.importsLead.length}"
  else s!"the source of {c.module} ({c.file}) is not known to match the build: {c.why}"

/-- What is known of the source text a module was compiled from, when a site's data is
captured: Lake's hash of that text, or why none is known. The generator, run later, compares it
with the file as it reads then (`BuiltSource.check`). -/
structure BuiltSource where
  module : Name
  /-- The source file, relative to the project root. -/
  file : String
  /-- Lake's hash of the source text (`lakeTextHash`) the compiled module was compiled from. -/
  hash : Option String := none
  /-- Why no hash is known. -/
  why : String := ""
deriving Repr, Inhabited, DecidableEq, ToJson, FromJson

/-- The record of `module`, compiled to `olean?`, whose source is `file` (relative to the project
root), by Lake's build record of it (`recordedSourceHash`). -/
def BuiltSource.read (module : Name) (file : String) (olean? : Option System.FilePath) :
    IO BuiltSource := do
  let some olean := olean? | return { module, file, why := "its compiled module was not found" }
  match ← recordedSourceHash olean file (what := s!"the compiled module {module}") with
  | .ok hash => return { module, file, hash := some hash }
  | .error why => return { module, file, why }

/-- What a site generated now must say of the module of `b`, whose source reads `text?` now:
nothing when it is the text that was compiled; else the change. -/
def BuiltSource.check (b : BuiltSource) (text? : Option String) : Option SourceChange :=
  match b.hash, text? with
  | none, _ => some { module := b.module, file := b.file, changed := false, why := b.why }
  | some _, none =>
    some { module := b.module, file := b.file, changed := false
           why := "the source file cannot be read" }
  | some h, some text =>
    if lakeTextHash text == h then none
    else some { module := b.module, file := b.file, changed := true }

/-- Whether the source of `module`, which reads `text?` now, is the one its compiled module
`olean?` was compiled from: nothing when it is, else the change. -/
def sourceChangeOf (module : Name) (file : String) (olean? : Option System.FilePath)
    (text? : Option String) : IO (Option SourceChange) :=
  return (← BuiltSource.read module file olean?).check text?

/-! ## Modules and what they import

A compiled module is built against the compiled modules it imports: a proof in it may rest on a
lemma of another module of the project whose source has been edited since, to `sorry` say. So a
module whose own source is the text that was compiled is still not known to match the build when
a project module it imports, directly or not, is not; Lake would rebuild it.

The imports are read from the module's source text, as Lake reads them (`Lean.parseImports'`),
and only from a text known to be the one that was compiled, so they are the imports of the
compiled module. Only the project's own modules are followed (`ModuleFinder.source?`); a module
of a package the project depends on, or of Lean, is not checked: the site shows no source of it,
and its build is the package's, at the revision the project's manifest pins. -/

/-- How a walk over a project's modules finds and checks each one. -/
structure ModuleFinder where
  /-- The source file of a module of the project, relative to the project root, or `none` for a
  module outside the project (of a package it depends on, or of Lean), which is not followed. -/
  source? : Name → IO (Option String)
  /-- The text of a source file of the project, as it reads now. -/
  text? : String → IO (Option String)
  /-- Whether the module's own source, `file` reading `text?`, is the text its compiled module was
  compiled from: nothing when it is, else the change (`sourceChangeOf`). -/
  check : Name → String → Option String → IO (Option SourceChange)

/-- The source file, relative to `root`, that Lake's build record of `module` names, when its
compiled module is in one of the project's own library directories (those of `dirs` inside
`root` and outside `.lake/packages`, and `.lake/build/lib/lean`): the file Lake compiled,
wherever the project's libraries keep their sources. -/
def tracedSource? (root : System.FilePath) (dirs : System.SearchPath) (module : Name) :
    IO (Option String) := do
  let realRoot := (← try IO.FS.realPath root catch _ => pure root).toString
  let prefixes := #[root.toString, realRoot].map fun r => if r.endsWith "/" then r else r ++ "/"
  let rel := "/".intercalate (module.components.map (·.toString (escape := false))) ++ ".lean"
  for dir in (root / ".lake" / "build" / "lib" / "lean") :: dirs do
    let real := (← try IO.FS.realPath dir catch _ => pure dir).toString ++ "/"
    unless prefixes.any (real.startsWith ·) && (real.splitOn "/.lake/packages/").length == 1 do
      continue
    let trace := modToFilePath dir module "trace"
    let some json ← (try some <$> IO.ofExcept (Json.parse (← IO.FS.readFile trace))
        catch _ => pure none) | continue
    for (path, _) in tracePairs (json.getObjValD "inputs") do
      unless path == rel || path.endsWith ("/" ++ rel) do continue
      if !path.startsWith "/" then return some path
      for p in prefixes do
        if path.startsWith p then return some (path.drop p.length).toString
      -- a project copied after its build: the record names the file where it was built, so the
      -- longest end of that path that is a file under `root` is the one
      let parts := (path.splitOn "/").filter (!·.isEmpty)
      let least := (rel.splitOn "/").length
      for k in (List.range (parts.length - least + 1)).reverse do
        let file := "/".intercalate (parts.drop (parts.length - (k + least)))
        if ← (root / file).pathExists then return some file
  return none

/-- The finder of the project at `root` that checks each module against Lake's build record of it
(`sourceChangeOf`): its source is the file Lake's build record of it names, when the project
built it (`tracedSource?`), else the first of `sourceDirs` (relative to `root`) that has it; its
compiled module is on `path` (`findBuiltModule?`). `texts` gives a file's text as the caller read
it, when it did, so that what is checked is what is shown; other files are read from the disk. -/
def ModuleFinder.ofLayout (root : System.FilePath) (sourceDirs : Array String)
    (path : System.SearchPath) (texts : String → Option String := fun _ => none) :
    ModuleFinder where
  source? module := do
    if let some file ← tracedSource? root path module then return some file
    let rel := "/".intercalate (module.components.map (·.toString (escape := false))) ++ ".lean"
    for dir in sourceDirs do
      let file := if dir == "." then rel else dir ++ "/" ++ rel
      if ← (root / file).pathExists then return some file
    return none
  text? file := do
    if let some text := texts file then return some text
    try some <$> IO.FS.readFile (root / file) catch _ => pure none
  check module file text? := do
    sourceChangeOf module file (← findBuiltModule? path module) text?

/-- What a walk found for one project module: its file, and the modules among it and those it
imports, directly or not, whose own source is not known to match the build (each once, sorted by
name): empty when it and everything of the project it imports match. -/
structure ModuleStanding where
  file : String
  causes : Array SourceChange := #[]
deriving Inhabited

/-- The change to show for `module` from its standing: its own, or that it imports modules that
are not known to match (`SourceChange.imported`); nothing when it matches. -/
def ModuleStanding.change? (s : ModuleStanding) (module : Name) : Option SourceChange :=
  if s.causes.isEmpty then none
  else match s.causes.find? (·.module == module) with
    | some own => some own
    | none => some (SourceChange.imported module s.file s.causes)

private def mergeCauses (a b : Array SourceChange) : Array SourceChange :=
  (b.foldl (init := a) fun acc c => if acc.any (·.module == c.module) then acc else acc.push c).qsort
    (·.module.toString < ·.module.toString)

/-- Walk from `starts` over the project modules they import, directly or not, checking each once
(`ModuleFinder.check`); a module that is not known to match is not followed further, since its
imports as written now need not be those it was compiled with. Returns the standing of every
project module reached; a module outside the project has none. -/
partial def walkModules (finder : ModuleFinder) (starts : Array Name) :
    IO (Std.HashMap Name ModuleStanding) := do
  let memo ← IO.mkRef ({} : Std.HashMap Name (Option ModuleStanding))
  let rec visit (module : Name) : IO (Option ModuleStanding) := do
    if let some known := (← memo.get)[module]? then return known
    -- a module being walked counts as nothing until it is done (imports have no cycle)
    memo.modify (·.insert module none)
    let result ← do
      let some file ← finder.source? module | pure none
      let text? ← finder.text? file
      if let some own ← finder.check module file text? then
        pure (some { file, causes := #[own] })
      else
        let text := text?.getD ""
        match ← (Lean.parseImports' text file).toBaseIO with
        | .error e =>
          pure (some { file, causes := #[{ module, file, changed := false
                                           why := s!"its imports cannot be read: {e}" }] })
        | .ok header =>
          let mut causes := #[]
          for imp in header.imports do
            if let some s ← visit imp.module then causes := mergeCauses causes s.causes
          pure (some { file, causes })
    memo.modify (·.insert module result)
    return result
  for m in starts do discard <| visit m
  return (← memo.get).fold (init := {}) fun acc m s? =>
    match s? with
    | some s => acc.insert m s
    | none => acc

/-- The changes of `walkModules`: every project module reached that is not known to match the
build, its own or because of what it imports, sorted by name. -/
def walkChanges (finder : ModuleFinder) (starts : Array Name) : IO (Array SourceChange) := do
  let standings ← walkModules finder starts
  let changes := standings.fold (init := #[]) fun acc m s =>
    match s.change? m with
    | some c => acc.push c
    | none => acc
  return changes.qsort (·.module.toString < ·.module.toString)

/-- The modules among `module` and the project modules it imports, directly or not, whose own
source is not known to match the build, sorted by name: empty when all of them match. -/
def closureCauses (finder : ModuleFinder) (module : Name) : IO (Array SourceChange) := do
  return ((← walkModules finder #[module])[module]?.map (·.causes)).getD #[]

end Informal.Stats
