/-
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

import Lean.Data.Json
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

/-- The change as a clause: "the source of Demo.A (Demo/A.lean) changed since the build", or "the
source of Demo.A (Demo/A.lean) is not known to match the build: why". -/
def SourceChange.text (c : SourceChange) : String :=
  if c.changed then s!"the source of {c.module} ({c.file}) changed since the build"
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

end Informal.Stats
