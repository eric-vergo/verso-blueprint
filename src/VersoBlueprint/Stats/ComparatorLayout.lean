/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

import Lean.Data.Json
import Lean.Data.Name

/-!
The layout of a project's Comparator challenges, and the check that a project follows it.

A project's Comparator challenges live in one folder each, `Comparator/<Name>/`, holding exactly
the challenge `Challenge.lean` (module `Comparator.<Name>.Challenge`), the solution
`Solution.lean` (module `Comparator.<Name>.Solution`) and the configuration `comparator.json`
that `lake comparator --config Comparator/<Name>/comparator.json` reads. The layout is a strict
subset of what `lake comparator` accepts: a project that follows it also works with that command,
run from the project root for each challenge.

`check` reads a project's files and returns the challenges it finds (`ChallengeConfig`) and every
place where the project does not follow the layout (`Violation`), each naming the file, the rule
and the change needed (the rules are `Rule`, written down in the manual's chapter "Comparator
challenges"). A project with no `Comparator` folder and no `comparator.json` has no challenge
and no violation. The layout of a single challenge (`Comparator/Challenge.lean`,
`Comparator/Solution.lean`, `comparator.json` at the root) is not accepted; its violation says how
to move it (`migrationPlan`, which `vbp comparator-migrate` carries out).

Everything read is the project's data: file names and contents are never run, every file is read
with a size limit, `comparator.json` is parsed only after its nesting depth was checked, symbolic
links are not followed, and the folder walk that looks for stray configuration files is bounded.
-/

namespace Informal.Stats

open Lean

/-- The file that configures a Comparator challenge, in its challenge's folder. -/
def comparatorConfigFile : String := "comparator.json"

/-- A Comparator challenge as `lake comparator` reads it from its `comparator.json`. -/
structure ChallengeConfig where
  /-- The challenge's name: its folder's name under `Comparator/`. -/
  name : String := ""
  challengeModule : Name := `Comparator.Challenge
  solutionModule : Name := `Comparator.Solution
  /-- The theorems to judge; none means every theorem the challenge states. -/
  theoremNames : Option (Array Name) := none
  /-- Definitions of the challenge whose value the solution supplies. -/
  definitionNames : Array Name := #[]
  /-- The axioms a proof may use; none when no list is stated. -/
  permittedAxioms : Option (Array Name) := none
  /-- The file the configuration was read from, relative to the project root. -/
  configFile : Option String := none
deriving Repr, Inhabited, ToJson, FromJson

namespace ComparatorLayout

/-! ## The rules -/

/-- The folder of the challenges at the project root. -/
def folder : String := "Comparator"

/-- The challenge's file name in its folder. -/
def challengeFileName : String := "Challenge.lean"

/-- The solution's file name in its folder. -/
def solutionFileName : String := "Solution.lean"

/-- The most bytes of a challenge's or a solution's file. -/
def leanFileLimit : Nat := 1024 * 1024

/-- The most bytes of a `comparator.json`. -/
def configLimit : Nat := 64 * 1024

/-- The deepest nesting of arrays and objects in a `comparator.json`. -/
def configDepthLimit : Nat := 8

/-- The most challenges of a project. -/
def challengeLimit : Nat := 64

/-- The most names in `theorem_names` and in `definition_names`. -/
def nameLimit : Nat := 256

/-- The most names in `permitted_axioms`. -/
def axiomLimit : Nat := 64

/-- The most characters of one name in `comparator.json`. -/
def nameLengthLimit : Nat := 1024

/-- The most entries of the project the search for stray `comparator.json` files looks at. -/
def walkLimit : Nat := 50000

/-- The most characters of a challenge's name. -/
def nameCharLimit : Nat := 64

/-- The rules of the layout, as the manual numbers them. -/
inductive Rule where
  /-- `L1`: the layout of a single challenge is not accepted. -/
  | legacy
  /-- `L2`: `Comparator` is a folder (not a file, not a link). -/
  | folderKind
  /-- `L3`: every entry of `Comparator/` is a challenge's folder with a name of the form
  `[A-Z][A-Za-z0-9]*`, at most 64 characters (entries whose names start with `.` are ignored). -/
  | challengeName
  /-- `L4`: at most `challengeLimit` challenges. -/
  | challengeCount
  /-- `L5`: no `comparator.json` outside the challenges' folders (folders of other Lake projects
  inside the project, which have a lakefile of their own, aside). -/
  | strayConfig
  /-- `F1`: a challenge's folder holds exactly `Challenge.lean`, `Solution.lean` and
  `comparator.json`, as regular files. -/
  | folderContents
  /-- `F2`: a Lean file is valid UTF-8 of at most `leanFileLimit` bytes. -/
  | leanFile
  /-- `J1`: `comparator.json` is a JSON object of at most `configLimit` bytes, nested at most
  `configDepthLimit` deep. -/
  | configSyntax
  /-- `J2`: `comparator.json` has the keys `challenge_module`, `solution_module`,
  `theorem_names`, `permitted_axioms`, may have `definition_names` and `external_kernels`, and
  nothing else. -/
  | configKeys
  /-- `J3`: the modules are `Comparator.<Name>.Challenge` and `Comparator.<Name>.Solution`. -/
  | configModules
  /-- `J4`: `theorem_names` is a non-empty list of distinct Lean names. -/
  | theoremNames
  /-- `J5`: `permitted_axioms` is a list of distinct Lean names. -/
  | permittedAxioms
  /-- `J6`: `definition_names` is a list of distinct Lean names, none of them a judged theorem. -/
  | definitionNames
  /-- `J7`: `external_kernels` maps names to non-empty lists of strings. -/
  | externalKernels
  /-- `C1`: the challenge imports no module under `Comparator`. -/
  | challengeImports
  /-- `C2`: the challenge states its theorems with `sorry`. -/
  | challengeSorry
  /-- `C3`, `S2`: every judged theorem is declared, with `theorem`, in the file. -/
  | theoremDeclared
  /-- `S1`: the solution imports no module under `Comparator`. -/
  | solutionImports
  /-- `K1`: the project's Lake workspace can build both modules (checked by `vbp`). -/
  | lakeModule
deriving Repr, Inhabited, BEq, DecidableEq, ToJson, FromJson

/-- The rule's number in the manual. -/
def Rule.code : Rule → String
  | .legacy => "L1" | .folderKind => "L2" | .challengeName => "L3" | .challengeCount => "L4"
  | .strayConfig => "L5" | .folderContents => "F1" | .leanFile => "F2"
  | .configSyntax => "J1" | .configKeys => "J2" | .configModules => "J3"
  | .theoremNames => "J4" | .permittedAxioms => "J5" | .definitionNames => "J6"
  | .externalKernels => "J7" | .challengeImports => "C1" | .challengeSorry => "C2"
  | .theoremDeclared => "C3" | .solutionImports => "S1" | .lakeModule => "K1"

/-- The rule in a few words. -/
def Rule.title : Rule → String
  | .legacy => "one folder per challenge"
  | .folderKind => "the Comparator folder"
  | .challengeName => "challenge folder names"
  | .challengeCount => "number of challenges"
  | .strayConfig => "configuration files"
  | .folderContents => "the files of a challenge"
  | .leanFile => "Lean files"
  | .configSyntax => "comparator.json syntax"
  | .configKeys => "comparator.json keys"
  | .configModules => "module names"
  | .theoremNames => "theorem_names"
  | .permittedAxioms => "permitted_axioms"
  | .definitionNames => "definition_names"
  | .externalKernels => "external_kernels"
  | .challengeImports => "the challenge's imports"
  | .challengeSorry => "the challenge's sorry"
  | .theoremDeclared => "judged theorems declared"
  | .solutionImports => "the solution's imports"
  | .lakeModule => "Lake builds the modules"

/-- A place where a project does not follow the layout. -/
structure Violation where
  /-- The file or folder, relative to the project root. -/
  file : String
  rule : Rule
  /-- What is wrong and the change that makes the project follow the rule. -/
  message : String
deriving Repr, Inhabited, BEq, ToJson, FromJson

/-- The violation as one line: `file: rule L3 (challenge folder names): message`. -/
def Violation.render (v : Violation) : String :=
  s!"{v.file}: rule {v.rule.code} ({v.rule.title}): {v.message}"

/-- A text shown inside a message: at most 120 characters, control characters replaced. -/
def shown (text : String) : String :=
  let clean := String.ofList (text.toList.map fun c => if c.val < 0x20 || c.val == 0x7f then '?' else c)
  if clean.length > 120 then (clean.take 117).toString ++ "..." else clean

/-- Whether `name` is a challenge's name: an ASCII capital, then ASCII letters and digits, at most
`nameCharLimit` characters, so that `Comparator.<Name>` needs no escaping. -/
def isChallengeName (name : String) : Bool :=
  match name.toList with
  | c :: rest => c.isUpper && c.val < 128 && rest.all (fun c => c.val < 128 && c.isAlphanum) &&
      name.length ≤ nameCharLimit
  | [] => false

/-- The challenge module of the challenge `name`. -/
def challengeModuleOf (name : String) : Name := (`Comparator).str name |>.str "Challenge"

/-- The solution module of the challenge `name`. -/
def solutionModuleOf (name : String) : Name := (`Comparator).str name |>.str "Solution"

/-- The folder of the challenge `name`, relative to the project root. -/
def folderOf (name : String) : String := s!"{folder}/{name}"

/-! ## Reading Lean source without running it -/

/-- The text with every comment and string literal replaced by spaces (line breaks kept), so that
words found in it are code. Block comments nest. -/
def codeOnly (text : String) : String := Id.run do
  let chars := text.toList.toArray
  let mut out : Array Char := Array.mkEmpty chars.size
  let mut i := 0
  let blank := fun (c : Char) => if c == '\n' then '\n' else ' '
  while i < chars.size do
    let c := chars[i]!
    let next := chars[i + 1]?
    if c == '-' && next == some '-' then
      while i < chars.size && chars[i]! != '\n' do
        out := out.push ' '; i := i + 1
    else if c == '/' && next == some '-' then
      let mut depth := 0
      let mut stop := false
      while i < chars.size && !stop do
        if chars[i]! == '/' && chars[i + 1]? == some '-' then
          depth := depth + 1; out := out.push ' ' |>.push ' '; i := i + 2
        else if chars[i]! == '-' && chars[i + 1]? == some '/' then
          depth := depth - 1; out := out.push ' ' |>.push ' '; i := i + 2
          if depth == 0 then stop := true
        else
          out := out.push (blank chars[i]!); i := i + 1
    else if c == '"' then
      out := out.push ' '; i := i + 1
      while i < chars.size && chars[i]! != '"' do
        if chars[i]! == '\\' && i + 1 < chars.size then
          out := out.push ' ' |>.push (blank chars[i + 1]!); i := i + 2
        else
          out := out.push (blank chars[i]!); i := i + 1
      if i < chars.size then out := out.push ' '; i := i + 1
    else
      out := out.push c; i := i + 1
  return String.ofList out.toList

/-- Whether `c` can be part of a Lean identifier as written (dots included). -/
private def isWordChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '\'' || c == '.' || c == '!' || c == '?' ||
    c == '«' || c == '»' || (c.val ≥ 0x80 && !c.isWhitespace && !"()[]{}⦃⦄⟨⟩:,".contains c)

/-- The words of a text of code, in order. -/
def words (code : String) : Array String := Id.run do
  let mut out := #[]
  let mut cur := ""
  for c in code.toList do
    if isWordChar c then cur := cur.push c
    else if !cur.isEmpty then out := out.push cur; cur := ""
  if !cur.isEmpty then out := out.push cur
  return out

/-- The modules a file imports: every word after `import` (and after `all` in `import all`). -/
def importsOf (code : String) : Array Name := Id.run do
  let ws := words code
  let mut out := #[]
  for i in [0:ws.size] do
    if ws[i]! == "import" then
      let next := if ws[i + 1]? == some "all" then ws[i + 2]? else ws[i + 1]?
      if let some m := next then out := out.push m.toName
  return out

/-- The declared names after `theorem`, each with the namespaces open around it: `namespace A`
and `end A` are followed, so a theorem `b` inside `namespace A` is `A.b`. -/
def theoremsOf (code : String) : Array Name := Id.run do
  let ws := words code
  let mut scopes : Array Name := #[]
  let mut out := #[]
  for i in [0:ws.size] do
    match ws[i]!, ws[i + 1]? with
    | "namespace", some n => scopes := scopes.push n.toName
    | "section", _ => scopes := scopes.push .anonymous
    | "end", some n =>
      if scopes.back?.any (· == n.toName) then scopes := scopes.pop
      else if scopes.back? == some .anonymous then scopes := scopes.pop
    | "theorem", some n =>
      let pre := scopes.foldl (fun acc s => s.components.foldl (fun a c => a ++ c) acc) Name.anonymous
      let written := (n.dropPrefix "_root_.").toString.toName
      out := out.push (if n.startsWith "_root_." then written else pre ++ written)
    | _, _ => pure ()
  return out

/-- Whether the code has `sorry` as a word. -/
def hasSorry (code : String) : Bool := (words code).contains "sorry"

/-! ## Reading files -/

/-- What is at a path, without following a symbolic link at its end. -/
inductive Entry where
  | missing | file (size : Nat) | dir | link | other
deriving BEq, Inhabited

/-- What is at `path`. -/
def entryAt (path : System.FilePath) : IO Entry := do
  let some md ← (try some <$> path.symlinkMetadata catch _ => pure none) | return .missing
  return match md.type with
    | .file => .file md.byteSize.toNat
    | .dir => .dir
    | .symlink => .link
    | _ => .other

/-- The names in a folder, sorted. -/
def namesIn (dir : System.FilePath) : IO (Array String) := do
  let entries ← (try dir.readDir catch _ => pure #[])
  return (entries.map (·.fileName)).qsort (· < ·)

/-- A file's text when it is a regular file of at most `limit` bytes in UTF-8. -/
def readLimited (path : System.FilePath) (limit : Nat) : IO (Except String String) := do
  match ← entryAt path with
  | .file size =>
    if size > limit then return .error s!"it has {size} bytes, more than the {limit} allowed"
    let bytes ← (try some <$> IO.FS.readBinFile path catch _ => pure none)
    let some bytes := bytes | return .error "it cannot be read"
    if bytes.size > limit then return .error s!"it has more than the {limit} bytes allowed"
    match String.fromUTF8? bytes with
    | some text => return .ok text
    | none => return .error "it is not valid UTF-8"
  | .link => return .error "it is a symbolic link; replace it with the file itself"
  | .missing => return .error "it is missing"
  | _ => return .error "it is not a regular file"

/-- The deepest nesting of `[` and `{` in a JSON text, outside its strings. -/
def jsonDepth (text : String) : Nat := Id.run do
  let mut depth := 0
  let mut most := 0
  let mut inString := false
  let mut escaped := false
  for c in text.toList do
    if inString then
      if escaped then escaped := false
      else if c == '\\' then escaped := true
      else if c == '"' then inString := false
    else if c == '"' then inString := true
    else if c == '[' || c == '{' then
      depth := depth + 1
      most := max most depth
    else if c == ']' || c == '}' then depth := depth - 1
  return most

/-! ## The configuration -/

/-- The keys `comparator.json` must have. -/
def requiredKeys : List String :=
  ["challenge_module", "solution_module", "theorem_names", "permitted_axioms"]

/-- The keys `comparator.json` may have besides. -/
def optionalKeys : List String := ["definition_names", "external_kernels"]

/-- `comparator.json`'s text checked against the rules `J1` to `J7` for the challenge `name`:
the configuration, and the violations found (with `file` the configuration's path). -/
def checkConfig (file name text : String) : ChallengeConfig × Array Violation := Id.run do
  let base : ChallengeConfig := { name, challengeModule := challengeModuleOf name
                                  solutionModule := solutionModuleOf name, configFile := some file }
  let v := fun (rule : Rule) (message : String) => ({ file, rule, message } : Violation)
  if text.utf8ByteSize > configLimit then
    return (base, #[v .configSyntax s!"it has {text.utf8ByteSize} bytes, more than the \
      {configLimit} allowed"])
  if jsonDepth text > configDepthLimit then
    return (base, #[v .configSyntax s!"arrays and objects are nested more than \
      {configDepthLimit} deep"])
  let json ← match Json.parse text with
    | .ok json => pure json
    | .error e => return (base, #[v .configSyntax s!"it is not valid JSON ({shown e})"])
  let .obj fields := json
    | return (base, #[v .configSyntax "it must be a JSON object ({ ... })"])
  let mut out : Array Violation := #[]
  let keys := fields.toArray.map (·.1)
  for k in requiredKeys do
    unless keys.contains k do
      out := out.push (v .configKeys s!"the key \"{k}\" is missing; add it")
  for k in keys do
    unless requiredKeys.contains k || optionalKeys.contains k do
      out := out.push (v .configKeys s!"the key \"{shown k}\" is not allowed; remove it (allowed: \
        {", ".intercalate (requiredKeys ++ optionalKeys)})")
  -- module names
  let mut config := base
  for (key, want) in [("challenge_module", challengeModuleOf name), ("solution_module", solutionModuleOf name)] do
    match json.getObjVal? key with
    | .ok (.str s) =>
      unless s == want.toString do
        out := out.push (v .configModules s!"\"{key}\" is \"{shown s}\"; set it to \"{want}\"")
    | .ok _ => out := out.push (v .configModules s!"\"{key}\" must be the string \"{want}\"")
    | .error _ => pure ()
  -- name lists
  let nameList (key : String) (rule : Rule) (limit : Nat) (nonEmpty : Bool) :
      Option (Array Name) × Array Violation := Id.run do
    match json.getObjVal? key with
    | .error _ => return (none, #[])
    | .ok (.arr items) =>
      if items.size > limit then
        return (none, #[v rule s!"\"{key}\" has {items.size} names, more than the {limit} allowed"])
      if nonEmpty && items.isEmpty then
        return (none, #[v rule s!"\"{key}\" is empty; name the theorems the challenge judges"])
      let mut names : Array Name := #[]
      let mut problems : Array Violation := #[]
      for item in items do
        match item with
        | .str s =>
          let n := s.toName
          if s.length > nameLengthLimit || n.isAnonymous || n.toString (escape := false) != s then
            problems := problems.push (v rule s!"\"{key}\" holds \"{shown s}\", which is not a \
              Lean name; write the declaration's full name, such as \"Foo.bar\"")
          else if names.contains n then
            problems := problems.push (v rule s!"\"{key}\" names {s} twice; keep one")
          else names := names.push n
        | _ => problems := problems.push (v rule s!"\"{key}\" must hold strings only")
      return (some names, problems)
    | .ok _ => return (none, #[v rule s!"\"{key}\" must be a list of names ([\"...\"])"])
  let (theorems, p1) := nameList "theorem_names" .theoremNames nameLimit true
  let (axioms, p2) := nameList "permitted_axioms" .permittedAxioms axiomLimit false
  let (definitions, p3) := nameList "definition_names" .definitionNames nameLimit false
  out := out ++ p1 ++ p2 ++ p3
  if let (some ts, some ds) := (theorems, definitions) then
    for d in ds do
      if ts.contains d then
        out := out.push (v .definitionNames s!"{d} is in both \"theorem_names\" and \
          \"definition_names\"; a definition hole is not a judged theorem: keep it in one")
  match json.getObjVal? "external_kernels" with
  | .error _ => pure ()
  | .ok (.obj kernels) =>
    for (k, cmd) in kernels.toArray do
      match cmd with
      | .arr parts =>
        if parts.isEmpty || !parts.all (fun | .str _ => true | _ => false) then
          out := out.push (v .externalKernels s!"the kernel \"{shown k}\" must be a non-empty list \
            of strings (the command and its arguments)")
      | _ => out := out.push (v .externalKernels s!"the kernel \"{shown k}\" must be a list of \
          strings (the command and its arguments)")
  | .ok _ => out := out.push (v .externalKernels "\"external_kernels\" must be an object that \
      maps a kernel's name to its command")
  config := { config with theoremNames := theorems, permittedAxioms := axioms
                          definitionNames := definitions.getD #[] }
  return (config, out)

/-! ## The project -/

/-- What `check` found: the challenges in name order and the violations. A challenge is listed
only when its folder has no violation. -/
structure Report where
  challenges : Array ChallengeConfig := #[]
  violations : Array Violation := #[]
  /-- Whether the project has any Comparator file: a `Comparator` entry or a `comparator.json`. -/
  hasComparator : Bool := false
deriving Inhabited

/-- The `git mv` lines that move the single-challenge layout into `Comparator/<name>/`. -/
def migrationLines (name : String) (hasRootConfig : Bool) : Array String :=
  #[s!"mkdir -p {folderOf name}",
    s!"git mv {folder}/{challengeFileName} {folderOf name}/{challengeFileName}",
    s!"git mv {folder}/{solutionFileName} {folderOf name}/{solutionFileName}"] ++
  (if hasRootConfig then #[s!"git mv {comparatorConfigFile} {folderOf name}/{comparatorConfigFile}"]
   else #[])

/-- The message of the single-challenge layout: the exact moves and edits. -/
def legacyMessage (hasRootConfig : Bool) : String :=
  let name := "Main"
  let lines := migrationLines name hasRootConfig
  s!"the single-challenge layout (Comparator/Challenge.lean, Comparator/Solution.lean, \
    comparator.json at the root) is not accepted; every challenge has a folder \
    Comparator/<Name>/. Run `lake exe vbp comparator-migrate --name {name}` (add `--dry-run` to \
    see the changes first), or by hand: {"; ".intercalate lines.toList}; then \
    {if hasRootConfig then "set" else "write"} {folderOf name}/{comparatorConfigFile} with \
    \"challenge_module\": \"{challengeModuleOf name}\", \"solution_module\": \
    \"{solutionModuleOf name}\", \"theorem_names\" and \"permitted_axioms\", and rename the \
    modules Comparator.Challenge and Comparator.Solution to {challengeModuleOf name} and \
    {solutionModuleOf name} where the project names them (its lakefile, imports)"

/-- Folders the search for stray configuration files does not enter: Lake's, Git's, build
outputs, and every folder whose name starts with `.`. -/
def skippedFolder (name : String) : Bool :=
  name.startsWith "." || name == "_out" || name == "build"

/-- Every `comparator.json` under `root` outside `Comparator/` and the root itself, relative to
`root`, looking at most at `walkLimit` entries, never following a symbolic link and never entering
a folder that holds a lakefile (another Lake project, such as a test fixture). -/
partial def strayConfigs (root : System.FilePath) : IO (Array String) := do
  let mut out := #[]
  let mut todo : Array (System.FilePath × String) := #[(root, "")]
  let mut seen := 0
  while h : todo.size > 0 do
    let (dir, rel) := todo[todo.size - 1]
    todo := todo.pop
    for name in ← namesIn dir do
      seen := seen + 1
      if seen > walkLimit then return out
      let path := dir / name
      let relPath := if rel.isEmpty then name else s!"{rel}/{name}"
      match ← entryAt path with
      | .dir =>
        -- a folder with a lakefile of its own is another project, with a layout of its own
        let otherProject := (← entryAt (path / "lakefile.toml")) != .missing ||
          (← entryAt (path / "lakefile.lean")) != .missing
        if !(skippedFolder name) && !(rel.isEmpty && name == folder) && !otherProject then
          todo := todo.push (path, relPath)
      | .file _ =>
        if name == comparatorConfigFile && !rel.isEmpty then out := out.push relPath
      | _ => pure ()
  return out.qsort (· < ·)

/-- Check one challenge's folder `Comparator/<name>/`. -/
def checkChallenge (root : System.FilePath) (name : String) :
    IO (Option ChallengeConfig × Array Violation) := do
  let dir := root / folder / name
  let rel := folderOf name
  let mut out : Array Violation := #[]
  let wanted := [challengeFileName, solutionFileName, comparatorConfigFile]
  for entry in ← namesIn dir do
    if entry.startsWith "." then continue
    unless wanted.contains entry do
      out := out.push { file := s!"{rel}/{entry}", rule := .folderContents
                        message := s!"a challenge's folder holds only {", ".intercalate wanted}; \
                          move or remove {shown entry}" }
  let read := fun (file : String) (limit : Nat) => do
    match ← readLimited (dir / file) limit with
    | .ok text => pure (some text, #[])
    | .error why =>
      let rule := if why == "it is missing" || why.startsWith "it is a symbolic" ||
          why == "it is not a regular file" then Rule.folderContents
        else if file == comparatorConfigFile then .configSyntax else .leanFile
      let fix := if why == "it is missing" then s!"; add {rel}/{file}" else ""
      pure (none, #[({ file := s!"{rel}/{file}", rule, message := why ++ fix } : Violation)])
  let (configText, v1) ← read comparatorConfigFile configLimit
  let (challenge, v2) ← read challengeFileName leanFileLimit
  let (solution, v3) ← read solutionFileName leanFileLimit
  out := out ++ v1 ++ v2 ++ v3
  let mut config? : Option ChallengeConfig := none
  if let some text := configText then
    let (config, problems) := checkConfig s!"{rel}/{comparatorConfigFile}" name text
    out := out ++ problems
    config? := some config
  let theorems := (config?.bind (·.theoremNames)).getD #[]
  let checkImports := fun (file : String) (code : String) (rule : Rule) =>
    (importsOf code).filterMap fun m =>
      if (`Comparator).isPrefixOf m then
        some ({ file := s!"{rel}/{file}", rule
                message := s!"it imports {m}; a challenge and its solution import no module \
                  under Comparator (they declare the same names, and each challenge stands \
                  alone): remove the import" } : Violation)
      else none
  let checkDeclared := fun (file : String) (code : String) =>
    let declared := theoremsOf code
    theorems.filterMap fun t =>
      if declared.contains t then none
      else some ({ file := s!"{rel}/{file}", rule := .theoremDeclared
                   message := s!"the judged theorem {t} (theorem_names) is not declared here with \
                     `theorem`; declare it, or correct its name in comparator.json" } : Violation)
  if let some text := challenge then
    let code := codeOnly text
    out := out ++ checkImports challengeFileName code .challengeImports
    unless hasSorry code do
      out := out.push { file := s!"{rel}/{challengeFileName}", rule := .challengeSorry
                        message := "the challenge states its theorems with `sorry` as their \
                          proofs, and this file has none: replace each proof by `sorry`" }
    out := out ++ checkDeclared challengeFileName code
  if let some text := solution then
    let code := codeOnly text
    out := out ++ checkImports solutionFileName code .solutionImports
    out := out ++ checkDeclared solutionFileName code
  return (if out.isEmpty then config? else none, out)

/-- Check the project at `root` against the layout (see the module docstring). -/
def check (root : System.FilePath) : IO Report := do
  let comparatorDir := root / folder
  let rootConfig := (← entryAt (root / comparatorConfigFile)) != .missing
  let strays ← strayConfigs root
  let dirEntry ← entryAt comparatorDir
  if dirEntry == .missing && !rootConfig && strays.isEmpty then return {}
  let mut out : Array Violation := #[]
  let mut challenges := #[]
  for stray in strays do
      out := out.push { file := stray, rule := .strayConfig
                        message := s!"a comparator.json belongs in a challenge's folder \
                          Comparator/<Name>/; move it there or remove it" }
  let legacy := (← entryAt (comparatorDir / challengeFileName)) != .missing ||
    (← entryAt (comparatorDir / solutionFileName)) != .missing
  if legacy || rootConfig then
    out := out.push { file := if legacy then s!"{folder}/{challengeFileName}" else comparatorConfigFile
                      rule := .legacy, message := legacyMessage rootConfig }
  match dirEntry with
  | .missing => pure ()
  | .dir =>
    let mut names := #[]
    for entry in ← namesIn comparatorDir do
      if entry.startsWith "." then continue
      if legacy && (entry == challengeFileName || entry == solutionFileName) then continue
      match ← entryAt (comparatorDir / entry) with
      | .dir =>
        if isChallengeName entry then names := names.push entry
        else
          out := out.push { file := s!"{folder}/{entry}", rule := .challengeName
                            message := s!"a challenge's folder name starts with a capital letter \
                              and has only ASCII letters and digits, at most {nameCharLimit} \
                              characters (it becomes the module Comparator.<Name>.Challenge); \
                              rename {shown entry}" }
      | _ =>
        out := out.push { file := s!"{folder}/{entry}", rule := .challengeName
                          message := s!"Comparator/ holds only challenge folders; move or remove \
                            {shown entry}" }
    if names.size > challengeLimit then
      out := out.push { file := folder, rule := .challengeCount
                        message := s!"there are {names.size} challenges, more than the \
                          {challengeLimit} allowed" }
    else
      for name in names do
        let (config?, problems) ← checkChallenge root name
        out := out ++ problems
        if let some config := config? then challenges := challenges.push config
  | _ =>
    out := out.push { file := folder, rule := .folderKind
                      message := "Comparator must be a folder of challenge folders, not a file or \
                        a symbolic link" }
  return { challenges, violations := out, hasComparator := true }

/-- The error text of a report with violations: one line each, after a sentence that names the
manual's chapter. -/
def Report.errorText (r : Report) : String :=
  s!"the project's Comparator files do not follow the layout (see the chapter \"Comparator \
    challenges\" of the Verso Blueprint manual); {r.violations.size} \
    {if r.violations.size == 1 then "problem" else "problems"}:\n" ++
    "\n".intercalate (r.violations.toList.map (s!"  {·.render}"))

/-- The challenges of the project at `root`, or an error naming every violation. -/
def challengesAt (root : System.FilePath) : IO (Array ChallengeConfig) := do
  let report ← check root
  unless report.violations.isEmpty do throw (IO.userError report.errorText)
  return report.challenges

end ComparatorLayout

end Informal.Stats
