/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

import Lean.Util.FoldConsts
import VersoBlueprint.Axioms
import VersoBlueprint.Stats.Collect

/-!
The headline of the project statistics: the theorems the project's Comparator challenge states,
compared with its solution.

A Comparator challenge follows `lake comparator`: a challenge module states theorems (proved by
`sorry`) together with every definition their statements need, and a solution module declares the
same theorems with the same statements and proves them. `comparator.json` at the project root
names the two modules (`challenge_module`, `solution_module`), the theorems to judge
(`theorem_names`), definition holes the solution fills in (`definition_names`) and the axioms a
proof may use (`permitted_axioms`). Without that file the modules are `Comparator.Challenge` and
`Comparator.Solution`, every theorem the challenge states is judged, and no axiom list is
stated.

The two modules declare the same names, so they cannot be imported into one environment. The
solution is taken from the environment the site is generated from, which must import it. The
challenge is read from its compiled module (the `.olean` files Lake writes), without importing
anything: only the declarations the challenge module itself makes are needed, because every
other constant its statements use comes from its imports, and those are the same compiled
modules in the environment of the site (`importsNotAvailable` otherwise).

A theorem of the challenge has the same statement in the solution when, as in `lake comparator`:
the solution declares it, as the same kind of declaration with the same universe parameters and
the same type; and every declaration of the challenge module that this type uses, directly or
through other such declarations, is declared identically by the solution (type and value,
compared as terms), except that a theorem or a definition hole only needs the same type. A
constant from an import counts as the same, since both sides have it from the same compiled
module.
-/

namespace Informal.Stats

open Lean
open Informal Data

/-! ## Configuration -/

/-- The file at the project root that configures a Comparator challenge. -/
def comparatorConfigFile : String := "comparator.json"

/-- A Comparator challenge as `lake comparator` reads it from `comparator.json`. -/
structure ChallengeConfig where
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
deriving Repr, Inhabited

/-- Read `comparator.json` text. The fields `lake comparator` requires must be there:
`challenge_module`, `solution_module`, `theorem_names` and `permitted_axioms`. -/
def ChallengeConfig.parse (text : String) : Except String ChallengeConfig := do
  let json ← Json.parse text
  let field (α : Type) [FromJson α] (name : String) (optional := false) :
      Except String (Option α) :=
    match json.getObjVal? name with
    | .ok .null | .error _ => if optional then pure none else throw s!"`{name}` is missing"
    | .ok value => (fromJson? value).map some |>.mapError fun e => s!"`{name}`: {e}"
  let moduleName (name : String) : Except String Name := do
    let module := ((← field String name).getD "").toName
    if module.isAnonymous then throw s!"`{name}` is not a module name" else pure module
  let names (name : String) (optional := false) : Except String (Option (Array Name)) := do
    return (← field (Array String) name optional).map (·.map String.toName)
  return {
    challengeModule := ← moduleName "challenge_module"
    solutionModule := ← moduleName "solution_module"
    theoremNames := ← names "theorem_names"
    definitionNames := (← names "definition_names" (optional := true)).getD #[]
    permittedAxioms := ← names "permitted_axioms"
    configFile := some comparatorConfigFile
  }

/-- The configuration in `comparator.json` at `root`, when the file is there. -/
def ChallengeConfig.atRoot? (root : System.FilePath) :
    IO (Option (Except String ChallengeConfig)) := do
  let file := root / comparatorConfigFile
  unless ← file.pathExists do return none
  try
    return some (ChallengeConfig.parse (← IO.FS.readFile file))
  catch e =>
    return some (.error (toString e))

/-- The source file of `module` in the first of `sourceDirs` (relative to `root`) that has it. -/
def moduleSource? (root : System.FilePath) (sourceDirs : Array String) (module : Name) :
    IO (Option String) := do
  let rel := modulePath module "lean"
  for dir in sourceDirs do
    let path := if dir == "." then rel else dir ++ "/" ++ rel
    if ← (root / path).pathExists then return some path
  return none

/-- The project's Comparator challenge: the one `comparator.json` configures, or else the default
modules when the source of `Comparator.Challenge` is in one of `sourceDirs`. -/
def ChallengeConfig.find? (root : System.FilePath) (sourceDirs : Array String) :
    IO (Option (Except String ChallengeConfig)) := do
  if let some config ← ChallengeConfig.atRoot? root then return some config
  let config : ChallengeConfig := {}
  if (← moduleSource? root sourceDirs config.challengeModule).isSome then
    return some (.ok config)
  return none

/-! ## The compiled challenge -/

/-- What the comparison needs from the compiled challenge module. -/
structure ChallengeModule where
  imports : Array Name := #[]
  /-- The module's declarations as an importer that sees only what it exports sees them (with
  the module system), in the order the module stores them. -/
  exported : Array ConstantInfo := #[]
  /-- The module's declarations as a non-module importer sees them, with theorems as theorems. -/
  complete : Array ConstantInfo := #[]
  /-- Where each declaration is in the source. -/
  ranges : NameMap DeclarationRanges := {}

/-- Module data stores extension entries untyped; those of `Lean.declRangeExt` are pairs. -/
private unsafe def declRangeEntriesImpl (entries : Array EnvExtensionEntry) :
    Array (Name × DeclarationRanges) :=
  entries.map unsafeCast

/-- The entries of `Lean.declRangeExt` stored in a module, which are name–range pairs. -/
@[implemented_by declRangeEntriesImpl]
private opaque declRangeEntries (entries : Array EnvExtensionEntry) :
    Array (Name × DeclarationRanges)

/-- Read a compiled module: its `.olean`, and with the module system also the `.olean.server`
and `.olean.private` parts that follow it. The regions stay mapped for the rest of the process,
since the declarations returned live in them. -/
def ChallengeModule.read (olean : System.FilePath) : IO ChallengeModule := do
  let server := olean.addExtension "server"
  let priv := olean.addExtension "private"
  let files := if ← priv.pathExists then #[olean, server, priv] else #[olean]
  let parts ← readModuleDataParts files
  let some (first, _) := parts[0]? | throw (IO.userError s!"{olean}: no module data")
  let some (last, _) := parts.back? | throw (IO.userError s!"{olean}: no module data")
  let mut ranges : NameMap DeclarationRanges := {}
  for (data, _) in parts do
    for (ext, entries) in data.entries do
      if ext == `Lean.declRangeExt then
        for (name, range) in declRangeEntries entries do
          ranges := ranges.insert name range
  return {
    imports := first.imports.map (·.module)
    exported := first.constants
    complete := last.constants
    ranges
  }

/-- The compiled module of `module`: the first `.olean` found in the directories of `path`. -/
def findCompiledModule? (path : System.SearchPath) (module : Name) :
    IO (Option System.FilePath) := do
  for dir in path do
    let file := modToFilePath dir module "olean"
    if ← file.pathExists then return some file
  return none

/-! ## Source text -/

/-- Whether `c` can be part of an identifier or keyword (any character outside ASCII that is not
a bracket, `:` or `,` counts, which is enough to find words). -/
private def isIdentChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '\'' || c == '!' || c == '?' || c == '.' ||
    (c.val ≥ 0x80 && !"()[]{}⦃⦄⟨⟩:,".contains c && !c.isWhitespace)

/-- The offset in `chars` of a position (lines from 1, columns in codepoints). -/
def offsetOf (chars : Array Char) (pos : Position) : Nat := Id.run do
  let mut line := 1
  let mut i := 0
  while line < pos.line && i < chars.size do
    if chars[i]! == '\n' then line := line + 1
    i := i + 1
  return min chars.size (i + pos.column)

/-- The offset just past the comment that starts at `i` (`--` to the end of the line, or a
nested `/- … -/`), or `i` when no comment starts there. -/
def skipComment (chars : Array Char) (i : Nat) : Nat := Id.run do
  let at_ (j : Nat) (c : Char) := chars[j]? == some c
  if at_ i '-' && at_ (i + 1) '-' then
    let mut j := i
    while j < chars.size && chars[j]! != '\n' do j := j + 1
    return j
  if at_ i '/' && at_ (i + 1) '-' then
    let mut depth := 1
    let mut j := i + 2
    while j < chars.size && depth > 0 do
      if at_ j '/' && at_ (j + 1) '-' then depth := depth + 1; j := j + 2
      else if at_ j '-' && at_ (j + 1) '/' then depth := depth - 1; j := j + 2
      else j := j + 1
    return j
  return i

/-- The docstring at offset `start` (after any whitespace), without its delimiters, with the
indentation its lines share removed. -/
def docstringAt? (chars : Array Char) (start : Nat) : Option String := Id.run do
  let mut i := start
  while i < chars.size && chars[i]!.isWhitespace do i := i + 1
  unless chars[i]? == some '/' && chars[i + 1]? == some '-' && chars[i + 2]? == some '-' do
    return none
  let stop := skipComment chars i
  if stop < i + 5 then return none
  let body := String.ofList (chars.extract (i + 3) (stop - 2)).toList
  let lines := body.splitOn "\n"
  let indent (l : String) := (l.toList.takeWhile (· == ' ')).length
  let rest := (lines.drop 1).filter (!·.trimAscii.isEmpty)
  let common := rest.foldl (init := (rest.head?.map indent).getD 0) fun m l => min m (indent l)
  let lines := lines.head!.trimAsciiStart.toString :: (lines.drop 1).map fun l =>
    String.ofList (l.toList.drop common)
  return some ("\n".intercalate lines).trimAscii.toString

/-- The statement of the declaration whose name is at `nameStart`–`nameStop`: from the keyword
before the name to the end of the signature, which is the first `:=`, `where` or `|` at the
start of a line outside brackets, comments and strings, not counting the `:=` of a `let` or
`have` inside the statement. -/
def statementAt (chars : Array Char) (nameStart nameStop : Nat) : String := Id.run do
  -- The keyword: the word before the name.
  let mut k := nameStart
  while k > 0 && chars[k - 1]!.isWhitespace do k := k - 1
  while k > 0 && isIdentChar chars[k - 1]! do k := k - 1
  let mut i := nameStop
  let mut depth := 0
  let mut pendingBinders := 0
  let mut lineStart := false
  let opens := "([{⦃⟨".toList
  let closes := ")]}⦄⟩".toList
  while i < chars.size do
    let c := chars[i]!
    let afterComment := skipComment chars i
    if afterComment != i then
      i := afterComment
      continue
    if c == '\n' then
      lineStart := true
      i := i + 1
      continue
    if c.isWhitespace then
      i := i + 1
      continue
    let atLineStart := lineStart
    lineStart := false
    if c == '"' then
      i := i + 1
      while i < chars.size && chars[i]! != '"' do
        i := if chars[i]! == '\\' then i + 2 else i + 1
      i := i + 1
      continue
    if opens.contains c then depth := depth + 1; i := i + 1; continue
    if closes.contains c then depth := depth - 1; i := i + 1; continue
    if depth == 0 then
      if c == ':' && chars[i + 1]? == some '=' then
        if pendingBinders == 0 then break
        pendingBinders := pendingBinders - 1
        i := i + 2
        continue
      if c == '|' && atLineStart then break
      if isIdentChar c && (i == 0 || !isIdentChar chars[i - 1]!) then
        let mut j := i
        while j < chars.size && isIdentChar chars[j]! do j := j + 1
        let word := String.ofList (chars.extract i j).toList
        if word == "where" then break
        if word == "let" || word == "have" then pendingBinders := pendingBinders + 1
        i := j
        continue
    i := i + 1
  return (String.ofList (chars.extract k i).toList).trimAsciiEnd.toString

/-! ## Comparison -/

/-- The modules `module` imports, directly or not, and `module` itself, when `env` has it. -/
def importClosure (env : Environment) (module : Name) : Option NameSet := Id.run do
  let names := env.header.moduleNames
  let index : Std.HashMap Name Nat := names.zipIdx.foldl (init := {}) fun m (n, i) => m.insert n i
  unless index.contains module do return none
  let mut seen : NameSet := {}
  let mut todo := #[module]
  while h : todo.size > 0 do
    let m := todo[todo.size - 1]
    todo := todo.pop
    if seen.contains m then continue
    seen := seen.insert m
    let some idx := index[m]? | continue
    for imp in (env.header.moduleData[idx]?.map (·.imports)).getD #[] do
      unless seen.contains imp.module do todo := todo.push imp.module
  return some seen

/-- What the comparison of one theorem needs. -/
structure CompareContext where
  /-- The challenge module's own declarations, at the level the solution is seen. -/
  challenge : NameMap ConstantInfo
  /-- Theorems judged; like holes, only their types are compared. -/
  targets : NameSet
  holes : NameSet
  /-- A declaration of the solution's environment: the solution module and its imports. -/
  solution : Name → Option ConstantInfo

private def kindTag : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

/-- The constants a declaration refers to, as `lake comparator` follows them: its type, its value,
the constructors and mutual types of an inductive, the type of a constructor, the rules of a
recursor. -/
def referencedConstants (info : ConstantInfo) : Array Name :=
  let refs := info.type.getUsedConstants ++
    ((info.value? (allowOpaque := true)).map (·.getUsedConstants)).getD #[]
  match info with
  | .inductInfo val => refs ++ val.ctors ++ val.all
  | .ctorInfo val => refs.push val.induct
  | .recInfo val => refs ++ val.rules.toArray.flatMap fun r => #[r.ctor] ++ r.rhs.getUsedConstants
  | _ => refs

/-- Compare one declaration by its type only (a judged theorem or a definition hole). -/
private def sameSignature (holes : NameSet) (c s : ConstantInfo) : Option String :=
  if kindTag c != kindTag s then
    some s!"the solution declares a {kindTag s}, the challenge a {kindTag c}"
  else if c.toConstantVal != s.toConstantVal then
    some (if c.isTheorem || c.isAxiom then "the statement differs" else "the type differs")
  else if holes.contains c.name then
    match c, s with
    | .defnInfo cv, .defnInfo sv =>
      if cv.safety != sv.safety then some "the definition's safety differs" else none
    | _, _ => none
  else none

/-- The first declaration on which the solution's `target` differs from the challenge's, and how:
the target's statement, then every declaration of the challenge its statement reaches. `none`
when they are the same. -/
def firstDifference (ctx : CompareContext) (target : Name) : Option (Name × String) := Id.run do
  let some c := ctx.challenge.find? target | return some (target, "not in the challenge")
  let some s := ctx.solution target | return some (target, "not in the solution")
  if let some why := sameSignature ctx.holes c s then return some (target, why)
  let mut todo := c.type.getUsedConstants
  let mut seen : NameSet := ({} : NameSet).insert target
  while h : todo.size > 0 do
    let name := todo[todo.size - 1]
    todo := todo.pop
    if seen.contains name then continue
    seen := seen.insert name
    let some s := ctx.solution name | return some (name, "not available to the solution")
    let some c := ctx.challenge.find? name | continue
    if ctx.targets.contains name || ctx.holes.contains name then
      if let some why := sameSignature ctx.holes c s then return some (name, why)
      todo := todo ++ s.type.getUsedConstants
    else
      if c != s then
        return some (name, if kindTag c != kindTag s then
          s!"the solution declares a {kindTag s}, the challenge a {kindTag c}"
          else s!"the {kindTag c} differs")
      todo := todo ++ referencedConstants c
  return none

/-- How the solution's declaration of the same name compares with a declaration of the challenge
that is not a judged theorem. -/
def correspondenceOf (ctx : CompareContext) (c : ConstantInfo) : Correspondence :=
  match ctx.solution c.name with
  | none => .missing
  | some s =>
    if ctx.holes.contains c.name then
      if (sameSignature ctx.holes c s).isNone then .hole else .differs
    else if c == s then .same else .differs

/-! ## The headline -/

/-- The Blueprint node whose Lean declarations include `name` (the first by label). -/
def nodeOfDeclaration? (state : Environment.State) (name : Name) : Option Name := Id.run do
  let mut found : Option Name := none
  for (label, registered) in state.data do
    let node := registered.toNode
    let has := node.associatedExternalRefs.any (fun r => r.present && r.canonical == name) ||
      node.literateCodes.any fun code =>
        code.definedDefs.any (·.name.eraseMacroScopes == name) ||
          code.definedTheorems.any (·.name.eraseMacroScopes == name)
    if has && found.all (label.toString < ·.toString) then found := some label
  return found

/-- Whether a declaration is one the challenge's author wrote (not generated by Lean). -/
private def isAuthored (ranges : NameMap DeclarationRanges) (info : ConstantInfo) : Bool :=
  ranges.contains info.name && !(privateToUserName info.name).isInternalDetail &&
    !info.isCtor && !(match info with | .recInfo _ => true | _ => false)

/-- Source order, from the declarations' ranges. -/
private def bySource (ranges : NameMap DeclarationRanges) (a b : ConstantInfo) : Bool :=
  match ranges.find? a.name, ranges.find? b.name with
  | some ra, some rb => ra.range.pos.line < rb.range.pos.line ||
      (ra.range.pos.line == rb.range.pos.line && ra.range.pos.column < rb.range.pos.column)
  | some _, none => true
  | _, _ => false

/-- The judged theorems' names, docstrings and statements from the challenge, before comparison. -/
private def challengeTheorems (config : ChallengeConfig) (challenge : ChallengeModule)
    (source : Option String) : Array HeadlineTheorem := Id.run do
  let chars := (source.map (·.toList.toArray)).getD #[]
  let authored := (challenge.complete.filter (isAuthored challenge.ranges ·)).qsort
    (bySource challenge.ranges)
  let names := config.theoremNames.getD (authored.filter (·.isTheorem) |>.map (·.name))
  return names.map fun name => Id.run do
    let some range := challenge.ranges.find? name | return { name }
    if chars.isEmpty then return { name }
    let start := offsetOf chars range.range.pos
    let nameStart := offsetOf chars range.selectionRange.pos
    let nameStop := offsetOf chars range.selectionRange.endPos
    return { name, docstring := docstringAt? chars start
             statement := statementAt chars nameStart nameStop }

/-- Whether the compiled challenge was compiled from `source`, as far as its declaration ranges
tell: the text at each theorem's name range spells the end of its name (theorems always have
a written name). An edit that moves a theorem breaks this, one inside a statement may not:
Lake decides when the module is rebuilt (`vbp build` builds it). -/
def matchesSource (challenge : ChallengeModule) (source : String) : Bool :=
  let chars := source.toList.toArray
  challenge.complete.all fun info =>
    if !info.isTheorem then true else
    match challenge.ranges.find? info.name with
    | none => true
    | some range =>
      let start := offsetOf chars range.selectionRange.pos
      let stop := offsetOf chars range.selectionRange.endPos
      let written := String.ofList (chars.extract start stop).toList
      let name := privateToUserName info.name
      !written.isEmpty && (name.toString (escape := false)).endsWith written

/-- The headline of a project with the given challenge configuration, comparing with the solution
in the current environment. `root` is the project root and `layout` where its sources and
compiled modules are; `libraryPath` is searched for the compiled challenge first. -/
def Headline.compute (config : ChallengeConfig) (root : System.FilePath)
    (layout : WorkspaceLayout) (libraryPath : System.SearchPath) : CoreM Headline := do
  let env ← getEnv
  let challengeFile ← moduleSource? root layout.sourceDirs config.challengeModule
  let solutionFile ← moduleSource? root layout.sourceDirs config.solutionModule
  let base : Headline := {
    challengeModule := config.challengeModule, solutionModule := config.solutionModule
    challengeFile, solutionFile, config := config.configFile
    permittedAxioms := config.permittedAxioms
  }
  let unavailable (why : Unavailable) (detail : Option String := none) (theorems := #[]) :
      Headline :=
    { base with unavailable := some why, unavailableDetail := detail, theorems }
  -- The compiled challenge, which must match its source.
  let path := libraryPath ++ layout.libraryDirs.toList.map fun dir : String => root / dir
  let some olean ← findCompiledModule? path config.challengeModule
    | return unavailable .challengeNotBuilt (some config.challengeModule.toString)
  let challenge ← match ← (ChallengeModule.read olean).toBaseIO with
    | .ok challenge => pure challenge
    | .error e => return unavailable .challengeUnreadable (some (toString e))
  let source ← challengeFile.mapM fun file =>
    try IO.FS.readFile (root / file) catch _ => pure ""
  if let (some file, some text) := (challengeFile, source) then
    unless matchesSource challenge text do
      return unavailable .challengeOutOfDate (some file)
  let theorems := challengeTheorems config challenge source
  -- The solution's environment, which must also have everything the challenge imports.
  for imp in challenge.imports do
    unless env.header.moduleNames.contains imp do
      return unavailable .importsNotAvailable (some imp.toString) theorems
  let some scope := importClosure env config.solutionModule
    | return unavailable .solutionNotImported (some config.solutionModule.toString) theorems
  let solution (name : Name) : Option ConstantInfo := do
    let info ← env.find? name
    let idx ← env.getModuleIdxFor? name
    let module ← env.header.moduleNames[idx.toNat]?
    guard (scope.contains module)
    return info
  let decls := if env.header.isModule then challenge.exported else challenge.complete
  let ctx : CompareContext := {
    challenge := decls.foldl (init := {}) fun m c => m.insert c.name c
    targets := theorems.foldl (init := {}) fun s t => s.insert t.name
    holes := config.definitionNames.foldl (init := {}) fun s n => s.insert n
    solution
  }
  let state := Environment.informalExt.getState env
  let mut judged := #[]
  for t in theorems do
    let node := nodeOfDeclaration? state t.name
    if (solution t.name).isNone then
      judged := judged.push { t with solution := .missing, node }
      continue
    let axioms := sortAxioms (← declarationAxioms t.name)
    let sorryFree := !axioms.contains sorryAxiom
    let axiomsPermitted := config.permittedAxioms.map fun ok => axioms.all ok.contains
    let t := { t with sorryFree, axioms, axiomsPermitted, node }
    judged := judged.push <| match firstDifference ctx t.name with
      | none => { t with solution := .same, proved := sorryFree }
      | some (decl, why) =>
        { t with solution := .differs, differingDeclaration := decl, difference := why }
  let authored := (challenge.complete.filter (isAuthored challenge.ranges ·)).qsort
    (bySource challenge.ranges)
  let definitions := authored.filter fun info => !info.isTheorem && !ctx.targets.contains info.name
  let definitions := definitions.map fun info =>
    let info := (ctx.challenge.find? info.name).getD info
    ({ name := info.name, solution := correspondenceOf ctx info } : HeadlineDefinition)
  return { base with theorems := judged, definitions }

/-- The project's headline, when it has a Comparator challenge (`ChallengeConfig.find?`). -/
def Headline.capture (root : System.FilePath) (layout : WorkspaceLayout) :
    CoreM (Option Headline) := do
  let some found ← ChallengeConfig.find? root layout.sourceDirs | return none
  match found with
  | .error msg =>
    return some {
      challengeModule := .anonymous, solutionModule := .anonymous
      config := some comparatorConfigFile, unavailable := some .configInvalid
      unavailableDetail := some msg }
  | .ok config =>
    let libraryPath := (← searchPathRef.get) ++
      ((← IO.getEnv "LEAN_PATH").map System.SearchPath.parse |>.getD [])
    some <$> Headline.compute config root layout libraryPath

/-- The statistics with the headline of the project's Comparator challenge, looked for in the
workspace's source directories. -/
def ProjectStats.withHeadline (stats : ProjectStats) : CoreM ProjectStats := do
  let root ← projectRoot
  let layout ← WorkspaceLayout.current root
  let headline ← Headline.capture root layout
  return { stats with headline, hasComparatorChallenge := headline.isSome }

end Informal.Stats
