/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

import Lean.Util.FoldConsts
import VersoBlueprint.Axioms
import VersoBlueprint.BuildRecord
import VersoBlueprint.Stats.Collect
import VersoBlueprint.Stats.ComparatorLayout

/-!
The headline of the project statistics: the theorems the project's Comparator challenge states,
compared with its solution.

A Comparator challenge follows `lake comparator`: a challenge module states theorems (proved by
`sorry`) together with every definition their statements need, and a solution module declares the
same theorems with the same statements and proves them. A project has one folder per challenge,
`Comparator/<Name>/` (`Informal.Stats.ComparatorLayout`, which checks the layout): the two
modules `Comparator.<Name>.Challenge` and `Comparator.<Name>.Solution`, and `comparator.json`,
which names them (`challenge_module`, `solution_module`), the theorems to judge
(`theorem_names`), definition holes the solution fills in (`definition_names`) and the axioms a
proof may use (`permitted_axioms`). Each challenge gets a headline of its own.

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

A theorem meets the comparison's conditions (`HeadlineTheorem.conditionsMet`) when the solution
has the same statement, does not depend on `sorry` and depends on no axiom outside the
challenge's permitted list (outside Lean's standard three when the challenge states no list).

What this is not: the comparison reads the compiled modules of the build the site is generated
from, and the axioms as Lean reports them for that build. It does not build the project from its
sources in a sandbox, as `lake comparator` does, and it runs no kernel: a proof that the kernel
never saw meets the conditions too. So a page calls a theorem proved only when a kernel replay
(`Informal.Replay`) also accepted the theorem with everything it depends on
(`ProjectStats.withKernelReplayAt`, which makes the comparison again in the environment the
replay exports from, with the axioms found by walking its terms). And none of this says anything
about what the statement means: that a Lean statement is the theorem of a manuscript is for a
reader to judge.
-/

namespace Informal.Stats

open Lean
open Informal Data

/-- The source file of `module` in the first of `sourceDirs` (relative to `root`) that has it. -/
def moduleSource? (root : System.FilePath) (sourceDirs : Array String) (module : Name) :
    IO (Option String) := do
  let rel := modulePath module "lean"
  for dir in sourceDirs do
    let path := if dir == "." then rel else dir ++ "/" ++ rel
    if ← (root / path).pathExists then return some path
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

/-- The compiled files of `module` on the search path `path`, each once by its real path: more
than one means that which of them a build means depends on the order of the path. -/
def compiledFilesOf (path : System.SearchPath) (module : Name) : IO (Array System.FilePath) := do
  let mut files := #[]
  for dir in path do
    let file := modToFilePath dir module "olean"
    if ← file.pathExists then
      let real ← try IO.FS.realPath file catch _ => pure file
      unless files.contains real do files := files.push real
  return files

/-- Why a module of a comparison cannot be named by its name alone, when it has more than one
compiled file on `path` (`compiledFilesOf`): the module and its files. -/
def ambiguousModule? (path : System.SearchPath) (module : Name) : IO (Option String) := do
  let files ← compiledFilesOf path module
  if files.size ≤ 1 then return none
  return some s!"{module}: {", ".intercalate (files.toList.map (·.toString))}"

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

/-- Whether a declaration is one the challenge's author wrote: it has a position in the source
(Lean records one for every declaration a command writes, whatever its name, also one whose
name starts with `_`), and it is not a constructor or a recursor. -/
private def isAuthored (ranges : NameMap DeclarationRanges) (info : ConstantInfo) : Bool :=
  ranges.contains info.name && !info.isCtor && !(match info with | .recInfo _ => true | _ => false)

/-- Whether a theorem without a source position is one Lean generates on its own: an equation
lemma, an unfolding or induction principle, an auxiliary proof, or a name Lean marks as an
internal detail. -/
private def isGeneratedTheorem (name : Name) : Bool :=
  let last := match name with | .str _ s => s | _ => ""
  (privateToUserName name).isInternalDetail || last.startsWith "eq_" || last == "eq_def" ||
    last == "eq_unfold" || last == "induct" || last == "induct_unfolding" ||
    last.startsWith "proof_" || last == "splitter" || last.startsWith "match_"

/-- The theorems of the challenge module that the default selection leaves out: those without a
source position that Lean did not generate on its own (`isGeneratedTheorem`), each with the
reason. Empty when the challenge names its theorems (`theorem_names`). -/
private def unjudgedTheorems (config : ChallengeConfig) (challenge : ChallengeModule) :
    Array (Name × String) :=
  if config.theoremNames.isSome then #[] else
    (challenge.complete.filter fun info =>
      info.isTheorem && !challenge.ranges.contains info.name && !isGeneratedTheorem info.name).map
      fun info => (info.name, "it has no position in the source, so it was not written as a \
        theorem of the challenge; name it in theorem_names to judge it")

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

/-- The axioms among `axioms` that the comparison does not allow, `sorryAx` aside (a
`sorry` is reported on its own): those outside `permitted` when the challenge states a list, else
those outside Lean's standard three. -/
def axiomsNotAllowed (permitted : Option (Array Name)) (axioms : Array Name) : Array Name :=
  axioms.filter fun a =>
    a != sorryAxiom && !(permitted.getD standardAxioms).contains a

/-- The modules `causes` that are not known to match the build, for the detail of a headline that
was not compared: "Demo.A in Demo/A.lean", with the reason when no build record says which
source it was, and how many others there are. Those that changed come first. -/
def causesDetail (causes : Array SourceChange) : String :=
  let causes := causes.filter (·.changed) ++ causes.filter (!·.changed)
  match causes[0]? with
  | none => ""
  | some c =>
    let why := if c.changed then "" else s!": {c.why}"
    let others := causes.size - 1
    let more := if others == 0 then ""
      else s!"; and {others} other {if others == 1 then "module" else "modules"}"
    s!"{c.place}{why}{more}"

/-- Why a challenge cannot be compared because a module the comparison rests on is not known to
match the build (`closureCauses`): the challenge module and the project modules it imports,
then the solution module and those it imports, directly or not. The compiled modules are what
is compared and replayed; a source edited since the build (a lemma of the library the proof uses
turned into `sorry`, say) is not what they say. A module of a package the project depends on is
not checked (`ModuleFinder`). Nothing when every one of them matches. -/
def sourcesUnavailable? (finder : ModuleFinder) (challengeModule solutionModule : Name) :
    IO (Option (Unavailable × String)) := do
  let challenge ← closureCauses finder challengeModule
  if !challenge.isEmpty then
    match challenge.find? (·.module == challengeModule) with
    | some own =>
      return some (if own.changed then (.challengeOutOfDate, own.file)
        else (.challengeProvenanceUnknown, own.why))
    | none =>
      let why := if challenge.any (·.changed) then Unavailable.challengeOutOfDate
        else .challengeProvenanceUnknown
      let changedFirst := challenge.filter (·.changed) ++ challenge.filter (!·.changed)
      return some (why, s!"{SourceChange.importsLead}{SourceChange.causesText changedFirst}")
  let solution ← closureCauses finder solutionModule
  if solution.isEmpty then return none
  let why := if solution.any (·.changed) then Unavailable.solutionOutOfDate
    else .solutionProvenanceUnknown
  return some (why, causesDetail solution)

/-- The headline of a project with the given challenge configuration, comparing with the solution
in the current environment. `root` is the project root and `layout` where its sources and
compiled modules are; `libraryPath` is searched for the compiled challenge first. -/
def Headline.compute (config : ChallengeConfig) (root : System.FilePath)
    (layout : WorkspaceLayout) (libraryPath : System.SearchPath) : CoreM Headline := do
  let env ← getEnv
  let challengeFile ← moduleSource? root layout.sourceDirs config.challengeModule
  let solutionFile ← moduleSource? root layout.sourceDirs config.solutionModule
  let base : Headline := {
    name := config.name
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
  -- the fixed names `Comparator.<Name>.*` are the same in a project and in one it depends on
  for module in #[config.challengeModule, config.solutionModule] do
    if let some why ← ambiguousModule? path module then
      return unavailable .moduleAmbiguous (some why)
  let challenge ← match ← (ChallengeModule.read olean).toBaseIO with
    | .ok challenge => pure challenge
    | .error e => return unavailable .challengeUnreadable (some (toString e))
  let source ← challengeFile.mapM fun file =>
    try IO.FS.readFile (root / file) catch _ => pure ""
  if let (some file, some text) := (challengeFile, source) then
    unless matchesSource challenge text do
      return unavailable .challengeOutOfDate (some file)
    -- the statements shown are cut from this text, the verdict is about the compiled module:
    -- the text must be the one it was compiled from
    match ← provenanceOf olean file text (what := "the compiled challenge") with
    | .same => pure ()
    | .differs => return unavailable .challengeOutOfDate (some file)
    | .unknown why => return unavailable .challengeProvenanceUnknown (some why)
  let theorems := challengeTheorems config challenge source
  let unjudged := unjudgedTheorems config challenge
  -- The solution's environment, which must also have everything the challenge imports.
  for imp in challenge.imports do
    unless env.header.moduleNames.contains imp do
      return { unavailable .importsNotAvailable (some imp.toString) theorems with unjudged }
  let some scope := importClosure env config.solutionModule
    | return { unavailable .solutionNotImported (some config.solutionModule.toString) theorems
               with unjudged }
  -- the verdict is about the compiled modules: every project module the challenge and the
  -- solution are built on must be the text that was compiled
  let finder := ModuleFinder.ofLayout root layout.sourceDirs path
  if let some (why, detail) ← sourcesUnavailable? finder config.challengeModule
      config.solutionModule then
    return { unavailable why (some detail) theorems with unjudged }
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
    -- only a theorem can be proved: a judged name the challenge declares otherwise is never one
    if let some info := challenge.complete.find? (·.name == t.name) then
      unless info.isTheorem do
        judged := judged.push { t with solution := .notTheorem, node
                                       difference := some s!"the challenge declares a \
                                         {kindTag info}" }
        continue
    if (solution t.name).isNone then
      judged := judged.push { t with solution := .missing, node }
      continue
    let axioms := sortAxioms (← declarationAxioms t.name)
    let sorryFree := !axioms.contains sorryAxiom
    let axiomsPermitted := config.permittedAxioms.map fun ok => axioms.all ok.contains
    let axiomsNotAllowed := axiomsNotAllowed config.permittedAxioms axioms
    let t := { t with sorryFree, axioms, axiomsPermitted, axiomsNotAllowed, node }
    judged := judged.push <| match firstDifference ctx t.name with
      | none =>
        { t with solution := .same, conditionsMet := sorryFree && axiomsNotAllowed.isEmpty }
      | some (decl, why) =>
        { t with solution := .differs, differingDeclaration := decl, difference := why }
  let authored := (challenge.complete.filter (isAuthored challenge.ranges ·)).qsort
    (bySource challenge.ranges)
  let definitions := authored.filter fun info => !info.isTheorem && !ctx.targets.contains info.name
  let definitions := definitions.map fun info =>
    let info := (ctx.challenge.find? info.name).getD info
    ({ name := info.name, solution := correspondenceOf ctx info } : HeadlineDefinition)
  return { base with theorems := judged, definitions, unjudged }

/-- The headline of a challenge that was not compared, with why: its modules, files and permitted
axioms, and no theorem. -/
def Headline.uncompared (config : ChallengeConfig) (root : System.FilePath)
    (layout : WorkspaceLayout) (why : Unavailable) (detail : Option String) : IO Headline := do
  return {
    name := config.name
    challengeModule := config.challengeModule, solutionModule := config.solutionModule
    challengeFile := ← moduleSource? root layout.sourceDirs config.challengeModule
    solutionFile := ← moduleSource? root layout.sourceDirs config.solutionModule
    config := config.configFile, permittedAxioms := config.permittedAxioms
    unavailable := some why, unavailableDetail := detail }

/-- The headline `h`, compared earlier, as not compared when a module the comparison rests on is
not known to match the build now (`sourcesUnavailable?`): what was compared is kept as the
challenge states it, and nothing of the solution's verdict. A headline that was not compared is
returned as it is. -/
def Headline.withSourcesChecked (finder : ModuleFinder) (h : Headline) : IO Headline := do
  if h.unavailable.isSome then return h
  let some (why, detail) ← sourcesUnavailable? finder h.challengeModule h.solutionModule
    | return h
  return { h with
    unavailable := some why, unavailableDetail := some detail, definitions := #[]
    theorems := h.theorems.map fun t =>
      { name := t.name, docstring := t.docstring, statement := t.statement } }

/-- The statistics with every compared headline checked again against the sources as they read
now (`Headline.withSourcesChecked`), just before the pages are written: a source edited after the
comparison, while the site was generated, takes the verdict back. -/
def ProjectStats.withHeadlineSources (stats : ProjectStats) (finder : ModuleFinder) :
    IO ProjectStats := do
  if stats.challenges.isEmpty then return stats
  return { stats with challenges := ← stats.challenges.mapM (·.withSourcesChecked finder) }

/-- `withHeadlineSources` for the project in the working directory, its modules found by the
captured layout and the search path of this process. Like `refreshWorkspace`, nothing changes
when the working directory is not the captured project. -/
def ProjectStats.withHeadlineSourcesNow (stats : ProjectStats) : IO ProjectStats := do
  if stats.challenges.isEmpty then return stats
  let root ← projectRoot stats.layout.projectRoot
  unless (← ProjectIdentity.read root).name == stats.identity.name do
    return stats
  let path := stats.layout.libraryDirs.toList.map (fun dir : String => root / dir) ++
    (← searchPathRef.get) ++ ((← IO.getEnv "LEAN_PATH").map System.SearchPath.parse |>.getD [])
  stats.withHeadlineSources (ModuleFinder.ofLayout root stats.layout.sourceDirs path)

/-- The headlines of the project's Comparator challenges (`ComparatorLayout.challengesAt`, which
throws when the project does not follow the layout), in the order of their names. -/
def Headline.captureAll (root : System.FilePath) (layout : WorkspaceLayout) :
    CoreM (Array Headline) := do
  let challenges ← ComparatorLayout.challengesAt root
  let libraryPath := (← searchPathRef.get) ++
    ((← IO.getEnv "LEAN_PATH").map System.SearchPath.parse |>.getD [])
  challenges.mapM fun config => Headline.compute config root layout libraryPath

/-- The statistics with a headline for each of the project's Comparator challenges. -/
def ProjectStats.withHeadline (stats : ProjectStats) : CoreM ProjectStats := do
  let root ← projectRoot stats.layout.projectRoot
  let layout ← WorkspaceLayout.current root
  let challenges ← Headline.captureAll root layout
  return { stats with challenges, hasComparatorChallenge := !challenges.isEmpty }

/-! ## The kernel replay -/

/-- The modules an environment must import before the challenge `config` can be compared in
it: the solution module and, when the compiled challenge can be read, the modules it imports. -/
def ChallengeConfig.modulesToLoad (config : ChallengeConfig) (root : System.FilePath)
    (layout : WorkspaceLayout) (libraryPath : System.SearchPath) : IO (Array Name) := do
  let path := libraryPath ++ layout.libraryDirs.toList.map fun dir : String => root / dir
  let imports ← match ← findCompiledModule? path config.challengeModule with
    | some olean =>
      match ← (ChallengeModule.read olean).toBaseIO with
      | .ok challenge => pure challenge.imports
      | .error _ => pure #[]
    | none => pure #[]
  return (#[config.solutionModule] ++ imports).foldl (init := #[]) fun acc m =>
    if acc.contains m then acc else acc.push m

/-- `Headline.compute` in the environment `env`. -/
def Headline.computeIn (env : Environment) (config : ChallengeConfig) (root : System.FilePath)
    (layout : WorkspaceLayout) (libraryPath : System.SearchPath) : IO Headline := do
  let ctx : Core.Context := { fileName := "<replay>", fileMap := default, maxHeartbeats := 0 }
  let (headline, _) ← (Headline.compute config root layout libraryPath).toIO ctx { env }
  return headline

/-- The judged theorems of `headline` with their axioms as `walked` has them (the axioms found
by walking the terms of the environment the headline was computed in, the standard three
included), and what follows from the axioms. -/
def Headline.withWalkedAxioms (headline : Headline) (walked : Array (Name × Array Name)) :
    Headline :=
  { headline with theorems := headline.theorems.map fun t =>
    -- a theorem the solution does not declare has no axioms to state
    if t.sorryFree.isNone then t else
    let axioms := sortAxioms (((walked.find? (·.1 == t.name)).map (·.2)).getD #[])
    let sorryFree := !axioms.contains sorryAxiom
    let notAllowed := axiomsNotAllowed headline.permittedAxioms axioms
    { t with
      axioms, sorryFree := some sorryFree, axiomsNotAllowed := notAllowed
      axiomsPermitted := headline.permittedAxioms.map fun ok => axioms.all ok.contains
      conditionsMet := t.solution == .same && sorryFree && notAllowed.isEmpty } }

/-- What the first half of a replay is asked to do, as a file a worker process reads
(`ReplayRequest.run`): load the compiled modules, compare the project's Comparator challenge in
that environment, and export the declarations with everything they depend on. -/
structure ReplayRequest where
  /-- The root of the Lean toolchain. -/
  sysroot : String
  /-- `ReplayConfig.searchPath`. -/
  searchPath : Array String
  /-- `ReplayConfig.projectDirs`. -/
  projectDirs : Array String
  /-- The Lean declarations of the site's nodes. -/
  targets : Array ReplayTarget
  /-- The project root. -/
  root : String
  layout : WorkspaceLayout
  /-- The project's Comparator challenges, when they are to be compared. -/
  challenges : Array ChallengeConfig := #[]
  /-- The file the export is written to. -/
  exportFile : String
  /-- The size limit of the export, in bytes. -/
  exportLimit? : Option Nat := none
  /-- The time the request may take, in milliseconds. -/
  limitMs : Nat
deriving ToJson, FromJson

/-- What the first half of a replay gave. -/
structure ReplayReply where
  /-- Why the compiled modules could not be loaded or compared, when that is so; nothing else
  is there then. -/
  notLoaded? : Option String := none
  /-- The headlines computed in the loaded environment, with the axioms walked from their terms,
  one for each challenge of the request. -/
  headlines : Array Headline := #[]
  /-- What was exported. -/
  prepared? : Option Prepared := none
deriving ToJson, FromJson

/-- Do what `request` asks, in this process. -/
def ReplayRequest.run (request : ReplayRequest) : IO ReplayReply := do
  let deadline := (← IO.monoMsNow) + request.limitMs
  let sysroot : System.FilePath := request.sysroot
  let root : System.FilePath := request.root
  let config : ReplayConfig := {
    searchPath := request.searchPath.map System.FilePath.mk
    projectDirs := request.projectDirs.map System.FilePath.mk }
  let libraryPath : System.SearchPath :=
    config.searchPath.toList ++ [sysroot / "lib" / "lean"]
  let mut modules := request.targets.filterMap (·.module?)
  -- a challenge or a solution that is not built is not compared, and the others still are
  let mut compared : Array ChallengeConfig := #[]
  let mut skipped : Array Headline := #[]
  for challenge in request.challenges do
    if (← findCompiledModule? libraryPath challenge.challengeModule).isNone then
      skipped := skipped.push (← Headline.uncompared challenge root request.layout
        .challengeNotBuilt (some challenge.challengeModule.toString))
      continue
    if (← findCompiledModule? libraryPath challenge.solutionModule).isNone then
      skipped := skipped.push (← Headline.uncompared challenge root request.layout
        .solutionNotImported (some s!"{challenge.solutionModule} is not built"))
      continue
    -- the challenge is read from its compiled file, which must be the only one of its name
    if let some message ← duplicateModule? config sysroot challenge.challengeModule then
      return { notLoaded? := some message }
    modules := modules ++ (← challenge.modulesToLoad root request.layout libraryPath)
    compared := compared.push challenge
  let loaded ← match ← loadModules config sysroot modules with
    | .ok loaded => pure loaded
    | .error message => return { notLoaded? := some message }
  -- the headline, from the environment that is exported
  let mut headlines : Array Headline := skipped
  let mut judged : Array ReplayTarget := #[]
  for challenge in compared do
    let computed ← (Headline.computeIn loaded.env challenge root request.layout
      libraryPath).toBaseIO
    let headline ← match computed with
      | .ok headline => pure headline
      | .error e =>
        return { notLoaded? := some s!"the Comparator challenge {challenge.name} could not be \
          compared: {e}" }
    let names := (headline.theorems.filter (·.sorryFree.isSome)).map (·.name)
    match restingAxioms loaded.env names (standard := true) with
    | .ok walked => headlines := headlines.push (headline.withWalkedAxioms walked)
    | .error message => return { notLoaded? := some message }
    judged := judged ++ (names.filter fun n => !judged.any (·.name == n)).map fun name =>
      ({ name } : ReplayTarget)
  let targets := request.targets ++ judged
  -- in the order of the challenges' names, as the layout lists them
  headlines := request.challenges.filterMap fun c => headlines.find? (·.name == c.name)
  if targets.isEmpty then
    let nothing : Prepared :=
      { stop? := some .failed, message := some "this site has no Lean declaration to check" }
    return { headlines, prepared? := some nothing }
  let prepared ← prepareExport loaded config.projectDirs targets request.exportFile
    request.exportLimit? deadline
  return { headlines, prepared? := some prepared }

/-- The `main` of a worker process: read the request file, do what it asks, write the reply
file (`ReplayRequest.run`). A program whose `main` calls this for `replayWorkerFlag` can be the
replay's worker (`registerReplayWorker`). -/
def replayWorkerMain (args : List String) : IO UInt32 := do
  let [requestFile, replyFile] := args
    | IO.eprintln s!"usage: {replayWorkerFlag} <request file> <reply file>"; return 2
  try
    let json ← IO.ofExcept (Json.parse (← IO.FS.readFile requestFile))
    let request ← IO.ofExcept (fromJson? (α := ReplayRequest) json)
    let reply ← request.run
    IO.FS.writeFile replyFile (toJson reply).compress
    return 0
  catch e =>
    IO.eprintln s!"kernel replay worker: {e}"
    return 1

/-- Why a replay without a worker program gives no verdict. -/
def noWorkerText : String :=
  "no program is known that loads the compiled modules in a process of its own: a generator \
    that `lean --run` runs is given one with --kernel-replay-with (`vbp build` passes itself)"

/-- The statistics with the kernel replay of the project at `root` (`Informal.Replay`): of the
Lean declarations `targets` of the site's nodes and of the theorems the project's Comparator
challenge judges, with everything they depend on.

The compiled modules are loaded once, in a process of its own: the worker the configuration
names (`ReplayConfig.worker?`). The generator's own process usually has the modules loaded
already, and a second copy of a compiled module is not mapped from the disk but read into
memory, so nothing is loaded here; without a worker the replay gives no verdict and says so
(`noWorkerText`). When the project has a Comparator
challenge (and `compare`), its headline is computed again in that environment and replaces the
captured one: the comparison, the axioms (walked from the terms, not read from the tables the
modules record) and the export that is checked then all come from the same loaded modules.
`nodeOf` gives the node of a judged theorem where the new headline has none. `config?` replaces
the configuration read from the environment (`ReplayConfig.fromEnv`), and `challenges?` the
challenges found under `root` (`ComparatorLayout.challengesAt`). -/
def ProjectStats.withKernelReplayAt (stats : ProjectStats) (root : System.FilePath)
    (targets : Array ReplayTarget) (config? : Option ReplayConfig := none)
    (compare : Bool := true) (nodeOf : Name → Option Name := fun _ => none)
    (challenges? : Option (Array ChallengeConfig) := none) :
    IO ProjectStats := do
  let config ← match config? with
    | some config => pure config
    | none => ReplayConfig.fromEnv root stats.layout.libraryDirs
  let say (line : String) : IO Unit := do
    if config.progress then IO.eprintln s!"Kernel replay: {line}"
  let asked := replayOrder (targets.map (·.name))
  let toolchain ← config.toolchain
  let version := match toolchain with
    | .ok t => t.version
    | .error (_, _, version) => version
  -- without a checker the comparison is still made, in an environment loaded the same way
  let sysroot? ← match toolchain with
    | .ok t => pure (some t.sysroot)
    | .error _ => pure (config.sysroot? <|> (← IO.getEnv "LEAN_SYSROOT").map System.FilePath.mk)
  let noVerdict (stats : ProjectStats) (outcome : Replay.Outcome)
      (message : Option String := none) : ProjectStats :=
    let result : Replay.Result := match toolchain with
      | .ok _ => { outcome, version, declarations := asked, message
                   limitSeconds := if outcome == .timedOut then some config.limitSeconds else none
                   memoryLimit := if outcome == .overMemory then config.memoryLimit? else none }
      | .error (outcome, message, _) => { outcome, version, declarations := asked, message }
    { stats with replay := some result }
  let some sysroot := sysroot?
    | return noVerdict stats .failed (some "the Lean toolchain of the checkers was not found")
  let start ← IO.monoMsNow
  let deadline := start + config.limitSeconds * 1000
  let challenges ← if !compare then pure #[]
    else match challenges? with
      | some challenges => pure challenges
      | none => ComparatorLayout.challengesAt root
  if targets.isEmpty && challenges.isEmpty then
    return noVerdict stats .failed (some "this site has no Lean declaration to check")
  -- when the modules are not loaded, nothing is compared here either, and a headline captured
  -- with the site's data in another environment is not shown beside that: the headline says why
  let uncompared (stats : ProjectStats) (why : String) : ProjectStats :=
    if challenges.isEmpty then stats else
    { stats with challenges := challenges.map fun challenge =>
        let earlier := stats.challenges.find? (·.name == challenge.name)
        { name := challenge.name
          challengeModule := challenge.challengeModule
          solutionModule := challenge.solutionModule
          challengeFile := earlier.bind (·.challengeFile)
          solutionFile := earlier.bind (·.solutionFile)
          config := challenge.configFile, permittedAxioms := challenge.permittedAxioms
          unavailable := some .modulesNotLoaded, unavailableDetail := some why } }
  let notLoaded (message : String) : ProjectStats :=
    uncompared (noVerdict stats .failed (some message)) message
  let work ← IO.FS.createTempDir
  let exportFile := work / "export.ndjson"
  let request : ReplayRequest := {
    sysroot := sysroot.toString
    searchPath := config.searchPath.map (·.toString)
    projectDirs := config.projectDirs.map (·.toString)
    targets, root := root.toString, layout := stats.layout, challenges
    exportFile := exportFile.toString, exportLimit? := config.exportLimit?
    limitMs := config.limitSeconds * 1000 }
  -- the first half, in a worker process: this process may have the modules loaded already
  let reply : Except ProjectStats ReplayReply ← match config.worker? with
    | none => pure (.error (noVerdict stats .failed (some noWorkerText)))
    | some _ => do
      say s!"loading the compiled modules and exporting \
        {Replay.counted asked.size "declaration"}\
        {if challenges.isEmpty then "" else " and the judged theorems"} with what they depend on"
      let requestFile := work / "request.json"
      let replyFile := work / "reply.json"
      IO.FS.writeFile requestFile (toJson request).compress
      match ← runWorker config sysroot requestFile replyFile deadline with
      | .timedOut => pure (.error (noVerdict stats .timedOut))
      | .overMemory => pure (.error (noVerdict stats .overMemory
          (some "the export of what the site's declarations depend on")))
      | .failed message => pure (.error (noVerdict stats .failed (some message)))
      | .done used =>
        say s!"the export process ran for {used}"
        let read : IO ReplayReply := do
          let json ← IO.ofExcept (Json.parse (← IO.FS.readFile replyFile))
          IO.ofExcept (fromJson? (α := ReplayReply) json)
        match ← read.toBaseIO with
        | .ok reply => pure (.ok reply)
        | .error e => pure (.error (noVerdict stats .failed
            (some s!"the export process left no result: {e}")))
  let cleanUp : IO Unit := do try IO.FS.removeDirAll work catch _ => pure ()
  let reply ← match reply with
    | .ok reply => pure reply
    | .error stats =>
      cleanUp
      let why := (stats.replay.map (·.whyNot)).getD ""
      say why
      return uncompared stats why
  if let some message := reply.notLoaded? then
    cleanUp
    say s!"the replay could not run to a verdict: {message}"
    return notLoaded message
  -- the headline of the loaded environment replaces the captured one
  let mut stats := stats
  if !reply.headlines.isEmpty then
    let earlier (name : Name) : Option Name :=
      (stats.challenges.findSome? (·.theorems.find? (·.name == name))).bind (·.node)
    let headlines := reply.headlines.map fun headline =>
      { headline with theorems := headline.theorems.map fun t =>
        { t with node := t.node <|> earlier t.name <|> nodeOf t.name } }
    stats := { stats with challenges := headlines, hasComparatorChallenge := true }
  let result ← match toolchain, reply.prepared? with
    | .error (outcome, message, _), prepared? =>
      -- nothing was checked: the last line says so, as it does after a check
      let result : Replay.Result := {
        outcome := outcome, version := version, message := message
        declarations := (prepared?.map (·.declarations)).getD asked
        notCovered := (prepared?.map (·.notCovered)).getD #[]
        axioms := (prepared?.map (·.axioms)).getD #[] }
      say result.whyNot
      pure result
    | .ok _, none => pure (noVerdict stats .failed (some "no export was written")).replay.get!
    | .ok toolchain, some prepared =>
      checkExport config toolchain prepared exportFile deadline
  cleanUp
  return { stats with replay := some result }

/-- `withKernelReplayAt` for the project in the working directory. Like `refreshWorkspace`,
nothing is replayed when the working directory is not the captured project. -/
def ProjectStats.withKernelReplay (stats : ProjectStats) (targets : Array ReplayTarget) :
    IO ProjectStats := do
  let root ← projectRoot stats.layout.projectRoot
  unless (← ProjectIdentity.read root).name == stats.identity.name do
    return stats
  stats.withKernelReplayAt root targets

end Informal.Stats
