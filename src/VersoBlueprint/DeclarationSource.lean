/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

import Lean
import SubVerso.Module
import SubVerso.Module.Decl
import VersoBlueprint.Data

/-!
Highlighted Lean source of the declarations that Blueprint nodes reference.

The source of a declaration is not part of the imported environment, so it is
read from the per-module highlighted-source JSON that SubVerso's `highlighted`
Lake module facet writes (`.lake/build/highlighted/<Module>.json`). Lake caches
the facet per module, so a module is only re-highlighted when it changes.

Generators call `prepare` once with every referenced module before rendering;
it runs one `lake build +M:highlighted …` for all of them and loads each module
once into a process-local store. Rendering then looks declarations up with
`find?`, which costs microseconds.
-/

namespace Informal.DeclarationSource

open Lean
open SubVerso.Highlighting
open SubVerso.Module

/--
Process-local state: whether pages render declaration sources (the side-by-side
layout), and the loaded modules (`none`: highlighting or loading failed).
-/
structure State where
  enabled : Bool := false
  modules : Std.HashMap Name (Option SubVerso.Module.Module) := {}
deriving Inhabited

initialize stateRef : IO.Ref State ← IO.mkRef {}

/-- Forget every loaded module and disable source rendering. -/
def clear : IO Unit :=
  stateRef.set {}

/-- Turn rendering of declaration sources (the side-by-side node layout) on or off. -/
def setEnabled (enabled : Bool) : IO Unit :=
  stateRef.modify fun st => { st with enabled }

/-- Whether pages currently render declaration sources. -/
def enabled : IO Bool :=
  return (← stateRef.get).enabled

/-- Run `act` with source rendering switched to `enabled`, restoring the previous setting. -/
def withEnabled {α : Type} (enabled : Bool) (act : IO α) : IO α := do
  let before ← DeclarationSource.enabled
  setEnabled enabled
  try act finally setEnabled before

/-- Register a module directly (used by tests and by callers that load data themselves). -/
def insert (moduleName : Name) (mod : SubVerso.Module.Module) : IO Unit :=
  stateRef.modify fun st => { st with modules := st.modules.insert moduleName (some mod) }

/-- Whether any module has been registered. -/
def isEmpty : IO Bool :=
  return (← stateRef.get).modules.isEmpty

/-- The JSON file that the `highlighted` facet writes for a module of the workspace at `root`. -/
def highlightedJsonPath (root : System.FilePath) (moduleName : Name) : System.FilePath :=
  let dir := root / ".lake" / "build" / "highlighted"
  (moduleName.components.foldl (init := dir) fun path c => path / c.toString (escape := false))
    |>.addExtension "json"

/--
Whether a declaration's module should get its source shown: the declaration is
present and its module is part of the workspace (not a dependency checked out
under `.lake/packages`).
-/
def wantsSource (decl : Data.ExternalRef) : Option Name := do
  guard decl.present
  match decl.provenance with
  | .inWorkspace moduleName sourcePath =>
    if (sourcePath.splitOn "/.lake/packages/").length > 1 then none else some moduleName
  | _ => none

private def loadModule (path : System.FilePath) : IO (Except String SubVerso.Module.Module) := do
  try
    let text ← IO.FS.readFile path
    match Json.parse text with
    | .error err => pure (.error s!"invalid JSON in {path}: {err}")
    | .ok json =>
      match SubVerso.Module.Module.fromJson? json with
      | .error err => pure (.error s!"could not decode {path}: {err}")
      | .ok mod => pure (.ok mod)
  catch err =>
    pure (.error s!"could not read {path}: {err}")

private def lakeCommand : IO String := do
  match ← IO.getEnv "LAKE" with
  | some lake => if lake.isEmpty then pure "lake" else pure lake
  | none => pure "lake"

/--
Highlight and load the given modules of the workspace at `root`.

Runs one `lake build +M:highlighted …` for the modules not loaded yet, then
reads their JSON files in parallel. Failures are reported through `logWarning`
and leave the affected modules without source (callers fall back to their
signature rendering).
-/
def prepare (root : System.FilePath) (modules : Array Name)
    (logWarning : String → IO Unit) (logProgress : String → IO Unit := fun _ => pure ()) :
    IO Unit := do
  let loaded := (← stateRef.get).modules
  let todo := modules.foldl (init := #[]) fun acc m =>
    if loaded.contains m || acc.contains m then acc else acc.push m
  if todo.isEmpty then return
  let targets := todo.map fun m => s!"+{m}:highlighted"
  logProgress s!"highlighting {todo.size} Lean modules for declaration sources"
  let out ← IO.Process.output {
    cmd := ← lakeCommand
    args := #["build"] ++ targets
    cwd := root
    -- SubVerso's extractor reads `.olean` files from the build directories, so
    -- artifacts kept only in a Lake artifact cache must be restored there.
    env := #[("LAKE_RESTORE_ARTIFACTS", some "true")]
  }
  if out.exitCode != 0 then
    let tail := String.intercalate "\n" ((out.stdout ++ out.stderr).splitOn "\n" |>.reverse.take 20 |>.reverse)
    logWarning s!"Blueprint declaration sources: `lake build` of the highlighted modules failed (exit {out.exitCode}); affected declarations fall back to their signatures.\n{tail}"
  let tasks ← todo.mapM fun m => IO.asTask (loadModule (highlightedJsonPath root m))
  let mut results : Array (Name × Option SubVerso.Module.Module) := #[]
  for (m, task) in todo.zip tasks do
    match task.get with
    | .ok (.ok mod) => results := results.push (m, some mod)
    | .ok (.error err) =>
      logWarning s!"Blueprint declaration sources: {err}"
      results := results.push (m, none)
    | .error err =>
      logWarning s!"Blueprint declaration sources: loading {m} failed: {err}"
      results := results.push (m, none)
  stateRef.modify fun st =>
    { st with modules := results.foldl (init := st.modules) fun ms (m, mod?) => ms.insert m mod? }

/-- Find the highlighted source of a declaration in the loaded modules. -/
def find? (decl : Data.ExternalRef) : IO (Option DeclSource) := do
  let some moduleName := wantsSource decl | return none
  let some (some mod) := (← stateRef.get).modules[moduleName]? | return none
  return mod.findDecl? decl.canonical (decl.range?.map (·.pos))

/-! ## Presentation helpers -/

/--
Drop proof states, message spans and points, keeping tokens and text. Blueprint
pages show declaration source as reading material; per-tactic proof states would
multiply the page size.
-/
partial def leaves : Highlighted → Array Highlighted
  | .seq hls => hls.foldl (init := #[]) fun acc hl => acc ++ leaves hl
  | .span _ hl => leaves hl
  | .tactics _ _ _ hl => leaves hl
  | .point .. => #[]
  | hl@(.text s) => if s.isEmpty then #[] else #[hl]
  | hl => #[hl]

private def tokenText? : Highlighted → Option String
  | .token tok => some tok.content
  | _ => none

private def opens : List String := ["(", "[", "{", "⦃", "⟨", "⟦", "⦋", "%["]

private def closes : List String := [")", "]", "}", "⦄", "⟩", "⟧", "⦌"]

private def isBlank : Highlighted → Bool
  | .text s => s.all Char.isWhitespace
  | _ => false

/-- Drop trailing whitespace from a list of leaves. -/
def trimEnd (hls : Array Highlighted) : Array Highlighted := Id.run do
  let mut hls := hls
  while hls.size > 0 do
    match hls.back? with
    | some (Highlighted.text s) =>
      let t := s.trimAsciiEnd.toString
      hls := hls.pop
      if !t.isEmpty then
        return hls.push (.text t)
    | _ => return hls
  return hls

private def isDocComment : Highlighted → Bool
  | .token ⟨.docComment, _⟩ => true
  | _ => false

/-- Drop leading whitespace, and a leading doc comment with the line break after it. -/
def trimStart (hls : Array Highlighted) : Array Highlighted := Id.run do
  let mut i := 0
  while i < hls.size && isBlank hls[i]! do i := i + 1
  if i < hls.size && isDocComment hls[i]! then
    i := i + 1
    while i < hls.size && isBlank hls[i]! do i := i + 1
  return hls.extract i hls.size

/--
The code of a command as shown next to a Blueprint node: its leaves, without
the surrounding whitespace and without its doc comment (the declaration's hover
shows the docstring).
-/
def presentation (hl : Highlighted) : Array Highlighted :=
  trimEnd (trimStart (leaves hl))

/--
Split the presented code of a theorem-like command after its top-level `:=`
(and a directly following `by`): the statement first, then the proof. Returns
`none` when there is no top-level `:=` (pattern-matching definitions,
structures) or nothing follows it.
-/
def splitStatement? (ls : Array Highlighted) : Option (Array Highlighted × Array Highlighted) := Id.run do
  let mut depth : Nat := 0
  for i in [0:ls.size] do
    if let some t := tokenText? ls[i]! then
      if opens.contains t then depth := depth + 1
      else if closes.contains t then depth := depth - 1
      else if t == ":=" && depth == 0 then
        -- include a following `by`
        let mut j := i + 1
        while j < ls.size && isBlank ls[j]! do j := j + 1
        let cut := if j < ls.size && tokenText? ls[j]! == some "by" then j + 1 else i + 1
        let rest := trimEnd (ls.extract cut ls.size)
        if rest.all isBlank then return none
        -- Drop the separator before the proof: spaces, then one line break.
        let rest : Array Highlighted := match rest[0]? with
          | some (Highlighted.text s) =>
            let s' := (s.dropWhile (· == ' ')).toString
            let s' := if s'.startsWith "\n" then (s'.drop 1).toString else s'
            if s'.isEmpty then rest.extract 1 rest.size else rest.set! 0 (Highlighted.text s')
          | _ => rest
        return some (ls.extract 0 cut, rest)
  return none

/--
Split presented code into source lines (without the line breaks), so that each
line can be laid out on its own, e.g. with a hanging indent when it wraps.
-/
def lines (hls : Array Highlighted) : Array (Array Highlighted) := Id.run do
  let mut out : Array (Array Highlighted) := #[]
  let mut current : Array Highlighted := #[]
  for hl in hls do
    match hl with
    | .text s | .unparsed s =>
      let pieces := s.splitOn "\n"
      for h : i in [0:pieces.length] do
        if i > 0 then
          out := out.push current
          current := #[]
        let piece := pieces[i]
        if !piece.isEmpty then current := current.push (.text piece)
    | other => current := current.push other
  return out.push current

end Informal.DeclarationSource
