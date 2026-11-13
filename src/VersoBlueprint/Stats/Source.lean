/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

import Lean.Data.Json

/-!
Line counts of Lean source, in the style of `cloc`: every physical line is blank, comment or
code.

* A line that holds only whitespace is blank, inside a comment or not.
* A line is code when any of it lies outside comments, string literals included.
* Every other line is a comment line. Line comments (`--`), block comments (`/- … -/`, which
  nest) and docstrings (`/-- … -/`, `/-! … -/`) all count as comments.

The scanner knows enough of Lean's lexical syntax not to mistake comment markers inside string
literals, raw string literals, character literals and `«…»` names for comments.

`leanFilesUnder` lists the `.lean` files of a directory tree, skipping hidden directories (which
include Lake's `.lake`) and never following symbolic links.
-/

namespace Informal.Stats

open Lean

/-- How many lines of a source text are blank, comments or code. -/
structure LineCounts where
  /-- Lines holding only whitespace. -/
  blank : Nat := 0
  /-- Lines holding comment text and nothing else. -/
  comment : Nat := 0
  /-- Lines holding anything outside comments. -/
  code : Nat := 0
deriving Repr, Inhabited, DecidableEq, ToJson, FromJson

/-- Every physical line. -/
def LineCounts.total (counts : LineCounts) : Nat :=
  counts.blank + counts.comment + counts.code

instance : Add LineCounts where
  add a b := { blank := a.blank + b.blank, comment := a.comment + b.comment, code := a.code + b.code }

namespace LineScan

/-- Lexical state carried from one character to the next. -/
private inductive Mode where
  | normal
  /-- Inside a block comment or docstring, with its nesting depth. -/
  | blockComment (depth : Nat)
  /-- Inside an ordinary string literal. -/
  | string
  /-- Inside a raw string literal closed by `"` and this many `#`. -/
  | rawString (hashes : Nat)
deriving Inhabited

/-- Whether a character can end an identifier, so that a following `'` belongs to it. -/
private def isIdentTail (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '\'' || c == '!' || c == '?' || c.toNat > 127

private structure State where
  mode : Mode := .normal
  /-- The current line has something outside comments. -/
  lineCode : Bool := false
  /-- The current line has comment text. -/
  lineComment : Bool := false
  /-- The current line has any character other than whitespace. -/
  lineAny : Bool := false
  counts : LineCounts := {}

private def State.endLine (s : State) : State :=
  let counts :=
    if !s.lineAny then { s.counts with blank := s.counts.blank + 1 }
    else if s.lineCode then { s.counts with code := s.counts.code + 1 }
    else { s.counts with comment := s.counts.comment + 1 }
  { s with lineCode := false, lineComment := false, lineAny := false, counts }

private def State.markCode (s : State) : State := { s with lineCode := true, lineAny := true }

private def State.markComment (s : State) : State := { s with lineComment := true, lineAny := true }

/-- The number of `#` characters at `i`. -/
private def hashesAt (cs : Array Char) (i : Nat) : Nat := Id.run do
  let mut n := 0
  while cs[i + n]? == some '#' do
    n := n + 1
  return n

/-- The index just after a character literal starting at `i` (a `'`), if there is one. -/
private def charLiteralEnd? (cs : Array Char) (i : Nat) : Option Nat :=
  match cs[i + 1]? with
  | some '\\' => Id.run do
    -- An escape: `'\n'`, `'\''`, `'\x41'`, `'\u{3B1}'`; the literal ends at the next `'`.
    let mut j := i + 3
    while j < cs.size && j < i + 12 do
      if cs[j]! == '\'' then return some (j + 1)
      if cs[j]! == '\n' then return none
      j := j + 1
    return none
  | some c => if c != '\n' && cs[i + 2]? == some '\'' then some (i + 3) else none
  | none => none

/-- Classify every line of `text`. -/
def run (text : String) : LineCounts := Id.run do
  let cs := text.toList.toArray
  let mut s : State := {}
  let mut i := 0
  while i < cs.size do
    let c := cs[i]!
    let next := cs[i + 1]?
    if c == '\n' then
      s := s.endLine
      i := i + 1
      continue
    match s.mode with
    | .blockComment depth =>
      if c == '/' && next == some '-' then
        s := { s.markComment with mode := .blockComment (depth + 1) }
        i := i + 2
      else if c == '-' && next == some '/' then
        s := { s.markComment with mode := if depth ≤ 1 then .normal else .blockComment (depth - 1) }
        i := i + 2
      else
        if !c.isWhitespace then s := s.markComment
        i := i + 1
    | .string =>
      if !c.isWhitespace then s := s.markCode
      if c == '\\' && next != some '\n' then
        i := i + 2
      else
        if c == '"' then s := { s with mode := .normal }
        i := i + 1
    | .rawString hashes =>
      if !c.isWhitespace then s := s.markCode
      if c == '"' && hashesAt cs (i + 1) ≥ hashes then
        s := { s with mode := .normal }
        i := i + 1 + hashes
      else
        i := i + 1
    | .normal =>
      let afterIdent := i > 0 && isIdentTail cs[i - 1]!
      if c == '-' && next == some '-' then
        s := s.markComment
        while i < cs.size && cs[i]! != '\n' do
          i := i + 1
      else if c == '/' && next == some '-' then
        s := { s.markComment with mode := .blockComment 1 }
        i := i + 2
      else if c == '"' then
        s := { s.markCode with mode := .string }
        i := i + 1
      else if c == 'r' && !afterIdent && cs[i + 1 + hashesAt cs (i + 1)]? == some '"' then
        let hashes := hashesAt cs (i + 1)
        s := { s.markCode with mode := .rawString hashes }
        i := i + 2 + hashes
      else if c == '\'' && !afterIdent then
        s := s.markCode
        i := (charLiteralEnd? cs i).getD (i + 1)
      else if c == '«' then
        s := s.markCode
        i := i + 1
        while i < cs.size && cs[i]! != '»' && cs[i]! != '\n' do
          i := i + 1
      else
        if !c.isWhitespace then s := s.markCode
        i := i + 1
  -- A last line without a final newline still counts.
  if s.lineAny || (cs.size > 0 && cs.back! != '\n') then
    s := s.endLine
  return s.counts

end LineScan

/-- Classify every line of a Lean source text as blank, comment or code. -/
def countLeanLines (text : String) : LineCounts :=
  LineScan.run text

/-- The `.lean` files under `root`, as paths relative to it with `/` separators, sorted.
Hidden directories (among them `.lake` and `.git`) are skipped and symbolic links are not
followed, so the walk stays inside the tree. -/
partial def leanFilesUnder (root : System.FilePath) : IO (Array String) := do
  let found ← go root ""
  return found.qsort (· < ·)
where
  go (dir : System.FilePath) (relDir : String) : IO (Array String) := do
    let entries ← try dir.readDir catch _ => pure #[]
    let mut out := #[]
    for entry in entries.qsort (·.fileName < ·.fileName) do
      if entry.fileName.startsWith "." then continue
      let rel := if relDir.isEmpty then entry.fileName else relDir ++ "/" ++ entry.fileName
      let info ← try some <$> entry.path.symlinkMetadata catch _ => pure none
      match info with
      | some m =>
        if m.type == .dir then
          out := out ++ (← go entry.path rel)
        else if m.type == .file && entry.fileName.endsWith ".lean" then
          out := out.push rel
      | none => pure ()
    return out

end Informal.Stats
