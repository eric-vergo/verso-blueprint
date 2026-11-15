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

/-- Whether a byte can end an identifier, so that a following `'` belongs to it. Every byte of
a non-ASCII character counts, as Lean identifiers may hold such letters. -/
private def isIdentTail (c : UInt8) : Bool :=
  (c >= 48 && c <= 57) || (c >= 65 && c <= 90) || (c >= 97 && c <= 122) || c == 95 ||
    c == 39 || c == 33 || c == 63 || c >= 128

/-- ASCII whitespace other than the newline. -/
private def isSpace (c : UInt8) : Bool :=
  c == 32 || c == 9 || c == 13 || c == 11 || c == 12

private structure State where
  mode : Mode := .normal
  /-- The current line has something outside comments. -/
  lineCode : Bool := false
  /-- The current line has any character other than whitespace. -/
  lineAny : Bool := false
  counts : LineCounts := {}

private def State.endLine (s : State) : State :=
  let counts :=
    if !s.lineAny then { s.counts with blank := s.counts.blank + 1 }
    else if s.lineCode then { s.counts with code := s.counts.code + 1 }
    else { s.counts with comment := s.counts.comment + 1 }
  { s with lineCode := false, lineAny := false, counts }

private def State.markCode (s : State) : State := { s with lineCode := true, lineAny := true }

private def State.markComment (s : State) : State := { s with lineAny := true }

/-- The byte at `i`, or `0` past the end. -/
@[inline] private def at_ (bs : ByteArray) (i : Nat) : UInt8 :=
  if h : i < bs.size then bs[i] else 0

/-- The number of `#` bytes at `i`. -/
private def hashesAt (bs : ByteArray) (i : Nat) : Nat := Id.run do
  let mut n := 0
  while at_ bs (i + n) == 35 do
    n := n + 1
  return n

/-- The length of the UTF-8 character whose first byte is `c`. -/
private def utf8Length (c : UInt8) : Nat :=
  if c < 0x80 then 1 else if c < 0xE0 then 2 else if c < 0xF0 then 3 else 4

/-- The index just after a character literal starting at `i` (a `'`), if there is one. -/
private def charLiteralEnd? (bs : ByteArray) (i : Nat) : Option Nat :=
  let c := at_ bs (i + 1)
  if c == 92 then Id.run do
    -- An escape: `'\n'`, `'\''`, `'\x41'`, `'\u{3B1}'`; the literal ends at the next `'`.
    let mut j := i + 3
    while j < bs.size && j < i + 12 do
      if at_ bs j == 39 then return some (j + 1)
      if at_ bs j == 10 then return none
      j := j + 1
    return none
  else if c == 10 || c == 0 then none
  else
    let close := i + 1 + utf8Length c
    if at_ bs close == 39 then some (close + 1) else none

/-- Classify every line of `text`. The scan works on UTF-8 bytes: every marker it looks for is
ASCII except `«` and `»`, which it matches by their two bytes. -/
def run (text : String) : LineCounts := Id.run do
  let bs := text.toUTF8
  let mut s : State := {}
  let mut i := 0
  while i < bs.size do
    let c := at_ bs i
    let next := at_ bs (i + 1)
    if c == 10 then
      s := s.endLine
      i := i + 1
      continue
    match s.mode with
    | .blockComment depth =>
      if c == 47 && next == 45 then
        s := { s.markComment with mode := .blockComment (depth + 1) }
        i := i + 2
      else if c == 45 && next == 47 then
        s := { s.markComment with mode := if depth ≤ 1 then .normal else .blockComment (depth - 1) }
        i := i + 2
      else
        if !isSpace c then s := s.markComment
        i := i + 1
    | .string =>
      if !isSpace c then s := s.markCode
      if c == 92 && next != 10 then
        i := i + 2
      else
        if c == 34 then s := { s with mode := .normal }
        i := i + 1
    | .rawString hashes =>
      if !isSpace c then s := s.markCode
      if c == 34 && hashesAt bs (i + 1) ≥ hashes then
        s := { s with mode := .normal }
        i := i + 1 + hashes
      else
        i := i + 1
    | .normal =>
      let afterIdent := i > 0 && isIdentTail (at_ bs (i - 1))
      if c == 45 && next == 45 then
        -- `--`: the rest of the line is a comment.
        s := s.markComment
        while i < bs.size && at_ bs i != 10 do
          i := i + 1
      else if c == 47 && next == 45 then
        s := { s.markComment with mode := .blockComment 1 }
        i := i + 2
      else if c == 34 then
        s := { s.markCode with mode := .string }
        i := i + 1
      else if c == 114 && !afterIdent && at_ bs (i + 1 + hashesAt bs (i + 1)) == 34 then
        let hashes := hashesAt bs (i + 1)
        s := { s.markCode with mode := .rawString hashes }
        i := i + 2 + hashes
      else if c == 39 && !afterIdent then
        s := s.markCode
        i := (charLiteralEnd? bs i).getD (i + 1)
      else if c == 0xC2 && next == 0xAB then
        -- `«…»`: a quoted name, which may hold comment markers.
        s := s.markCode
        i := i + 2
        while i < bs.size && at_ bs i != 10 && !(at_ bs i == 0xC2 && at_ bs (i + 1) == 0xBB) do
          i := i + 1
      else
        if !isSpace c then s := s.markCode
        i := i + 1
  -- A last line without a final newline still counts.
  if s.lineAny || (bs.size > 0 && at_ bs (bs.size - 1) != 10) then
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
