/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

import SubVerso.Highlighting.Highlighted
import VersoBlueprint.CodeSite.Data

/-!
Highlighted Lean source without elaborating it: the source excerpts of a site generated from
compiled code.

A Verso Blueprint's own pages highlight a declaration from the information Lean's elaborator
recorded for it (SubVerso's `highlighted` facet: every token's kind, every name's signature and
docstring, local variables' types, tactic states). A site generated from a project's build has
less: the source text, the positions of the constants each declaration mentions (a module's
`.ilean` file records them) and, for each such constant, its signature and docstring as the
compiled environment gives them. `highlight` builds SubVerso's `Highlighted` code from exactly
that, so the excerpt is rendered by the same code, with the same classes and hovers, as a
Blueprint's own:

* a lexer splits the text into Lean's token classes: keywords, comments (line, block, doc),
  string, character and number literals, sorts, brackets, separators, delimiters and operators,
  identifiers;
* an identifier at a recorded occurrence of a constant becomes that constant, with its
  signature and docstring as hover (`Token.Kind.const`); the declaration's own name is marked as
  its definition;
* everything else is plain text.

What it cannot give, compared with an elaborated source: local variables' types, hovers on
notation and on tactic keywords, tactic states and messages. Keywords are recognised by name,
so an identifier spelled like a keyword in a position where Lean reads it as a name is coloured
as a keyword.
-/

namespace Informal.CodeSite.Highlight

open Lean
open SubVerso.Highlighting

/-- Words coloured as keywords: Lean's commands and term syntax, and the common tactics. -/
def keywords : Std.HashSet String := Std.HashSet.ofList [
  "theorem", "lemma", "def", "instance", "structure", "class", "inductive", "abbrev", "axiom",
  "opaque", "example", "where", "extends", "deriving", "with", "fun", "λ", "let", "have", "show",
  "from", "by", "at", "match", "if", "then", "else", "do", "return", "for", "in", "unless",
  "open", "namespace", "section", "end", "variable", "universe", "noncomputable", "private",
  "protected", "partial", "unsafe", "mutual", "termination_by", "decreasing_by", "calc",
  "import", "export", "set_option", "attribute", "local", "scoped", "macro", "syntax",
  "macro_rules", "notation", "infix", "infixl", "infixr", "prefix", "postfix", "omit", "include",
  "suffices", "obtain", "intro", "intros", "rintro", "exact", "refine", "apply", "rw", "rwa",
  "simp", "simp_all", "simpa", "dsimp", "norm_num", "ring", "ring_nf", "linarith", "nlinarith",
  "positivity", "omega", "decide", "native_decide", "field_simp", "push_cast", "exact_mod_cast",
  "norm_cast", "constructor", "cases", "rcases", "induction", "use", "exists", "refine'",
  "specialize", "contradiction", "exfalso", "by_contra", "by_cases", "split", "split_ifs",
  "congr", "gcongr", "ext", "funext", "trivial", "rfl", "assumption", "aesop", "tauto",
  "convert", "change", "unfold", "subst", "symm", "trans", "left", "right", "filter_upwards",
  "fin_cases", "interval_cases", "nth_rw", "calc", "first", "try", "repeat", "all_goals",
  "any_goals", "on_goal", "case", "next", "focus", "sorry", "admit", "show_term", "conv",
  "lift", "set", "clear", "rename_i", "revert", "generalize", "bound", "fun_prop", "continuity",
  "measurability", "infer_instance", "inferInstance"]

/-- Bracket atoms. -/
def brackets : List String := ["(", ")", "[", "]", "{", "}", "⟨", "⟩", "⦃", "⦄", "⟦", "⟧"]

/-- Delimiter atoms, longest first. -/
def delims : List String := ["@[", ":=", "=>", "←", "↦", ":", "|"]

/-- A position in the excerpt: 0-based line and UTF-16 column, as the data's positions are. -/
structure Pos where
  line : Nat
  col : Nat
deriving Inhabited, BEq, Repr

/-- Whether `a` comes before `b`. -/
def Pos.lt (a b : Pos) : Bool := a.line < b.line || (a.line == b.line && a.col < b.col)

/-- A lexed token with its start. -/
structure Lexeme where
  kind : Token.Kind
  text : String
  start : Pos
  /-- Plain text (white space), not a token. -/
  plain : Bool := false
deriving Inhabited

/-- The position after `c` at `p`. -/
def advance (p : Pos) (c : Char) : Pos :=
  if c == '\n' then { line := p.line + 1, col := 0 } else { p with col := p.col + c.utf16Size.toNat }

/-- The position after `s` at `p`. -/
def advanceStr (p : Pos) (s : String) : Pos := s.foldl advance p

private def isIdRestChar (c : Char) : Bool := isIdRest c

/-- Lex `chars` (the excerpt's characters) starting at `start` into lexemes. -/
partial def lex (chars : Array Char) (start : Pos) : Array Lexeme := Id.run do
  let n := chars.size
  let get (i : Nat) : Char := chars.getD i ' '
  let startsWith (i : Nat) (s : String) : Bool :=
    let cs := s.toList
    cs.length + i ≤ n && (List.range cs.length).all fun k => get (i + k) == cs[k]!
  let slice (i j : Nat) : String := String.ofList (chars.extract i j).toList
  let mut out : Array Lexeme := #[]
  let mut i := 0
  let mut pos := start
  while i < n do
    let c := get i
    let mut j := i + 1
    let mut kind : Token.Kind := .unknown
    let mut plain := false
    if c.isWhitespace then
      while j < n && (get j).isWhitespace do j := j + 1
      plain := true
    else if startsWith i "--" then
      while j < n && get j != '\n' do j := j + 1
      kind := .lineComment
    else if startsWith i "/-" then
      -- nested block comments; `/--` and `/-!` are doc comments
      let isDoc := startsWith i "/--" || startsWith i "/-!"
      let mut depth := 1
      j := i + 2
      while j < n && depth > 0 do
        if startsWith j "/-" then depth := depth + 1; j := j + 2
        else if startsWith j "-/" then depth := depth - 1; j := j + 2
        else j := j + 1
      kind := if isDoc then .docComment else .blockComment
    else if c == '"' then
      while j < n && get j != '"' do
        j := if get j == '\\' then j + 2 else j + 1
      j := min n (j + 1)
      kind := .str none false
    else if c == '\'' && i + 2 < n && (get (i + 2) == '\'' ||
        (get (i + 1) == '\\' && i + 3 < n && get (i + 3) == '\'')) &&
        !(i > 0 && isIdRestChar (get (i - 1))) then
      j := if get (i + 1) == '\\' then i + 4 else i + 3
      kind := .char (get (i + 1))
    else if c.isDigit then
      while j < n && ((get j).isAlphanum || get j == '.' && (get (j + 1)).isDigit) do j := j + 1
      kind := .num none none
    else if c == '«' then
      while j < n && get j != '»' do j := j + 1
      j := min n (j + 1)
      kind := .unknown
    else if isIdFirst c then
      -- a dotted identifier: `Nat.succ_le`, `h.1`, `x.«y»`
      while j < n && (isIdRestChar (get j) ||
          (get j == '.' && j + 1 < n && (isIdFirst (get (j + 1)) || get (j + 1) == '«' ||
            (get (j + 1)).isDigit))) do
        if get j == '.' && get (j + 1) == '«' then
          j := j + 2
          while j < n && get j != '»' do j := j + 1
          j := min n (j + 1)
        else j := j + 1
      let word := slice i j
      kind := if keywords.contains word then .keyword none none none
        else if word == "Type" || word == "Prop" || word == "Sort" then .sort none
        else .unknown
    else
      match brackets.find? (startsWith i ·) with
      | some b => j := i + b.length; kind := .bracket none none none
      | none =>
      match delims.find? (startsWith i ·) with
      | some d => j := i + d.length; kind := .delim none none none
      | none =>
      if c == ',' || c == ';' then kind := .separator none none none
      else
        -- a run of symbol characters is one operator
        let isSym (d : Char) := !d.isWhitespace && !isIdFirst d && !d.isDigit &&
          !brackets.any (·.startsWith d.toString) && d != ',' && d != ';' && d != '"'
        while j < n && isSym (get j) && !startsWith j "--" && !startsWith j "/-" do j := j + 1
        kind := .operator none none none
    let text := slice i j
    out := out.push { kind, text, start := pos, plain }
    pos := advanceStr pos text
    i := j
  return out

/-- A constant occurrence on the excerpt: where it starts and ends, the constant, whether it is
its definition. -/
structure Mark where
  start : Pos
  stop : Pos
  name : Name
  isDef : Bool

/-- The token of a constant, with its signature and docstring; plain when the data has no hover
for it (an empty hover would show nothing). -/
def constToken (hovers : NameMap Hover) (m : Mark) (text : String) : Highlighted :=
  match hovers.find? m.name with
  | some h => .token ⟨.const m.name h.signature h.doc m.isDef none, text⟩
  | none => .token ⟨.unknown, text⟩

/-- An identifier lexeme with the occurrences inside it: the parts before, at and after each
occurrence. -/
def splitIdent (hovers : NameMap Hover) (lx : Lexeme) (marks : Array Mark) : Array Highlighted :=
  Id.run do
  let chars := lx.text.toList.toArray
  let mut out := #[]
  let mut pos := lx.start
  let mut i := 0
  let mut buf := ""
  let mut current : Option Mark := none
  let flushPlain (buf : String) (out : Array Highlighted) : Array Highlighted :=
    if buf.isEmpty then out else out.push (.token ⟨.unknown, buf⟩)
  while i < chars.size do
    match current with
    | some m =>
      if !pos.lt m.stop then
        out := out.push (constToken hovers m buf)
        buf := ""
        current := none
        continue
    | none =>
      if let some m := marks.find? (·.start == pos) then
        out := flushPlain buf out
        buf := ""
        current := some m
    buf := buf.push chars[i]!
    pos := advance pos chars[i]!
    i := i + 1
  match current with
  | some m => out := out.push (constToken hovers m buf)
  | none => out := flushPlain buf out
  return out

/-- The highlighted form of `text`, an excerpt whose first character is at `start` in its file;
`occurrences` are the constants the data records in it, `hovers` their signatures and
docstrings. -/
def highlight (text : String) (start : Pos) (occurrences : Array Occurrence)
    (hovers : NameMap Hover) : Highlighted := Id.run do
  let marks := occurrences.map fun o =>
    ({ start := ⟨o.range.start.line, o.range.start.character⟩,
       stop := ⟨o.range.«end».line, o.range.«end».character⟩,
       name := o.name, isDef := o.isDef } : Mark)
  let lexemes := lex text.toList.toArray start
  let mut parts : Array Highlighted := #[]
  for lx in lexemes do
    if lx.plain then
      parts := parts.push (.text lx.text)
    else if lx.kind matches .unknown then
      let stop := advanceStr lx.start lx.text
      let inside := marks.filter fun m => !m.start.lt lx.start && m.start.lt stop
      if inside.isEmpty then parts := parts.push (.token ⟨.unknown, lx.text⟩)
      else parts := parts ++ splitIdent hovers lx inside
    else
      parts := parts.push (.token ⟨lx.kind, lx.text⟩)
  return .seq parts

/-- The highlighted form of a printed signature: token classes only (its positions are not the
source's, so no constants). -/
def highlightPlain (text : String) : Highlighted :=
  highlight text ⟨0, 0⟩ #[] {}

end Informal.CodeSite.Highlight
