/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

import Lean.Data.Json

/-!
# Names in Blueprint JSON

Blueprint labels are arbitrary strings made into names (`Name.mkSimple`), so a label need not be
writable as a Lean name: `Name.toString` cannot escape a component that holds `»`, and Lean then
reads the string back as another name or not at all. The render model, the manifests and the
generated pages carry labels, their parents and declaration names as JSON, so every name written
there has to read back as itself.

`Informal.NameJson.encode` writes a name as `Name.toString` does whenever Lean reads that back as
the same name (every name that can be written in Lean syntax), and otherwise in an escaped form:
each string component in guillemets with every `»` doubled, each numeric component as its digits,
joined by `.`. `Informal.NameJson.decode?` reads both. The instances are scoped to `Informal`: the
structures declared in that namespace (the render model and everything in it) use them, and so does
code that opens it; other code keeps Lean's own.
-/

namespace Informal.NameJson

open Lean

/-- The name Lean reads from `s` as a name literal (`` `s ``), as `FromJson Name` does. -/
def leanRead? (s : String) : Option Name :=
  (fromJson? (α := Name) (Json.str s)).toOption

/-- The escaped form of `n`'s components (see the module docstring). -/
def escapedParts : Name → List String
  | .anonymous => []
  | .str p s => escapedParts p ++ ["«" ++ s.replace "»" "»»" ++ "»"]
  | .num p k => escapedParts p ++ [toString k]

mutual
/-- Reads the escaped form from `cs`, after the components `pre`; `none` when it is not one. -/
def readParts : List Char → Name → Option Name
  | '«' :: cs, pre => readQuoted cs pre ""
  | c :: cs, pre => if c.isDigit then readDigits cs pre c.toString else none
  | [], _ => none

/-- Reads a quoted component whose text so far is `acc`, after the components `pre`. -/
def readQuoted : List Char → Name → String → Option Name
  | '»' :: '»' :: cs, pre, acc => readQuoted cs pre (acc.push '»')
  | '»' :: '.' :: cs, pre, acc => readParts cs (.str pre acc)
  | ['»'], pre, acc => some (.str pre acc)
  | '»' :: _ :: _, _, _ => none
  | c :: cs, pre, acc => readQuoted cs pre (acc.push c)
  | [], _, _ => none

/-- Reads a numeric component whose digits so far are `acc`, after the components `pre`. -/
def readDigits : List Char → Name → String → Option Name
  | '.' :: cs, pre, acc => readParts cs (.num pre acc.toNat!)
  | c :: cs, pre, acc => if c.isDigit then readDigits cs pre (acc.push c) else none
  | [], pre, acc => some (.num pre acc.toNat!)
end

/-- How `n` is written: `Name.toString` when Lean reads that back as `n`, else the escaped form. -/
def encode (n : Name) : String :=
  let s := n.toString
  if leanRead? s == some n then s else ".".intercalate (escapedParts n)

/--
The name written as `s`. Of the names Lean reads from `s` and from its escaped form, the one that
`encode` writes as `s`; when neither is (text that no name is written as), the name Lean reads,
as `FromJson Name` would. `none` when neither reading succeeds.
-/
def decode? (s : String) : Option Name :=
  let escaped? := (readParts s.toList .anonymous).filter (encode · == s)
  match leanRead? s with
  | some n => if encode n == s then some n else escaped?.orElse fun _ => some n
  | none => escaped?

end Informal.NameJson

namespace Informal

open Lean NameJson

/-- Every name read back as itself: `decode? (encode n) = some n` (checked in the tests). -/
scoped instance (priority := high) instToJsonName : ToJson Name := ⟨fun n => .str (encode n)⟩

/-- Reads what `instToJsonName` writes; an error naming the text when it is no name. -/
scoped instance (priority := high) instFromJsonName : FromJson Name where
  fromJson? json := do
    let s ← json.getStr?
    match decode? s with
    | some n => return n
    | none => throw s!"not a name: {s.quote}"

end Informal
