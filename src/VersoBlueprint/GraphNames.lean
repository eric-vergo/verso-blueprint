/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

import Lean

/-!
The Lean names a dependency graph shows on its nodes.

A node with a Lean statement is labelled with the name of its statement's first declaration
without its namespaces (`rho_irrational` for `Project.rho_irrational`), followed by `+2` when the
statement has two more. Trailing components are added where the last one does not name the
declaration to a reader (a numeric component, or one that starts with `_`), and where the name
would read the same as the label of another node of the graph or as another declaration of the
same statement. A label longer than `maxLabelLength` characters is shortened with an ellipsis in
the middle of its last component, and at the namespace side where its namespaces take more than
half of it.
-/

namespace Informal.GraphNames

open Lean

/-- A declaration name as a reader writes it: macro scopes erased and the prefix of a private
declaration left out. -/
def userName (name : Name) : Name :=
  privateToUserName name.eraseMacroScopes

/-- Whether a component of a name names a declaration to a reader on its own: a string that is
not empty, does not start with `_` and is not a number. -/
def readableComponent : Name → Bool
  | .str _ s => !s.isEmpty && !s.startsWith "_" && !s.all Char.isDigit
  | _ => false

/-- The last `count` components of `name` (all of them when it has fewer). -/
def suffix (name : Name) (count : Nat) : Name :=
  let components := name.components
  (components.drop (components.length - count)).foldl (· ++ ·) .anonymous

/-- The fewest trailing components of `name` that include a readable one
(`readableComponent`); all of them when none is. -/
def readableLength (name : Name) : Nat :=
  let components := name.components.reverse
  match components.findIdx? readableComponent with
  | some i => i + 1
  | none => components.length

/-- The most characters of a node's Lean label, without the count of further declarations. -/
def maxLabelLength : Nat := 30

/-- `text` cut in the middle to `limit` characters, an ellipsis in place of what is left out. -/
def cutMiddle (text : String) (limit : Nat := maxLabelLength) : String :=
  if text.length ≤ limit then text
  else
    let tail := limit / 2
    let head := limit - 1 - tail
    (text.take head).toString ++ "…" ++ (text.takeEnd tail).toString

/-- The last `count` components of `name` as a label of at most `limit` characters. A label
that is too long keeps the components before the last one where they take at most half of it,
leaving out leading ones behind an ellipsis where they take more, and is cut in the middle of
its last component: the components that tell two names apart stay where they fit. -/
def shorten (name : Name) (count : Nat) (limit : Nat := maxLabelLength) : String := Id.run do
  let full := (suffix name count).toString
  if full.length ≤ limit then return full
  let last := (suffix name 1).toString
  for j in (List.range (count + 1)).reverse do
    if j ≥ 1 then
      let leading := if j ≥ 2 then
        (((suffix name j).components.dropLast).foldl (· ++ ·) Name.anonymous).toString ++ "."
        else ""
      let head := (if j < count then "…" else "") ++ leading
      if j == 1 || head.length ≤ limit / 2 then
        return head ++ cutMiddle last (limit - head.length)
  return cutMiddle last limit

/-- The Lean label of a node: its text, the declaration it names and how many further
declarations the node's statement has. -/
structure Label where
  text : String
  name : Name
  more : Nat
deriving Inhabited, Repr, BEq

/-- The distinct names of `names` as a reader writes them (`userName`), in their order. -/
def distinctNames (names : Array Name) : Array Name :=
  names.foldl (init := #[]) fun acc name =>
    let name := userName name
    if name.isAnonymous || acc.contains name then acc else acc.push name

/-- The Lean labels of the nodes of one graph, from the declarations of each node's statement
in the order the author wrote them; `none` for a node without one. A node's label names its
first declaration with the fewest trailing components that are readable
(`readableLength`) and that no other node's first declaration, and no other declaration of the
node, ends with. -/
def labels (nodes : Array (Array Name)) : Array (Option Label) := Id.run do
  let nodes := nodes.map distinctNames
  let firsts := nodes.foldl (init := #[]) fun acc names =>
    match names[0]? with
    | some name => if acc.contains name then acc else acc.push name
    | none => acc
  -- for every suffix, how many distinct first declarations end with it
  let mut ending : Std.HashMap Name Nat := {}
  for name in firsts do
    for k in [1:name.getNumParts + 1] do
      let key := suffix name k
      ending := ending.insert key (ending.getD key 0 + 1)
  let mut out := #[]
  for names in nodes do
    match names[0]? with
    | none => out := out.push none
    | some name =>
      let length := name.getNumParts
      let others := names.extract 1 names.size
      let clear := fun (k : Nat) =>
        let key := suffix name k
        ending.getD key 0 ≤ 1 && others.all (suffix · k != key)
      let count := ((List.range (length + 1)).find? fun k =>
        k ≥ readableLength name && clear k).getD length
      out := out.push (some { text := shorten name count, name, more := names.size - 1 })
  return out

end Informal.GraphNames
