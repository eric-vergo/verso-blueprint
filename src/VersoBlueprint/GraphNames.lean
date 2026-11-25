/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude (Anthropic)
-/

import Lean
import Verso.Instances.Deriving

/-!
The Lean names a dependency graph shows on its nodes.

A node with a Lean statement is labelled with the name of one declaration of its statement
(`chooseShown`: for a theorem-like node its first theorem, for a definition its first definition
that is not a constructor, field, recursor or instance of another of its declarations), without
its namespaces (`rho_irrational` for `Project.rho_irrational`) and followed by `+2` when the
statement has two more.

`labels` chooses the labels of a whole graph:

* trailing components are added where the last one does not name the declaration to a reader (a
  numeric component, or one that starts with `_`), and where the name would read the same as the
  label of another node of the graph or as another declaration of the same statement;
* a label takes up to two lines of at most `maxLineLength` characters, broken after a `.` or a
  `_`; a name that does not fit is cut in its last component, at `_` boundaries where it can,
  keeping its beginning and its end, and never in the namespaces that tell it apart;
* nodes that would still read alike, such as two nodes whose statements name the same
  declaration, show their numbers under their names (`quiet`), on a line of its own.
-/

namespace Informal.GraphNames

open Lean

/-- A declaration of a node's Lean statement, as the graph data carries it. -/
structure LeanName where
  name : Name
  /-- Whether it is a theorem-like declaration rather than a definition. -/
  isTheorem : Bool := false
  /-- Whether it was found in the environment the site was built from. -/
  present : Bool := true
deriving Inhabited, Repr, BEq, ToJson, FromJson, Quote

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

/-- The distinct declarations of `names` with their names as a reader writes them
(`userName`), in their order; anonymous names are left out. -/
def distinctNames (names : Array LeanName) : Array LeanName :=
  let (_, out) := names.foldl (init := (({} : Std.HashSet Name), #[])) fun (seen, acc) decl =>
    let name := userName decl.name
    if name.isAnonymous || seen.contains name then (seen, acc)
    else (seen.insert name, acc.push { decl with name })
  out

/-- Whether `name` is the name Lean gives an instance (`instFooBar`). -/
def instanceName (name : Name) : Bool :=
  match name with
  | .str _ s => s.startsWith "inst" && ((s.drop 4).toString.front).isUpper
  | _ => false

/-- Whether `decl` belongs to another declaration of `decls` (a constructor, field, projection
or recursor of a type, named inside its namespace) or is an instance. -/
def auxiliary (decls : Array LeanName) (decl : LeanName) : Bool :=
  instanceName decl.name ||
    decls.any fun other => other.name != decl.name && other.name.isPrefixOf decl.name

/-- The position in `decls` of the declaration a node shows: for a theorem-like node its first
theorem-like declaration, for a definition its first definition that is not `auxiliary`; else
the first that is not auxiliary, else the first. -/
def chooseShown (theoremNode : Bool) (decls : Array LeanName) : Nat :=
  let definition := decls.findIdx? fun d => !d.isTheorem && !auxiliary decls d
  let preferred := if theoremNode then decls.findIdx? (·.isTheorem) <|> definition else definition
  (preferred <|> decls.findIdx? (!auxiliary decls ·)).getD 0

/-- `decls` with the one at `i` first, the others in their order. -/
def shownFirst (decls : Array LeanName) (i : Nat) : Array LeanName :=
  match decls[i]? with
  | some shown => #[shown] ++ (decls.eraseIdxIfInBounds i)
  | none => decls

/-- The most characters of a line of a node's Lean label. -/
def maxLineLength : Nat := 20

/-- `text` on one line, or on two lines of at most `width` characters each, broken as evenly as
it can: after a `.` where one fits (namespaces on a line of their own), else after a `_` or an
ellipsis, else between the words of a camel-case name (`previewExternal` and `Missing`); `none`
when no such break fits. -/
def fitLines (text : String) (width : Nat := maxLineLength) : Option (Array String) := Id.run do
  if text.length ≤ width then return some #[text]
  let chars := text.toList.toArray
  let breakAt := fun (allowed : Nat → Bool) => Id.run do
    let mut best : Option (Nat × Nat) := none
    for i in [1:chars.size] do
      if allowed i then
        let longer := max i (chars.size - i)
        if longer ≤ width && best.all (longer < ·.2) then best := some (i, longer)
    return best
  let after := fun (p : Char → Bool) (i : Nat) => p chars[i - 1]!
  let camel := fun (i : Nat) => (chars[i - 1]!.isLower || chars[i - 1]!.isDigit) && chars[i]!.isUpper
  let best := breakAt (after (· == '.')) <|>
    breakAt (after fun c => c == '.' || c == '_' || c == '…') <|> breakAt camel
  return best.map fun (i, _) => #[String.ofList (chars.toList.take i), String.ofList (chars.toList.drop i)]

/-- `text` cut in the middle to `limit` characters, an ellipsis in place of what is left out. -/
def cutMiddle (text : String) (limit : Nat) : String :=
  if text.length ≤ limit then text
  else
    let tail := limit / 2
    let head := limit - 1 - tail
    (text.take head).toString ++ "…" ++ (text.takeEnd tail).toString

/-- The lines of the last `count` components of `name`: one or two lines of at most `width`
characters (`lines` of them at most). A name too long for them is cut in its last component:
whole `_`-separated words from its beginning and its end where they fit (the most text, then the
most of its end), else characters; the components before the last one are kept whole. -/
def layoutName (name : Name) (count : Nat) (width : Nat := maxLineLength) (lines : Nat := 2) :
    Array String := Id.run do
  let full := (suffix name count).toString
  let fits := fun (text : String) =>
    if lines ≤ 1 then if text.length ≤ width then some #[text] else none else fitLines text width
  if let some ls := fits full then return ls
  let last := (suffix name 1).toString
  let pre := if count ≥ 2 then (suffix name count).toString.dropEnd last.length |>.toString else ""
  let words := (last.splitOn "_").toArray
  let mut best : Option (Nat × Nat × Array String) := none
  for h in [1:words.size] do
    for t in [1:words.size - h + 1] do
      if h + t < words.size then
        let text := pre ++ "_".intercalate (words.extract 0 h).toList ++ "…" ++
          "_".intercalate (words.extract (words.size - t) words.size).toList
        if let some ls := fits text then
          let kept := text.length
          let tailLength := ("_".intercalate (words.extract (words.size - t) words.size).toList).length
          if best.all fun (k, tl, _) => kept > k || (kept == k && tailLength > tl) then
            best := some (kept, tailLength, ls)
  if let some (_, _, ls) := best then return ls
  -- no cut at word boundaries fits: characters, the namespaces kept whole where they fit
  if lines ≤ 1 then
    return #[if pre.length + 4 ≤ width then pre ++ cutMiddle last (width - pre.length)
      else cutMiddle full width]
  if full.length ≤ 2 * width then
    return #[(full.take width).toString, (full.drop width).toString]
  if pre.length + 4 ≤ width then
    let room := width - pre.length
    return #[pre ++ (last.take room).toString, "…" ++ (last.takeEnd (width - 1)).toString]
  return #[(full.take width).toString, "…" ++ (full.takeEnd (width - 1)).toString]

/-- A node's Lean label: its lines, the declaration it names, how many further declarations
its statement has, and the line under it that tells it from nodes that read alike (`quiet`,
its number). -/
structure Label where
  lines : Array String
  name : Name
  more : Nat
  quiet : Option String := none
deriving Inhabited, Repr, BEq

/-- The text of a label on one line, for comparing labels. -/
def Label.text (label : Label) : String :=
  String.join label.lines.toList

/-- What `labels` needs of a node: the declarations of its Lean statement in the order the
author wrote them, whether it is theorem-like, and its number (or its name), shown under the
label of a node that would read like another. -/
structure Input where
  decls : Array LeanName
  theoremNode : Bool := false
  number : String := ""
deriving Inhabited

/-- The keys under which two labels a reader could take for one meet: the label's text, and for
a cut label the text around its ellipsis (its first and last four characters), so that labels
that differ only in where their ellipses fall meet too. -/
def alikeKeys (text : String) : Array String :=
  if text.contains '…' then
    #[text, "…" ++ (((text.splitOn "…").getD 0 "").take 4).toString ++ "…" ++
      (((text.splitOn "…").getLastD "").takeEnd 4).toString]
  else #[text]

/-- The Lean labels of the nodes of one graph (see the module docstring); `none` for a node
without a Lean statement. A node's label names its shown declaration (`chooseShown`) with the
fewest trailing components that are readable (`readableLength`) and that no other node's shown
declaration, and no other declaration of the node, ends with. -/
def labels (nodes : Array Input) (width : Nat := maxLineLength) : Array (Option Label) := Id.run do
  let nodes := nodes.map fun n => { n with decls := distinctNames n.decls }
  let shown : Array (Option Name) := nodes.map fun n =>
    (n.decls[chooseShown n.theoremNode n.decls]?).map (·.name)
  -- how many nodes show each declaration, and how many distinct shown names end with a suffix
  let mut uses : Std.HashMap Name Nat := {}
  for s in shown do
    if let some name := s then uses := uses.insert name (uses.getD name 0 + 1)
  let mut ending : Std.HashMap Name Nat := {}
  for (name, _) in uses do
    for k in [1:name.getNumParts + 1] do
      let key := suffix name k
      ending := ending.insert key (ending.getD key 0 + 1)
  let mut counts : Array Nat := #[]
  for n in nodes, s in shown do
    match s with
    | none => counts := counts.push 0
    | some name =>
      let others := n.decls.filter (·.name != name)
      let clear := fun (k : Nat) =>
        let key := suffix name k
        ending.getD key 0 ≤ 1 && others.all (suffix ·.name k != key)
      let length := name.getNumParts
      counts := counts.push (((List.range (length + 1)).find? fun k =>
        k ≥ readableLength name && clear k).getD length)
  -- the labels, then the nodes that would read alike get their numbers under their names
  let layout : Nat → Bool → Option Label := fun i quiet => do
    let name ← shown[i]!
    let n := nodes[i]!
    let lines := layoutName name counts[i]! width
    some { lines, name, more := n.decls.size - 1, quiet := if quiet then some n.number else none }
  let mut out : Array (Option Label) := (Array.range nodes.size).map fun i =>
    layout i (shown[i]!.any (uses.getD · 0 > 1))
  -- nodes whose labels meet under a key (`alikeKeys`) but show different declarations
  let mut groups : Std.HashMap String (Array Nat) := {}
  for label? in out, i in [0:out.size] do
    if let some label := label? then
      for key in alikeKeys label.text do
        groups := groups.insert key ((groups.getD key #[]).push i)
  let mut alike : Std.HashSet Nat := {}
  for (_, members) in groups do
    let names := members.foldl (init := ({} : Std.HashSet Name)) fun acc i =>
      match shown[i]! with | some n => acc.insert n | none => acc
    if names.size > 1 then
      for i in members do alike := alike.insert i
  for i in alike do
    out := out.set! i (layout i true)
  return out

end Informal.GraphNames
