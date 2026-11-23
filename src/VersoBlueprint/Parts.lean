/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

import VersoManual
import VersoBlueprint.Lib.ExtensionDecode

/-!
Parts: a grouping level above chapters, as in a LaTeX book.

A part is an ordinary Verso part directly under the document's root whose text contains
`{blueprint_part}`; its own subparts are its chapters. Before the document is traversed,
`numberParts` gives each part its number (`Part II`) and moves its chapters out of it, so that they
follow the part's page as siblings. Verso then numbers the chapters as it numbers every chapter of
the root: in one sequence through all parts, with the numbers of their statements following. The
part's page is unnumbered and is titled `Part II — <title>`.
-/

namespace Informal.Parts

open Lean
open Verso Doc Genre Manual

/-- What a part's marker knows once the document's parts are numbered: the part's numeral. -/
structure PartMarker where
  /-- The part's number as a Roman numeral, set by `numberParts`. A marker without one is not in
  a part directly under the document's root. -/
  numeral : Option String := none
deriving Inhabited, Repr, BEq, ToJson, FromJson

block_extension Block.part (marker : PartMarker) where
  data := toJson marker
  traverse _id _data _contents := pure none
  toTeX := some fun _goI _goB _id _data _blocks => pure .empty
  toHtml := some fun _goI _goB _id json _blocks => do
    let some marker ← Informal.ExtensionDecode.decode? (α := PartMarker) json
        (fun err => s!"Malformed data in Block.part.toHtml ({err})")
      | pure .empty
    if marker.numeral.isNone then
      Verso.reportError "`{blueprint_part}` marks a part only directly under the document's \
        root, with its chapters as the part's subparts; this one is deeper in the document"
    pure .empty

/-- The Roman numeral of a positive number, such as `XIV` for 14; `0` gives the empty string. -/
def romanNumeral (n : Nat) : String := Id.run do
  let table : List (Nat × String) := [(1000, "M"), (900, "CM"), (500, "D"), (400, "CD"),
    (100, "C"), (90, "XC"), (50, "L"), (40, "XL"), (10, "X"), (9, "IX"), (5, "V"), (4, "IV"),
    (1, "I")]
  let mut rest := n
  let mut out := ""
  for (value, numeral) in table do
    while rest ≥ value do
      out := out ++ numeral
      rest := rest - value
  return out

/-- Whether a block is a part's marker, or holds one (a command's block is elaborated into a
sequence). -/
partial def isMarker : Doc.Block Manual → Bool
  | .other block _ => block.name == ``Block.part
  | .concat blocks => blocks.any isMarker
  | _ => false

/-- The block with its markers numbered `numeral`. -/
partial def numberMarkers (numeral : String) : Doc.Block Manual → Doc.Block Manual
  | .other block contents =>
    if block.name == ``Block.part then .other (Block.part { numeral := some numeral }) #[]
    else .other block contents
  | .concat blocks => .concat (blocks.map (numberMarkers numeral))
  | block => block

/-- Whether a part is marked as a part of the document (`{blueprint_part}` in its own text). -/
def isMarked (part : Part Manual) : Bool :=
  part.content.any isMarker

/-- The title prefix of the part numbered `numeral`. -/
def titlePrefix (numeral : String) : String := s!"Part {numeral} — "

/-- The part's page, numbered: titled `Part II — <title>`, unnumbered among the chapters, written
to the folder `Part-II` unless the part names its own file, without its chapters. -/
def numberedPage (numeral : String) (part : Part Manual) : Part Manual :=
  let metadata := part.metadata.getD {}
  let pre := titlePrefix numeral
  { part with
    title := #[.text pre] ++ part.title
    titleString := pre ++ part.titleString
    metadata := some { metadata with number := false, file := metadata.file <|> some s!"Part-{numeral}" }
    content := part.content.map fun block =>
      if isMarker block then numberMarkers numeral block else block
    subParts := #[] }

/--
Number the parts of a document: every part directly under the root that contains
`{blueprint_part}` is followed by its own subparts, its chapters, as parts of the root, and its
page is numbered (`numberedPage`). A document without parts is returned as it is.
-/
def numberParts (text : Part Manual) : Part Manual := Id.run do
  if !text.subParts.any isMarked then return text
  let mut subParts : Array (Part Manual) := #[]
  let mut count := 0
  for part in text.subParts do
    if isMarked part then
      count := count + 1
      subParts := subParts.push (numberedPage (romanNumeral count) part) ++ part.subParts
    else
      subParts := subParts.push part
  return { text with subParts }

end Informal.Parts

open Verso Doc Elab in
/--
`{blueprint_part}` makes the part it stands in a part of the document, a grouping of chapters: its
subparts are its chapters. Chapter numbers run on from part to part.
-/
@[block_command]
public meta def blueprint_part : BlockCommandOf Unit
  | () => ``(Verso.Doc.Block.other (Informal.Parts.Block.part {}) #[])
