/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

-- XXX VersoManual is not module yet
-- module

import VersoManual

open Verso Doc
open Verso.Genre Manual
open Verso.Output

namespace Informal.SideBySideRuns

/-!
# Runs of side-by-side nodes

In the side-by-side layout, consecutive Blueprint blocks form a *run*: one element
(`div.bp_sbs_run`) that holds the nodes and their proofs, so the stylesheet can space a run as a
unit (each node draws its own column divider). Anything else between two blocks that shows
something on the page (prose, a code block, a heading) ends the run; a block that renders
nothing (group metadata, hidden external markup) neither joins nor ends one.

`groupRuns` wraps each stretch of blocks from one Blueprint block to another before traversal.
Whether a block between them ends the run is decided on its rendered output, when the run is
rendered. Each proof that directly follows its statement node (with the proof's Lean references
panel, if any) moves into the node's informal column, so the statement, its folded proof and the
Lean source form one unit whether or not the page script runs.
-/

/-- The name of Blueprint's informal block extension (statements and proofs). -/
def informalBlockName : Lean.Name := `Informal.Block.informal

/-- HTML class of a run element. -/
def runClass : String := "bp_sbs_run"

/-- The value of attribute `name` of a tag. -/
private def attr? (attrs : Array (String × String)) (name : String) : Option String :=
  attrs.findSome? fun (k, v) => if k == name then some v else none

/-- Whether the attributes give class `cls`. -/
private def classesContain (attrs : Array (String × String)) (cls : String) : Bool :=
  ((attr? attrs "class").getD "").splitOn " " |>.contains cls

/-- Whether an element carries class `cls`. -/
private def hasClass : Html → String → Bool
  | .element _ attrs _, cls => classesContain attrs cls
  | _, _ => false

/-- The label of a side-by-side statement node. -/
private def nodeLabel? : Html → Option String
  | .element _ attrs _ => if classesContain attrs "bp_sbs" then attr? attrs "data-bp-node" else none
  | _ => none

/-- The statement label of a proof block. -/
private def proofLabel? : Html → Option String
  | .element _ attrs _ =>
    if attr? attrs "data-bp-facet" == some "proof" then attr? attrs "data-bp-node" else none
  | _ => none

/-- Append the items of `html` to `acc`, flattening nested sequences and dropping empty ones. -/
def flattenInto (acc : Array Html) : Html → Array Html
  | .seq xs => xs.attach.foldl (init := acc) fun acc ⟨x, _⟩ => flattenInto acc x
  | h => acc.push h

/-- Whether `html` shows nothing: it has no element, and its text is only whitespace. -/
def rendersNothing (html : Html) : Bool :=
  (flattenInto #[] html).all fun
    | .text s | .raw s => s.all Char.isWhitespace
    | _ => false

/-- Append `extra` to the node's informal column. -/
private def appendToInformal (node : Html) (extra : Array Html) : Html :=
  node.rewritePost fun
    | h@(.element name attrs contents) =>
      if classesContain attrs "bp_sbs_informal" then
        .element name attrs (.seq (#[contents] ++ extra))
      else h
    | h => h

/--
Move each proof that directly follows its statement node, with the proof's Lean references
panel if one follows it, into the node's informal column.
-/
def attachProofs (items : Array Html) : Array Html := Id.run do
  let mut out : Array Html := #[]
  let mut i := 0
  while h : i < items.size do
    let item := items[i]
    i := i + 1
    match nodeLabel? item with
    | none => out := out.push item
    | some label =>
      let mut attached : Array Html := #[]
      while h' : i < items.size do
        if proofLabel? items[i] != some label then break
        attached := attached.push items[i]
        i := i + 1
        if h'' : i < items.size then
          if hasClass items[i] "bp_code_panel_wrapper" then
            attached := attached.push items[i]
            i := i + 1
      out := out.push (if attached.isEmpty then item else appendToInformal item attached)
  return out

/--
Render a run from its blocks' renderings, each paired with whether the block is a Blueprint
block. A run element holds the Blueprint blocks, each proof inside its node; another block that
renders nothing is dropped, and one that shows something ends the run element and stands between
it and the next.
-/
def renderRun (parts : Array (Bool × Html)) : Html := Id.run do
  let mut out : Array Html := #[]
  let mut run : Array Html := #[]
  for (member, html) in parts do
    if member then
      run := flattenInto run html
    else if !rendersNothing html then
      out := close out run |>.push html
      run := #[]
  return .seq (close out run)
where
  close (out run : Array Html) : Array Html :=
    if run.isEmpty then out else out.push (.element "div" #[("class", runClass)] (.seq (attachProofs run)))

/-- Whether `block` is a Blueprint block, which takes part in runs. -/
def isRunMember : Block Manual → Bool
  | .other b _ => b.name == informalBlockName
  | _ => false

-- A stretch of blocks from one Blueprint block to another, rendered as runs (see `renderRun`).
block_extension Block.sideBySideRun where
  traverse _ _ _ := pure none
  toTeX := some <| fun _goI goB _id _data blocks => do
    pure <| .seq (← blocks.mapM goB)
  toHtml :=
    open Verso.Doc.Html in
    some <| fun _goI goB _id _data blocks => do
      let parts ← blocks.mapM fun b => return (isRunMember b, ← goB b)
      pure <| renderRun parts

/--
Wrap each maximal stretch of `blocks` that begins and ends with a Blueprint block in a
`Block.sideBySideRun`; the blocks before the first and after the last stay outside.
-/
def wrapRuns (blocks : Array (Block Manual)) : Array (Block Manual) := Id.run do
  let mut out : Array (Block Manual) := #[]
  let mut run : Array (Block Manual) := #[]
  -- other blocks seen since the last Blueprint block of the run
  let mut pending : Array (Block Manual) := #[]
  for b in blocks do
    if isRunMember b then
      run := run ++ pending |>.push b
      pending := #[]
    else if run.isEmpty then
      out := out.push b
    else
      pending := pending.push b
  return (if run.isEmpty then out else out.push (.other Block.sideBySideRun run)) ++ pending

mutual
/--
The blocks that `block` stands for at its own level, with the runs of its contents grouped: the
blocks of a concatenation (at any depth), a Blueprint block as it is, and any other block with
{name}`groupBlocks` applied to the blocks it contains.
-/
def prepareBlock : Block Manual → Array (Block Manual)
  | .concat bs => bs.attach.flatMap fun ⟨b, _⟩ => prepareBlock b
  | .other ext contents =>
    if ext.name == informalBlockName then #[.other ext contents]
    else #[.other ext (groupBlocks contents)]
  | .blockquote bs => #[.blockquote (groupBlocks bs)]
  | .ul items => #[.ul (items.attach.map fun ⟨⟨bs⟩, _⟩ => ⟨groupBlocks bs⟩)]
  | .ol start items => #[.ol start (items.attach.map fun ⟨⟨bs⟩, _⟩ => ⟨groupBlocks bs⟩)]
  | .dl items => #[.dl (items.attach.map fun ⟨⟨t, bs⟩, _⟩ => ⟨t, groupBlocks bs⟩)]
  | b => #[b]
termination_by b => sizeOf b
decreasing_by
  all_goals (try decreasing_tactic)
  all_goals
    have := Array.sizeOf_lt_of_mem ‹_ ∈ items›
    grind

/--
Group the runs of `blocks` (see {name}`wrapRuns`), after flattening concatenations and grouping
inside every block that contains blocks.
-/
def groupBlocks (blocks : Array (Block Manual)) : Array (Block Manual) :=
  wrapRuns (blocks.attach.flatMap fun ⟨b, _⟩ => prepareBlock b)
termination_by sizeOf blocks
decreasing_by have := Array.sizeOf_lt_of_mem ‹_ ∈ blocks›; omega
end

/-- Wrap the runs of Blueprint blocks in every part of a document (see {name}`groupBlocks`). -/
def groupRuns (part : Part Manual) : Part Manual :=
  { part with
    content := groupBlocks part.content
    subParts := part.subParts.attach.map fun ⟨p, _⟩ => groupRuns p }
termination_by sizeOf part
decreasing_by
  have := Array.sizeOf_lt_of_mem ‹_ ∈ part.subParts›
  cases part
  simp only [Part.subParts, Lean.Doc.Part.mk.sizeOf_spec] at this ⊢
  omega

end Informal.SideBySideRuns
