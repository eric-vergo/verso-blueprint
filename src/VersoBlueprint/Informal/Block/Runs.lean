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
unit and draw one column divider through it. Anything else between two blocks (prose, a code
block, a heading) ends the run.

`groupRuns` wraps the runs of a document before traversal. When a run is rendered, each
proof that directly follows its statement node (with the proof's Lean references panel, if any)
moves into the node's informal column, so the statement, its folded proof and the Lean source
form one unit whether or not the page script runs.
-/

/-- The name of Blueprint's informal block extension (statements and proofs). -/
def informalBlockName : Lean.Name := `Informal.Block.informal

/-- Blocks that render nothing and so neither join nor end a run on their own. -/
def transparentBlockNames : List Lean.Name := [`Informal.Block.groupMetadata]

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
  | .tag _ attrs _, cls => classesContain attrs cls
  | _, _ => false

/-- The label of a side-by-side statement node. -/
private def nodeLabel? : Html → Option String
  | .tag _ attrs _ => if classesContain attrs "bp_sbs" then attr? attrs "data-bp-node" else none
  | _ => none

/-- The statement label of a proof block. -/
private def proofLabel? : Html → Option String
  | .tag _ attrs _ =>
    if attr? attrs "data-bp-facet" == some "proof" then attr? attrs "data-bp-node" else none
  | _ => none

/-- Flatten nested sequences, dropping empty ones. -/
private partial def flattenInto (acc : Array Html) : Html → Array Html
  | .seq xs => xs.foldl flattenInto acc
  | h => acc.push h

/-- Append `extra` to the node's informal column. -/
private def appendToInformal (node : Html) (extra : Array Html) : Html :=
  node.visitM (m := Id) (tag := fun name attrs contents =>
    if classesContain attrs "bp_sbs_informal" then
      some (.tag name attrs (.seq (#[contents] ++ extra)))
    else none)

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

/-- A rendered run: the run element around its parts, each proof inside its node. -/
def renderRun (parts : Array Html) : Html :=
  .tag "div" #[("class", runClass)] (.seq (attachProofs (parts.foldl flattenInto #[])))

-- A run of consecutive side-by-side blocks, rendered as one `div.bp_sbs_run`.
block_extension Block.sideBySideRun where
  traverse _ _ _ := pure none
  toTeX := some <| fun _goI goB _id _data blocks => do
    pure <| .seq (← blocks.mapM goB)
  toHtml :=
    open Verso.Doc.Html in
    some <| fun _goI goB _id _data blocks => do
      let parts ← blocks.mapM goB
      pure <| renderRun parts

/-- Whether `block` takes part in runs (`some true`), is transparent (`none`), or ends one. -/
private def runRole? : Block Manual → Option Bool
  | .other b _ =>
    if b.name == informalBlockName then some true
    else if transparentBlockNames.contains b.name then none
    else some false
  | _ => some false

/--
Wrap each maximal run of consecutive Blueprint blocks of `blocks` in a
`Block.sideBySideRun`. Blocks that render nothing (group metadata) stay inside a run
without ending it; a run never starts or ends with them. Blocks outside runs are searched for
runs in their own contents.
-/
partial def groupBlocks (blocks : Array (Block Manual)) : Array (Block Manual) := Id.run do
  let flat := blocks.foldl (init := #[]) fun acc b =>
    match b with
    | .concat bs => acc ++ bs
    | b => acc.push b
  let mut out : Array (Block Manual) := #[]
  let mut run : Array (Block Manual) := #[]
  -- transparent blocks seen since the last run member
  let mut pending : Array (Block Manual) := #[]
  for b in flat do
    match runRole? b with
    | some true =>
      run := run ++ pending |>.push b
      pending := #[]
    | none =>
      if run.isEmpty then out := out.push b else pending := pending.push b
    | some false =>
      out := flush out run ++ pending |>.push (descend b)
      run := #[]
      pending := #[]
  return flush out run ++ pending
where
  flush (out run : Array (Block Manual)) : Array (Block Manual) :=
    if run.isEmpty then out else out.push (.other Block.sideBySideRun run)
  descend : Block Manual → Block Manual
    | .other b contents => .other b (groupBlocks contents)
    | .blockquote contents => .blockquote (groupBlocks contents)
    | .ul items => .ul (items.map fun ⟨bs⟩ => ⟨groupBlocks bs⟩)
    | .ol start items => .ol start (items.map fun ⟨bs⟩ => ⟨groupBlocks bs⟩)
    | .dl items => .dl (items.map fun ⟨t, bs⟩ => ⟨t, groupBlocks bs⟩)
    | b => b

/-- Wrap the runs of Blueprint blocks in every part of a document (see {name}`groupBlocks`). -/
partial def groupRuns (part : Part Manual) : Part Manual :=
  { part with
    content := groupBlocks part.content
    subParts := part.subParts.map groupRuns }

end Informal.SideBySideRuns
