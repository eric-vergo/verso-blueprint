/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

import VersoBlueprint
import VersoBlueprintTests.Blueprint.Support

namespace Verso.VersoBlueprintTests.BlueprintWorkQueue

open Lean
open Verso Genre Manual
open Informal
open Verso.VersoBlueprintTests.Blueprint.Support

set_option doc.verso true

private def node (label : Name) (kind : Data.NodeKind)
    (statementStatus : Graph.StatementStatus) (proofStatus : Graph.ProofStatus := .none)
    (statementUses proofUses : Array Name := #[]) : Graph.NodeData := {
  label, kind, statementStatus, proofStatus
  title := s!"Title {label}"
  displayLabel := s!"N {label}"
  statementUses := statementUses.map fun l => { label := l }
  proofUses := proofUses.map fun l => { label := l }
  visual := default
}

-- Ready entries come first (in model order), then incomplete ones; `needs` lists open dependencies.
/-- info: true -/
#guard_msgs in
#eval
  let model : Graph.GraphModel := { nodes := #[
    node `a .definition .ready,
    node `b .theorem .formalized .incomplete (statementUses := #[`a]),
    node `c .theorem .formalized .ready (proofUses := #[`b, `d]),
    node `d .definition .formalized,
    node `e .theorem .blocked .none (statementUses := #[`a])
  ] }
  let queue := Informal.Commands.workQueue model
  queue.map (fun e => (e.node.label, e.stage, e.ready)) ==
      #[(`a, "statement", true), (`c, "proof", true), (`b, "proof", false)] &&
    queue.map (fun e => e.needs.map (·.label)) == #[#[], #[`b], #[`a]]

#docs (Genre.Manual) workQueueDoc "Work Queue Doc" :=
:::::::
:::definition "wq.base"
A base definition.
:::

:::theorem "wq.top" (uses := "wq.base")
A theorem.
:::

{blueprint_work_queue}
:::::::

-- The page body lists the ready definition with a link to it; the blocked theorem is not listed.
/-- info: true -/
#guard_msgs in
#eval
  show IO Bool from do
    let out ← renderManualDocHtmlString extension_impls% workQueueDoc
    pure (
      hasSubstr out "class=\"bp_work_queue\"" &&
      hasSubstr out "data-bp-node=\"«wq.base»\"" &&
      !hasSubstr out "data-bp-node=\"«wq.top»\"" &&
      hasSubstr out "statement ready to formalize"
    )

end Verso.VersoBlueprintTests.BlueprintWorkQueue
