/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Emilio J. Gallego Arias
-/

import Lean
import Lean.Elab.Command
import Verso
import VersoManual
import VersoBlueprint.Commands.Common
import VersoBlueprint.Commands.SerializedExtension
import VersoBlueprint.Commands.Summary.Collect
import VersoBlueprint.Commands.Summary.Render

namespace Informal.Commands

open Lean Elab Command
open Informal Data Environment

open Verso Doc Elab Syntax in
def mkSummaryPart (stx : Syntax) (endPos : String.Pos.Raw) : PartElabM FinishedPart := do
  let titlePreview := "Blueprint Summary"
  let expandedTitle := #[← ``(Verso.Doc.Inline.text "Blueprint Summary")]
  let metadata : Option (TSyntax `term) := some (← `(term| { number := false }))
  reportImportedConflicts
  let options ← Lean.getOptions
  if verso.blueprint.debug.commands.get (← Lean.getOptions) then
    let count := (informalExt.getState (← getEnv)).data.size
    logInfo m!"Blueprint summary for {count} entries"
  let block ← serializedBlockTerm `Informal.Commands.Block.summary
    ({ showDebugDiagnostics := verso.blueprint.summary.debugDiagnostics.get options } : SummaryBlockData)
  let subParts := #[]
  pure <| FinishedPart.mk stx stx expandedTitle titlePreview metadata #[block] subParts endPos

open Verso Doc Elab Syntax PartElabM in
@[part_command Lean.Doc.Parser.Block.command]
public meta def blueprintSummaryCmd : PartCommand
  | .command v => do
    unless v.name.getId == `blueprint_summary do Lean.Elab.throwUnsupportedSyntax
    unless v.args.isEmpty do Lean.Elab.throwUnsupportedSyntax
    let stx : Syntax := v.stx
    let endPos := stx.getTailPos?.get!
    closePartsUntil 1 endPos
    addPart (← mkSummaryPart stx endPos)
  | _ => (Lean.Elab.throwUnsupportedSyntax : PartElabM Unit)

end Informal.Commands
