import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

namespace PreviewRuntimeShowcase.SideBySideRunDecls

theorem runFirst (n : Nat) : n + 0 = n := by
  simp

def runDefinition (n : Nat) : Nat := n + 1

theorem runLeanOnly (n : Nat) : runDefinition n = n + 1 := by
  rfl

/-- A statement whose Lean proof is many lines long. -/
theorem runLongProof (a b c : Nat) : a + b + c = c + b + a := by
  have h₁ : a + b = b + a := Nat.add_comm a b
  have h₂ : b + a + c = c + (b + a) := Nat.add_comm (b + a) c
  have h₃ : c + (b + a) = c + b + a := (Nat.add_assoc c b a).symm
  calc a + b + c = b + a + c := by rw [h₁]
    _ = c + (b + a) := h₂
    _ = c + b + a := h₃

end PreviewRuntimeShowcase.SideBySideRunDecls

#doc (Manual) "Side-by-Side Runs" =>

Consecutive nodes form one run.

:::theorem "runs_first" (lean := "PreviewRuntimeShowcase.SideBySideRunDecls.runFirst")
Adding zero changes nothing.
:::

:::proof "runs_first"
Zero is the neutral element of addition.
:::

:::definition "runs_definition" (lean := "PreviewRuntimeShowcase.SideBySideRunDecls.runDefinition")
The successor of a number.
:::

:::lemma_ "runs_lean_only" (lean := "PreviewRuntimeShowcase.SideBySideRunDecls.runLeanOnly")
The successor is one more.
:::

Prose between two nodes ends a run.

:::theorem "runs_long_proof" (lean := "PreviewRuntimeShowcase.SideBySideRunDecls.runLongProof")
Addition of three numbers can be reversed.
:::

:::proof "runs_long_proof"
Commute the first two summands, then move the third to the front and regroup.
:::
