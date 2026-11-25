import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

namespace PreviewRuntimeShowcase.ReadingAidDecls

theorem aidBase (n : Nat) : n ≤ n + 1 := Nat.le_succ n

/-- A chain of inequalities with a signature too long for one line of a narrow column. -/
theorem aidLongSignature (first second third fourth : Nat) (hFirst : first ≤ second)
    (hSecond : second ≤ third) (hThird : third ≤ fourth) : first ≤ fourth :=
  Nat.le_trans hFirst (Nat.le_trans hSecond hThird)

theorem aidSectioned (n : Nat) : n + 0 = n := Nat.add_zero n

/-- A bound that no statement of the Blueprint names: the text below uses it. -/
def aidSlack : Nat := 2

end PreviewRuntimeShowcase.ReadingAidDecls

#doc (Manual) "Reading Aids" =>

Statements and sections of this chapter are numbered side by side. The package's
{repoFile "README.md"}[README] is linked at the commit the site is built from.

:::theorem "aids_first" (lean := "PreviewRuntimeShowcase.ReadingAidDecls.aidBase")
Every number is at most its successor.
:::

:::proof "aids_first" (lean := "PreviewRuntimeShowcase.ReadingAidDecls.aidLongSignature")
Chain the inequalities.
:::

# A Numbered Section

:::lemma_ "aids_sectioned" (lean := "PreviewRuntimeShowcase.ReadingAidDecls.aidSectioned")
Adding zero changes nothing.
:::

# Lean in the Text

Lean code in the running text is highlighted as in the Lean column: the bound
{Verso.Genre.Manual.InlineLean.lean}`PreviewRuntimeShowcase.ReadingAidDecls.aidBase 3` is the
statement of the first theorem of this chapter.

```Verso.Genre.Manual.InlineLean.lean
namespace PreviewRuntimeShowcase.ReadingAidDecls

-- Two steps up, from the first theorem of the chapter.
/-- Every number is at most two more than itself. -/
theorem aidTwoSteps (n : Nat) :
    n ≤ n + aidSlack := by
  have h : n ≤ n + 1 := aidBase n
  exact Nat.le_trans h
    (Nat.succ_le_succ (Nat.le_succ n))

def aidLabel : String := "two steps"

example : aidSlack = 2 ∧ (Nat : Type) = Nat :=
  ⟨rfl, rfl⟩

end PreviewRuntimeShowcase.ReadingAidDecls
```
