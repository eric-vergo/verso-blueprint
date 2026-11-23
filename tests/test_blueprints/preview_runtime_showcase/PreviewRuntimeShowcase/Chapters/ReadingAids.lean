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
