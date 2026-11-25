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

/-- A lemma attached to the proof of a statement that has no Lean declaration. -/
theorem aidProofOnly (n : Nat) : n * 1 = n := Nat.mul_one n

/-- A lemma attached to a proof and still open. -/
theorem aidOpen (n : Nat) : 0 + n = n := by
  sorry

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

:::proof "aids_sectioned" (lean := "PreviewRuntimeShowcase.ReadingAidDecls.aidOpen")
The attached lemma is still open, so the node is incomplete.
:::

A placement of the node carries the same mark.

{blueprint_node "aids_sectioned"}

:::theorem "aids_proof_only"
A statement with no Lean declaration of its own.
:::

:::proof "aids_proof_only" (lean := "PreviewRuntimeShowcase.ReadingAidDecls.aidProofOnly")
The lemma attached here is complete, but there is no Lean statement to prove.
:::

The prose of a section reads in one centred column, and its headings share that column's axis.

## A Subsection Whose Heading Is Long Enough to Wrap Onto a Second Line of the Column

A paragraph long enough to fill several lines of the reading column, so that its left edge, its
right edge and the centre between them can be compared with the headings above and below it. The
text inside the column stays aligned to its start.

* A list in the reading column keeps its markers inside the column.
* Its items wrap within the same measure as the paragraphs around it.

> A quotation sits in the reading column, indented from both of its edges.

$$`\sum_{i = 0}^{n} i = \frac{n (n + 1)}{2}`

```
-- a code block in the prose
theorem add_zero' (n : Nat) : n + 0 = n := rfl
```

### A Third-Level Heading

The last paragraph of the section.

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

An error that Lean reports is shown in Lean's message colours:

```Verso.Genre.Manual.InlineLean.lean +error
open PreviewRuntimeShowcase.ReadingAidDecls in
example : aidSlack = 3 := by decide
```
