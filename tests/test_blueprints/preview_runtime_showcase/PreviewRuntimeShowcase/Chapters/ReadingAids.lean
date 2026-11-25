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
