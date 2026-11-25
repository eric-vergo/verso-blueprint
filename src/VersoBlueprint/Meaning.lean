/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

/-!
The words a Blueprint site uses for what was checked, in one place.

A site reports facts about Lean code: a declaration and what it uses contain no `sorry`; it
depends on these axioms; the solution of a Comparator challenge states the same Lean terms as the
challenge. It also shows informal text beside that code: a Blueprint statement, a docstring, an
author's claim about a manuscript. No tool compares the two. The texts here keep the pages from
saying more than that: a mark names what was looked at, informal text that is not the Blueprint's
own is shown with its source, and the one sentence about the gap between them is the same
everywhere.
-/

namespace Informal.Meaning

/-- The sentence shown where informal text stands beside a Lean statement. -/
def uncheckedNote : String :=
  "No tool has checked that this text says the same as the Lean statement."

/-- The short form of `uncheckedNote`, for a caption beside informal text. -/
def uncheckedTag : String := "not checked against the Lean statement"

/-- The text of links to the explanation (`anchor`). -/
def linkText : String := "What this means"

/-- The id of the explanation of the marks, on the Project Stats page. -/
def anchor : String := "bp-what-this-means"

/-- The tag under an informal statement that a site generated from code took from somewhere
other than a Blueprint, naming that source (`tex`, `attribute`, `docstring`): the reader knows
whose words they are reading. A statement written in the Blueprint (`none`, `blueprint`) has
no tag. -/
def sourceTag? : Option String → Option String
  | none | some "blueprint" => none
  | some "tex" => some "From the project's TeX blueprint"
  | some "attribute" => some "From a blueprint attribute"
  | some "docstring" => some "From the docstring"
  | some _ => some "From the project"

end Informal.Meaning
