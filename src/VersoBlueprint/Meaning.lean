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
saying more than that: a mark names what was looked at, informal text is shown with its source,
and the one sentence about the gap between them is the same everywhere.
-/

namespace Informal.Meaning

/-- The sentence shown where informal text stands beside a Lean statement. -/
def uncheckedNote : String :=
  "No tool has checked that this text says the same as the Lean statement."

/-- The short form of `uncheckedNote`, for a line under a statement on a chapter page. -/
def uncheckedTag : String := "not checked against the Lean statement"

/-- The text of links to the explanation (`anchor`). -/
def linkText : String := "What this means"

/-- The id of the explanation of the marks, on the Project Stats page. -/
def anchor : String := "bp-what-this-means"

/-- Where an informal statement comes from, as a noun phrase: a statement written in the
Blueprint is `none`; a site generated from code names the source in its data (`tex`,
`attribute`, `docstring`, `blueprint`). -/
def sourcePhrase : Option String → String
  | none | some "blueprint" => "the blueprint"
  | some "tex" => "the project's TeX blueprint"
  | some "attribute" => "a blueprint attribute"
  | some "docstring" => "the docstring"
  | some _ => "the project"

/-- The line under an informal statement that has Lean code beside it. -/
def sourceLine (source : Option String) : String :=
  s!"Informal statement from {sourcePhrase source} · {uncheckedTag}"

end Informal.Meaning
