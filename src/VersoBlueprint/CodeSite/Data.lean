/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

import Lean.Data.Json
import VersoBlueprint.Data

/-!
The input of a site generated from compiled Lean code: a project's declarations, module by
module, as a tool that read the project's build reports them.

A Blueprint site is usually written by hand: chapters of informal statements attached to Lean
declarations. A project without a Blueprint still has the structure a reader wants to see — its
declarations, what each one uses, which proofs are complete, what they rest on — and all of it is
in the compiled modules. `Informal.CodeSite` turns this data into a Blueprint site: one chapter
per module, one node per declaration, the dependency graph and the summary and statistics pages.

The data is plain JSON (`doc/schemas/code-site.schema.json`, format tag `formatTag`), so any tool
that can read a build can produce it; the generator itself never loads the project's
environment. Positions are Language Server Protocol positions: 0-based lines, UTF-16 columns.
-/

namespace Informal.CodeSite

open Lean

/-- The format tag of the input file. -/
def formatTag : String := "verso-blueprint-code-1"

/-- A position in a source file: 0-based line, UTF-16 column. -/
structure Position where
  line : Nat
  character : Nat
deriving Inhabited, Repr, BEq, ToJson, FromJson

/-- A range in a source file. -/
structure Range where
  start : Position
  «end» : Position
deriving Inhabited, Repr, BEq, ToJson, FromJson

/-- A use of another declaration of the project. -/
structure Use where
  /-- The declaration used. -/
  name : Name
  /-- `statement` (it occurs in the type) or `proof` (only in the value). -/
  kind : String
deriving Inhabited, Repr, BEq, ToJson, FromJson

/-- One declaration of the project. -/
structure Declaration where
  /-- The constant's name; a private declaration keeps Lean's `_private` prefix. -/
  name : Name
  /-- The name as written in the source, when it differs from `name`. -/
  display : Option Name := none
  /-- `theorem`, `def`, `instance`, `structure`, `class`, `inductive`, `axiom` or `opaque`. -/
  kind : String
  isPrivate : Bool := false
  /-- The whole declaration in its source file. -/
  range : Option Range := none
  /-- The declaration's name in its source file. -/
  selection : Option Range := none
  /-- The printed signature, keyword and name included (`theorem foo (n : ℕ) : …`). -/
  signature : String := ""
  doc : Option String := none
  /-- `proved`, `sorry-here`, `depends-on-sorry`, `axiom`, `opaque` or `unverified` (the value
  could not be inspected). -/
  status : String := "proved"
  /-- The axioms it depends on. -/
  axioms : Array Name := #[]
  /-- Attributes of interest (`simp`, `instance`, `noncomputable`, …). -/
  attrs : Array String := #[]
  /-- The project's declarations it uses. -/
  uses : Array Use := #[]
  /-- Constants of other packages it uses. -/
  external : Array Name := #[]
deriving Inhabited, Repr, ToJson, FromJson

/-- The declarations of one module, in source order. -/
structure Module where
  module : Name
  /-- The module's source file relative to the project root (empty when unknown). -/
  source : String := ""
  declarations : Array Declaration := #[]
deriving Inhabited, Repr, ToJson, FromJson

/-- A module left out of the data, with the reason. -/
structure Skipped where
  module : Name
  reason : String
deriving Inhabited, Repr, ToJson, FromJson

/-- The input file. -/
structure Project where
  format : String := formatTag
  /-- The site's title (default: the name of the project root's folder). -/
  title : Option String := none
  /-- The project's Lean toolchain, as its `lean-toolchain` file names it. -/
  toolchain : Option String := none
  modules : Array Module := #[]
  /-- Source modules without build output: their declarations are not in the data. -/
  unbuilt : Array Name := #[]
  skipped : Array Skipped := #[]
deriving Inhabited, Repr, ToJson, FromJson

/-- Parse the input file's text. -/
def Project.parse (text : String) : Except String Project := do
  let json ← Json.parse text
  let project ← fromJson? (α := Project) json
  unless project.format == formatTag do
    throw s!"expected format {formatTag}, found {project.format}"
  return project

/-! ## How declarations become nodes -/

/-- The node kind of a declaration kind: theorems are theorems, everything else a definition. -/
def nodeKind (kind : String) : Data.NodeKind :=
  if kind == "theorem" then .theorem else .definition

/-- The proof status of a declaration status. A `sorry` of its own counts as a hole in the
proof (the data does not say where it is); one reached through another declaration as a hole
of a dependency. -/
def provedStatus (decl : Declaration) : Data.ProvedStatus :=
  match decl.status with
  | "proved" => .proved
  | "sorry-here" => .incomplete { knownSorry := #[{ location := .proof, origin := .direct }] }
  | "depends-on-sorry" =>
    .incomplete { knownSorry := #[{ location := .proof, origin := .dependency }] }
  | "axiom" | "opaque" => .axiomLike
  | _ => .incomplete { unverified := #[{ location := .unknown, declaration := decl.name,
                                         reason := .bodyUnavailable }] }

/-- The label of a module's group in the graph: not an identifier, so it cannot be a
declaration's label. -/
def moduleGroup (module : Name) : Name :=
  .mkSimple s!"module:{module}"

/-- A declaration's name as a reader sees it. -/
def Declaration.shownName (decl : Declaration) : Name :=
  decl.display.getD decl.name

end Informal.CodeSite
