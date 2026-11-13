/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

import VersoBlueprint.Graph
import VersoBlueprint.Stats.Repo
import VersoBlueprint.Stats.Source

/-!
The project statistics a Blueprint site shows to a first-time reader: what the project is, how
big it is, how far along it is, whether it builds and what its proofs rest on.

`ProjectStats` is captured with the render model and serialised as JSON. The JSON shape is
written down in `doc/schemas/project-stats.schema.json`; `projectStatsSchemaVersion` changes
whenever it does. Every path in it is relative to the project root and every list has a fixed
order, so the same project gives the same bytes. It holds no version-control data.
-/

namespace Informal.Stats

open Lean

/-- The version of the JSON shape of `ProjectStats`. -/
def projectStatsSchemaVersion : Nat := 1

/-- Declarations of the project's own modules by kind. Generated declarations (recursors,
constructors, structure projections, equation lemmas, matchers and other names Lean marks as
internal) are not counted. -/
structure DeclarationCounts where
  theorems : Nat := 0
  definitions : Nat := 0
  instances : Nat := 0
  structures : Nat := 0
  classes : Nat := 0
  inductives : Nat := 0
  axioms : Nat := 0
  opaques : Nat := 0
deriving Repr, Inhabited, DecidableEq, ToJson, FromJson

/-- Every counted declaration. -/
def DeclarationCounts.total (c : DeclarationCounts) : Nat :=
  c.theorems + c.definitions + c.instances + c.structures + c.classes + c.inductives + c.axioms +
    c.opaques

/-- A module of the checked environment whose source lies in the project. -/
structure ModuleStats where
  /-- The module name. -/
  name : Name
  /-- The source file, relative to the project root. -/
  path : String
  /-- Its counted declarations (`DeclarationCounts.total`). -/
  declarations : Nat := 0
deriving Repr, Inhabited, DecidableEq, ToJson, FromJson

/-- How a `.lean` file of the project relates to the build that produced the site. -/
inductive FileStatus where
  /-- A module of the environment the site was generated from. -/
  | imported
  /-- Not imported by the site, but a compiled module of the workspace (its `.olean` exists). -/
  | compiled
  /-- Neither: no build target of the workspace has compiled it. -/
  | notBuilt
deriving Repr, Inhabited, DecidableEq, ToJson, FromJson

/-- One `.lean` file under the project root. -/
structure SourceFile where
  /-- Relative to the project root, with `/` separators. -/
  path : String
  lines : LineCounts := {}
  status : FileStatus := .notBuilt
deriving Repr, Inhabited, DecidableEq, ToJson, FromJson

/-- Every `.lean` file under the project root, outside hidden directories such as `.lake`. -/
structure SourceStats where
  /-- Sorted by path. -/
  files : Array SourceFile := #[]
  /-- The sum of every file's lines. -/
  lines : LineCounts := {}
deriving Repr, Inhabited, DecidableEq, ToJson, FromJson

/-- The files that are in no build: neither imported nor compiled. -/
def SourceStats.notBuilt (s : SourceStats) : Array SourceFile :=
  s.files.filter (·.status == .notBuilt)

/-- Blueprint nodes by the dependency graph's progress status (`Graph.ProofStatus`), the
status that colours a node's fill. Placeholders for unknown references are not nodes. -/
structure ProgressCounts where
  /-- Not ready: something it depends on is not formalized. -/
  notReady : Nat := 0
  ready : Nat := 0
  /-- Lean code is attached but has a `sorry` or another gap. -/
  incomplete : Nat := 0
  /-- Formalized, but something it depends on is not. -/
  formalized : Nat := 0
  /-- Formalized together with everything it depends on. -/
  formalizedWithAncestors : Nat := 0
deriving Repr, Inhabited, DecidableEq, ToJson, FromJson

/-- Every node counted. -/
def ProgressCounts.total (c : ProgressCounts) : Nat :=
  c.notReady + c.ready + c.incomplete + c.formalized + c.formalizedWithAncestors

/-- Add one node with the given status. -/
def ProgressCounts.add (c : ProgressCounts) : Graph.ProofStatus → ProgressCounts
  | .none => { c with notReady := c.notReady + 1 }
  | .ready => { c with ready := c.ready + 1 }
  | .incomplete => { c with incomplete := c.incomplete + 1 }
  | .formalized => { c with formalized := c.formalized + 1 }
  | .formalizedWithAncestors => { c with formalizedWithAncestors := c.formalizedWithAncestors + 1 }

/-- Progress of the nodes rendered in one chapter of the site. The chapter's title is not part
of the statistics; pages that show it look it up from the site. -/
structure ChapterProgress where
  /-- The first path segment of the chapter's pages, which names it in the site. -/
  chapter : String
  progress : ProgressCounts := {}
deriving Repr, Inhabited, DecidableEq, ToJson, FromJson

/-- The size of the dependency graph. -/
structure GraphSize where
  nodes : Nat := 0
  /-- Dependencies of statements. -/
  statementEdges : Nat := 0
  /-- Dependencies of proofs. -/
  proofEdges : Nat := 0
  /-- Distinct dependent–dependency pairs, whichever axis they are on. -/
  edges : Nat := 0
  groups : Nat := 0
  /-- Nodes by kind (`Data.NodeKind`), as a kind–count list in the kinds' order. -/
  byKind : Array (String × Nat) := #[]
deriving Repr, Inhabited, DecidableEq, ToJson, FromJson

/-- A declaration a node uses and the axioms that put it on a ledger row. -/
structure TrustEntry where
  /-- The Blueprint node. -/
  label : Name
  /-- The Lean declaration of the node. -/
  declaration : Name
  /-- The axioms behind the row: the `sorryAx`, the extra axioms or the compiled-code axioms. -/
  axioms : Array Name := #[]
deriving Repr, Inhabited, DecidableEq, ToJson, FromJson

/-- A Lean name a node refers to that is not in the environment. -/
structure MissingDeclaration where
  label : Name
  declaration : Name
deriving Repr, Inhabited, DecidableEq, ToJson, FromJson

/-- A Blueprint label that nodes depend on but no node defines. -/
structure UnknownReference where
  label : Name
  /-- The nodes that depend on it, sorted. -/
  referencedBy : Array Name := #[]
deriving Repr, Inhabited, DecidableEq, ToJson, FromJson

/-- What the project's proofs rest on beyond Lean's logic, node by node, from the axioms of
each declaration (`Data.AxiomClass`) and its recorded proof status. Each list is sorted by
label, then declaration. -/
structure TrustLedger where
  /-- Declarations with a `sorry` of their own. -/
  sorryDirect : Array TrustEntry := #[]
  /-- Declarations without a `sorry` of their own that depend on one. -/
  sorryThroughDependency : Array TrustEntry := #[]
  /-- Declarations that depend on axioms outside Lean's standard three. -/
  extraAxioms : Array TrustEntry := #[]
  /-- Declarations whose proofs trust compiled code (`native_decide` and similar tactics). -/
  compilerTrusted : Array TrustEntry := #[]
  /-- Lean names nodes refer to that the environment does not have. -/
  missingDeclarations : Array MissingDeclaration := #[]
  /-- Labels nodes depend on that no node defines. -/
  unknownReferences : Array UnknownReference := #[]
deriving Repr, Inhabited, DecidableEq, ToJson, FromJson

/-- Whether nothing in the ledger limits trust. -/
def TrustLedger.isClear (t : TrustLedger) : Bool :=
  t.sorryDirect.isEmpty && t.sorryThroughDependency.isEmpty && t.extraAxioms.isEmpty &&
    t.compilerTrusted.isEmpty && t.missingDeclarations.isEmpty && t.unknownReferences.isEmpty

/-- Where the statistics looked, relative to the project root: the source directories of the
workspace's packages inside the project, and their compiled-module directories. -/
structure WorkspaceLayout where
  sourceDirs : Array String := #[]
  libraryDirs : Array String := #[]
deriving Repr, Inhabited, DecidableEq, ToJson, FromJson

/-- The statistics of one Blueprint project. -/
structure ProjectStats where
  schemaVersion : Nat := projectStatsSchemaVersion
  identity : ProjectIdentity := {}
  layout : WorkspaceLayout := {}
  /-- The project's modules in the checked environment, sorted by name. -/
  modules : Array ModuleStats := #[]
  declarations : DeclarationCounts := {}
  sources : SourceStats := {}
  progress : ProgressCounts := {}
  /-- Progress by chapter, in the order chapters first appear in the graph. Empty until the
  site's pages are known (`ProjectStats.withChapters`). -/
  chapters : Array ChapterProgress := #[]
  graph : GraphSize := {}
  trust : TrustLedger := {}
  /-- The project's headline result, when one is selected; its shape belongs to the rule
  that selects it. -/
  headline : Option Json := none
deriving Inhabited, ToJson, FromJson

/-- The first directory of a site address: `"/Sums/#x"` and `"Sums/index.html"` give
`"Sums"`. A page at the site root (`"index.html#x"`, `"/#x"`) has no chapter. -/
def chapterOfHref? (href : String) : Option String :=
  let path := (href.splitOn "#").head!
  let path := (path.splitOn "?").head!
  let segments := (path.splitOn "/").filter fun s => !s.isEmpty && s != "."
  -- The last segment is a file unless the path ends with `/`.
  let dirs := if path.endsWith "/" then segments else segments.dropLast
  dirs.head?

/-- Progress by chapter, from graph nodes that know their address. Chapters keep the order in
which their first node appears; nodes without a chapter and unknown references are left out. -/
def chapterProgress (nodes : Array Graph.NodeData) : Array ChapterProgress := Id.run do
  let mut chapters : Array ChapterProgress := #[]
  for node in nodes do
    if node.warnings.unknownRef then continue
    let some chapter := node.href.bind chapterOfHref? | continue
    match chapters.findIdx? (·.chapter == chapter) with
    | some i => chapters := chapters.modify i fun c => { c with progress := c.progress.add node.proofStatus }
    | none => chapters := chapters.push { chapter, progress := ({} : ProgressCounts).add node.proofStatus }
  return chapters

/-- The statistics with chapter progress filled from graph nodes that know their address. -/
def ProjectStats.withChapters (stats : ProjectStats) (nodes : Array Graph.NodeData) :
    ProjectStats :=
  { stats with chapters := chapterProgress nodes }

end Informal.Stats
