/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

import VersoBlueprintTests.Blueprint.Support
import VersoBlueprint.Stats.Collect
import VersoBlueprint.PreviewManifest

/-!
The project statistics captured with the render model: declaration kinds, the trust ledger,
progress and graph size of a fixture blueprint, the workspace layout and file classes on a
scratch project, chapter progress from node addresses, and the JSON form.
-/

namespace Verso.VersoBlueprintTests.BlueprintStats

open Lean
open Verso
open Verso.Genre.Manual
open Informal
open Informal.Data
open Informal.Stats
open Verso.VersoBlueprintTests.Blueprint.Support

set_option doc.verso true

-- Fixture declarations

/-- A project axiom. -/
axiom statsAxiom : 2 + 2 = 4

/-- A theorem on the project axiom. -/
theorem onAxiom : 2 + 2 = 4 := statsAxiom

/-- A theorem left unproved. -/
theorem unproved : 1 + 1 = 3 := by sorry

/-- A theorem whose only gap is the theorem it uses. -/
theorem onUnproved : 1 + 1 = 3 ∧ True := ⟨unproved, trivial⟩

/-- A theorem proved by compiled code. -/
theorem byNative : 10 * 10 = 100 := by native_decide

/-- A structure, with its generated constructor, projections and recursors. -/
structure Point where
  /-- The first coordinate. -/
  x : Nat
  /-- The second coordinate. -/
  y : Nat

/-- A class. -/
class Sized (α : Type) where
  size : α → Nat

/-- An instance. -/
instance : Sized Point := ⟨fun p => p.x + p.y⟩

/-- An inductive type. -/
inductive Colour where
  | red
  | green

/-- A definition by pattern matching, with a matcher and equation lemmas. -/
def Colour.flip : Colour → Colour
  | .red => .green
  | .green => .red

/-- Flipping twice changes nothing. -/
theorem Colour.flip_flip (c : Colour) : c.flip.flip = c := by
  cases c <;> rfl

/-- An abbreviation counts as a definition. -/
abbrev Pair := Nat × Nat

/-- An opaque constant. -/
opaque hidden : Nat

/-- A private definition counts. -/
private def helper : Nat := 3

private def ns : Name := `Verso.VersoBlueprintTests.BlueprintStats

private def kindOf (name : Name) : MetaM (Option String) := do
  let env ← getEnv
  return (env.find? name).bind (declarationKind? env)

-- Declarations by kind; what Lean generates is not counted.
/--
info: [("statsAxiom", some "axioms"), ("onAxiom", some "theorems"), ("Point", some "structures"), ("Sized", some "classes"),
  ("instSizedPoint", some "instances"), ("Colour", some "inductives"), ("Colour.flip", some "definitions"),
  ("Pair", some "definitions"), ("hidden", some "opaques"), ("Point.mk", none), ("Point.x", none), ("Point.rec", none),
  ("Point.recOn", none), ("Point.casesOn", none), ("Point.noConfusion", none), ("Point.mk.injEq", none),
  ("Point.mk.inj", none), ("Colour.red", none), ("Colour.toCtorIdx", none), ("Colour.flip.match_1", none),
  ("Colour.flip.eq_1", none), ("Sized.size", none)]
-/
#guard_msgs in
#eval show MetaM _ from do
  -- Realise the equation lemma so that it exists.
  let _ ← Meta.getEqnsFor? (ns ++ `Colour.flip)
  [`statsAxiom, `onAxiom, `Point, `Sized, `instSizedPoint, `Colour, `Colour.flip, `Pair, `hidden,
      `Point.mk, `Point.x, `Point.rec, `Point.recOn, `Point.casesOn, `Point.noConfusion,
      `Point.mk.injEq, `Point.mk.inj, `Colour.red, `Colour.toCtorIdx, `Colour.flip.match_1,
      `Colour.flip.eq_1, `Sized.size].mapM fun n => do
    return (n.toString, ← kindOf (ns ++ n))

-- A private name is counted under its user name.
/-- info: some "definitions" -/
#guard_msgs in
#eval show MetaM _ from do
  let env ← getEnv
  let some info := env.constants.toList.find? (fun (n, _) =>
      isPrivateName n && privateToUserName n == ns ++ `helper) |>.map (·.2)
    | return none
  return declarationKind? env info

-- A fixture blueprint

#docs (Genre.Manual) statsDoc "Stats Doc" :=
:::::::
:::definition "def:st.point" (lean := "Verso.VersoBlueprintTests.BlueprintStats.Point")
A point.
:::

:::theorem "thm:st.axiom" (lean := "Verso.VersoBlueprintTests.BlueprintStats.onAxiom") (uses := "def:st.point")
Rests on an axiom of the project.
:::

:::theorem "thm:st.sorry" (lean := "Verso.VersoBlueprintTests.BlueprintStats.unproved")
Not proved yet.
:::

:::theorem "thm:st.dep" (lean := "Verso.VersoBlueprintTests.BlueprintStats.onUnproved") (uses := "thm:st.sorry")
Proved from an unproved theorem.
:::

:::theorem "thm:st.native" (lean := "Verso.VersoBlueprintTests.BlueprintStats.byNative")
Checked by compiled code.
:::

:::lemma_ "lem:st.prose" (uses := "lem:st.nowhere, thm:st.axiom")
No Lean declaration yet, and a dependency nobody defines.
:::

{blueprint_graph}
:::::::

private def statsBlueprint : BlueprintDocument := .capture statsDoc.toPart

private def stats : ProjectStats := statsBlueprint.model.stats

private def short (n : Name) : String := (n.replacePrefix ns .anonymous).toString

private def rows (entries : Array TrustEntry) : List (String × String × List String) :=
  entries.toList.map fun e => (e.label.toString, short e.declaration, e.axioms.toList.map short)

-- The trust ledger: a sorry of its own, one through a dependency, an extra axiom and a proof
-- that trusts compiled code; the unknown label and who depends on it.
/--
info: ([("«thm:st.sorry»", "unproved", ["sorryAx"])], [("«thm:st.dep»", "onUnproved", ["sorryAx"])],
  [("«thm:st.axiom»", "onAxiom", ["statsAxiom"])],
  [("«thm:st.native»", "byNative", ["byNative._native.native_decide.ax_1_1"])],
  [("«lem:st.nowhere»", ["«lem:st.prose»"])])
-/
#guard_msgs in
#eval
  (rows stats.trust.sorryDirect, rows stats.trust.sorryThroughDependency,
    rows stats.trust.extraAxioms, rows stats.trust.compilerTrusted,
    stats.trust.unknownReferences.toList.map fun u =>
      (u.label.toString, u.referencedBy.toList.map (·.toString)))

-- Progress and graph size: unknown references are not nodes.
/--
info: ({ notReady := 1, ready := 0, incomplete := 2, formalized := 0, formalizedWithAncestors := 3 },
 { nodes := 6,
   statementEdges := 4,
   proofEdges := 0,
   edges := 4,
   groups := 0,
   byKind := #[("definition", 1), ("lemma", 1), ("theorem", 4)] })
-/
#guard_msgs in
#eval (stats.progress, stats.graph)

-- The module being elaborated is a project module, with its declarations counted.
/-- info: some ("tests/VersoBlueprintTests/BlueprintStats.lean", true) -/
#guard_msgs in
#eval (stats.modules.find? (·.name == `VersoBlueprintTests.BlueprintStats)).map fun m =>
  (m.path, decide (m.declarations ≥ 11))

-- The statistics hold no absolute path.
/-- info: true -/
#guard_msgs in
#eval
  let json := (toJson stats).compress
  (json.splitOn "\"/").length == 1 && stats.sources.files.all (!·.path.startsWith "/") &&
    stats.layout.sourceDirs.contains "tests" && stats.layout.sourceDirs.contains "src"

-- JSON round trip, and the schema version.
/-- info: (true, 1) -/
#guard_msgs in
#eval
  match fromJson? (α := ProjectStats) (toJson stats) with
  | .ok back => ((toJson back).compress == (toJson stats).compress, back.schemaVersion)
  | .error _ => (false, 0)

-- Workspace layout and files, on a scratch project

/-- A scratch directory, removed afterwards; its real path is passed on. -/
private def withScratch (k : System.FilePath → IO α) : IO α := do
  let dir ← IO.FS.createTempDir
  try k (← IO.FS.realPath dir) finally IO.FS.removeDirAll dir

private def write (path : System.FilePath) (text : String) : IO Unit := do
  if let some parent := path.parent then IO.FS.createDirAll parent
  IO.FS.writeFile path text

-- Library directories inside the project and outside `.lake/packages`; source directories: the
-- source path inside the project and outside `.lake`, each package directory and their
-- non-hidden subdirectories. Directories elsewhere are left out.
/--
info: (#[".", "Local", "Local/src", "blueprint", "extra", "extra/src", "scripts"],
  #[".lake/build/lib/lean", "Local/.lake/build/lib/lean"])
-/
#guard_msgs in
#eval withScratch fun root => do
  for dir in ["blueprint", "scripts", ".hidden", "Local/src", "extra/src", ".lake/packages/dep",
      ".lake/build/lib/lean", ".lake/packages/dep/.lake/build/lib/lean",
      "Local/.lake/build/lib/lean"] do
    IO.FS.createDirAll (root / dir)
  let layout ← WorkspaceLayout.ofSearchPaths root
    [root / "extra/src", root / ".lake/packages/dep", "/usr", root / "absent"]
    [root / ".lake/build/lib/lean", root / ".lake/packages/dep/.lake/build/lib/lean",
      root / "Local/.lake/build/lib/lean", "/usr"]
  return (layout.sourceDirs, layout.libraryDirs)

-- An empty project: the root is its one source directory.
/-- info: (#["."], #[]) -/
#guard_msgs in
#eval withScratch fun root => do
  let layout ← WorkspaceLayout.ofSearchPaths root ["/usr"] []
  return (layout.sourceDirs, layout.libraryDirs)

-- Files: imported, compiled (an `.olean` in a library directory) or in no build; hidden
-- directories and symbolic links are not entered.
/--
info: (#[("A.lean", Informal.Stats.FileStatus.imported, 2), ("Local/Sub/B.lean", Informal.Stats.FileStatus.compiled, 1),
   ("scripts/C.lean", Informal.Stats.FileStatus.notBuilt, 3)],
 6)
-/
#guard_msgs in
#eval withScratch fun root => do
  write (root / "A.lean") "import B\n-- docs\n"
  write (root / "Local/Sub/B.lean") "def b := 1\n"
  write (root / "scripts/C.lean") "/- a\n\n-/\n"
  write (root / ".lake/packages/dep/D.lean") "def d := 1\n"
  write (root / ".hidden/E.lean") "def e := 1\n"
  write (root / "Local/.lake/build/lib/lean/Sub/B.olean") ""
  IO.FS.createDirAll (root / "outside")
  write (root / "outside/F.lean") "def f := 1\n"
  let _ ← IO.Process.output { cmd := "ln", args := #["-s", (root / "outside").toString, (root / "link").toString] }
  IO.FS.removeFile (root / "outside/F.lean")
  write (root / "outside.txt") ""
  let layout : WorkspaceLayout := { sourceDirs := #[".", "Local"], libraryDirs := #["Local/.lake/build/lib/lean"] }
  let sources ← SourceStats.read root layout #[{ name := `A, path := "A.lean" }]
  return (sources.files.map fun f => (f.path, f.status, f.lines.total), sources.lines.total)

-- Refreshing reads the files again in the same project, and changes nothing elsewhere.
/-- info: (2, 1) -/
#guard_msgs in
#eval withScratch fun root => do
  write (root / "lake-manifest.json") "{\"name\": \"Other\", \"packages\": []}"
  let base : ProjectStats := { identity := { name := some "Other" }, sources := { files := #[{ path := "X.lean" }, { path := "Y.lean" }] } }
  let elsewhere : ProjectStats := { base with identity := { name := some "Mine" } }
  let cwd ← IO.currentDir
  IO.Process.setCurrentDir root
  try
    let a ← base.refreshWorkspace
    let b ← elsewhere.refreshWorkspace
    return (b.sources.files.size, a.sources.files.size + 1)
  finally
    IO.Process.setCurrentDir cwd

-- Chapters

/-- info: [some "Sums", some "Sums", some "Sums", none, none, none, some "a"] -/
#guard_msgs in
#eval ["/Sums/#x", "Sums/index.html", "Sums/Part/#y", "index.html#z", "/#w", "", "./a/b.html"].map
  chapterOfHref?

private def graphNode (label : String) (href : Option String) (proof : Graph.ProofStatus)
    (unknown : Bool := false) : Graph.NodeData :=
  { label := Name.mkSimple label, title := label, displayLabel := label, href, proofStatus := proof
    warnings := { unknownRef := unknown }, visual := default }

-- Chapters in order of first appearance; root pages and unknown references are left out.
/--
info: [("Two", 1, 1, 2), ("One", 0, 1, 1)]
-/
#guard_msgs in
#eval
  (chapterProgress #[graphNode "a" (some "/Two/#a") .formalizedWithAncestors,
    graphNode "b" (some "/One/#b") .ready, graphNode "c" (some "/Two/#c") .incomplete,
    graphNode "d" (some "/#d") .ready, graphNode "e" (some "/Two/#e") .ready (unknown := true),
    graphNode "f" none .ready]).toList.map fun c =>
      (c.chapter, c.progress.formalizedWithAncestors, c.progress.total - c.progress.formalizedWithAncestors,
        c.progress.total)

end Verso.VersoBlueprintTests.BlueprintStats
