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
info: ({ notReady := 1, ready := 0, incomplete := 2, formalized := 0, formalizedWithAncestors := 3, sourceChanged := 0 },
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

-- A Blueprint that is a package of its own inside the project it describes names the project's
-- root; its own folder is then not part of the project's files.
/-- info: true -/
#guard_msgs in
#eval show IO Bool from do
  let cwd ← workingDirectory
  let here ← projectRoot
  let named ← projectRoot (some "tests")
  let parent ← projectRoot (some "..")
  return here == cwd && (← projectRoot (some " ")) == cwd &&
    named.toString.endsWith "/tests" && (← blueprintFolder? cwd) == none &&
    -- seen from the parent folder, the working directory is the Blueprint's own folder
    (← blueprintFolder? parent) == cwd.fileName &&
    insideFolder (some "blueprint") "blueprint" &&
    insideFolder (some "blueprint") "blueprint/Chapter1.lean" &&
    !insideFolder (some "blueprint") "blueprints/A.lean" && !insideFolder none "blueprint/A.lean" &&
    stats.layout.projectRoot == none

-- JSON round trip, and the schema version.
/-- info: (true, 11) -/
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

-- A file run as a script has no module name; it counts by its file name.
/-- info: (#[(`scripts.Gen, "scripts/Gen.lean", true)], #["."]) -/
#guard_msgs in
#eval show CoreM _ from do
  let env ← getEnv
  withScratch fun root => do
    write (root / "scripts/Gen.lean") "def main : IO Unit := pure ()\n"
    let (modules, dirs) ← projectModules env root { sourceDirs := #["."] } (some "scripts/Gen.lean")
    return (modules.map fun (m, _) => (m.name, m.path, decide (m.declarations ≥ 11)), dirs)

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

-- The written schema (`doc/schemas/project-stats.schema.json`) names exactly the fields the
-- JSON has, at every level of a filled-in example, and the same version.

/-- `s` with a local `$ref` resolved against `root`. -/
private def resolveRef (root s : Json) : Json :=
  match s.getObjValAs? String "$ref" with
  | .ok ref =>
    (ref.drop 2).copy.splitOn "/" |>.foldl (init := root) fun j key => (j.getObjVal? key).toOption.getD .null
  | .error _ => s

/-- Check that every object of `v` has exactly the `required` fields of its schema `s`. -/
private partial def schemaFieldsAgree (root s v : Json) (at_ : String := "") : Except String Unit := do
  let s := resolveRef root s
  if (s.getObjValAs? String "type").toOption == some "null" && !(v matches .null) then
    throw s!"{at_}: not null"
  if let .ok (.arr alternatives) := s.getObjVal? "oneOf" then
    if alternatives.any (fun alt => (schemaFieldsAgree root alt v at_).toBool) then return
    throw s!"{at_}: no alternative fits"
  match v with
  | .obj fields =>
    let some props := (s.getObjVal? "properties").toOption | return
    let required ← match s.getObjVal? "required" with
      | .ok (.arr names) => names.mapM fun n => match n with
        | .str n => pure n
        | _ => throw s!"{at_}: bad required"
      | _ => throw s!"{at_}: no required list"
    let keys := fields.toArray.map (·.1)
    unless keys.qsort (· < ·) == required.qsort (· < ·) do
      throw s!"{at_}: fields {keys} but the schema requires {required}"
    for (key, value) in fields do
      schemaFieldsAgree root ((props.getObjVal? key).toOption.getD .null) value s!"{at_}.{key}"
  | .arr items =>
    if let .ok item := s.getObjVal? "items" then
      for value in items do schemaFieldsAgree root item value s!"{at_}[]"
  | _ => return

/-- info: (true, true) -/
#guard_msgs in
#eval show IO _ from do
  let schema ← IO.ofExcept <| Json.parse (← IO.FS.readFile "doc/schemas/project-stats.schema.json")
  let sample := stats.withChapters #[graphNode "a" (some "/One/#a") .ready]
  let sample := { sample with
    identity := { sample.identity with license := some { file := "LICENSE", spdx := some "MIT" } }
    trust := { sample.trust with missingDeclarations := #[{ label := `l, declaration := `d }] }
    challenges := #[{
      name := "C", challengeModule := `C, solutionModule := `S
      theorems := #[{ name := `t, node := some `n }]
      definitions := #[{ name := `d, solution := .same }] }]
    hasComparatorChallenge := true }
  let version := (schema.getObjVal? "properties" >>= (·.getObjVal? "schemaVersion") >>=
    (·.getObjValAs? Nat "const")).toOption
  let agree := (schemaFieldsAgree schema schema (toJson sample)).toBool &&
    (schemaFieldsAgree schema schema (toJson ({} : ProjectStats))).toBool
  return (agree, version == some projectStatsSchemaVersion)

-- Source text and the build, on a Blueprint. The data a Blueprint captures records the source
-- text each module of its nodes' declarations was compiled from; the generator compares it with
-- the file when it runs and shows the declarations of a module whose file changed with no
-- positive mark.

/-- The source of `Demo.A` as it was compiled. -/
private def builtText : String := "theorem t : True := trivial\n"

/-- A model with a node `t.node` on `Demo.t` of `Demo.A`, rendered with the status badge of a
declaration without `sorry`, and a node `u.node` that depends on it, both complete with their
dependencies, and the record that `Demo.A` was compiled from `builtText`. -/
private def builtModel (root : System.FilePath) : RenderModel :=
  let view := ProvedStatus.proved.presentation
  let badge : ExternalDeclHeaderBadge :=
    { className := view.externalDeclClass, text := view.externalHeaderText }
  let ref : ExternalRef := { ExternalRef.ofName `Demo.t with
    present := true, provedStatus := .proved
    provenance := .inWorkspace `Demo.A (root / "Demo" / "A.lean").toString
    render := .ok { html := s!"<div class=\"decl\">{badge.html.render}</div>", hoverPayloads := #[] } }
  let graphNode (label : Name) (uses : Array Name) : Graph.NodeData :=
    { label, title := label.toString, displayLabel := label.toString, kind := some .theorem
      statementUses := uses.map fun l => { label := l, origin := .automatic }
      statementStatus := .formalized, proofStatus := .formalizedWithAncestors
      visual := { fillcolor := "#ffffff" } }
  { nodes := #[{ label := `t.node, kind := .theorem, externalRefs := #[ref] },
               { label := `u.node, kind := .theorem }]
    graph := { nodes := #[graphNode `t.node #[], graphNode `u.node #[`t.node]] }
    stats := { (default : ProjectStats) with
      builtSources := #[{ module := `Demo.A, file := "Demo/A.lean"
                          hash := some (lakeTextHash builtText) }] } }

-- The file edited after the data was captured: the declaration says so, its rendered badge says
-- so, its node has the neutral status, the node that depends on it is not complete with its
-- dependencies, the counts have it in a bucket of its own, and its mark is ◌. As built: nothing
-- changes.
/-- info: (true, true) -/
#guard_msgs in
#eval show IO _ from do
  let root := System.FilePath.mk s!"/tmp/vbp-built-source-test-{← IO.monoNanosNow}"
  IO.FS.createDirAll (root / "Demo")
  try
    IO.FS.writeFile (root / "Demo" / "A.lean") builtText
    let model := builtModel root
    let same ← sourceChangesNow model.stats.builtSources root
    IO.FS.writeFile (root / "Demo" / "A.lean") (builtText ++ "-- edited after the build\n")
    let changes ← sourceChangesNow model.stats.builtSources root
    let m := model.withSourceChanges changes
    let refs := (m.nodes[0]?.map (·.externalRefs)).getD #[]
    let some ref := refs[0]? | return (false, false)
    let html := match ref.render with | .ok r => r.html | _ => ""
    let mark? := CodeSummary.statusMark? .theorem (some { externalDecls := refs })
    let (kind, words) := statusGlyph mark? none
    let unchanged := model.withSourceChanges same
    return (same.isEmpty && unchanged.graph.nodes.all (·.proofStatus == .formalizedWithAncestors) &&
        unchanged.stats.sourceChanged.isEmpty,
      changes.size == 1 && changes.all (·.changed) &&
      ref.sourceChange? == some "the source of Demo.A (Demo/A.lean) changed since the build" &&
      hasSubstr html "source changed since the build" && !hasSubstr html "no sorry" &&
      m.graph.nodes[0]!.proofStatus == .sourceChanged &&
      m.graph.nodes[1]!.proofStatus == .formalized &&
      m.stats.progress.sourceChanged == 1 && m.stats.progress.formalizedWithAncestors == 0 &&
      m.stats.sourceChanged.size == 1 && kind.glyph == "◌" &&
      words.startsWith "Lean proof: the source of Demo.A (Demo/A.lean) changed since the build")
  finally IO.FS.removeDirAll root

-- A source not known to match the build: no record, and a file that cannot be read.
/-- info: [(false, "its compiled module was not found"), (false, "the source file cannot be read")] -/
#guard_msgs in
#eval show IO _ from do
  let root := System.FilePath.mk s!"/tmp/vbp-built-source-test-{← IO.monoNanosNow}"
  IO.FS.createDirAll root
  let noRecord ← BuiltSource.read `Demo.A "Demo/A.lean" none
  let changes ← sourceChangesNow
    #[noRecord, { module := `Demo.B, file := "Demo/B.lean", hash := some (lakeTextHash "x") }] root
  IO.FS.removeDirAll root
  return changes.toList.map fun c => (c.changed, c.why)

end Verso.VersoBlueprintTests.BlueprintStats
