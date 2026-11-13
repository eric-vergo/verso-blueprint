/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

import VersoBlueprintTests.Blueprint.Support
import VersoBlueprint.CodeSite.Main

/-!
Sites generated from compiled-code data (`vbp code-site`): the data's nodes, edges, statuses and
groups, the document, and a whole site generated from a small project.
-/

namespace Verso.VersoBlueprintTests.BlueprintCodeSite

open Lean
open Informal Informal.CodeSite
open Verso.VersoBlueprintTests.Blueprint.Support

/-- A project with two modules: a definition, a theorem using it, a lemma with a `sorry`, a
theorem that depends on it, a private declaration and an axiom. -/
def fixtureJson : String := "{\"format\":\"verso-blueprint-code-1\",
  \"toolchain\":\"leanprover/lean4:v4.35.0\",
  \"modules\":[
    {\"module\":\"Demo.Basic\",\"source\":\"Demo/Basic.lean\",\"declarations\":[
      {\"name\":\"Demo.double\",\"kind\":\"def\",\"signature\":\"def Demo.double (n : Nat) : Nat\",
       \"doc\":\"Twice `n`.\",\"status\":\"proved\",
       \"range\":{\"start\":{\"line\":2,\"character\":0},\"end\":{\"line\":3,\"character\":9}}},
      {\"name\":\"Demo.double_eq\",\"kind\":\"theorem\",
       \"signature\":\"theorem Demo.double_eq (n : Nat) : Demo.double n = n + n\",
       \"status\":\"proved\",\"axioms\":[\"propext\"],
       \"uses\":[{\"name\":\"Demo.double\",\"kind\":\"statement\"},
                 {\"name\":\"Demo.double\",\"kind\":\"proof\"},
                 {\"name\":\"Other.unknown\",\"kind\":\"proof\"}]},
      {\"name\":\"_private.Demo.Basic.0.Demo.helper\",\"display\":\"Demo.helper\",
       \"kind\":\"theorem\",\"isPrivate\":true,\"signature\":\"theorem Demo.helper : True\",
       \"status\":\"proved\"}]},
    {\"module\":\"Demo.Hard\",\"source\":\"Demo/Hard.lean\",\"declarations\":[
      {\"name\":\"Demo.hard\",\"kind\":\"theorem\",\"signature\":\"theorem Demo.hard : False\",
       \"status\":\"sorry-here\",\"axioms\":[\"sorryAx\"]},
      {\"name\":\"Demo.uses_hard\",\"kind\":\"theorem\",\"signature\":\"theorem Demo.uses_hard : False\",
       \"status\":\"depends-on-sorry\",\"axioms\":[\"sorryAx\"],
       \"uses\":[{\"name\":\"Demo.hard\",\"kind\":\"proof\"}]},
      {\"name\":\"Demo.ax\",\"kind\":\"axiom\",\"signature\":\"axiom Demo.ax : True\",
       \"status\":\"axiom\",\"axioms\":[\"Demo.ax\"]}]}],
  \"unbuilt\":[\"Demo.Later\"],
  \"skipped\":[{\"module\":\"Demo.Twin\",\"reason\":\"declares Demo.double as Demo.Basic does\"}]}"

def fixture : Project :=
  match Project.parse fixtureJson with
  | .ok p => p
  | .error e => panic! e

def basicSource : String :=
  "-- Demo\n\n/-- Twice `n`. -/\ndef double (n : Nat) : Nat :=\n  n + n\n"

def fixtureState : Environment.State :=
  stateOf fixture fun m => if m == `Demo.Basic then some basicSource else none

-- Another format is refused.
/-- info: true -/
#guard_msgs in
#eval (Project.parse "{\"format\":\"other\"}" matches .error _)

-- One node per declaration, each in its module's group, with its Lean declaration attached.
/-- info: true -/
#guard_msgs in
#eval
  let s := fixtureState
  s.data.size == 6 &&
    s.groups.toArray.map (·.2) == #["Demo.Basic", "Demo.Hard"] &&
    (s.data.find? `Demo.double).any fun n =>
      n.parent == some (moduleGroup `Demo.Basic) && n.kind == .definition &&
        n.externalRefs.map (·.canonical) == #[`Demo.double]

-- A use is a statement edge or a proof edge, never both; uses outside the data are dropped.
/-- info: true -/
#guard_msgs in
#eval
  match fixtureState.data.find? `Demo.double_eq with
  | some n =>
    (n.statement.map fun (d : Data.InformalData) => Data.UseRef.labels d.useDeclarations) == some #[`Demo.double] &&
      (n.proof.map fun (d : Data.InformalData) => Data.UseRef.labels d.useDeclarations) == some #[]
  | none => false

-- Statuses: a sorry of its own is a direct hole, one reached through a use a dependency hole.
/-- info: true -/
#guard_msgs in
#eval
  let st (n : Name) := (fixtureState.data.find? n).bind (·.externalRefs[0]?) |>.map (·.provedStatus)
  (st `Demo.double).any (·.isProved) &&
    (st `Demo.hard).any (·.containsExplicitSorry) &&
    (st `Demo.uses_hard).any fun s => s.dependsOnSorry && !s.containsExplicitSorry &&
    (st `Demo.ax).any (·.isAxiomLike)

-- The declaration card carries the signature, the docstring and the source excerpt.
/-- info: true -/
#guard_msgs in
#eval
  match (fixtureState.data.find? `Demo.double).bind (·.externalRefs[0]?) |>.map (·.render) with
  | some (.ok r) =>
    hasSubstr r.html "def Demo.double (n : Nat) : Nat" && hasSubstr r.html "Twice" &&
      hasSubstr r.html "def double (n : Nat) : Nat :=" && hasSubstr r.html "Demo/Basic.lean:3"
  | _ => false

def isNodeBlock : Verso.Doc.Block Verso.Genre.Manual → Bool
  | .other b _ => b.name == ``Informal.Block.informal
  | _ => false

def graphInitialView (p : Project) : Option String := do
  let part ← (documentOf "Demo" p).subParts.find? (·.titleString == "Dependency Graph")
  match (part.content[0]? : Option (Verso.Doc.Block Verso.Genre.Manual)) with
  | some (.other b _) => (fromJson? (α := Informal.Commands.GraphBlockData) b.data).toOption.bind (·.initialView)
  | _ => none

-- The document: the front page, one chapter per module, the graph and the summary.
/-- info: true -/
#guard_msgs in
#eval
  let doc := documentOf "Demo" fixture
  doc.titleString == "Demo" &&
    doc.subParts.map (·.titleString) ==
      #["Demo.Basic", "Demo.Hard", "Dependency Graph", "Blueprint Summary"] &&
    (doc.subParts[0]!.content.filter isNodeBlock).size == 3

-- Small graphs open on the full graph; above the threshold on the module view.
/-- info: true -/
#guard_msgs in
#eval
  let decls : Array CodeSite.Declaration :=
    (Array.range 301).map fun i => { name := .mkSimple s!"d{i}", kind := "def" }
  let many : Project := { fixture with modules := #[{ module := `Big, declarations := decls }] }
  graphInitialView fixture == none && graphInitialView many == some "group"

/-- A scratch project root with the module sources and a README. -/
def withProject (k : System.FilePath → IO Bool) : IO Bool := do
  let root := System.FilePath.mk s!"/tmp/vbp-code-site-test-{← IO.monoNanosNow}"
  IO.FS.createDirAll (root / "Demo")
  IO.FS.writeFile (root / "Demo" / "Basic.lean") basicSource
  IO.FS.writeFile (root / "Demo" / "Hard.lean") "theorem hard : False := sorry\n"
  IO.FS.writeFile (root / "README.md") "# Demo project\n\nA small project.\n"
  IO.FS.writeFile (root / "code.json") fixtureJson
  try k root finally IO.FS.removeDirAll root

-- A whole site: chapters, the graph with a node view per declaration, the stats page.
/-- info: true -/
#guard_msgs in
#eval withProject fun root => do
  let code ← generate (root / "code.json") root none
    ["--output", (root / "_out").toString, "--reproducible"]
  let html := root / "_out" / "html-multi"
  let index ← IO.FS.readFile (html / "index.html")
  let views ← IO.FS.readFile (html / "-verso-data" / "blueprint-node-views.json")
  let stats ← IO.FS.readFile (html / "Project-Stats" / "index.html")
  let chapter ← IO.FS.readFile (html / "Demo___Basic" / "index.html")
  return code == 0 && hasSubstr index "Demo project" && hasSubstr index "Demo.Later" &&
    hasSubstr views "Demo.uses_hard" && hasSubstr views "data-lean-decls" &&
    hasSubstr views "lean:decl/Demo.double_eq" &&
    hasSubstr stats "Project Stats" && hasSubstr chapter "Demo.double_eq" &&
    (← (html / "Dependency-Graph" / "index.html").pathExists)

-- `--no-stats-page` leaves the page out.
/-- info: true -/
#guard_msgs in
#eval withProject fun root => do
  let code ← generate (root / "code.json") root none
    ["--output", (root / "_out").toString, "--reproducible", "--no-stats-page"]
  return code == 0 && !(← (root / "_out" / "html-multi" / "Project-Stats").pathExists)

-- The command line.
/-- info: true -/
#guard_msgs in
#eval
  (match parseOptions ["--data", "d.json", "--root", "r", "--output", "o", "--no-stats-page"] {} with
    | .ok o => o.data == some "d.json" && o.root == some "r" &&
        o.rest == #["--output", "o", "--no-stats-page"]
    | .error _ => false) &&
  (parseOptions ["--bogus"] {} matches .error _) &&
  (parseOptions ["--data"] {} matches .error _)

end Verso.VersoBlueprintTests.BlueprintCodeSite
