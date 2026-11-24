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
    hasSubstr r.html ">Demo.double</span>" && hasSubstr r.html "Twice" &&
      hasSubstr r.html "bp_plain_decl_source" && hasSubstr r.html ">double</span>" &&
      hasSubstr r.html "Demo/Basic.lean:3"
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

/-- The fixture with an informal statement on `Demo.double_eq` (title, math, proof) and a
hostile one on `Demo.hard` (raw HTML, a script link). -/
def statedFixture : Project :=
  let stated : Statement := { text := "For all $n$, $$2n = n + n.$$", proof := some "Unfold $2n$."
                              title := some "Doubling", source := some "tex" }
  let hostile : Statement :=
    { text := "<script>alert(1)</script> [x](javascript:alert(1)) and $a$", source := some "docstring" }
  let set (d : CodeSite.Declaration) : CodeSite.Declaration :=
    if d.name == `Demo.double_eq then { d with statement := some stated }
    else if d.name == `Demo.hard then { d with statement := some hostile } else d
  { fixture with modules := fixture.modules.map fun m => { m with declarations := m.declarations.map set }
                 texPrelude := "\\newcommand{\\twice}{2}</script><i id=\"prelude-escaped\">" }

-- The statement field is read from the data, and its absence is no statement.
/-- info: true -/
#guard_msgs in
#eval
  let j := "{\"format\":\"verso-blueprint-code-1\",\"modules\":[{\"module\":\"M\",\"declarations\":[
    {\"name\":\"M.a\",\"kind\":\"theorem\",\"statement\":{\"text\":\"$x$\",\"proof\":\"p\",
      \"title\":\"T\",\"source\":\"tex\"}},
    {\"name\":\"M.b\",\"kind\":\"def\",\"statement\":null},
    {\"name\":\"M.c\",\"kind\":\"def\"}]}]}"
  match Project.parse j with
  | .ok p =>
    let ds := p.modules[0]!.declarations
    ds[0]!.statement == some ({ text := "$x$", proof := some "p", title := some "T"
                                source := some "tex" } : Statement) &&
      ds[1]!.statement.isNone && ds[2]!.statement.isNone
  | .error _ => false

-- A statement becomes the node's statement body (math as Blueprint math), its proof the proof body; a node
-- without one keeps empty bodies.
/-- info: true -/
#guard_msgs in
#eval
  let s := stateOf statedFixture fun _ => none
  let mathIn (d : Option Data.InformalData) : Bool := (d.map fun d => d.previewBlocks.any fun
    | .para inls => inls.any fun
      | .other i _ => i.name == ``Informal.Math.Inline.bpMath
      | _ => false
    | _ => false).getD false
  match s.data.find? `Demo.double_eq, s.data.find? `Demo.double with
  | some n, some plain =>
    mathIn n.statement && mathIn n.proof &&
      (n.statement.map (fun (d : Data.InformalData) => d.previewBlocks.size)) == some 2 &&
      plain.statement.any (fun (d : Data.InformalData) => d.previewBlocks.isEmpty) &&
      plain.proof.isNone
  | _, _ => false

-- The chapter: a statement block per declaration, a proof block after a stated proof.
/-- info: true -/
#guard_msgs in
#eval
  let doc := documentOf "Demo" statedFixture
  let blocks := doc.subParts[0]!.content.filter isNodeBlock
  let proofs := blocks.filter fun
    | .other b _ => (fromJson? (α := Informal.BlockOccurrence) b.data).toOption.any (·.isProof)
    | _ => false
  blocks.size == 4 && proofs.size == 1

-- The front page says how many nodes have a statement.
/-- info: true -/
#guard_msgs in
#eval
  let text (p : Project) : String := (frontMatter p).foldl (init := "") fun acc b => match b with
    | .para inls => inls.foldl (init := acc) fun acc i => match i with
      | .text t => acc ++ t
      | _ => acc
    | _ => acc
  hasSubstr (text statedFixture) "2 of them have an informal statement" &&
    hasSubstr (text fixture) "there are no informal statements"

-- Raw HTML in a statement is text, a script link keeps its text and loses its target.
/-- info: true -/
#guard_msgs in
#eval
  let blocks := statementTextBlocks "<b>x</b> [y](javascript:alert(1)) [z](https://lean-lang.org)"
  let links := blocks.foldl (init := #[]) fun acc b => match b with
    | .para inls => acc ++ inls.filterMap fun | .link _ h => some h | _ => none
    | _ => acc
  links == #["https://lean-lang.org"] &&
    blocks.all fun b => match b with
      | .para inls => inls.any fun | .text t => hasSubstr t "<b>" | _ => false
      | _ => false

/-- The text of the paragraphs of `blocks`, with each formula as `[mode:tex]`. -/
def paraText (blocks : Array (Verso.Doc.Block Verso.Genre.Manual)) : String :=
  blocks.foldl (init := "") fun acc b => match b with
    | .para inls => inls.foldl (init := acc) fun acc i => match i with
      | .text t => acc ++ t
      | .math .display t => acc ++ s!"[display:{t}]"
      | .math .inline t => acc ++ s!"[inline:{t}]"
      | _ => acc
    | _ => acc

-- Module docstrings: raw HTML is shown as text, in paragraphs (not the code-block fallback).
/-- info: true -/
#guard_msgs in
#eval
  #["type List<Nat> here", "a <br> break", "a<b and c>d", "inline <b>bold</b> html"].all fun d =>
    let blocks := moduleDocBlocks d
    blocks.all (fun b => b matches .para _) && paraText blocks == d

-- Module docstrings: Verso's docstring math and TeX math spans are formulas.
/-- info: true -/
#guard_msgs in
#eval
  paraText (moduleDocBlocks "Let $`y` be $$`x^2`, and $z$.") ==
    "Let [inline:y] be [display:x^2], and [inline:z]." &&
  paraText (moduleDocBlocks "costs `5` and $`a`") == "costs  and [inline:a]"

/-- A build record as Lake writes it beside a compiled module (`<module>.trace` in the project's
`.lake/build/lib/lean`, beside a stand-in `.olean` whose bytes it names), saying that `module` was
compiled from the text `file` (relative to `root`) has now. -/
def recordBuild (root : System.FilePath) (module : Name) (file : String) : IO Unit := do
  let text ← IO.FS.readFile (root / file)
  let olean := modToFilePath (root / ".lake" / "build" / "lib" / "lean") module "olean"
  if let some dir := olean.parent then IO.FS.createDirAll dir
  let bytes := s!"compiled {module}".toUTF8
  IO.FS.writeBinFile olean bytes
  let trace := Json.mkObj [
    ("outputs", Json.mkObj [("o", Json.arr #[.str s!"{Stats.lakeBytesHash bytes}.olean"])]),
    ("inputs", Json.arr #[Json.arr #[.str (root / file).toString, .str (Stats.lakeTextHash text)]])]
  IO.FS.writeFile (olean.withExtension "trace") trace.compress

/-- A scratch project root with the module sources and a README, each module with a build record
of its source as written (`recordBuild`). -/
def withProject (k : System.FilePath → IO Bool) : IO Bool := do
  let root := System.FilePath.mk s!"/tmp/vbp-code-site-test-{← IO.monoNanosNow}"
  IO.FS.createDirAll (root / "Demo")
  IO.FS.writeFile (root / "Demo" / "Basic.lean") basicSource
  IO.FS.writeFile (root / "Demo" / "Hard.lean") "theorem hard : False := sorry\n"
  IO.FS.writeFile (root / "README.md") "# Demo project\n\nA small project.\n"
  IO.FS.writeFile (root / "code.json") fixtureJson
  recordBuild root `Demo.Basic "Demo/Basic.lean"
  recordBuild root `Demo.Hard "Demo/Hard.lean"
  -- the generator's progress lines (the kernel replay's, for one) are not what is tested
  try (·.2) <$> IO.FS.withIsolatedStreams (k root) finally IO.FS.removeDirAll root

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

-- A site with statements: the node view shows the informal column beside the Lean one, with the
-- math for the page's renderer (after the TeX prelude, whose angle brackets cannot end a script)
-- and the proof folded; a node without a statement shows Lean alone; a hostile statement's HTML
-- is escaped.
/-- info: true -/
#guard_msgs in
#eval withProject fun root => do
  IO.FS.writeFile (root / "code.json") (toJson statedFixture).compress
  let code ← generate (root / "code.json") root none
    ["--output", (root / "_out").toString, "--reproducible"]
  let html := root / "_out" / "html-multi"
  let views ← IO.FS.readFile (html / "-verso-data" / "blueprint-node-views.json")
  let some entries := (Json.parse views).toOption.bind
      (fun j => (j.getObjValAs? (Array Json) "entries").toOption) | return false
  let viewOf (l : String) : String := (entries.findSome? fun e =>
    if (e.getObjValAs? String "label").toOption == some l then (e.getObjValAs? String "html").toOption
    else none).getD ""
  let stated := viewOf "Demo.double_eq"
  let plain := viewOf "Demo.double"
  let hostile := viewOf "Demo.hard"
  let graph ← IO.FS.readFile (html / "Dependency-Graph" / "index.html")
  return code == 0 && hasSubstr stated "bp_sbs_informal" && hasSubstr stated "bp_math display" &&
    hasSubstr stated "data-bp-tex-prelude-id=\"default\"" &&
    !hasSubstr graph "<i id=\"prelude-escaped\">" &&
    hasSubstr stated "Doubling" && hasSubstr stated "bp_node_view_proof" &&
    !hasSubstr plain "bp_sbs_informal" && hasSubstr plain "bp_sbs_single" &&
    hasSubstr hostile "&lt;script&gt;" && !hasSubstr hostile "<script>" &&
    !hasSubstr hostile "javascript:"

/-- The fixture with a statement on `Demo.double_eq` whose formulas use the prelude's macro,
and the statement `other` on `Demo.double`. -/
def mathFixture (other : String) : Project :=
  let stated : Statement := { text := "For all $n$, $$\\twice n = n + n.$$"
                              proof := some "Unfold $\\twice n$.", source := some "tex" }
  let set (d : CodeSite.Declaration) : CodeSite.Declaration :=
    if d.name == `Demo.double_eq then { d with statement := some stated }
    else if d.name == `Demo.double then { d with statement := some { text := other } } else d
  { fixture with modules := fixture.modules.map fun m => { m with declarations := m.declarations.map set }
                 texPrelude := "\\newcommand{\\twice}{2}" }

/-- The pages (`index.html` files) under a folder, as text. -/
partial def pagesUnder (dir : System.FilePath) : IO (Array String) := do
  let mut out := #[]
  for e in ← dir.readDir do
    if ← e.path.isDir then out := out ++ (← pagesUnder e.path)
    else if e.fileName == "index.html" then out := out.push (← IO.FS.readFile e.path)
  return out

-- Statement formulas are typeset when the site is built: pictures on the chapter page, and in
-- the node view a reference to the formula's template in the page of the graph, which holds
-- each formula once. With every formula accepted no page loads KaTeX's files.
/-- info: true -/
#guard_msgs in
#eval withProject fun root => do
  IO.FS.writeFile (root / "code.json") (toJson (mathFixture "Twice $n$.")).compress
  let code ← generate (root / "code.json") root none
    ["--output", (root / "_out").toString, "--reproducible"]
  let html := root / "_out" / "html-multi"
  let views ← IO.FS.readFile (html / "-verso-data" / "blueprint-node-views.json")
  let graph ← IO.FS.readFile (html / "Dependency-Graph" / "index.html")
  let chapter ← IO.FS.readFile (html / "Demo___Basic" / "index.html")
  let pages ← pagesUnder html
  let keysOf (s : String) : List String :=
    ((s.splitOn " data-bp-math-key=\"").drop 1).map fun t => (t.splitOn "\"").headD ""
  let stored := keysOf graph
  let refs := keysOf (views.replace "\\\"" "\"")
  return code == 0 && refs.length == 4 && stored.length == 3 && refs.all stored.contains &&
    stored.eraseDups.length == stored.length && stored.all refs.contains &&
    !hasSubstr views "bp_math_static" && !hasSubstr views "<code class=\\\"bp_math " &&
    hasSubstr views "\\\\twice n = n + n.</code>" &&
    countSubstr chapter "data-bp-math-rendered=\"1\"" == 4 &&
    !hasSubstr chapter "<code class=\"bp_math " && !hasSubstr chapter "<template class=\"bp_math" &&
    pages.size > 3 && pages.all (fun p => !hasSubstr p "katex/katex.js" &&
      !hasSubstr p "katex/katex.css" && !hasSubstr p "data-bp-glyphs")

-- A formula that is not accepted keeps the browser path, alone: it stays TeX in the node view
-- and on its page, the other statement's formulas are still typeset, and the pages keep KaTeX.
/-- info: true -/
#guard_msgs in
#eval withProject fun root => do
  IO.FS.writeFile (root / "code.json") (toJson (mathFixture "Half $\\frac{1}{$.")).compress
  let code ← generate (root / "code.json") root none
    ["--output", (root / "_out").toString, "--reproducible"]
  let html := root / "_out" / "html-multi"
  let views ← IO.FS.readFile (html / "-verso-data" / "blueprint-node-views.json")
  let graph ← IO.FS.readFile (html / "Dependency-Graph" / "index.html")
  let chapter ← IO.FS.readFile (html / "Demo___Basic" / "index.html")
  return code == 0 && countSubstr views "bp_math_ref" == 3 &&
    countSubstr views "<code class=\\\"bp_math inline\\\" data-bp-tex-prelude-id" == 1 &&
    hasSubstr views ">\\\\frac{1}{</code>" &&
    countSubstr graph "<template class=\"bp_math_stored\"" == 3 &&
    countSubstr chapter "data-bp-math-rendered=\"1\"" == 3 &&
    countSubstr chapter "<code class=\"bp_math inline\"" == 1 &&
    hasSubstr graph "katex/katex.js" && hasSubstr chapter "katex/katex.js"

/-- The files of a challenge `Demo` that follows the layout (`Informal.Stats.ComparatorLayout`). -/
private def writeDemoChallenge (root : System.FilePath) : IO Unit := do
  IO.FS.createDirAll (root / "Comparator" / "Demo")
  IO.FS.writeFile (root / "Comparator" / "Demo" / "Challenge.lean")
    "namespace Demo\n\n/-- Doubling. -/\ntheorem double_eq : 2 * 3 = 3 + 3 := by\n  sorry\n\nend Demo\n"
  IO.FS.writeFile (root / "Comparator" / "Demo" / "Solution.lean")
    "namespace Demo\n\n/-- Doubling <b>here</b>. -/\ntheorem double_eq : 2 * 3 = 3 + 3 := rfl\n\nend Demo\n"
  IO.FS.writeFile (root / "Comparator" / "Demo" / "comparator.json")
    ("{\"challenge_module\": \"Comparator.Demo.Challenge\", " ++
      "\"solution_module\": \"Comparator.Demo.Solution\", " ++
      "\"theorem_names\": [\"Demo.double_eq\"], \"permitted_axioms\": [\"propext\"]}")

-- `--challenge-not-built <reason>`: nothing is compared, and the headline says the challenge
-- module was not built, with the reason. The Comparator pages list the challenge with the same
-- words, and its page shows its three files in full, escaped.
/-- info: true -/
#guard_msgs in
#eval withProject fun root => do
  writeDemoChallenge root
  let code ← generate (root / "code.json") root none
    ["--output", (root / "_out").toString, "--reproducible"]
    (challengeNotBuilt? := some "Comparator.Demo.Challenge: lake build failed: exit 1")
  let site := root / "_out" / "html-multi"
  let stats ← IO.FS.readFile (site / "Project-Stats" / "index.html")
  let index ← IO.FS.readFile (site / "Comparator" / "index.html")
  let page ← IO.FS.readFile (site / "Comparator" / "Demo" / "index.html")
  let notBuilt := "Not compared: the challenge module has not been built \
      (Comparator.Demo.Challenge: lake build failed: exit 1)."
  return code == 0 && hasSubstr stats "bp_stats_headline_unavailable" && hasSubstr stats notBuilt &&
    hasSubstr stats "class=\"bp_stats_challenge_link\"" &&
    hasSubstr index notBuilt && hasSubstr index "Comparator.Demo.Solution" &&
    hasSubstr page notBuilt && hasSubstr page "Comparator/Demo/comparator.json" &&
    hasSubstr page "Doubling &lt;b&gt;here&lt;/b&gt;." && !hasSubstr page "<b>here</b>" &&
    hasSubstr page "\"theorem_names\": [\"Demo.double_eq\"]" &&
    hasSubstr page (Informal.Commands.challengePageIntroText "Demo")

-- A project that depends on another one, from a path outside it, with a challenge folder of the
-- same name: the challenge's module has a compiled file in both builds, so it is not compared,
-- and the card names the module and both files.
/-- info: true -/
#guard_msgs in
#eval withProject fun root => do
  writeDemoChallenge root
  let dep := System.FilePath.mk s!"{root}-dependency"
  try
    for base in [root, dep] do
      let lib := base / ".lake" / "build" / "lib" / "lean" / "Comparator" / "Demo"
      IO.FS.createDirAll lib
      IO.FS.writeFile (lib / "Challenge.olean") s!"compiled in {base}"
    IO.FS.writeFile (root / "lake-manifest.json") (Json.mkObj [("version", "1.1.0"),
      ("packagesDir", ".lake/packages"), ("packages", Json.arr #[Json.mkObj [("type", "path"),
        ("name", "dependency"), ("dir", s!"../{dep.fileName.getD ""}")]])]).compress
    let code ← generate (root / "code.json") root none
      ["--output", (root / "_out").toString, "--reproducible"] (kernelReplay := false)
    let stats ← IO.FS.readFile (root / "_out" / "html-multi" / "Project-Stats" / "index.html")
    return code == 0 && hasSubstr stats "Not compared: a module of the comparison has a compiled \
      file in more than one directory of the search path" &&
      hasSubstr stats s!"(Comparator.Demo.Challenge: {← IO.FS.realPath root}/.lake" &&
      hasSubstr stats s!"{← IO.FS.realPath dep}/.lake" &&
      hasSubstr stats "give the challenges of each project folder names of their own."
  finally IO.FS.removeDirAll dep

-- A project whose Comparator files do not follow the layout is not generated: the generator
-- fails and names the file, the rule and the change.
/-- info: true -/
#guard_msgs in
#eval withProject fun root => do
  writeDemoChallenge root
  IO.FS.writeFile (root / "Comparator" / "Demo" / "notes.md") "x"
  let failed ← try
      let code ← generate (root / "code.json") root none
        ["--output", (root / "_out").toString, "--reproducible", "--no-kernel-replay"]
      pure (code != 0)
    catch e => pure ((toString e).contains "Comparator/Demo/notes.md: rule F1")
  return failed && !(← (root / "_out" / "html-multi" / "Comparator").pathExists)

-- Module docstrings on a chapter page: raw HTML as text, Verso's display math as a formula.
/-- info: true -/
#guard_msgs in
#eval withProject fun root => do
  IO.FS.writeFile (root / "Demo" / "Basic.lean")
    ("/-! Lists: type List<Nat> here, a <br> break, a<b and c>d, inline <b>bold</b> html.\n\n" ++
      "The number is\n$$`\\rho = \\sum_k 2^{-k}`.\n-/\n" ++ basicSource)
  recordBuild root `Demo.Basic "Demo/Basic.lean"
  let code ← generate (root / "code.json") root none
    ["--output", (root / "_out").toString, "--reproducible"]
  let chapter ← IO.FS.readFile (root / "_out" / "html-multi" / "Demo___Basic" / "index.html")
  return code == 0 && hasSubstr chapter "List&lt;Nat&gt;" && hasSubstr chapter "a&lt;b and c&gt;d" &&
    !hasSubstr chapter "<b>bold</b>" && !hasSubstr chapter "$$<code>" &&
    hasSubstr chapter "\\rho = \\sum_k"

-- `--no-stats-page` leaves the page out, also when an earlier build into the same folder wrote it.
/-- info: true -/
#guard_msgs in
#eval withProject fun root => do
  let out := (root / "_out").toString
  let first ← generate (root / "code.json") root none ["--output", out, "--reproducible"]
  let page := root / "_out" / "html-multi" / Informal.Commands.statsPageFolder
  let before ← page.pathExists
  let code ← generate (root / "code.json") root none
    ["--output", out, "--reproducible", "--no-stats-page"]
  return first == 0 && before && code == 0 && Informal.Commands.statsPageFolder == "Project-Stats" &&
    !(← page.pathExists) && (← (root / "_out" / "html-multi" / "index.html").pathExists)

-- The command line.
/-- info: true -/
#guard_msgs in
#eval
  (match parseOptions ["--data", "d.json", "--root", "r", "--output", "o", "--no-stats-page"] {} with
    | .ok o => o.data == some "d.json" && o.root == some "r" &&
        o.rest == #["--output", "o", "--no-stats-page"]
    | .error _ => false) &&
  (match parseOptions ["--challenge-not-built", "why"] {} with
    | .ok o => o.challengeNotBuilt == some "why" && o.compare
    | .error _ => false) &&
  (parseOptions ["--challenge-not-built"] {} matches .error _) &&
  (parseOptions ["--bogus"] {} matches .error _) &&
  (parseOptions ["--graphviz", "dot"] {} matches .error _) &&
  (parseOptions ["--no-graph-layout"] {} matches .error _) &&
  (parseOptions ["--data"] {} matches .error _)

/-! ## What the data cannot make a site say -/

-- A declaration whose data states no status is unverified, never proved: a minimal entry the
-- schema allows does not count as proved anywhere.
/-- info: true -/
#guard_msgs in
#eval
  match Project.parse "{\"format\":\"verso-blueprint-code-1\",\"modules\":[{\"module\":\"M\",\
      \"declarations\":[{\"name\":\"M.t\",\"kind\":\"theorem\"}]}]}" with
  | .ok (p : Project) =>
    match p.modules[0]?.bind (fun (m : Informal.CodeSite.Module) => m.declarations[0]?) with
    | some (d : Informal.CodeSite.Declaration) =>
      d.status == "unverified" && !(provedStatus d).isProved
    | none => false
  | .error _ => false

-- The front page counts the chapters: a module without declarations has none.
/-- info: true -/
#guard_msgs in
#eval
  let p : Project := { modules := #[{ module := `A, declarations := #[{ name := `A.x, kind := "def" }] },
    { module := `B, declarations := #[{ name := `B.y, kind := "def" }] }, { module := `Empty }] }
  let text := (frontMatter p).foldl (init := "") fun acc b => match b with
    | .para inls => acc ++ inls.foldl (init := "") fun a i => match i with
      | .text t => a ++ t | _ => a
    | _ => acc
  hasSubstr text "2 declarations in 3 modules, one chapter per module with declarations \
    (2 chapters)" && (documentOf "t" p).subParts.size == 4

-- A module's source is read only when it is a file inside the project root: an absolute path,
-- a path through `..`, a symbolic link that leads out of the root, a folder and a missing file
-- are not read, and the site names no file for them; a link inside the root is followed.
/-- info: (true, true) -/
#guard_msgs in
#eval show IO _ from do
  let root := System.FilePath.mk s!"/tmp/vbp-source-bound-test-{← IO.monoNanosNow}"
  let outside := System.FilePath.mk s!"{root}-outside"
  IO.FS.createDirAll (root / "Src")
  IO.FS.createDirAll outside
  IO.FS.writeFile (root / "Src" / "A.lean") "theorem a : True := trivial\n"
  IO.FS.writeFile (outside / "secret.txt") "not for the site\n"
  let link (target name : System.FilePath) : IO Unit := discard <| IO.Process.output
    { cmd := "ln", args := #["-s", target.toString, name.toString] }
  link (outside / "secret.txt") (root / "Src" / "Out.lean")
  link (root / "Src" / "A.lean") (root / "Src" / "In.lean")
  let modules := [("M.A", "Src/A.lean"), ("M.Abs", (outside / "secret.txt").toString),
    ("M.Up", "Src/../../" ++ (outside.fileName.getD "") ++ "/secret.txt"), ("M.Out", "Src/Out.lean"),
    ("M.In", "Src/In.lean"), ("M.Dir", "Src"), ("M.None", "Src/None.lean")]
  let json := Json.mkObj [("format", "verso-blueprint-code-1"), ("modules", Json.arr
    (modules.toArray.map fun (m, src) => Json.mkObj [("module", toJson m), ("source", toJson src),
      ("declarations", Json.arr #[])]))]
  IO.FS.writeFile (root / "code.json") json.compress
  let (project, sources) ← IO.FS.withIsolatedStreams (load (root / "code.json") root) >>= (pure ·.2)
  IO.FS.removeDirAll root
  IO.FS.removeDirAll outside
  let kept := project.modules.filter (!·.source.isEmpty) |>.map (·.module.toString)
  let read := (sources.toArray.map (·.1.toString)).qsort (· < ·)
  return (kept == #["M.A", "M.In"], read == #["M.A", "M.In"] &&
    sources.toArray.all fun (_, text) => !hasSubstr text "not for the site")

-- A build into a folder an earlier build wrote: a chapter the data no longer has is gone, with
-- its folder, while a file the generator did not write stays.
/-- info: true -/
#guard_msgs in
#eval withProject fun root => do
  let out := (root / "_out").toString
  let html := root / "_out" / "html-multi"
  let first ← generate (root / "code.json") root none ["--output", out, "--reproducible"]
  let hardBefore ← (html / "Demo___Hard" / "index.html").pathExists
  IO.FS.writeFile (html / "notes.txt") "kept"
  -- the same project without its second module
  let data ← IO.ofExcept (Json.parse (← IO.FS.readFile (root / "code.json")))
  let modules := (data.getObjValAs? (Array Json) "modules").toOption.getD #[]
  IO.FS.writeFile (root / "code.json")
    (data.setObjVal! "modules" (Json.arr (modules.extract 0 1))).compress
  IO.sleep 20
  let second ← generate (root / "code.json") root none ["--output", out, "--reproducible"]
  return first == 0 && second == 0 && hardBefore &&
    !(← (html / "Demo___Hard").pathExists) && (← (html / "Demo___Basic" / "index.html").pathExists) &&
    (← IO.FS.readFile (html / "notes.txt")) == "kept"

/-! ## Source text and the build

A site shows a module's source as it reads when the site is generated, and what the build says of
the compiled module. When the two are not known to be of the same text, nothing positive is shown
for the module's declarations. -/

/-- The parts of a generated site a reader sees that the next tests look at. -/
structure SitePages where
  chapter : String
  graph : String
  stats : String
  views : String

/-- Generate the site of the project at `root` without a kernel replay, and read its pages. -/
def sitePages (root : System.FilePath) : IO (UInt32 × SitePages) := do
  let code ← generate (root / "code.json") root none
    ["--output", (root / "_out").toString, "--reproducible"] (kernelReplay := false)
  let html := root / "_out" / "html-multi"
  return (code, { chapter := ← IO.FS.readFile (html / "Demo___Basic" / "index.html")
                  graph := ← IO.FS.readFile (html / "Dependency-Graph" / "index.html")
                  stats := ← IO.FS.readFile (html / "Project-Stats" / "index.html")
                  views := ← IO.FS.readFile (html / "-verso-data" / "blueprint-node-views.json") })

/-- Whether the pages show the module `Demo.Basic` with no positive mark: the words `words` on its
declarations' heading, Lean-code link, graph node and stats page, no "no sorry" beside them, the
neutral graph fill, and the module on the stats page. -/
def shownWithoutVerdict (pages : SitePages) (words : String) : Bool :=
  hasSubstr pages.chapter "Lean proof: the source of Demo.Basic (Demo/Basic.lean)" &&
  hasSubstr pages.chapter words &&
  !hasSubstr pages.chapter "Lean proof without sorry, as the compiled files report" &&
  !hasSubstr pages.chapter "bp_code_decl_status bp_code_decl_status_ok" &&
  hasSubstr pages.graph "class=\"node bp_graph_status_source_changed" &&
  hasSubstr pages.graph "Demo.double_eq: Lean proof: the source of Demo.Basic" &&
  hasSubstr pages.stats "data-bp-module=\"Demo.Basic\"" &&
  hasSubstr pages.stats "data-bp-status=\"source-changed\"" &&
  hasSubstr pages.stats "This is said of the compiled modules: the Lean source of " &&
  hasSubstr pages.views "so nothing is shown as checked"

-- The module's source edited after the build: its declarations are shown with no verdict, as
-- "source changed since the build"; the other module keeps its marks.
/-- info: true -/
#guard_msgs in
#eval withProject fun root => do
  IO.FS.writeFile (root / "Demo" / "Basic.lean") (basicSource ++ "-- edited after the build\n")
  let (code, pages) ← sitePages root
  return code == 0 && shownWithoutVerdict pages "changed since the build" &&
    hasSubstr pages.chapter "This is Demo/Basic.lean as it reads now" &&
    !hasSubstr pages.stats "data-bp-module=\"Demo.Hard\""

-- No build record: "not known to match the build", with the reason.
/-- info: true -/
#guard_msgs in
#eval withProject fun root => do
  IO.FS.removeDirAll (root / ".lake")
  let (code, pages) ← sitePages root
  return code == 0 && shownWithoutVerdict pages "is not known to match the build: its compiled \
    module was not found"

-- A build record of other compiled files than those beside it says nothing.
/-- info: true -/
#guard_msgs in
#eval withProject fun root => do
  IO.FS.writeFile (root / ".lake" / "build" / "lib" / "lean" / "Demo" / "Basic.olean") "other"
  let (code, pages) ← sitePages root
  return code == 0 && shownWithoutVerdict pages "describes other compiled files than Basic.olean"

-- The same project with its records as built: no module is shown without a verdict.
/-- info: true -/
#guard_msgs in
#eval withProject fun root => do
  let (code, pages) ← sitePages root
  return code == 0 && !hasSubstr pages.chapter "so nothing is shown as checked" &&
    hasSubstr pages.chapter "Lean proof without sorry, as the compiled files report" &&
    !hasSubstr pages.graph "class=\"node bp_graph_status_source_changed" &&
    !hasSubstr pages.stats "data-bp-module="

/-! ## Modules and what they import

A compiled module is built against the compiled modules it imports. A module whose own source is
the text that was compiled is still not known to match the build when a project module it
imports, directly or not, changed since: its declarations get no positive mark either, and a
Comparator challenge whose solution is built on such a module is not compared. -/

/-- The project of `withProject` with `Demo.Hard` importing `Demo.Basic` through `Demo.Mid`, a
module of the project that the data does not list (it declares nothing), each with a build
record of its source as written. -/
def withImportingProject (k : System.FilePath → IO Bool) : IO Bool := withProject fun root => do
  IO.FS.writeFile (root / "Demo" / "Mid.lean") "import Demo.Basic\n"
  IO.FS.writeFile (root / "Demo" / "Hard.lean")
    "import Lean\nimport Demo.Mid\ntheorem hard : False := sorry\n"
  recordBuild root `Demo.Mid "Demo/Mid.lean"
  recordBuild root `Demo.Hard "Demo/Hard.lean"
  k root

/-- The finder of the project at `root` as the generator builds it (`moduleFinderOf`). -/
def finderAt (root : System.FilePath) : IO Stats.ModuleFinder := do
  let project ← match Project.parse (← IO.FS.readFile (root / "code.json")) with
    | .ok p => pure p
    | .error e => throw (IO.userError e)
  moduleFinderOf root project fun _ => none

-- As built, nothing is out of step: Lean's own `Lean` is not followed, `Demo.Mid` is reached.
/-- info: true -/
#guard_msgs in
#eval withImportingProject fun root => do
  let finder ← finderAt root
  let standings ← Stats.walkModules finder #[`Demo.Hard]
  return (← Stats.walkChanges finder #[`Demo.Hard]).isEmpty &&
    (standings.toList.map (·.1)).mergeSort (·.toString < ·.toString) ==
      [`Demo.Basic, `Demo.Hard, `Demo.Mid]

-- `Demo.Basic` edited after the build: `Demo.Mid` and `Demo.Hard`, whose own sources match, are
-- not known to match the build either, and each names the module that changed.
/-- info: true -/
#guard_msgs in
#eval withImportingProject fun root => do
  IO.FS.writeFile (root / "Demo" / "Basic.lean") (basicSource.replace "n + n" "sorry")
  return ((← Stats.walkChanges (← finderAt root) #[`Demo.Hard]).map (·.text)).toList == [
    "the source of Demo.Basic (Demo/Basic.lean) changed since the build",
    "Demo.Hard (Demo/Hard.lean) imports Demo.Basic in Demo/Basic.lean, which changed since the \
      build",
    "Demo.Mid (Demo/Mid.lean) imports Demo.Basic in Demo/Basic.lean, which changed since the \
      build"]

-- A module that changed is not followed further: what it imports now need not be what it was
-- compiled with (here a module that does not exist).
/-- info: true -/
#guard_msgs in
#eval withImportingProject fun root => do
  IO.FS.writeFile (root / "Demo" / "Mid.lean") "import Demo.Basic\nimport Demo.Nowhere\n"
  return ((← Stats.walkChanges (← finderAt root) #[`Demo.Hard]).map (·.text)).toList == [
    "Demo.Hard (Demo/Hard.lean) imports Demo.Mid in Demo/Mid.lean, which changed since the build",
    "the source of Demo.Mid (Demo/Mid.lean) changed since the build"]

-- The site: `Demo.Hard`'s declarations get the neutral mark with the module that changed named,
-- on the chapter, the graph and the stats page, beside `Demo.Basic`'s own.
/-- info: true -/
#guard_msgs in
#eval withImportingProject fun root => do
  IO.FS.writeFile (root / "Demo" / "Basic.lean") (basicSource ++ "-- edited after the build\n")
  let (code, pages) ← sitePages root
  let hard ← IO.FS.readFile (root / "_out" / "html-multi" / "Demo___Hard" / "index.html")
  let imports := "Demo.Hard (Demo/Hard.lean) imports Demo.Basic in Demo/Basic.lean, which \
    changed since the build"
  return code == 0 && shownWithoutVerdict pages "changed since the build" &&
    hasSubstr hard s!"Lean proof: {imports}" &&
    hasSubstr pages.graph s!"Demo.uses_hard: Lean proof: {imports}" &&
    hasSubstr pages.stats "data-bp-module=\"Demo.Hard\"" &&
    hasSubstr pages.stats "data-bp-module=\"Demo.Mid\"" &&
    hasSubstr pages.stats imports

-- What a Comparator challenge's headline is told (`Stats.sourcesUnavailable?`): its solution
-- `Demo.Hard` is built on `Demo.Basic`, edited after the build, so it is not compared, with the
-- module named; a challenge `Demo.Mid` that imports it is out of date; as built, nothing.
/-- info: true -/
#guard_msgs in
#eval withImportingProject fun root => do
  let asBuilt ← Stats.sourcesUnavailable? (← finderAt root) `Demo.Basic `Demo.Hard
  IO.FS.writeFile (root / "Demo" / "Basic.lean") (basicSource ++ "-- edited after the build\n")
  let finder ← finderAt root
  return asBuilt.isNone &&
    (← Stats.sourcesUnavailable? finder `Demo.Mid `Demo.Hard) == some (.challengeOutOfDate,
      "it imports Demo.Basic in Demo/Basic.lean, which changed since the build") &&
    (← Stats.sourcesUnavailable? finder `Demo.Basic.Missing `Demo.Hard) ==
      some (.solutionOutOfDate, "Demo.Basic in Demo/Basic.lean")

-- A build record missing for a module the solution is built on: not compared, with why.
/-- info: true -/
#guard_msgs in
#eval withImportingProject fun root => do
  IO.FS.removeFile (root / ".lake" / "build" / "lib" / "lean" / "Demo" / "Mid.trace")
  return (← Stats.sourcesUnavailable? (← finderAt root) `Demo.Basic.Missing `Demo.Hard) ==
    some (.solutionProvenanceUnknown, "Demo.Mid in Demo/Mid.lean: Lake's build record Mid.trace \
      of the compiled module Demo.Mid is missing or cannot be read")

/-- A headline of the challenge `P` whose theorem `P.t` met the comparison's conditions, with
`challenge` and `solution` as its modules. -/
def comparedHeadline (challenge solution : Name) : Stats.Headline :=
  { name := "P", challengeModule := challenge, solutionModule := solution
    theorems := #[{ name := `P.t, statement := "theorem t : True", solution := .same
                    sorryFree := some true, conditionsMet := true, node := some `P.t }]
    definitions := #[{ name := `P.d, solution := .same }] }

-- Checked again just before the pages are written (`Headline.withSourcesChecked`): a source
-- edited after the comparison takes the verdict back, keeping the statement as the challenge
-- states it; as built, the headline is kept as it is.
/-- info: true -/
#guard_msgs in
#eval withImportingProject fun root => do
  let h := comparedHeadline `Demo.Basic.Missing `Demo.Hard
  let kept ← h.withSourcesChecked (← finderAt root)
  IO.FS.writeFile (root / "Demo" / "Basic.lean") (basicSource ++ "-- edited after the build\n")
  let checked ← h.withSourcesChecked (← finderAt root)
  let t := checked.theorems[0]!
  return kept == h && checked.unavailable == some .solutionOutOfDate &&
    checked.unavailableDetail == some "Demo.Basic in Demo/Basic.lean" && !t.conditionsMet &&
    t.solution == .notCompared && t.statement == "theorem t : True" &&
    checked.definitions.isEmpty

end Verso.VersoBlueprintTests.BlueprintCodeSite
