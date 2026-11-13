/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

import VersoBlueprintTests.Blueprint.Support
import VersoBlueprint.CodeSite.Main

/-!
The API entries of sites generated from compiled-code data: source highlighted from recorded
constant positions (`Informal.CodeSite.Highlight`), declaration cards with hovers, Markdown
docstrings and their link targets, module docstrings, the declarations' search entries,
neighbourhood and source links, build-time graph layout and the Comparator headline.
-/

namespace Verso.VersoBlueprintTests.BlueprintCodeSiteApi

open Lean
open Informal Informal.CodeSite
open SubVerso.Highlighting
open Verso.VersoBlueprintTests.Blueprint.Support

/-! ## The lexer -/

/-- The token classes of a line of Lean, in order (the CSS class the HTML gets, and the text). -/
def classes (text : String) : Array String :=
  (Highlight.lex text.toList.toArray ⟨0, 0⟩).filterMap fun lx =>
    if lx.plain then none else some s!"{lx.kind.cssClass}:{lx.text}"

/--
info: #["keyword:theorem", "unknown:foo", "punctuation bracket:(", "unknown:n", "built-in delim::", "unknown:Nat",
  "punctuation bracket:)", "built-in delim::", "unknown:n", "punctuation operator:+", "literal number:0",
  "punctuation operator:=", "unknown:n", "built-in delim::=", "keyword:by", "keyword:simp", "comment line:-- done"]
-/
#guard_msgs in
#eval classes "theorem foo (n : Nat) : n + 0 = n := by simp -- done"

-- Strings, characters, doc and nested block comments, sorts, dotted names, primes.
/--
info: #["doc-comment:/-- doc -/", "comment block:/- a /- nested -/ comment -/", "keyword:def", "unknown:x'",
  "built-in delim::", "sort:Type", "built-in delim::=", "literal string:\"a \\\"q\\\" b\"", "literal char:'c'",
  "unknown:Nat.succ_le.mp", "punctuation separator:,", "unknown:h.1"]
-/
#guard_msgs in
#eval classes
  "/-- doc -/ /- a /- nested -/ comment -/ def x' : Type := \"a \\\"q\\\" b\" 'c' Nat.succ_le.mp, h.1"

/-! ## Highlighting from recorded positions -/

def occ (line c1 c2 : Nat) (name : Name) (isDef := false) : Occurrence :=
  { range := { start := ⟨line, c1⟩, «end» := ⟨line, c2⟩ }, name, isDef }

def hovers : Lean.NameMap Hover :=
  ({} : Lean.NameMap Hover)
    |>.insert `Nat { name := `Nat, signature := "Nat : Type", doc := some "The naturals." }
    |>.insert `Nat.succ { name := `Nat.succ, signature := "Nat.succ (n : Nat) : Nat" }

def consts (h : Highlighted) : Array (Name × String × Bool × String) :=
  match h with
  | .seq parts => parts.filterMap fun
    | .token ⟨.const n sig _ isDef _, text⟩ => some (n, sig, isDef, text)
    | _ => none
  | _ => #[]

-- An identifier at a recorded occurrence is that constant, with its hover (one without a hover
-- stays plain); positions count from the excerpt's first line in the file.
/--
info: #[(`Nat, "Nat : Type", false, "Nat"), (`Nat.succ, "Nat.succ (n : Nat) : Nat", false, "Nat.succ")]
-/
#guard_msgs in
#eval consts <| Highlight.highlight "def demo : Nat :=\n  Nat.succ 0" ⟨10, 0⟩
  #[occ 10 4 8 `demo (isDef := true), occ 10 11 14 `Nat, occ 11 2 10 `Nat.succ] hovers

-- An occurrence on part of a dotted identifier (a field projection) splits it there.
/-- info: #[(`Nat.succ, "Nat.succ (n : Nat) : Nat", false, "succ")] -/
#guard_msgs in
#eval consts <| Highlight.highlight "h.succ" ⟨0, 0⟩ #[occ 0 2 6 `Nat.succ] hovers

-- Columns are UTF-16 code units, as in `.ilean` files.
/-- info: #[(`Nat, "Nat : Type", false, "Nat")] -/
#guard_msgs in
#eval consts <| Highlight.highlight "x𝔸y Nat" ⟨0, 0⟩ #[occ 0 5 8 `Nat] hovers

/-! ## Docstrings and module docstrings -/

/-- info: true -/
#guard_msgs in
#eval
  let html := docHtml "Uses `Nat` and [docs](https://example.org); <b>raw</b> [bad](javascript:alert(1))"
  hasSubstr html "<code>Nat</code>" && hasSubstr html "href=\"https://example.org\"" &&
    !hasSubstr html "javascript:" && !hasSubstr html "<b>"

/-- info: #[true, true, true, true, false, false, false] -/
#guard_msgs in
#eval #["https://a.b/c", "mailto:x@y", "../Chapter/#x", "#frag", "javascript:x", " JavaScript:x",
  "data:text/html,x"].map safeHref

/-- info: #["# Title\n\nSome *text*.\n  indented", "Second."] -/
#guard_msgs in
#eval moduleDocs "/-!\n  # Title\n\n  Some *text*.\n    indented\n-/\n\n/-- not a module doc -/\ndef x := 1\n/-! Second. -/\n"

/-- info: true -/
#guard_msgs in
#eval
  match moduleDocBlocks "# Title\n\nSome *text* with [a link](javascript:x)." with
  | #[.para #[.bold _], .para inls] => !inls.any (· matches .link ..)
  | _ => false

/-! ## The declaration card -/

def fixtureJson : String := "{\"format\":\"verso-blueprint-code-1\",
  \"modules\":[
    {\"module\":\"Demo.Basic\",\"source\":\"Demo/Basic.lean\",\"declarations\":[
      {\"name\":\"Demo.double\",\"kind\":\"def\",\"signature\":\"def Demo.double (n : Nat) : Nat\",
       \"doc\":\"Twice `n`, see [the docs](https://example.org).\",\"status\":\"proved\",
       \"range\":{\"start\":{\"line\":3,\"character\":0},\"end\":{\"line\":4,\"character\":7}},
       \"occurrences\":[
         {\"range\":{\"start\":{\"line\":3,\"character\":4},\"end\":{\"line\":3,\"character\":10}},
          \"name\":\"Demo.double\",\"isDef\":true},
         {\"range\":{\"start\":{\"line\":3,\"character\":16},\"end\":{\"line\":3,\"character\":19}},
          \"name\":\"Nat\"}]}]}],
  \"hovers\":[{\"name\":\"Nat\",\"signature\":\"Nat : Type\",\"doc\":\"The natural numbers.\"}]}"

def fixture : Project :=
  match Project.parse fixtureJson with
  | .ok p => p
  | .error e => panic! e

def basicSource : String :=
  "/-! # Basic\n\nDoubling. -/\ndef double (n : Nat) : Nat :=\n  n + n\n"

def card (ctx : RenderContext) : Option ExternalDeclRenderedHtml := do
  let state := stateOf fixture (fun _ => some basicSource) ctx
  let ref ← (state.data.find? `Demo.double).bind (·.externalRefs[0]?)
  match ref.render with
  | .ok r => some r
  | .error _ => none

-- The source is highlighted: keywords, the constants with hovers; the docstring is Markdown;
-- the card links to the declaration's neighbourhood and, for a GitHub checkout, to its source.
/-- info: true -/
#guard_msgs in
#eval
  let ctx : RenderContext := {
    hovers := fixture.hovers.foldl (init := {}) fun m h => m.insert h.name h
    sourceBase? := some "https://github.com/o/r/blob/abc/" }
  match card ctx with
  | some r =>
    hasSubstr r.html "keyword token" && hasSubstr r.html "const token" &&
      r.hoverPayloads.any (hasSubstr ·.html "The natural numbers.") &&
      hasSubstr r.html "<code>n</code>" && hasSubstr r.html "href=\"https://example.org\"" &&
      hasSubstr r.html "href=\"../Dependency-Graph/#ego=Demo.double\"" &&
      hasSubstr r.html "href=\"https://github.com/o/r/blob/abc/Demo/Basic.lean#L4-L5\""
  | none => false

-- Without a web address the source is named, not linked; without a graph page no neighbourhood.
/-- info: true -/
#guard_msgs in
#eval
  match card { graphPage? := none } with
  | some r => hasSubstr r.html "Demo/Basic.lean:4" && !hasSubstr r.html "github.com" &&
      !hasSubstr r.html "#ego="
  | none => false

/-! ## The module page and the search entries -/

def isSearchBlock (name : Name) : Verso.Doc.Block Verso.Genre.Manual → Bool
  | .other b contents => b.name == ``Informal.CodeSite.Block.declSearch &&
      b.data == toJson name && !contents.isEmpty
  | _ => false

-- A module page starts with its module docstrings; each declaration has its search entries.
/-- info: true -/
#guard_msgs in
#eval
  let part := moduleChapter fixture.modules[0]! (some basicSource)
  part.content.any (· matches .para #[.bold _]) &&
    part.content.any (isSearchBlock `Demo.double)

/-- A scratch project root with the module source and the data. -/
def withProject (k : System.FilePath → IO Bool) : IO Bool := do
  let root := System.FilePath.mk s!"/tmp/vbp-code-site-api-test-{← IO.monoNanosNow}"
  IO.FS.createDirAll (root / "Demo")
  IO.FS.writeFile (root / "Demo" / "Basic.lean") basicSource
  IO.FS.writeFile (root / "code.json") fixtureJson
  try k root finally IO.FS.removeDirAll root

-- A generated site: the declaration is in the quick search's documentation domain and its
-- docstring in the full-text index; the module docstring is on its page.
/-- info: true -/
#guard_msgs in
#eval withProject fun root => do
  let code ← generate (root / "code.json") root none
    ["--output", (root / "_out").toString, "--reproducible"] (graphviz := none)
  let html := root / "_out" / "html-multi"
  let xref ← IO.FS.readFile (html / "xref.json")
  let chapter ← IO.FS.readFile (html / "Demo___Basic" / "index.html")
  let mut indexed := false
  for f in ← (html / "-verso-search").readDir do
    if f.fileName.startsWith "searchIndex_" then
      if hasSubstr (← IO.FS.readFile f.path) "Twice" then indexed := true
  let some domain := (Json.parse xref).toOption.bind
      (·.getObjVal? "Verso.Genre.Manual.doc" |>.toOption) | return false
  return code == 0 && hasSubstr domain.compress "Demo.double" && indexed &&
    hasSubstr chapter "Doubling." && hasSubstr chapter "bp_code_site_anchor"

/-! ## Graph layout at build time -/

/-- info: (2, false) -/
#guard_msgs in
#eval do
  let dot := "digraph {\n  \"a\" [id=\"bp-node-a\", label=\"a\"];\n  \"b\" [id=\"bp-node-b\"];\n}"
  return (GraphLayout.nodeCount dot, ← GraphLayout.available "/nonexistent/dot")

-- A missing program gives the page's layout (an error, no layout).
/-- info: true -/
#guard_msgs in
#eval do
  return (← GraphLayout.layoutDot { program := "/nonexistent/dot" } "digraph {}") matches .error _

-- With Graphviz present, a laid-out source carries positions and draws as SVG.
/-- info: true -/
#guard_msgs in
#eval do
  if !(← GraphLayout.available "dot") then return true
  let dot := "digraph {\n  \"a\" [id=\"bp-node-a\"];\n  \"b\" [id=\"bp-node-b\"];\n  \"a\" -> \"b\";\n}"
  match ← GraphLayout.layoutDot {} dot with
  | .ok laid =>
    match ← GraphLayout.prerender {} laid with
    | .ok svg => return hasSubstr laid "pos=" && svg.startsWith "<svg" && hasSubstr svg "class=\"node\""
    | .error _ => return false
  | .error _ => return false

-- A generated site with layout: one raw-text layout per view and the first view drawn.
/-- info: true -/
#guard_msgs in
#eval withProject fun root => do
  if !(← GraphLayout.available "dot") then return true
  let code ← generate (root / "code.json") root none
    ["--output", (root / "_out").toString, "--reproducible"]
  let page ← IO.FS.readFile (root / "_out" / "html-multi" / "Dependency-Graph" / "index.html")
  return code == 0 && hasSubstr page "class=\"bp-graph-layout\" data-variant=\"full\"" &&
    hasSubstr page "<svg class=\"bp_graph_prerendered\" data-variant=\"full\""

/-! ## The Comparator headline -/

-- No challenge, no headline.
/-- info: true -/
#guard_msgs in
#eval withProject fun root => do
  return (← headlineOf? root fixture {}).isNone

/-- The fork's root, three directories above this test file. -/
def packageRoot : IO System.FilePath := do
  let file : System.FilePath := "tests/VersoBlueprintTests/BlueprintCodeSiteApi.lean"
  return (← IO.currentDir) / (file.parent.bind (·.parent) |>.bind (·.parent) |>.getD ".")

/-- A project whose challenge is the `Match` fixture (compiled with this package's tests): the
challenge and solution sources, `comparator.json`, and the compiled modules beside them. -/
def withChallenge (k : System.FilePath → Project → IO Bool) : IO Bool := do
  let pkg ← packageRoot
  let root := System.FilePath.mk s!"/tmp/vbp-code-site-cmp-test-{← IO.monoNanosNow}"
  let dir := root / "tests" / "VersoBlueprintTests" / "ComparatorFixtures" / "Match"
  IO.FS.createDirAll dir
  for f in ["Challenge.lean", "Solution.lean"] do
    IO.FS.writeFile (dir / f) (← IO.FS.readFile
      (pkg / "tests" / "VersoBlueprintTests" / "ComparatorFixtures" / "Match" / f))
  IO.FS.createDirAll (root / ".lake" / "build" / "lib")
  let _ ← IO.Process.output { cmd := "ln", args := #["-s",
    (pkg / ".lake" / "build" / "lib" / "lean").toString,
    (root / ".lake" / "build" / "lib" / "lean").toString] }
  IO.FS.writeFile (root / "comparator.json") (Json.compress <| json% {
    "challenge_module": "VersoBlueprintTests.ComparatorFixtures.Match.Challenge",
    "solution_module": "VersoBlueprintTests.ComparatorFixtures.Match.Solution",
    "theorem_names": ["CmpMatch.double_eq"], "permitted_axioms": ["propext"] })
  let project : Project := { modules := #[{
    module := `VersoBlueprintTests.ComparatorFixtures.Match.Solution
    source := "tests/VersoBlueprintTests/ComparatorFixtures/Match/Solution.lean"
    declarations := #[{ name := `CmpMatch.double_eq, kind := "theorem" }] }] }
  try k root project finally IO.FS.removeDirAll root

-- With a challenge, the headline compares it as a Blueprint site does; the theorem's node is
-- its declaration.
/-- info: true -/
#guard_msgs in
#eval withChallenge fun root project => do
  match ← headlineOf? root project ((({} : NameSet).insert `CmpMatch.double_eq)) with
  | some h => return h.unavailable.isNone && h.theorems.any fun t =>
      t.name == `CmpMatch.double_eq && t.solution == .same && t.node == some `CmpMatch.double_eq
  | none => return false

-- A challenge that is not built is reported as such.
/-- info: true -/
#guard_msgs in
#eval withChallenge fun root project => do
  IO.FS.removeFile (root / ".lake" / "build" / "lib" / "lean")
  match ← headlineOf? root project {} with
  | some h => return h.unavailable == some .challengeNotBuilt
  | none => return false

end Verso.VersoBlueprintTests.BlueprintCodeSiteApi
