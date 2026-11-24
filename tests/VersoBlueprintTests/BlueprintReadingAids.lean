/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

import VersoBlueprint
import VersoBlueprint.PreviewManifest
import VersoBlueprintTests.Blueprint.Support

/-!
What helps a reader find their way in a site: parts and the numbers of chapters, sections and
statements (`Informal.Parts`, `Informal.PageText`), the check of the site's navigation
(`Informal.LinkCheck`), the labels of the dependency graph's nodes (`Informal.GraphLayout`) and
links to the repository's files (`Informal.RepoFile`).
-/

namespace Verso.VersoBlueprintTests.BlueprintReadingAids

open Lean
open Verso Genre Manual
open Informal
open Verso.VersoBlueprintTests.Blueprint.Support

set_option doc.verso true

-- Roman numerals of parts

/-- info: true -/
#guard_msgs in
#eval
  Parts.romanNumeral 1 == "I" && Parts.romanNumeral 2 == "II" && Parts.romanNumeral 4 == "IV" &&
    Parts.romanNumeral 9 == "IX" && Parts.romanNumeral 14 == "XIV" && Parts.romanNumeral 40 == "XL" &&
    Parts.romanNumeral 1994 == "MCMXCIV" && Parts.romanNumeral 0 == ""

-- Numbering the parts of a document

private def page (title : String) (content : Array (Doc.Block Manual) := #[])
    (subParts : Array (Doc.Part Manual) := #[]) : Doc.Part Manual :=
  .mk #[.text title] title none content subParts

private def marker : Doc.Block Manual := .other (Parts.Block.part {}) #[]

/-- info: true -/
#guard_msgs in
#eval
  let doc := page "Book" #[] #[
    page "Intro",
    page "Foundations" #[marker] #[page "Groups", page "Orbits"],
    page "Main" #[marker] #[page "Result"],
    page "Appendix"]
  let numbered := Parts.numberParts doc
  let titles := numbered.subParts.map (·.titleString)
  let partOne := numbered.subParts[1]!
  titles == #["Intro", "Part I — Foundations", "Groups", "Orbits", "Part II — Main", "Result",
      "Appendix"] &&
    partOne.subParts.isEmpty &&
    (partOne.metadata.map (·.number)) == some false &&
    (partOne.metadata.bind (·.file)) == some "Part-I" &&
    -- the marker knows its numeral
    (partOne.content.any fun
      | .other b _ => b.data.compress == "{\"numeral\":\"I\"}"
      | _ => false) &&
    -- a document without parts is unchanged
    Parts.numberParts (page "Book" #[] #[page "A", page "B" #[] #[page "B.1"]]) ==
      page "Book" #[] #[page "A", page "B" #[] #[page "B.1"]]

-- A part that names its own file keeps it.
/-- info: true -/
#guard_msgs in
#eval
  let part : Doc.Part Manual := .mk #[.text "Main"] "Main" (some { file := some "Main-Part" })
    #[marker] #[page "Result"]
  let numbered := Parts.numberParts (page "Book" #[] #[part])
  (numbered.subParts[0]!.metadata.bind (·.file)) == some "Main-Part"

-- Section numbers below chapters, with a section sign

/-- info: true -/
#guard_msgs in
#eval
  PageText.sectionSigns "<span class=\"number\">4.1.</span> Nested" ==
      "<span class=\"number\">§4.1</span> Nested" &&
    PageText.sectionSigns "<span class=\"number\">4.</span> Chapter" ==
      "<span class=\"number\">4.</span> Chapter" &&
    PageText.sectionSigns "<td class=\"num\">10.2.3.</td>" == "<td class=\"num\">§10.2.3</td>" &&
    PageText.sectionSigns "<td class=\"num\">A.1.</td>" == "<td class=\"num\">§A.1</td>" &&
    PageText.sectionSigns "<h1 id=\"x-y\">4.1. Nested<span>" == "<h1 id=\"x-y\">§4.1 Nested<span>" &&
    PageText.sectionSigns "<h2 id=\"x\">4. Chapter" == "<h2 id=\"x\">4. Chapter" &&
    PageText.sectionSigns "<h2 class=\"c\" id=\"x\">4.1. Not Verso's" ==
      "<h2 class=\"c\" id=\"x\">4.1. Not Verso's" &&
    PageText.sectionSigns "<span class=\"where\">4.1. Nested</span>" ==
      "<span class=\"where\">§4.1 Nested</span>" &&
    PageText.sectionSigns "rel=\"next\" title=\"4.1. Nested\"" == "rel=\"next\" title=\"§4.1 Nested\"" &&
    PageText.sectionSigns "\"sectionNum\":\"4.1.\"" == "\"sectionNum\":\"§4.1\"" &&
    PageText.sectionSigns "\"sectionNum\":\"4.\"" == "\"sectionNum\":\"4.\"" &&
    -- a statement's number is not a section's
    PageText.sectionSigns "<span class=\"bp_label\">4.1.1</span>" ==
      "<span class=\"bp_label\">4.1.1</span>" &&
    -- a title that starts with initials is a title
    PageText.sectionSigns "<h1 id=\"x\">U.S. Patent law" == "<h1 id=\"x\">U.S. Patent law" &&
    PageText.sectionSigns "<h2 id=\"x\">A.B. Smith's lemma" == "<h2 id=\"x\">A.B. Smith's lemma" &&
    PageText.sectionSigns "<h2 id=\"x\">A.2. Appendix" == "<h2 id=\"x\">§A.2 Appendix"

-- Only the pages the build wrote are changed: a page left by an earlier build, or a file a
-- person put into the folder, keeps its text.
/-- info: true -/
#guard_msgs in
#eval show IO Bool from do
  let dir ← IO.FS.createTempDir
  let old := "<h1 id=\"x\">4.1. Kept</h1>"
  IO.FS.writeFile (dir / "kept.html") old
  IO.sleep 20
  let marker := dir / ".started"
  IO.FS.writeFile marker ""
  let since := (← marker.metadata).modified
  IO.FS.writeFile (dir / "new.html") "<h1 id=\"x\">4.1. Written</h1>"
  let changed ← PageText.finishSite dir since
  let kept ← IO.FS.readFile (dir / "kept.html")
  let written ← IO.FS.readFile (dir / "new.html")
  IO.FS.removeDirAll dir
  return changed == 1 && kept == old && written == "<h1 id=\"x\">§4.1 Written</h1>"

-- A link to a repository file: its path percent-encoded, slashes kept; only a file the
-- repository tracks has an address at the commit.
/-- info: (true, true, false) -/
#guard_msgs in
#eval show IO _ from do
  let dir ← IO.FS.createTempDir
  let git (args : Array String) := IO.Process.output { cmd := "git", args, cwd := dir }
  let _ ← git #["init", "--quiet"]
  IO.FS.writeFile (dir / "kept.md") "x"
  IO.FS.writeFile (dir / "loose.md") "y"
  let _ ← git #["add", "kept.md"]
  let tracked ← Informal.RepoFile.tracked dir "kept.md"
  let untracked ← Informal.RepoFile.tracked dir "loose.md"
  IO.FS.removeDirAll dir
  return (LeanSourceAnchor.percentEncode "notes/my file#1.md" == "notes/my%20file%231.md",
    tracked, untracked)

-- The viewport lets the reader zoom

/-- info: true -/
#guard_msgs in
#eval
  let page := s!"<meta name=\"viewport\" {PageText.versoViewport}/>"
  let out := PageText.allowZoom page
  hasSubstr out "width=device-width, initial-scale=1" && !hasSubstr out "maximum-scale" &&
    !hasSubstr out "minimum-scale"

-- Links of the navigation

/-- info: true -/
#guard_msgs in
#eval
  LinkCheck.resolve ["Stats"] (some "./../") "#what" == some ([], "what") &&
    LinkCheck.resolve ["Stats"] (some "./../") "Stats/#what" == some (["Stats"], "what") &&
    LinkCheck.resolve ["A", "B"] none "../C/#x%20y" == some (["A", "C"], "x y") &&
    LinkCheck.resolve [] none "https://example.org/#x" == none &&
    LinkCheck.resolve [] none "lean:decl/X#y" == none &&
    LinkCheck.resolve [] none "Stats/" == none &&
    LinkCheck.resolve [] none "Dependency-Graph/#ego=Demo.a" == none &&
    LinkCheck.navigationLinks
      "<nav id=\"toc\"><a href=\"A/#a\">A</a></nav><p><a href=\"B/#b\">B</a> \
        <a class=\"bp_meaning_link\" href=\"C/#c\">C</a></p>" == #["A/#a", "C/#c"]

private partial def freshRoot (name : String) : IO System.FilePath := do
  let root := (← IO.currentDir) / ".lake" / "build" / "tmp" / name / toString (← IO.rand 0 1000000000000)
  if ← root.pathExists then freshRoot name else pure root

-- A site whose navigation names a place that a page does not have is reported; one that names
-- places that exist is not.
/-- info: true -/
#guard_msgs in
#eval
  show IO Bool from do
    let root ← freshRoot "verso-blueprint-link-check-test"
    IO.FS.createDirAll (root / "Stats")
    IO.FS.writeFile (root / "index.html")
      "<html><head><base href=\"./\"/></head><body><nav><a href=\"Stats/#here\">S</a></nav></body></html>"
    IO.FS.writeFile (root / "Stats" / "index.html")
      "<html><head><base href=\"./../\"/></head><body><section id=\"here\"></section>\
        <a class=\"bp_meaning_link\" href=\"#here\">self</a></body></html>"
    let dead ← LinkCheck.checkSite root
    pure (dead.map (·.href) == #["#here"] && dead.map (·.page) == #["Stats/index.html"])

-- The labels of the dependency graph's nodes

private def graphNode (label : Name) (caption? : Option String := none) : Graph.GraphNode String :=
  { label, caption?, deps := #[], fillcolor := "#ffffff" }

/-- info: true -/
#guard_msgs in
#eval
  let numbered := graphNode `critical_radius_five (some "Theorem 6.5")
  let plain := graphNode `Some.Namespace.helper
  let web := GraphLayout.webNode numbered
  GraphLayout.labelLines numbered == #["Theorem 6.5"] &&
    GraphLayout.labelLines plain == #["Some.Namespace.helper"] &&
    web.name == "critical_radius_five" &&
    GraphLayout.accessibleName web == "Theorem 6.5 (critical_radius_five)" &&
    GraphLayout.accessibleName (GraphLayout.webNode plain) == "Some.Namespace.helper" &&
    Graph.numberedCaption? "Theorem 6.5" == some "Theorem 6.5" &&
    Graph.numberedCaption? "Lemma A.2" == some "Lemma A.2" &&
    Graph.numberedCaption? "Theorem 12" == some "Theorem 12" &&
    Graph.numberedCaption? "Definition Demo.a" == none &&
    Graph.numberedCaption? "Theorem Project.T2" == none &&
    Graph.numberedCaption? "critical_radius_five" == none

-- A drawing names its nodes for a reader of the page.
/-- info: true -/
#guard_msgs in
#eval
  let view : GraphLayout.View := { graph := #[graphNode `a (some "Lemma 1.1"), { graphNode `b with deps := #[`a] }] }
  let drawing := GraphLayout.drawing "full" view .TB false
  hasSubstr drawing.svg "class=\"node\" role=\"img\" aria-label=\"Lemma 1.1 (a)\">" &&
    hasSubstr drawing.svg "aria-label=\"b\"" &&
    hasSubstr drawing.svg ">Lemma 1.1</text>" &&
    hasSubstr drawing.svg "<title>a</title>"

-- A node's accessible name says its state after its name (its tooltip), and keeps no character
-- XML cannot carry, so the drawing stays a well-formed document.
/-- info: true -/
#guard_msgs in
#eval
  let node := { graphNode `a (some "Lemma 1.1") with
    tooltip? := some s!"Lean proof complete{Char.ofNat 1}: no \"sorry\" & <more>{Char.ofNat 0xFFFE}" }
  let drawing := GraphLayout.drawing "full" { graph := #[node] } .TB false
  GraphLayout.accessibleName (GraphLayout.webNode node) ==
      "Lemma 1.1 (a): Lean proof complete: no \"sorry\" & <more>" &&
    hasSubstr drawing.svg
      "aria-label=\"Lemma 1.1 (a): Lean proof complete: no &quot;sorry&quot; &amp; &lt;more&gt;\"" &&
    !drawing.svg.any (fun c => c.val < 0x20 && c != '\n' && c != '\t' && c != '\r')

-- Links to the repository's files

/-- info: true -/
#guard_msgs in
#eval
  RepoFile.splitFragment "notes/engine.md" == ("notes/engine.md", "") &&
    RepoFile.splitFragment "Main.lean#L10-L20" == ("Main.lean", "#L10-L20") &&
    RepoFile.pathProblem? "notes/engine.md" == none &&
    (RepoFile.pathProblem? "/etc/x").isSome && (RepoFile.pathProblem? "../x").isSome &&
    (RepoFile.pathProblem? "").isSome

-- A site with parts: chapters numbered across parts, statements numbered in their chapters,
-- sections with a section sign, pages that let the reader zoom, and navigation that finds every
-- place it names (the build fails otherwise).

#docs (Manual) partsDoc "Parts Site" :=
:::::::
# Introduction

:::definition "parts.base"
A base definition.
:::

# Foundations

{blueprint_part}

The chapters of the first part.

## Groups

:::theorem "parts.groups" (uses := "parts.base")
A theorem about groups.
:::

### Orbits

:::lemma_ "parts.orbits"
A lemma in a section.
:::

# Main Result

{blueprint_part}

## Result

:::theorem "parts.result" (uses := "parts.groups")
The result.
:::
:::::::

/-- info: true -/
#guard_msgs in
#eval
  show IO Bool from do
    let root ← freshRoot "verso-blueprint-parts-test"
    let code ← Informal.PreviewManifest.blueprintMain partsDoc.toPart
      (extensionImpls := by exact extension_impls%)
      (options := ["--output", root.toString, "--without-html-single"])
    let site := root / "html-multi"
    let index ← IO.FS.readFile (site / "index.html")
    let groups ← IO.FS.readFile (site / "Groups" / "index.html")
    let orbits ← IO.FS.readFile (site / "Groups" / "Orbits" / "index.html")
    let result ← IO.FS.readFile (site / "Result" / "index.html")
    let partPage ← IO.FS.readFile (site / "Part-I" / "index.html")
    pure (code == 0 &&
      -- chapters run on across parts; the parts' pages are unnumbered
      hasSubstr index "<span class=\"number\">1.</span> Introduction" &&
      hasSubstr index "Part I — Foundations" && hasSubstr index "Part II — Main Result" &&
      hasSubstr index "<span class=\"number\">2.</span> Groups" &&
      hasSubstr index "<span class=\"number\">3.</span> Result" &&
      appearsBefore index "Part I — Foundations" "<span class=\"number\">2.</span> Groups" &&
      -- statements keep the numbers of their chapters; a section carries a section sign
      hasSubstr groups ">2.1</span>" && hasSubstr orbits ">2.1.1</span>" &&
      hasSubstr orbits "\">§2.1\u00A0Orbits" && !hasSubstr orbits "2.1. Orbits" &&
      hasSubstr groups "<span class=\"number\">§2.1</span> Orbits" &&
      hasSubstr result ">3.1</span>" &&
      hasSubstr partPage "The chapters of the first part." &&
      -- the viewport lets the reader zoom
      !hasSubstr index "maximum-scale" && hasSubstr index "width=device-width, initial-scale=1")

end Verso.VersoBlueprintTests.BlueprintReadingAids
