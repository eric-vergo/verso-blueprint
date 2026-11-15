/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude (Anthropic)
-/

import VersoBlueprintTests.Blueprint.Support
import VersoBlueprint.StaticMath

namespace Verso.VersoBlueprintTests.BlueprintStaticMath

open Lean
open Verso
open Verso.Genre.Manual
open Informal
open Verso.VersoBlueprintTests.Blueprint.Support

set_option doc.verso true

private def manualImpls : ExtensionImpls := extension_impls%

-- A formula LeAnTeX accepts becomes inline SVG: glyphs as paths, no script, the source as its
-- title, sized in `em` and on the baseline, hidden from screen readers, which read its MathML;
-- its TeX source is there for copying.
/-- info: true -/
#guard_msgs in
#eval
  show IO Bool from do
    let some svg ← StaticMath.render? false r#"x^2 + \frac{a}{b} < c"# "" "t1-"
      | return false
    pure (
      hasSubstr svg "<svg" && hasSubstr svg "aria-hidden=\"true\"" &&
      hasSubstr svg "<title>x^2 + \\frac{a}{b} &lt; c</title>" &&
      hasSubstr svg "<path id=\"bpg-" && hasSubstr svg "xlink:href=\"#bpg-" &&
      hasSubstr svg "vertical-align:-" && hasSubstr svg "em\"" &&
      hasSubstr svg "fill=\"currentColor\"" &&
      hasSubstr svg "<math class=\"bp_math_mathml\"" && hasSubstr svg "<mfrac>" &&
      hasSubstr svg "<annotation encoding=\"application/x-tex\">" &&
      hasSubstr svg "<span class=\"bp_math_source\" aria-hidden=\"true\">$x^2" &&
      !hasSubstr svg "<script" && !hasSubstr svg "<text" && !hasSubstr svg "font-family"
    )

/-- The value in em of an attribute or style property of a picture. -/
def emValue (svg name : String) : Option Float := do
  let after ← ((svg.splitOn (name ++ "=\"")).drop 1).head? <|>
    ((svg.splitOn (name ++ ":")).drop 1).head?
  let num := ((after.splitOn "em").headD "").trimAscii.toString
  let neg := num.startsWith "-"
  let num := if neg then (num.drop 1).toString else num
  let (whole, frac) := match num.splitOn "." with
    | [w, f] => (w, f)
    | [w] => (w, "")
    | _ => ("", "")
  let w ← whole.toNat?
  let f := frac.toNat?.getD 0
  let v := w.toFloat + f.toFloat / (10 : Float) ^ frac.length.toFloat
  return if neg then -v else v

/-- Whether two lengths in em agree to a thousandth. -/
def near (a b : Float) : Bool := (a - b).abs < 0.001

-- The picture's size and baseline are KaTeX's for the formula, with 0.05 em of padding on every
-- side: `x` (KaTeX's metrics: 0.57153 wide, 0.43056 high, no depth) and `y` (0.49028 wide with
-- its italic correction of 0.03588 after it, 0.19444 deep).
/-- info: true -/
#guard_msgs in
#eval
  show IO Bool from do
    let some x ← StaticMath.render? false "x" "" "t5-" | return false
    let some y ← StaticMath.render? false "y" "" "t6-" | return false
    let ok := fun (svg : String) (w h d : Float) =>
      (emValue svg "width").any (near · (w + 0.1)) &&
      (emValue svg "height").any (near · (h + d + 0.1)) &&
      (emValue svg "vertical-align").any (near · (-(d + 0.05)))
    pure (ok x 0.57153 0.43056 0 && ok y (0.49028 + 0.03588) 0.43056 0.19444)

-- An inline formula is cut where KaTeX lets a line break, after its relations and binary
-- operators: `a+b=c` is three pictures with break opportunities between them, which together
-- are as wide as the formula; a display formula stays one picture.
/-- info: true -/
#guard_msgs in
#eval
  show IO Bool from do
    let some i ← StaticMath.render? false "a+b=c" "" "t7-" | return false
    let some d ← StaticMath.render? true "a+b=c" "" "t8-" | return false
    let some dl ← StaticMath.layout? false "a+b=c" "" | return false
    let pics := (i.splitOn "<svg").length - 1
    let widths := ((i.splitOn "<svg").drop 1).filterMap fun p => emValue p "width"
    let total := widths.foldl (· + ·) 0 - 0.1 * widths.length.toFloat
    pure (pics == 3 && (i.splitOn "<wbr>").length == 3 && (d.splitOn "<svg").length == 2 &&
      near total (dl.width.raw.toNat.toFloat / 655360))

-- Each page carries its glyph outlines once: the definitions of all its pictures move into one
-- hidden set at the end of the page, each id once and every glyph used defined; KaTeX's files
-- leave a page with no formula for the browser, unless the site's data needs them.
/-- info: true -/
#guard_msgs in
#eval
  show IO Bool from do
    let some a ← StaticMath.render? false "x+y" "" "t9-" | return false
    let some b ← StaticMath.render? false "y+x" "" "t10-" | return false
    let head := String.join StaticMath.katexTags
    let page := s!"<html><head>{head}</head><body><p>{a} and {b}</p></body></html>"
    let (out, st) := StaticMath.finishPage page false
    let ids := ((out.splitOn " id=\"").drop 1).map fun s => (s.splitOn "\"").headD ""
    let refs := ((out.splitOn "xlink:href=\"#").drop 1).map fun s => (s.splitOn "\"").headD ""
    let (kept, _) := StaticMath.finishPage page true
    let withCode := page.replace "</p>" "<code class=\"bp_math inline\">z</code></p>"
    let (codePage, _) := StaticMath.finishPage withCode false
    pure (
      !hasSubstr out "data-bp-glyphs" && countSubstr out "<defs>" == 1 &&
      hasSubstr out "class=\"bp_math_glyphs\"" &&
      ids.length == ids.eraseDups.length && refs.all ids.contains &&
      st.dropped > 0 && st.clashes == 0 && st.katexRemoved == 1 &&
      !hasSubstr out "katex/katex.js" &&
      hasSubstr kept "katex/katex.js" && hasSubstr codePage "katex/katex.css"
    )

-- A site's data decides whether KaTeX stays on its pages: a formula left to the browser needs
-- it; a build-time formula with its copyable source, a reference to a stored formula, and text
-- that merely has dollar signs (a docstring, a comment in highlighted source) do not.
/-- info: true -/
#guard_msgs in
#eval
  let browser := r#"{"html":"<p>Hence <code class=\"bp_math inline\">q_k \\equiv 1</code>.</p>"}"#
  let static := r#"{"html":"<span class=\"bp_math inline bp_math_static\"><svg></svg><span class=\"bp_math_source\" aria-hidden=\"true\">$x$</span></span>"}"#
  let stored := r#"{"html":"<code class=\"bp_math_ref bp_math inline\" data-bp-math-key=\"bpm-1-2\">x</code>"}"#
  let text := r#"{"7":"<code class=\"docstring\">the interval $[a, b]$.</code><span class=\"comment\">-- $A$</span>"}"#
  StaticMath.textNeedsKaTeX browser && !StaticMath.textNeedsKaTeX static &&
    !StaticMath.textNeedsKaTeX stored && !StaticMath.textNeedsKaTeX text

/-- A node view's statement around the given formulas (already rendered), as a node view has
it. -/
def viewHtml (formulas : List String) : String :=
  "<article class=\"bp_node_view\"><div class=\"bp_sbs_informal\"><p>" ++
    " and ".intercalate formulas ++ "</p></div></article>"

/-- The element of a formula as a page has it, if the formula is accepted. -/
def staticSpan? (display : Bool) (source idPrefix : String) : IO (Option String) := do
  let some inner ← StaticMath.render? display source "" idPrefix | return none
  let mode := if display then "display" else "inline"
  return some s!"<span class=\"bp_math {mode} bp_math_static\" data-bp-math-rendered=\"1\">\
    {inner}</span>"

/-- The values of an attribute in a text. -/
def attrValues (html name : String) : List String :=
  ((html.splitOn (" " ++ name ++ "=\"")).drop 1).map fun s => (s.splitOn "\"").headD ""

-- The formulas of a node view go into the store, each once, and the view keeps a reference in
-- each one's place: a `code` element with the formula's key and its TeX source as text. A
-- formula left to the browser stays as it is, and so does everything else.
/-- info: true -/
#guard_msgs in
#eval
  show IO Bool from do
    let some x ← staticSpan? false "x<y" "s1-" | return false
    let some d ← staticSpan? true r#"\int_0^1 f"# "s2-" | return false
    let rejected := "<code class=\"bp_math inline\">\\frac{1}{</code>"
    let html := viewHtml [x, d, x, rejected]
    let (store, out) := StaticMath.storeFormulas {} html
    let keys := attrValues out "data-bp-math-key"
    let (store2, again) := StaticMath.storeFormulas store out
    pure (
      store.keys.size == 2 && keys.length == 3 && keys[0]? == keys[2]? && keys[0]? != keys[1]? &&
      keys.all store.byKey.contains &&
      hasSubstr out s!"<code class=\"bp_math_ref bp_math inline\" data-bp-math-key=\"\
        {keys.headD ""}\" data-bp-tex-prelude-id=\"default\">x&lt;y</code>" &&
      hasSubstr out "<code class=\"bp_math_ref bp_math display\"" &&
      hasSubstr out ">\\int_0^1 f</code>" && hasSubstr out rejected &&
      !hasSubstr out "bp_math_static" && !hasSubstr out "<svg" &&
      store.byKey[keys.headD ""]? == some x &&
      hasSubstr out "<article class=\"bp_node_view\"><div class=\"bp_sbs_informal\"><p>" &&
      -- nothing left to store the second time
      store2.keys.size == 2 && again == out &&
      -- a text without formulas is returned as it is
      (StaticMath.storeFormulas {} "<p>no math, $5</p>").2 == "<p>no math, $5</p>"
    )

-- Two different elements never share a key, also when their keys' hashes agree.
/-- info: true -/
#guard_msgs in
#eval
  let a := "<span class=\"bp_math inline bp_math_static\">a</span>"
  let b := "<span class=\"bp_math inline bp_math_static\">b</span>"
  let taken : Std.HashMap String String := Std.HashMap.ofList [(StaticMath.storeKey b, a)]
  let st : StaticMath.Store := { byKey := taken, keys := #[StaticMath.storeKey b] }
  let (st', key) := st.add b
  key != StaticMath.storeKey b && st'.byKey[key]? == some b && st'.keys.size == 2 &&
    (st'.add b).2 == key && (st'.add b).1.keys.size == 2

/-- A scratch site: a page with a dependency graph, a chapter page and the given node views
(label and HTML), in a folder removed afterwards. -/
def withSite (views : List (String × String)) (k : System.FilePath → IO Bool) : IO Bool := do
  let dir := System.FilePath.mk s!"/tmp/vbp-static-math-test-{← IO.monoNanosNow}"
  let head := "<head>" ++ String.join StaticMath.katexTags ++ "</head>"
  IO.FS.createDirAll (dir / "Graph")
  IO.FS.createDirAll (dir / "-verso-data")
  IO.FS.writeFile (dir / "Graph" / "index.html")
    s!"<html>{head}<body><div class=\"bp_graph_fullwidth\"></div></body></html>"
  IO.FS.writeFile (dir / "index.html") s!"<html>{head}<body><p>A chapter.</p></body></html>"
  let entries := views.map fun (label, html) =>
    Json.mkObj [("label", .str label), ("html", .str html)]
  IO.FS.writeFile (dir / "-verso-data" / StaticMath.nodeViewsFile)
    (Json.mkObj [("entries", .arr entries.toArray)]).compress
  try k dir finally IO.FS.removeDirAll dir

/-- The contents of the stored templates of a page. -/
def templates (page : String) : List String :=
  ((page.splitOn "<template class=\"bp_math_stored\" ").drop 1).map fun s =>
    (((s.splitOn "</template>").headD "").splitOn ">").drop 1 |> ">".intercalate

-- A site whose node views have accepted formulas only: the page with the graph carries each
-- formula once in an inert template (pictures, MathML and source, as a chapter page has them),
-- the views refer to them by key, the glyph outlines are in the page's one set, no id is there
-- twice, and no page loads KaTeX's files. The chapter page gets no templates.
/-- info: true -/
#guard_msgs in
#eval
  show IO Bool from do
    let some x ← staticSpan? false "x+y" "v1-" | return false
    let some x' ← staticSpan? false "x+y" "v2-" | return false
    let some d ← staticSpan? true r#"\sum_{k=1}^n k"# "v3-" | return false
    withSite [("a", viewHtml [x, d]), ("b", viewHtml [x'])] fun dir => do
      let st ← StaticMath.finishSite dir
      let graph ← IO.FS.readFile (dir / "Graph" / "index.html")
      let chapter ← IO.FS.readFile (dir / "index.html")
      let views ← IO.FS.readFile (dir / "-verso-data" / StaticMath.nodeViewsFile)
      let keys := attrValues graph "data-bp-math-key"
      let refs := (((views.replace "\\\"" "\"").splitOn " data-bp-math-key=\"").drop 1).map
        fun s => (s.splitOn "\"").headD ""
      let ids := attrValues graph "id"
      let uses := attrValues graph "xlink:href"
      let tpls := templates graph
      -- a second run finds nothing to do
      let st2 ← StaticMath.finishSite dir
      let graph2 ← IO.FS.readFile (dir / "Graph" / "index.html")
      pure (
        st.stored == keys.length && keys.length ≥ 2 && keys.eraseDups.length == keys.length &&
        refs.length == 3 && refs.all keys.contains && keys.all refs.contains &&
        tpls.length == keys.length &&
        tpls.all (fun t => hasSubstr t "<svg" && hasSubstr t "<math class=\"bp_math_mathml\"" &&
          hasSubstr t "class=\"bp_math_source\"" && hasSubstr t "data-bp-math-rendered=\"1\"") &&
        hasSubstr graph "<div class=\"bp_math_store\" hidden=\"\">" &&
        !hasSubstr graph "data-bp-glyphs" && countSubstr graph "class=\"bp_math_glyphs\"" == 1 &&
        ids.eraseDups.length == ids.length && !uses.isEmpty &&
        uses.all (fun u => u.startsWith "#" && ids.contains (u.drop 1).toString) &&
        !hasSubstr views "bp_math_static" && !hasSubstr views "<svg" &&
        !hasSubstr graph "katex/katex.js" && !hasSubstr chapter "katex/katex.css" &&
        !hasSubstr chapter "bp_math_store" && !hasSubstr chapter "<template" &&
        st.katexRemoved == 2 && st.clashes == 0 &&
        st2.stored == 0 && graph2 == graph
      )

-- A formula LeAnTeX rejects keeps the browser path for that formula only: it stays TeX in a
-- `code` element in the view, the accepted one beside it is stored, and the pages keep KaTeX's
-- files. Without any node view formula, pages get no templates.
/-- info: true -/
#guard_msgs in
#eval
  show IO Bool from do
    let some x ← staticSpan? false "x+y" "w1-" | return false
    let rejected := "<code class=\"bp_math inline\">\\frac{1}{</code>"
    let mixed ← withSite [("a", viewHtml [x, rejected])] fun dir => do
      let st ← StaticMath.finishSite dir
      let graph ← IO.FS.readFile (dir / "Graph" / "index.html")
      let chapter ← IO.FS.readFile (dir / "index.html")
      let views ← IO.FS.readFile (dir / "-verso-data" / StaticMath.nodeViewsFile)
      pure (
        st.stored == 1 && (templates graph).length == 1 && st.katexRemoved == 0 &&
        hasSubstr graph "katex/katex.js" && hasSubstr chapter "katex/katex.js" &&
        hasSubstr views "<code class=\\\"bp_math inline\\\">\\\\frac{1}{</code>" &&
        countSubstr views "bp_math_ref" == 1
      )
    let none ← withSite [("a", "<article class=\"bp_node_view\">Lean only</article>")] fun dir => do
      let st ← StaticMath.finishSite dir
      let graph ← IO.FS.readFile (dir / "Graph" / "index.html")
      pure (st.stored == 0 && !hasSubstr graph "<template" && st.katexRemoved == 2)
    pure (mixed && none)

/-- The tags of a markup text, each from its name to the end of its attributes (text between
tags has its angle brackets escaped, so every opening angle bracket opens a tag). -/
def tagTexts (html : String) : List String :=
  ((html.splitOn "<").drop 1).map fun s => (s.splitOn ">").headD ""

/-- Whether a tag has an attribute whose name starts with "on" (an event handler). -/
def hasHandlerAttr (tag : String) : Bool :=
  ((tag.splitOn " on").drop 1).any fun s =>
    let name := (s.takeWhile Char.isAlpha).toString
    !name.isEmpty && (s.drop name.length).startsWith "="

-- What a template holds is inert: pictures, MathML and text, with no script element, no event
-- handler attribute, no address but references to the page's own glyphs, and nothing a browser
-- loads. A source that looks like markup is text in the template and in the reference.
/-- info: true -/
#guard_msgs in
#eval
  show IO Bool from do
    let hostile := r#"\text{<img src=x onerror=alert(1)><script>alert(2)</script>} "# ++
      r#"\href{javascript:alert(3)}{x} < y"#
    let some h ← staticSpan? false hostile "h1-" | return false
    let some d ← staticSpan? true r#"\frac{a}{b} \ne \sqrt{c}"# "h2-" | return false
    withSite [("a", viewHtml [h, d])] fun dir => do
      let _ ← StaticMath.finishSite dir
      let graph ← IO.FS.readFile (dir / "Graph" / "index.html")
      let views ← IO.FS.readFile (dir / "-verso-data" / StaticMath.nodeViewsFile)
      let tpls := templates graph
      let allowed := ["span", "svg", "title", "use", "path", "rect", "g", "wbr", "math",
        "semantics", "annotation", "mrow", "mi", "mo", "mn", "mfrac", "msqrt", "mtext"]
      let tags := tpls.flatMap tagTexts
      let names := (tags.filter (!·.startsWith "/")).map fun t =>
        (t.takeWhile Char.isAlphanum).toString
      pure (
        tpls.length == 2 && !names.isEmpty && names.all allowed.contains &&
        tags.all (fun t => !hasHandlerAttr t && !hasSubstr t "javascript:" &&
          !hasSubstr t " src=" && !hasSubstr t "url(" && (attrValues t "href").isEmpty &&
          (attrValues t "xlink:href").all (·.startsWith "#bpg-") &&
          (attrValues t "id").isEmpty) &&
        hasSubstr graph "&lt;img src=x onerror=alert(1)&gt;" &&
        !hasSubstr graph "<img" && !hasSubstr graph "<script>alert" &&
        hasSubstr views "&lt;script&gt;alert(2)&lt;/script&gt;" &&
        !hasSubstr views "<script>" && !hasSubstr views "<img"
      )

-- The fonts come from LeAnTeX's package, found where the build's modules are, not from the
-- working directory; when they are missing, the warning names the folders looked in.
/-- info: true -/
#guard_msgs in
#eval
  show IO Bool from do
    let dirs ← StaticMath.fontDirs
    let some first := dirs[0]? | return false
    let w := StaticMath.missingFontsWarning #["/nowhere/a", "/nowhere/b"]
    pure (
      first.isAbsolute && (← (first / "NewCMMath-Book.otf").pathExists) &&
      hasSubstr w "/nowhere/a" && hasSubstr w "/nowhere/b" &&
      hasSubstr w "VERSO_BLUEPRINT_MATH_FONTS"
    )

-- A formula LeAnTeX rejects is left to the browser.
/-- info: true -/
#guard_msgs in
#eval
  show IO Bool from do
    let bad ← StaticMath.render? false r#"\frac{1}{"# "" "t2-"
    let undefined ← StaticMath.accepted false r#"\undefinedmacro"# ""
    pure (bad.isNone && !undefined)

-- The TeX prelude's macros apply, as in the browser.
/-- info: true -/
#guard_msgs in
#eval
  show IO Bool from do
    let without ← StaticMath.accepted false r#"\foo^n"# ""
    let withPrelude ← StaticMath.accepted false r#"\foo^n"# r#"\newcommand{\foo}{\mathsf{Foo}}"#
    pure (!without && withPrelude)

-- Display formulas are laid out in display style: a display sum is taller than an inline one.
/-- info: true -/
#guard_msgs in
#eval
  show IO Bool from do
    let some i ← StaticMath.layout? false r#"\sum_{k=1}^n k"# "" | return false
    let some d ← StaticMath.layout? true r#"\sum_{k=1}^n k"# "" | return false
    pure (d.height.raw + d.depth.raw > i.height.raw + i.depth.raw)

set_option verso.blueprint.math.lint false in
#docs (Genre.Manual) staticMathDoc "Static Math Doc" :=
:::::::
:::definition "static_math_def"
The norm $`\|x\|^2 = \sum_i x_i^2` is finite, and $`\frac{1}{` is not accepted.

$$`\int_0^1 f(x)\,dx`
:::
:::::::

set_option verso.blueprint.math.lint false in
#docs (Genre.Manual) allStaticMathDoc "All Static Math Doc" :=
:::::::
:::definition "all_static_math_def"
The norm $`\|x\|^2 = \sum_i x_i^2` is finite.
:::
:::::::

set_option verso.blueprint.math.static false in
#docs (Genre.Manual) browserMathDoc "Browser Math Doc" :=
:::::::
:::definition "browser_math_def"
The norm $`\|x\|^2`.
:::
:::::::

-- In a page, accepted formulas are inline SVG marked as rendered (so the browser script leaves
-- them alone), a rejected one stays a `code` element for KaTeX, and the page carries the style
-- rules and still the browser script for the rejected formula.
/-- info: true -/
#guard_msgs in
#eval
  show IO Bool from do
    let (html, st) ← renderManualDocHtmlStringAndState manualImpls staticMathDoc
    pure (
      countSubstr html "bp_math_static" == 2 &&
      hasSubstr html "class=\"bp_math inline bp_math_static\" data-bp-math-rendered=\"1\"" &&
      hasSubstr html "class=\"bp_math display bp_math_static\"" &&
      hasSubstr html "<code class=\"bp_math inline\">\\frac{1}{</code>" &&
      hasExtraCss st "bp_math_static" &&
      hasExtraJs st "katex.render"
    )

-- A page whose formulas are all typeset at build time still carries the prelude table and the
-- browser script: it can show other formulas later (previews, the graph's node views, code-site
-- statements), and those that take the browser path need them.
/-- info: true -/
#guard_msgs in
#eval
  show IO Bool from do
    let (html, st) ← renderManualDocHtmlStringAndState manualImpls allStaticMathDoc
    pure (
      countSubstr html "bp_math_static" == 1 && !hasSubstr html "<code class=\"bp_math" &&
      hasExtraJs st "katex.render" && hasExtraJs st "window.bpTexPreludeTable = Object.assign" &&
      hasExtraCss st "bp_math_static"
    )

-- With `verso.blueprint.math.static` off, formulas take the browser path.
/-- info: true -/
#guard_msgs in
#eval
  show IO Bool from do
    let (html, st) ← renderManualDocHtmlStringAndState manualImpls browserMathDoc
    pure (
      !hasSubstr html "bp_math_static" && !hasSubstr html "<svg" &&
      hasSubstr html "<code class=\"bp_math inline\">" &&
      hasExtraJs st "katex.render"
    )

end Verso.VersoBlueprintTests.BlueprintStaticMath
