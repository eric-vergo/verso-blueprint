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
