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

-- A formula LeAnTeX accepts becomes an inline SVG picture: glyphs as paths, no script, the
-- source as its title, sized in `em` and on the baseline.
/-- info: true -/
#guard_msgs in
#eval
  show IO Bool from do
    let some svg ← StaticMath.render? false r#"x^2 + \frac{a}{b} < c"# "" "t1-"
      | return false
    pure (
      hasSubstr svg "<svg" && hasSubstr svg "role=\"img\"" &&
      hasSubstr svg "<title>x^2 + \\frac{a}{b} &lt; c</title>" &&
      hasSubstr svg "<path id=\"t1-" && hasSubstr svg "xlink:href=\"#t1-" &&
      hasSubstr svg "vertical-align:-" && hasSubstr svg "em\"" &&
      hasSubstr svg "fill=\"currentColor\"" &&
      !hasSubstr svg "<script" && !hasSubstr svg "<text" && !hasSubstr svg "font-family"
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
