/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude (Anthropic)
-/

import Lean
import LeAnTeX

/-!
# Math typeset when the site is built

Blueprint formulas are typeset by LeAnTeX's KaTeX-compatible layout while the site is generated
and written into the page as inline SVG: the glyphs are New Computer Modern's outlines, drawn in
the text colour, so a formula needs no script, no font file and no style sheet beyond a few
rules. A formula LeAnTeX does not accept keeps the browser path (KaTeX, as before), and the
option `verso.blueprint.math.static` (default `true`) sends every formula to it.

* The TeX prelude of the document is prepended to each formula, as the browser path does.
* The fonts are read once per process from LeAnTeX's copy in the project's package folder
  (`.lake/packages/leantex/fonts/newcomputermodern`, relative to the working directory of the
  build), or from the folder named by the environment variable `VERSO_BLUEPRINT_MATH_FONTS`.
  Without them every formula takes the browser path.
* Inline formulas sit on the baseline (`vertical-align` from the formula's depth); the picture
  is sized in `em` of its element, whose font size (`css`) is the size KaTeX's formulas have on
  the page: 1.21 em inside the 0.86 em of the `code` element they replace, and with the
  side-by-side style's text-sized formulas, 1.04 em of that. Display formulas are centred.
* The SVG has `role="img"` and the formula's source as its title.
-/

namespace Informal.StaticMath

open LeAnTeX.Backend

/-- The font files the formulas are drawn with: the math fonts and the text fonts the
KaTeX-compatible layout's faces map to. -/
def fontFiles : List String :=
  ["NewCMMath-Book.otf", "NewCMMath-Bold.otf", "NewCM10-Book.otf", "NewCM10-BookItalic.otf",
    "NewCM10-BoldItalic.otf"]

/-- Where the fonts are read from: `VERSO_BLUEPRINT_MATH_FONTS`, else LeAnTeX's copy in the
package folder of the project being built. -/
def fontDir : IO System.FilePath := do
  if let some d ← IO.getEnv "VERSO_BLUEPRINT_MATH_FONTS" then
    if !d.isEmpty then return d
  return System.FilePath.mk ".lake" / "packages" / "leantex" / "fonts" / "newcomputermodern"

/-- The fonts, read on first use: `some` when every file read, `none` otherwise. -/
initialize fontCache : IO.Ref (Option (Option FontSet)) ← IO.mkRef none

/-- The fonts, read once per process (see `fontCache`). -/
def fonts? : IO (Option FontSet) := do
  if let some r ← fontCache.get then return r
  let dir ← fontDir
  let r ← try
      let (fs, missing) ← FontSet.load dir fontFiles
      pure (if missing.isEmpty then some fs else none)
    catch _ => pure none
  fontCache.set (some r)
  return r

/-- The layouts made so far, by display mode, prelude and source: the display list, or `none`
for a formula LeAnTeX does not accept. -/
initialize layoutCache :
    IO.Ref (Std.HashMap (Bool × String × String) (Option LeAnTeX.DisplayList)) ← IO.mkRef {}

/-- The formula laid out by LeAnTeX, or `none` when it does not accept it (cached). -/
def layout? (display : Bool) (source texPrelude : String) : IO (Option LeAnTeX.DisplayList) := do
  let key := (display, texPrelude, source)
  if let some r := (← layoutCache.get)[key]? then return r
  let input := if texPrelude.trimAscii.isEmpty then source else texPrelude ++ "\n" ++ source
  let r := match (LeAnTeX.layout input { displayMode := display }).result with
    | .ok b => some (LeAnTeX.DisplayList.ofBox b)
    | .error _ => none
  layoutCache.modify (·.insert key r)
  return r


/-- The em of the layout, in sp (ten points). -/
def emSp : Int := 10 * 65536

/-- A length in sp as `em` of the formula's element, four decimals. -/
def emText (sp : Int) : String :=
  fixed sp emSp 4 ++ "em"

/-- The formula as an inline SVG element whose ids start with `idPrefix` (see the module
docstring). -/
def svg (fs : FontSet) (dl : LeAnTeX.DisplayList) (source idPrefix : String) : String := Id.run do
  let pad := emSp / 20
  let opts : SvgOptions := { em := emSp, padding := pad, title := source, idPrefix,
                             color := some "currentColor" }
  let p := picture fs dl opts
  let style := s!"vertical-align:-{emText (p.top + p.height)};margin:0 -{emText pad}"
  let attr := fun (n v : String) => s!" {n}=\"{escape v}\""
  let mut out : Array String := #[]
  out := out.push s!"<svg xmlns=\"http://www.w3.org/2000/svg\" \
    xmlns:xlink=\"http://www.w3.org/1999/xlink\"{attr "width" (emText p.width)}\
    {attr "height" (emText p.height)}\
    {attr "viewBox" s!"{ptText p.left} {ptText p.top} {ptText p.width} {ptText p.height}"}\
    {attr "style" style} fill=\"currentColor\" role=\"img\" focusable=\"false\">"
  out := out.push s!"<title>{escape source}</title>"
  if !p.defs.isEmpty then
    out := out.push "<defs>"
    for (id, d) in p.defs do out := out.push s!"<path{attr "id" id}{attr "d" d}/>"
    out := out.push "</defs>"
  for e in p.body do
    out := out.push <| match e with
      | .inl u =>
        let fill := match u.fill.bind cssColor? with | some c => attr "fill" c | none => ""
        s!"<use{attr "xlink:href" ("#" ++ u.ref)}{attr "transform" s!"matrix({u.matrix})"}{fill}/>"
      | .inr s => s
  out := out.push "</svg>"
  return String.join out.toList

/-- The formula as inline SVG, or `none` when it takes the browser path: LeAnTeX does not accept
it or the fonts are missing. `idPrefix` must be unique on the page. -/
def render? (display : Bool) (source texPrelude idPrefix : String) : IO (Option String) := do
  let some fs ← fonts? | return none
  let some dl ← layout? display source texPrelude | return none
  return some (svg fs dl source idPrefix)

/-- Whether the formula is typeset when the site is built (`render?` gives `some`). -/
def accepted (display : Bool) (source texPrelude : String) : IO Bool := do
  if (← fonts?).isNone then return false
  return (← layout? display source texPrelude).isSome

/-- The style rules of formulas typeset when the site is built: the size KaTeX's formulas have
(see the module docstring), no line break inside a formula, display formulas centred. -/
def css : String :=
  ".bp_math.bp_math_static{white-space:nowrap;font-size:1.0406em}\n" ++
  "html:has(meta[name=\"verso-blueprint-default-style\"][content=\"sbs\"])" ++
  ":not([data-bp-style]:not([data-bp-style=\"sbs\"])) main .bp_math.bp_math_static" ++
  "{font-size:0.8944em}\n" ++
  ".bp_math.bp_math_static>svg{display:inline-block;overflow:visible}\n" ++
  ".bp_math.display.bp_math_static{display:block;text-align:center;margin:1em 0}\n" ++
  ".bp_math.display.bp_math_static>svg{max-width:100%}\n"

end Informal.StaticMath
