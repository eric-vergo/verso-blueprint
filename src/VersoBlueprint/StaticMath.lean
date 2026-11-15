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
and written into the page as inline SVG: the glyphs are New Computer Modern's outlines (GUST
Font License), drawn in the text colour, so a formula needs no script, no font file and no style
sheet beyond a few rules. A formula LeAnTeX does not accept keeps the browser path (KaTeX, as
before), and the option `verso.blueprint.math.static` (default `true`) sends every formula to it.

* The TeX prelude of the document is prepended to each formula, as the browser path does.
* The fonts are read once per process from LeAnTeX's package: the folder named by the
  environment variable `VERSO_BLUEPRINT_MATH_FONTS`, else the `fonts/newcomputermodern` folder of
  the `leantex` package found on Lean's search path (where the build's modules are), else beside
  the running program's project (`.lake/packages/leantex`), else relative to the working
  directory. Without them every formula takes the browser path, and the build says so once, with
  the folders it looked in.
* Each formula is written three times over, for three readers: the picture (`aria-hidden`), its
  MathML (`LeAnTeX.Backend.mathML`, hidden from sight, for screen readers), and its TeX source
  (hidden from sight and from screen readers, so that copying the formula copies its source).
* An inline formula is cut into pictures at the places KaTeX lets a line break (after relations
  and binary operators at the top level), with a break opportunity between them, so a narrow
  screen wraps it instead of running past the edge; a piece wider than the line is scaled down
  to fit. A display formula wider than its column scrolls sideways.
* Inline formulas sit on the baseline (`vertical-align` from the formula's depth); the pictures
  are sized in `em` of their element, whose font size (`css`) is the size KaTeX's formulas have
  on the page: 1.21 em inside the 0.86 em of the `code` element they replace, and with the
  side-by-side style's text-sized formulas, 1.04 em of that. Display formulas are centred.
* Glyph outlines are written once per page: each picture references its glyphs by an id derived
  from the outline, and after the site is written `finishSite` moves the definitions of every
  page into one hidden `<svg>` at its end (`finishPage`). A fragment taken out of a page before
  that (a preview's HTML) keeps its own definitions. KaTeX's style sheet and script are removed
  from a page that has no formula for the browser to draw, unless the site's data files, which
  previews, node views and hovers show on any page, have such formulas (including statements
  kept as TeX between dollar signs for the page's script).
* The formulas of the dependency graph's node views are kept in the pages that show them, not
  in the node views' data: `finishSite` replaces each formula in `blueprint-node-views.json` by
  a reference (`reference`: a `code` element with the TeX source and the formula's key) and
  writes the formula once, in an inert `<template>` element, into every page that has a graph
  (`storeMarkup`); its glyph definitions join the page's set. The page's script puts a copy of
  the template's nodes in the reference's place when it shows a node view. A page that shows
  node views without a graph of its own (one built by a script) has no templates: there a
  reference shows its TeX source, typeset by KaTeX when the page loads it.
-/

namespace Informal.StaticMath

open LeAnTeX.Backend

/-- The font files the formulas are drawn with: the math fonts and the text fonts the
KaTeX-compatible layout's faces map to. -/
def fontFiles : List String :=
  ["NewCMMath-Book.otf", "NewCMMath-Bold.otf", "NewCM10-Book.otf", "NewCM10-BookItalic.otf",
    "NewCM10-BoldItalic.otf"]

/-- The fonts' folder inside LeAnTeX's package. -/
def packageFontDir : System.FilePath := "fonts" / "newcomputermodern"

/-- The `leantex` package's root for an entry of Lean's search path that is its build folder
(`…/.lake/build/lib/lean`). -/
def packageOfLibDir (p : System.FilePath) : Option System.FilePath := do
  guard (p.fileName == some "lean")
  let lib ← p.parent
  guard (lib.fileName == some "lib")
  let build ← lib.parent
  guard (build.fileName == some "build")
  let lake ← build.parent
  guard (lake.fileName == some ".lake")
  lake.parent

/-- The folders the fonts are looked for in, in order (see the module docstring). -/
def fontDirs : IO (Array System.FilePath) := do
  let mut out : Array System.FilePath := #[]
  if let some d ← IO.getEnv "VERSO_BLUEPRINT_MATH_FONTS" then
    if !d.isEmpty then out := out.push d
  let searchPath ← Lean.searchPathRef.get
  let envPath := match ← IO.getEnv "LEAN_PATH" with
    | some v => System.SearchPath.parse v
    | none => []
  for p in searchPath ++ envPath do
    if let some pkg := packageOfLibDir p then
      if (← (pkg / "LeAnTeX.lean").pathExists) && !out.contains (pkg / packageFontDir) then
        out := out.push (pkg / packageFontDir)
  -- the program's project: the executable is in `<project>/.lake/build/bin`
  let app ← IO.appPath
  if let some proj := app.parent.bind (·.parent) |>.bind (·.parent) |>.bind (·.parent) then
    let d := proj / ".lake" / "packages" / "leantex" / packageFontDir
    if !out.contains d then out := out.push d
  let cwd := System.FilePath.mk ".lake" / "packages" / "leantex" / packageFontDir
  if !out.contains cwd then out := out.push cwd
  return out

/-- The fonts, read on first use: `some` when every file read, `none` otherwise. -/
initialize fontCache : IO.Ref (Option (Option FontSet)) ← IO.mkRef none

/-- The fonts read from the first folder that has every file, with the folders looked in. -/
def loadFonts : IO (Option FontSet × Array System.FilePath) := do
  let dirs ← fontDirs
  for dir in dirs do
    if !(← (dir / (fontFiles.headD "")).pathExists) then continue
    let r ← try
        let (fs, missing) ← FontSet.load dir fontFiles
        pure (if missing.isEmpty then some fs else none)
      catch _ => pure none
    if r.isSome then return (r, dirs)
  return (none, dirs)

/-- The warning when the fonts are missing, naming the folders looked in. -/
def missingFontsWarning (dirs : Array System.FilePath) : String :=
  s!"warning: verso-blueprint: the New Computer Modern fonts for build-time math were not \
    found (looked in {", ".intercalate (dirs.toList.map toString)}); every formula is left \
    to KaTeX in the browser. Set VERSO_BLUEPRINT_MATH_FONTS to the folder that has \
    {", ".intercalate fontFiles}."

/-- The fonts, read once per process (see `fontCache`); the first time they are missing, a
warning naming the folders looked in goes to standard error. -/
def fonts? : IO (Option FontSet) := do
  if let some r ← fontCache.get then return r
  let (r, dirs) ← loadFonts
  if r.isNone then IO.eprintln (missingFontsWarning dirs)
  fontCache.set (some r)
  return r

/-- A formula laid out: its display list (with the advances of the glyphs that draw characters
KaTeX's fonts lack) and its MathML. -/
structure Laid where
  /-- The display list. -/
  dl : LeAnTeX.DisplayList
  /-- The MathML, with the source as its annotation. -/
  mathml : String

/-- The layouts made so far, by display mode, prelude and source (`none`: LeAnTeX does not
accept the formula). -/
initialize layoutCache : IO.Ref (Std.HashMap (Bool × String × String) (Option Laid)) ←
  IO.mkRef {}

/-- The formula laid out by LeAnTeX with the fonts `fs`, or `none` when it does not accept it
(cached). -/
def layoutWith (fs : FontSet) (display : Bool) (source texPrelude : String) :
    IO (Option Laid) := do
  let key := (display, texPrelude, source)
  if let some r := (← layoutCache.get)[key]? then return r
  let input := if texPrelude.trimAscii.isEmpty then source else texPrelude ++ "\n" ++ source
  let settings : LeAnTeX.Settings := { displayMode := display }
  let r := match (LeAnTeX.layout input settings).result with
    | .ok b =>
      let mathml := match (LeAnTeX.parse input settings).result with
        | .ok tree => mathMLOfTree tree display source
        | .error _ => ""
      some { dl := LeAnTeX.DisplayList.ofBox b { fallbackAdvance := fs.fallbackAdvance },
             mathml }
    | .error _ => none
  layoutCache.modify (·.insert key r)
  return r

/-- The formula's display list, or `none` when LeAnTeX does not accept it or the fonts are
missing. -/
def layout? (display : Bool) (source texPrelude : String) : IO (Option LeAnTeX.DisplayList) := do
  let some fs ← fonts? | return none
  return (← layoutWith fs display source texPrelude).map (·.dl)

/-- The em of the layout, in sp (ten points). -/
def emSp : Int := 10 * 65536

/-- The padding around each picture, in sp (0.05 em), which its margins take back. -/
def padSp : Int := emSp / 20

/-- A length in sp as `em` of the formula's element, four decimals. -/
def emText (sp : Int) : String :=
  fixed sp emSp 4 ++ "em"

/-- The id of a glyph outline: derived from the outline's path data, so the same glyph has the
same id in every picture of a page. -/
def glyphId (d : String) : String :=
  "bpg-" ++ String.ofList (Nat.toDigits 16 (hash d).toNat) ++ "-" ++
    String.ofList (Nat.toDigits 16 d.length)

/-- The left end of an item, in em's scaled points. -/
def itemX : LeAnTeX.Item → Int
  | .glyph _ _ x .. | .rule x .. | .path _ _ _ x .. | .image _ _ x .. => x.raw

/-- The pieces of an inline formula: its display list cut at its unbreakable parts (KaTeX's
break opportunities on its first line), each piece with the formula's height and depth so that
the pictures share the baseline. A formula of one part, a display formula or one of several
lines is one piece. -/
def pieces (dl : LeAnTeX.DisplayList) (display : Bool) : Array LeAnTeX.DisplayList := Id.run do
  let parts := dl.parts.filter fun p => p.line == 0 && !p.tag
  if display || parts.size ≤ 1 || dl.lines.size > 1 then return #[dl]
  let mut out := #[]
  for h : k in [0:parts.size] do
    let lo := parts[k].x.raw
    let last := k + 1 == parts.size
    let hi := if last then dl.width.raw else (parts[k + 1]?.map (·.x.raw)).getD dl.width.raw
    let items := dl.items.filter fun it => lo ≤ itemX it && (itemX it < hi || last)
    let items := items.map (·.shift ⟨-lo⟩ ⟨0⟩)
    let w : LeAnTeX.Em := ⟨hi - lo⟩
    let line : LeAnTeX.Line := { start := 0, stop := items.size, width := w, height := dl.height,
                                 depth := dl.depth }
    out := out.push { dl with items, width := w, lines := #[line], parts := #[], regions := #[],
                              mirrored := #[] }
  return out

/-- One picture: an inline SVG element of the display list, its glyph definitions in a
`<defs data-bp-glyphs="">` with outline-derived ids (see `finishPage`). -/
def svg (fs : FontSet) (dl : LeAnTeX.DisplayList) (source idPrefix : String) : String := Id.run do
  let opts : SvgOptions := { em := emSp, padding := padSp, title := source, idPrefix,
                             color := some "currentColor" }
  let p := picture fs dl opts
  let ids : Std.HashMap String String :=
    p.defs.foldl (init := {}) fun m (id, d) => m.insert id (glyphId d)
  let style := s!"vertical-align:-{emText (p.top + p.height)};margin:0 -{emText padSp}"
  let attr := fun (n v : String) => s!" {n}=\"{escape v}\""
  let mut out : Array String := #[]
  out := out.push s!"<svg xmlns=\"http://www.w3.org/2000/svg\" \
    xmlns:xlink=\"http://www.w3.org/1999/xlink\"{attr "width" (emText p.width)}\
    {attr "height" (emText p.height)}\
    {attr "viewBox" s!"{ptText p.left} {ptText p.top} {ptText p.width} {ptText p.height}"}\
    {attr "style" style} fill=\"currentColor\" aria-hidden=\"true\" focusable=\"false\">"
  out := out.push s!"<title>{escape source}</title>"
  if !p.defs.isEmpty then
    out := out.push "<defs data-bp-glyphs=\"\">"
    for (id, d) in p.defs do out := out.push s!"<path{attr "id" (ids.getD id id)}{attr "d" d}/>"
    out := out.push "</defs>"
  for e in p.body do
    out := out.push <| match e with
      | .inl u =>
        let fill := match u.fill.bind cssColor? with | some c => attr "fill" c | none => ""
        s!"<use{attr "xlink:href" ("#" ++ ids.getD u.ref u.ref)}\
          {attr "transform" s!"matrix({u.matrix})"}{fill}/>"
      | .inr s => s
  out := out.push "</svg>"
  return String.join out.toList

/-- The formula's markup inside its element: the pictures (one per piece, with a break
opportunity between them), the MathML and the source (see the module docstring). -/
def markup (fs : FontSet) (l : Laid) (display : Bool) (source idPrefix : String) : String :=
  let ps := pieces l.dl display
  let pics := ps.toList.mapIdx fun k dl => svg fs dl source s!"{idPrefix}{k}-"
  let (openD, closeD) := if display then ("\\[", "\\]") else ("$", "$")
  "<wbr>".intercalate pics ++
    l.mathml.replace "<math " "<math class=\"bp_math_mathml\" " ++
    s!"<span class=\"bp_math_source\" aria-hidden=\"true\">\
      {escape (openD ++ source ++ closeD)}</span>"

/-- The formula as inline markup, or `none` when it takes the browser path: LeAnTeX does not
accept it or the fonts are missing. `idPrefix` names the picture's own ids. -/
def render? (display : Bool) (source texPrelude idPrefix : String) : IO (Option String) := do
  let some fs ← fonts? | return none
  let some l ← layoutWith fs display source texPrelude | return none
  return some (markup fs l display source idPrefix)

/-- Whether the formula is typeset when the site is built (`render?` gives `some`). -/
def accepted (display : Bool) (source texPrelude : String) : IO Bool := do
  return (← layout? display source texPrelude).isSome

/-- The style rules of formulas typeset when the site is built: the size KaTeX's formulas have
(see the module docstring), pictures that wrap only between pieces, display formulas centred
and scrolling when wider than their column, the MathML and the source hidden from sight (the
MathML left out of a copied selection, the source copied). -/
def css : String :=
  ".bp_math.bp_math_static{font-size:1.0406em;position:relative}\n" ++
  "html:has(meta[name=\"verso-blueprint-default-style\"][content=\"sbs\"])" ++
  ":not([data-bp-style]:not([data-bp-style=\"sbs\"])) main .bp_math.bp_math_static" ++
  "{font-size:0.8944em}\n" ++
  ".bp_math.bp_math_static>svg{display:inline-block;overflow:visible;max-width:100%}\n" ++
  ".bp_math.inline.bp_math_static>svg{height:auto}\n" ++
  ".bp_math.display.bp_math_static{display:block;text-align:center;margin:1em 0;" ++
  "overflow-x:auto;overflow-y:hidden;padding:0.2em 0}\n" ++
  ".bp_math.display.bp_math_static>svg{max-width:none}\n" ++
  ".bp_math_static>.bp_math_mathml,.bp_math_static>.bp_math_source{position:absolute;" ++
  "left:0;top:0;width:1px;height:1px;overflow:hidden;clip-path:inset(50%);white-space:nowrap}\n" ++
  ".bp_math_static>.bp_math_mathml{user-select:none}\n"

/-! ### Pages -/

/-- The glyph definitions of a `<defs data-bp-glyphs="">` element's content (as `svg` writes
it): ids and path data. -/
def glyphDefs (inner : String) : Array (String × String) := Id.run do
  let mut out := #[]
  for piece in (inner.splitOn "<path id=\"").drop 1 do
    match piece.splitOn "\" d=\"" with
    | id :: d :: _ => out := out.push (id, (d.splitOn "\"").headD "")
    | _ => pure ()
  return out

/-- What `finishPage` did: the glyph definitions kept, those dropped as repeated, and whether
it removed KaTeX's files. -/
structure PageStats where
  /-- Definitions written once in the page's set. -/
  kept : Nat := 0
  /-- Repeated definitions dropped. -/
  dropped : Nat := 0
  /-- Two different outlines under one id (never expected). -/
  clashes : Nat := 0
  /-- Pages whose KaTeX style sheet and script were removed. -/
  katexRemoved : Nat := 0
  /-- Formulas of node views kept in the pages' templates (each once). -/
  stored : Nat := 0
  deriving Repr

/-- Whether a page has a formula for the browser to draw: a blueprint formula left to KaTeX
(`<code class="bp_math …`) or Verso's own math (`class="math …`). -/
def needsKaTeX (html : String) : Bool :=
  (html.splitOn "<code class=\"bp_math ").length > 1 || (html.splitOn "class=\"math ").length > 1

/-- The tags of KaTeX's files in a page head. -/
def katexTags : List String :=
  ["<script src=\"-verso-data/katex/katex.js\"></script>",
    "<script src=\"-verso-data/katex/math.js\"></script>",
    "<link rel=\"stylesheet\" href=\"-verso-data/katex/katex.css\">"]

/-- The marker that opens a picture's glyph definitions. -/
def defsOpen : String := "<defs data-bp-glyphs=\"\">"

/-- A written page with its glyph definitions moved into one hidden `<svg>` before `</body>`
(each once), and KaTeX's file tags removed when `keepKaTeX` is false and the page has no
formula for the browser to draw. -/
def finishPage (html : String) (keepKaTeX : Bool) : String × PageStats := Id.run do
  let mut st : PageStats := {}
  let mut defs : Std.HashMap String String := {}
  let mut order : Array String := #[]
  let chunks := html.splitOn defsOpen
  let mut out := chunks.headD ""
  for c in chunks.drop 1 do
    match c.splitOn "</defs>" with
    | inner :: rest =>
      for (id, d) in glyphDefs inner do
        match defs[id]? with
        | some d' => st := if d' == d then { st with dropped := st.dropped + 1 }
            else { st with clashes := st.clashes + 1 }
        | none => defs := defs.insert id d; order := order.push id
      out := out ++ "</defs>".intercalate rest
    | [] => out := out ++ c
  st := { st with kept := order.size }
  if !order.isEmpty then
    let sprite := "<svg class=\"bp_math_glyphs\" xmlns=\"http://www.w3.org/2000/svg\" " ++
      "aria-hidden=\"true\" focusable=\"false\" width=\"0\" height=\"0\" " ++
      "style=\"position:absolute;width:0;height:0;overflow:hidden\"><defs>" ++
      String.join (order.toList.map fun id =>
        s!"<path id=\"{id}\" d=\"{defs.getD id ""}\"/>") ++ "</defs></svg>"
    out := match out.splitOn "</body>" with
      | [a, b] => a ++ sprite ++ "</body>" ++ b
      | _ => out ++ sprite
  if !keepKaTeX && !needsKaTeX out && katexTags.any (fun t => (out.splitOn t).length > 1) then
    for t in katexTags do out := out.replace t ""
    st := { st with katexRemoved := 1 }
  return (out, st)

/-! ### Formulas of node views, kept in the page -/

/-- The file of the dependency graph's node views in a site's data folder. -/
def nodeViewsFile : String := "blueprint-node-views.json"

/-- How the element of a formula typeset at build time starts, up to its display mode. -/
def staticOpen : String := "<span class=\"bp_math "

/-- How the copyable source inside such an element starts. -/
def sourceOpen : String := "<span class=\"bp_math_source\" aria-hidden=\"true\">"

/-- A formula typeset at build time at the start of `piece`, a text that followed `staticOpen`:
whether it is a display formula, its element without `staticOpen`, its source as written in the
markup (escaped, without the math delimiters) and the text after the element. `none` when
`piece` does not start with such an element as `Informal.Math` and `markup` write it. -/
def staticElement? (piece : String) : Option (Bool × String × String × String) := do
  let display ←
    if piece.startsWith "inline bp_math_static\"" then some false
    else if piece.startsWith "display bp_math_static\"" then some true
    else none
  let (body, tail) ← match piece.splitOn sourceOpen with
    | body :: tail@(_ :: _) => some (body, sourceOpen.intercalate tail)
    | _ => none
  let close := "</span></span>"
  let (source, rest) ← match tail.splitOn close with
    | source :: rest@(_ :: _) => some (source, close.intercalate rest)
    | _ => none
  guard ((source.splitOn "<").length == 1)
  let (openD, closeD) := if display then ("\\[", "\\]") else ("$", "$")
  guard (source.startsWith openD && source.endsWith closeD &&
    source.length ≥ openD.length + closeD.length)
  let bare := ((source.drop openD.length).dropEnd closeD.length).toString
  return (display, body ++ sourceOpen ++ source ++ close, bare, rest)

/-- The key of a formula's element in a page's templates: derived from the element, so the
same formula has the same key wherever it is shown. -/
def storeKey (element : String) : String :=
  "bpm-" ++ String.ofList (Nat.toDigits 16 (hash element).toNat) ++ "-" ++
    String.ofList (Nat.toDigits 16 element.length)

/-- The reference that stands for a stored formula in a node view: the TeX source in a `code`
element of the browser path's classes (so the formula is still there, as text or for KaTeX,
where no template is), with the template's key. `source` is escaped already. -/
def reference (display : Bool) (key source : String) : String :=
  s!"<code class=\"bp_math_ref bp_math {if display then "display" else "inline"}\" \
    data-bp-math-key=\"{key}\" data-bp-tex-prelude-id=\"default\">{source}</code>"

/-- The formulas kept for a site's pages: each element once, by key, in the order met. -/
structure Store where
  /-- The elements by key. -/
  byKey : Std.HashMap String String := {}
  /-- The keys, in the order met. -/
  keys : Array String := #[]

/-- The key under which `element` is in the store, added when it is new. Two different
elements never share a key: the second gets the next free key after its own. -/
def Store.add (st : Store) (element : String) : Store × String := Id.run do
  let base := storeKey element
  let mut key := base
  let mut n := 1
  while true do
    match st.byKey[key]? with
    | some e =>
      if e == element then return (st, key)
      key := s!"{base}-{n}"
      n := n + 1
    | none => break
  return ({ byKey := st.byKey.insert key element, keys := st.keys.push key }, key)

/-- `html` with each formula typeset at build time replaced by its reference, the formulas
added to the store. Anything else is left as it is. -/
def storeFormulas (st : Store) (html : String) : Store × String := Id.run do
  match html.splitOn staticOpen with
  | [] | [_] => return (st, html)
  | first :: pieces =>
    let mut st := st
    let mut out := first
    for piece in pieces do
      match staticElement? piece with
      | some (display, element, source, rest) =>
        let (st', key) := st.add (staticOpen ++ element)
        st := st'
        out := out ++ reference display key source ++ rest
      | none => out := out ++ staticOpen ++ piece
    return (st, out)

/-- The text of a node-views file with the formulas of its views moved to the store
(`storeFormulas` on each entry's `html`); `none` when the file is not one. -/
def storeNodeViews (st : Store) (text : String) : Option (Store × String) := do
  let json ← (Lean.Json.parse text).toOption
  let entries ← (json.getObjValAs? (Array Lean.Json) "entries").toOption
  let mut st := st
  let mut out : Array Lean.Json := #[]
  for e in entries do
    match e.getObjValAs? String "html" with
    | .ok html =>
      let (st', html') := storeFormulas st html
      st := st'
      out := out.push (e.setObjVal! "html" (.str html'))
    | .error _ => out := out.push e
  return (st, (json.setObjVal! "entries" (.arr out)).compress)

/-- How the templates' container in a page starts. -/
def storeOpen : String := "<div class=\"bp_math_store\" hidden=\"\">"

/-- How the templates' container ends: its own comment, so that the container can be found
again whatever its templates hold. -/
def storeClose : String := "<!--bp_math_store--></div>"

/-- The store as page markup: a hidden container of one inert `<template>` per formula, each
with its key. Empty for an empty store. -/
def storeMarkup (st : Store) : String :=
  if st.keys.isEmpty then "" else
  storeOpen ++ String.join (st.keys.toList.map fun key =>
    s!"<template class=\"bp_math_stored\" data-bp-math-key=\"{key}\">\
      {st.byKey.getD key ""}</template>") ++ storeClose

/-- Whether a page shows node views: it has a dependency graph. -/
def showsNodeViews (html : String) : Bool :=
  (html.splitOn "class=\"bp_graph_fullwidth\"").length > 1

/-- A page with the templates `templates` (`storeMarkup`) before `</body>`, in place of the
container it had, if any. -/
def withStore (html templates : String) : String :=
  let html := match html.splitOn storeOpen with
    | [before, after] =>
      match after.splitOn storeClose with
      | _ :: rest@(_ :: _) => before ++ storeClose.intercalate rest
      | _ => html
    | _ => html
  if templates.isEmpty then html else
  match html.splitOn "</body>" with
  | [a, b] => a ++ templates ++ "</body>" ++ b
  | _ => html ++ templates

/-- The files under a folder, recursively, links not followed. -/
partial def filesUnder (dir : System.FilePath) : IO (Array System.FilePath) := do
  let mut out := #[]
  for e in ← dir.readDir do
    let md ← e.path.symlinkMetadata
    if md.type == .dir then out := out ++ (← filesUnder e.path)
    else if md.type == .file then out := out.push e.path
  return out

/-- A text without the parts between each `opener` and the next `closer` (both kept out); an
`opener` without a `closer` after it is kept with what follows it. -/
def withoutBetween (s opener closer : String) : String :=
  match s.splitOn opener with
  | first :: rest =>
    first ++ String.join (rest.map fun piece =>
      match piece.splitOn closer with
      | _ :: after@(_ :: _) => closer.intercalate after
      | _ => opener ++ piece)
  | [] => s

/-- A data file's text (JSON-escaped HTML) without the TeX sources that build-time formulas
carry for copying (`<span class="bp_math_source" …>…</span>`) and without docstrings (`<code
class="docstring">`, `<pre class="docstring">`), which pages render as Markdown, not as TeX. -/
def withoutSources (s : String) : String :=
  let s := withoutBetween s "<span class=\\\"bp_math_source\\\"" "</span>"
  let s := withoutBetween s "<code class=\\\"docstring\\\">" "</code>"
  withoutBetween s "<pre class=\\\"docstring\\\">" "</pre>"

/-- Whether a data file's text (JSON) has a formula for the browser to draw: a blueprint formula
left to KaTeX, Verso's own math, or TeX between dollar signs, as the statements of a site
generated from code carry them for the page's script to typeset (any `$` outside the sources of
build-time formulas and outside docstrings counts, so a stray one only keeps KaTeX). -/
def textNeedsKaTeX (s : String) : Bool :=
  (s.splitOn "<code class=\\\"bp_math ").length > 1 ||
    (s.splitOn "class=\\\"math ").length > 1 || (withoutSources s).contains '$'

/-- Whether a site's data files (`.json`: previews, node views, hovers, which any page may
show) have a formula for the browser to draw (`textNeedsKaTeX`). -/
def dataNeedsKaTeX (files : Array System.FilePath) : IO Bool := do
  for f in files do
    if f.extension == some "json" then
      if textNeedsKaTeX (← IO.FS.readFile f) then return true
  return false

/-- Finishes a written site in `dir`: the formulas of its node views go into templates in the
pages that have a graph (`storeNodeViews`, `withStore`), then every page is finished
(`finishPage`); KaTeX's files stay on every page when `dataNeedsKaTeX`. Returns the totals. -/
def finishSite (dir : System.FilePath) : IO PageStats := do
  if !(← dir.isDir) then return {}
  let files ← filesUnder dir
  let mut store : Store := {}
  for f in files do
    if f.fileName == some nodeViewsFile then
      let text ← IO.FS.readFile f
      if let some (store', text') := storeNodeViews store text then
        store := store'
        if text' != text then IO.FS.writeFile f text'
  let templates := storeMarkup store
  let keep ← dataNeedsKaTeX files
  let mut total : PageStats := { stored := store.keys.size }
  for f in files do
    if f.extension != some "html" then continue
    let html ← IO.FS.readFile f
    let page := if !templates.isEmpty && showsNodeViews html then withStore html templates
      else html
    let (out, st) := finishPage page keep
    if out != html then IO.FS.writeFile f out
    total := { total with kept := total.kept + st.kept, dropped := total.dropped + st.dropped,
                          clashes := total.clashes + st.clashes,
                          katexRemoved := total.katexRemoved + st.katexRemoved }
  return total

end Informal.StaticMath
