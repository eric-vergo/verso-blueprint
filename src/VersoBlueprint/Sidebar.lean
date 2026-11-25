/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

import Lean.Data.Json
import VersoManual
import VersoBlueprint.Html
import VersoBlueprint.PageText
import VersoBlueprint.Parts

/-!
A navigation sidebar for Blueprint sites, built from Verso's table of contents.

When a generator enables it, every page announces it with
`<meta name="verso-blueprint-sidebar">` and carries a small JSON configuration,
and the site's data folder holds the document's outline (`outlineFile`): every
part, chapter and section with its title, number and address, with a part's
chapters inside the part. The sidebar script shows the outline as a tree whose
rows open and close, and adds a "Blueprint Home" entry, separators, the
configured external links and a light/dark theme switch at the foot. Without
JavaScript the stylesheet restyles Verso's table of contents (the chapters as a
list, the parts set apart, the current chapter bold).
-/

namespace Informal.Sidebar

open Lean
open Verso.Genre.Manual

/-- An external link shown in the sidebar, such as a paper or the source repository. -/
structure Link where
  label : String
  href : String
deriving Inhabited, Repr, BEq

/-- Sidebar configuration for a Blueprint site. -/
structure Config where
  /-- Label of the entry that links to the site's front page. -/
  homeLabel : String := "Blueprint Home"
  /-- External links, shown after the table of contents in this order. -/
  links : Array Link := #[]
deriving Inhabited, Repr, BEq

def metaName : String := "verso-blueprint-sidebar"

/-- Generator flag that enables the sidebar with the default configuration. -/
def flag : String := "--sidebar"

/-- Extract `--sidebar`: it enables the default sidebar unless one is configured already. -/
def parseFlag (sidebar? : Option Config) (args : List String) : Option Config × List String :=
  let sidebar? := if args.contains flag then sidebar?.getD {} |> some else sidebar?
  (sidebar?, args.filter (· != flag))

def configElementId : String := "verso-blueprint-sidebar-config"

def css : String := include_str "Sidebar/sidebar.css"

def js : String := include_str "Sidebar/sidebar.js"

/-- The JSON configuration read by the sidebar script. -/
def Config.toJson (cfg : Config) : Json :=
  Json.mkObj [
    ("homeLabel", cfg.homeLabel),
    ("links", Json.arr (cfg.links.map fun link =>
      Json.mkObj [("label", link.label), ("href", link.href)]))
  ]

/--
Inline `<head>` script that applies a stored theme choice before the page is
painted, so that a dark choice does not flash light on load.
-/
def themeInitScript : String :=
  "(function(){try{var t=localStorage.getItem(\"verso-theme\");" ++
  "if(t===\"dark\"||t===\"light\")document.documentElement.setAttribute(\"data-theme\",t);}" ++
  "catch(e){}})();"

/-- The file in the site's data folder (`-verso-data`) that holds the document's outline. -/
def outlineFile : String := "blueprint-sidebar-outline.js"

/-- The global variable the outline file sets. -/
def outlineVariable : String := "versoBlueprintSidebarOutline"

/-- The `<head>` elements that enable the sidebar. -/
def headHtml (cfg : Config) : Array Verso.Output.Html :=
  -- `<` cannot occur in the JSON payload's markup context once escaped this way.
  let json := (cfg.toJson.compress.replace "<" "\\u003c")
  #[
    .element "meta" #[("name", metaName), ("content", "on")] .empty,
    .element "script" #[("type", "application/json"), ("id", configElementId)] (.raw json),
    .element "script" #[] (.raw themeInitScript),
    -- relative to the page's `<base>`, the site's root
    .element "script" #[("src", s!"-verso-data/{outlineFile}"), ("defer", "defer")] .empty
  ]

/-- Enable the sidebar for a generated site. -/
def withSidebar (cfg : Config) (config : RenderConfig) : RenderConfig :=
  let htmlConfig := config.toHtmlConfig
  let assets : HtmlAssets := { extraCss := [css], extraJs := [js] }
  { config with
    toHtmlConfig := {
      htmlConfig with
      toHtmlAssets := htmlConfig.toHtmlAssets.combine assets
      extraHead := headHtml cfg |>.foldl VersoBlueprint.Html.pushIfRenderedMissing htmlConfig.extraHead
    }
  }

/-- A section number as the site shows it: `§9.1` below chapters, `9.` for a chapter
(`Informal.PageText`). -/
def numberText (number : String) : String :=
  match PageText.leadingSectionNumber? number with
  | some (comps, used) => if used == number.length then PageText.sectionSign comps else number
  | none => number

/-- One entry of the outline and the entries below it. `pagePath` is the path of the page of the
entry above it: an entry whose own path is longer has a page of its own. -/
partial def entryJson (pagePath : Verso.Multi.Path) (entry : Html.Toc) : Json :=
  let ownPage := entry.path.size > pagePath.size
  let title := Verso.Output.Html.asString <| Verso.Genre.Manual.Html.Hoist.postprocess <| relativizeLinks (entry.shortTitle.getD entry.title)
  let fields : List (String × Json) := [
    ("title", title),
    ("href", Verso.Multi.Path.relativeLink entry.path entry.id),
    ("children", Json.arr (entry.children.toArray.map (entryJson entry.path)))]
  let fields := match entry.sectionNum with
    | some ns => ("number", Json.str (numberText (sectionNumberString ns))) :: fields
    | none => fields
  let fields := if ownPage then ("page", Json.str (Verso.Multi.Path.relativeLink entry.path)) :: fields
    else fields
  Json.mkObj fields

/-- The outline's top-level entries: the document's own parts, each numbered part
(`Informal.Parts`) with its chapters inside it again, marked `"part": true`. -/
def outlineJson (parts : Array (Verso.Doc.Part Verso.Genre.Manual × Html.Toc)) : Json := Id.run do
  let mut out : Array Json := #[]
  let mut i := 0
  while h : i < parts.size do
    let (part, entry) := parts[i]
    match Parts.partMarker? part with
    | some marker =>
      let chapters := (parts.extract (i + 1) (i + 1 + marker.chapters)).map fun (_, c) =>
        entryJson #[] c
      let own := entryJson #[] entry
      out := out.push <| own.setObjVal! "part" true |>.setObjVal! "children" (Json.arr chapters)
      i := i + 1 + marker.chapters
    | none =>
      out := out.push (entryJson #[] entry)
      i := i + 1
  return Json.mkObj [("entries", Json.arr out)]

/-- Write the outline of the traversed document `text` into the data folder of the site in `dir`,
for pages whose own files stop at depth `depth` (`0` for a single page): the titles as the table of
contents shows them, and the addresses relative to the site's root. -/
def writeOutline (dir : System.FilePath) (depth : Nat) (config : RenderConfig)
    (state : TraverseState) (text : Verso.Doc.Part Verso.Genre.Manual) : EmitM Unit := do
  let opts : Verso.Doc.Html.Options := {}
  let ctxt : TraverseContext := {}
  let definitionIds := state.definitionIds ctxt
  let linkTargets := config.linkTargets state {}
  let entries : StateT (Verso.Code.Hover.State Verso.Output.Html)
      (ReaderT Verso.Multi.AllRemotes EmitM) (Array Html.Toc) :=
    text.subParts.mapM fun p =>
      Verso.Genre.Manual.toc depth opts (ctxt.inPart p) state definitionIds linkTargets p
  let entries ← (entries.run' .empty).run {}
  let json := outlineJson (text.subParts.zip entries)
  let data := dir / "-verso-data"
  IO.FS.createDirAll data
  IO.FS.writeFile (data / outlineFile) s!"window.{outlineVariable} = {json.compress};\n"

end Informal.Sidebar
