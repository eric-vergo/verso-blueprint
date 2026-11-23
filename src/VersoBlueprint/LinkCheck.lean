/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

import Std.Data.HashMap
import Std.Data.HashSet
import VersoBlueprint.StaticMath

/-!
A check of a written site: every link of its navigation that names a place on a page of the site
(`page/#id`) must find that place. The navigation is what the site generates for moving around it:
the `nav` elements (Verso's table of contents, the buttons to the previous and next page, a
sidebar) and the Blueprint's own links (an `a` element with a `bp_` class). Links written in the
document's text are the author's and are not checked here.

Pages are read as Verso writes them: their links resolve against the page's `<base href>`. A
fragment with `=` (`#node=…`) is state that a page's script reads, not a place, and is not checked.
-/

namespace Informal.LinkCheck

open Std

/-- A link that names a place on a page that does not have it. -/
structure DeadLink where
  /-- The page with the link, relative to the site's folder. -/
  page : String
  /-- The link as written. -/
  href : String
deriving Inhabited, Repr, BEq

/-- `&amp;` and `%xx` escapes of a link, undone. -/
def unescape (s : String) : String := Id.run do
  let s := s.replace "&amp;" "&"
  let chars := s.toList.toArray
  let hex (c : Char) : Option Nat :=
    if c.isDigit then some (c.toNat - '0'.toNat)
    else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
    else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
    else none
  let mut bytes : ByteArray := .empty
  let mut i := 0
  while i < chars.size do
    let c := chars[i]!
    if c == '%' && i + 2 < chars.size then
      match hex chars[i+1]!, hex chars[i+2]! with
      | some h, some l =>
        bytes := bytes.push (h * 16 + l).toUInt8
        i := i + 3
        continue
      | _, _ => pure ()
    bytes := bytes ++ c.toString.toUTF8
    i := i + 1
  return (String.fromUTF8? bytes).getD s

/-- The value of attribute `name` in the text of a tag (`<a … name="value" …>`). -/
def attribute? (tag name : String) : Option String :=
  match tag.splitOn s!" {name}=\"" with
  | _ :: value :: _ => (value.splitOn "\"").head?
  | _ => none

/-- Every `id` of a page. -/
def pageIds (html : String) : HashSet String :=
  (html.splitOn " id=\"").drop 1 |>.foldl (init := {}) fun ids piece =>
    match (piece.splitOn "\"").head? with
    | some id => ids.insert (unescape id)
    | none => ids

/-- The attributes of the `a` tags of a text, each with a leading space and up to its `>`. -/
def anchorTags (html : String) : List String :=
  (html.splitOn "<a ").drop 1 |>.map fun piece => " " ++ ((piece.splitOn ">").head?.getD "")

/-- The text of the page's `nav` elements. -/
def navigationText (html : String) : List String :=
  (html.splitOn "<nav").drop 1 |>.map fun piece => ((piece.splitOn "</nav>").head?.getD "")

/-- The links of a page's navigation (`navigationText`, and `a` elements with a `bp_` class). -/
def navigationLinks (html : String) : Array String := Id.run do
  let mut out : Array String := #[]
  for nav in navigationText html do
    for tag in anchorTags nav do
      if let some href := attribute? tag "href" then out := out.push href
  for tag in anchorTags html do
    if let some cls := attribute? tag "class" then
      if (cls.splitOn " ").any (·.startsWith "bp_") then
        if let some href := attribute? tag "href" then
          unless out.contains href do out := out.push href
  return out

/-- A path of folders and a file, without `.` and with `..` taken back. -/
def normalize (parts : List String) : List String :=
  (parts.foldl (init := ([] : List String)) fun acc part =>
    if part == "" || part == "." then acc
    else if part == ".." then acc.drop 1
    else part :: acc).reverse

/-- Whether a link leaves the site: it has a scheme (`https:`, `lean:`) or is protocol-relative. -/
def isExternal (href : String) : Bool :=
  href.startsWith "//" ||
    (match (href.splitOn ":").head? with
     | some lead => lead.length < href.length && !lead.contains '/' && !lead.contains '#' && !lead.contains '?'
     | none => false)

/--
The page and place a link of the page at `pagePath` (its folders, from the site's folder) names:
the target's folders and the fragment. `none` for a link without a fragment or one that leaves the
site.
-/
def resolve (pagePath : List String) (base? : Option String) (href : String) :
    Option (List String × String) := do
  if isExternal href || href.startsWith "/" then none
  let (pathPart, fragment) ← match href.splitOn "#" with
    | [p, f] => some (p, f)
    | _ => none
  -- `#node=…` and `#ego=…` are state a page's script reads, not places
  if fragment.isEmpty || fragment.contains '=' then none
  let pathPart := ((pathPart.splitOn "?").head?.getD "")
  let baseDir := match base? with
    | some base => normalize (pagePath ++ base.splitOn "/")
    | none => pagePath
  let target := normalize (baseDir ++ pathPart.splitOn "/")
  return (target, unescape fragment)

/-- The dead links of the navigation of the site in `dir` (see the module's description). -/
def checkSite (dir : System.FilePath) : IO (Array DeadLink) := do
  if !(← dir.isDir) then return #[]
  let files := (← Informal.StaticMath.filesUnder dir).filter (·.extension == some "html")
  let root := dir.toString
  let rel (f : System.FilePath) : List String :=
    normalize (((f.toString.drop root.length).toString).splitOn "/")
  let mut pages : HashMap String (HashSet String) := {}
  let mut texts : Array (List String × String) := #[]
  for f in files do
    let html ← IO.FS.readFile f
    let path := rel f
    let key := "/".intercalate path
    let ids := pageIds html
    -- a folder written as `Chapter` into a file system that keeps an earlier `chapter` and
    -- ignores case is found by either name, as the server of such a file system finds it
    pages := (pages.insert key ids).insertIfNew key.toLower ids
    texts := texts.push (path, html)
  let mut dead : Array DeadLink := #[]
  for (path, html) in texts do
    let folders := path.dropLast
    let base? := (html.splitOn "<base ").drop 1 |>.head? |>.bind (attribute? s!" {·}" "href")
    for href in navigationLinks html do
      let some (target, fragment) := resolve folders base? (href.replace "&amp;" "&") | continue
      let key := if target.isEmpty then "index.html"
        else if (target.getLast!).endsWith ".html" then "/".intercalate target
        else "/".intercalate (target ++ ["index.html"])
      let found := match pages.get? key <|> pages.get? key.toLower with
        | some ids => ids.contains fragment
        | none => false
      unless found do
        dead := dead.push { page := "/".intercalate path, href }
  return dead

end Informal.LinkCheck
