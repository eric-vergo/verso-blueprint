/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

import VersoBlueprint.StaticMath

/-!
What a Blueprint site changes in the text of the pages Verso writes, once they are written.

* The viewport: Verso's pages ask the browser not to zoom (`maximum-scale=1`); a Blueprint page
  lets the reader zoom (`allowZoom`).
* Section numbers: a statement is numbered in its chapter (`Theorem 9.1`) and a section by its
  place in the chapter (`9.1`), so the same number could name both. Sections below a chapter are
  shown with a section sign and without Verso's closing dot (`§9.1`), in headings, tables of
  contents, the buttons to the previous and next page, and the site's cross-reference data
  (`sectionSigns`). Chapter numbers (`9.`) stay as Verso writes them.
-/

namespace Informal.PageText

/-- The viewport Verso writes into every page. -/
def versoViewport : String :=
  "content=\"height=device-height, width=device-width, initial-scale=1, minimum-scale=1, maximum-scale=1\""

/-- The viewport of a Blueprint page: the width of the device, and zoom left to the reader. -/
def blueprintViewport : String := "content=\"width=device-width, initial-scale=1\""

/-- The page with a viewport that lets the reader zoom. -/
def allowZoom (html : String) : String :=
  html.replace versoViewport blueprintViewport

/-- A section number at the start of `s` as Verso writes it, `9.1.` or `A.2.3.`, with at least two
components: the components and the length of the number in characters. -/
def leadingSectionNumber? (s : String) : Option (List String × Nat) := Id.run do
  let chars := (s.take 48).toString.toList
  let mut comps : Array String := #[]
  let mut cur := ""
  let mut used := 0
  for c in chars do
    if c.isDigit then
      cur := cur.push c
      used := used + 1
    else if c.isUpper && cur.isEmpty then
      cur := cur.push c
      used := used + 1
    else if c == '.' && !cur.isEmpty && (cur.all Char.isDigit || cur.length == 1) then
      comps := comps.push cur
      cur := ""
      used := used + 1
    else
      break
  if cur.isEmpty && comps.size ≥ 2 then some (comps.toList, used) else none

/-- `9.1` as the reader sees a section: `§9.1`. -/
def sectionSign (comps : List String) : String :=
  "§" ++ ".".intercalate comps

/-- Rewrite each section number that follows `opener` and is followed by a character `stop`
accepts. -/
def rewriteAfter (text opener : String) (stop : Char → Bool) : String :=
  match text.splitOn opener with
  | [] | [_] => text
  | first :: rest =>
    let rest := rest.map fun piece =>
      match leadingSectionNumber? piece with
      | some (comps, used) =>
        let after := (piece.drop used).toString
        if !after.isEmpty && stop after.front then sectionSign comps ++ after else piece
      | none => piece
    opener.intercalate (first :: rest)

/-- The section numbers of headings: Verso writes a heading as `<h2 id="…">9.1. Title`. -/
def rewriteHeadings (text : String) : String :=
  match text.splitOn "<h" with
  | [] | [_] => text
  | first :: rest =>
    let rest := rest.map fun piece =>
      let level := piece.front
      if !('1' ≤ level && level ≤ '6') || !((piece.drop 1).toString.startsWith " id=\"") then piece
      else
        match (piece.splitOn "\">") with
        | tag :: body :: more =>
          if tag.contains '>' then piece
          else match leadingSectionNumber? body with
            | some (comps, used) =>
              let after := (body.drop used).toString
              if after.startsWith " " || after.startsWith "\u00A0" then
                "\">".intercalate (tag :: (sectionSign comps ++ after) :: more)
              else piece
            | none => piece
        | _ => piece
    "<h".intercalate (first :: rest)

/-- A page with its section numbers below chapters written `§9.1`. -/
def sectionSigns (html : String) : String :=
  let html := rewriteAfter html "<span class=\"number\">" (· == '<')
  let html := rewriteAfter html "<td class=\"num\">" (· == '<')
  let html := rewriteAfter html "<span class=\"where\">" (· == ' ')
  let html := rewriteAfter html "rel=\"next\" title=\"" (· == ' ')
  let html := rewriteAfter html "rel=\"prev\" title=\"" (· == ' ')
  let html := rewriteAfter html "\"sectionNum\":\"" (· == '"')
  rewriteHeadings html

/-- A page as a Blueprint site shows it (`allowZoom`, `sectionSigns`). -/
def finishPage (html : String) : String :=
  sectionSigns (allowZoom html)

/-- Finish every page of the site in `dir`, and the site's cross-reference data (`xref.json`).
Returns the number of files changed. -/
def finishSite (dir : System.FilePath) : IO Nat := do
  if !(← dir.isDir) then return 0
  let mut changed := 0
  for f in ← Informal.StaticMath.filesUnder dir do
    let page := f.extension == some "html"
    if !page && f.fileName != some "xref.json" then continue
    let text ← IO.FS.readFile f
    let out := if page then finishPage text else sectionSigns text
    if out != text then
      IO.FS.writeFile f out
      changed := changed + 1
  return changed

end Informal.PageText
