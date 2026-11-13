/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

import Lean.Data.Json

/-!
What a project says about itself in the files at its root: the title and first paragraph of
its README, the license its LICENSE file most likely carries (as an SPDX identifier), the Lean
toolchain it pins and the revisions of the packages its Lake manifest locks.

Every reader is a pure function of a file's text, so the rules can be checked on fixtures;
`ProjectIdentity.read` applies them to the files of a project root. No version-control data is
read.
-/

namespace Informal.Stats

open Lean

/-- A package locked by the project's Lake manifest. -/
structure ManifestPackage where
  /-- The package name. -/
  name : String
  /-- How Lake obtains it: `git` or `path`. -/
  source : String
  /-- The locked commit of a `git` package. -/
  rev : Option String := none
  /-- The branch, tag or commit the project asked for, when it named one. -/
  inputRev : Option String := none
  /-- The repository of a `git` package, without any user name or password it carried. -/
  url : Option String := none
  /-- The directory of a `path` package, relative to the project root. -/
  dir : Option String := none
  /-- Whether the package is required only through another package. -/
  inherited : Bool := false
deriving Repr, Inhabited, DecidableEq, ToJson, FromJson

/-- The project's license file and the license it most likely carries. -/
structure LicenseInfo where
  /-- The file name, relative to the project root. -/
  file : String
  /-- The SPDX identifier of the license text, when it is recognised. -/
  spdx : Option String := none
deriving Repr, Inhabited, DecidableEq, ToJson, FromJson

/-- How a project presents itself: what its root files say, with no version-control data. -/
structure ProjectIdentity where
  /-- The root package's name in the Lake manifest. -/
  name : Option String := none
  /-- The README file name, relative to the project root. -/
  readme : Option String := none
  /-- The README's first heading. -/
  title : Option String := none
  /-- The README's first paragraph of prose, as plain text. -/
  description : Option String := none
  /-- The license file; `none` when the project root has none. -/
  license : Option LicenseInfo := none
  /-- The contents of `lean-toolchain`. -/
  toolchain : Option String := none
  /-- The packages the Lake manifest locks, in manifest order. -/
  packages : Array ManifestPackage := #[]
deriving Repr, Inhabited, DecidableEq, ToJson, FromJson

private def trimText (s : String) : String := s.trimAscii.copy

/-- Collapse runs of whitespace into single spaces and trim the ends. -/
private def collapseWhitespace (s : String) : String :=
  " ".intercalate ((s.split Char.isWhitespace).toList.map (·.copy) |>.filter (!·.isEmpty))

/-! ## README -/

namespace Readme

private def isHeading (line : String) : Bool :=
  let t := (trimText line).toList
  t.head? == some '#' && (t.dropWhile (· == '#')).head? == some ' '

private def headingText (line : String) : String :=
  let t := (trimText line).toList.dropWhile (· == '#')
  let t := (trimText (String.ofList t)).toList.reverse.dropWhile (· == '#') |>.reverse
  trimText (String.ofList t)

private def isSetextUnderline (line : String) : Bool :=
  let t := trimText line
  !t.isEmpty && (t.all (· == '=') || t.all (· == '-'))

private def isFence (line : String) : Bool :=
  let t := trimText line
  t.startsWith "```" || t.startsWith "~~~"

/-- Inline Markdown to plain text: link and image targets dropped (link text kept, images
removed), emphasis stars and code backticks removed, autolinks unwrapped. -/
partial def plainText (s : String) : String := Id.run do
  let cs := s.toList.toArray
  let mut out : Array Char := #[]
  let mut i := 0
  while i < cs.size do
    let c := cs[i]!
    -- `![alt](target)`: an image, dropped with its target.
    if c == '!' && cs[i + 1]? == some '[' then
      match closeOf cs (i + 1) ']' with
      | some j =>
        if cs[j + 1]? == some '(' then
          if let some k := closeOf cs (j + 1) ')' then
            i := k + 1
            continue
      | none => pure ()
    -- `[text](target)`: the text stays.
    if c == '[' then
      if let some j := closeOf cs i ']' then
        if cs[j + 1]? == some '(' then
          if let some k := closeOf cs (j + 1) ')' then
            out := out ++ (plainText (String.ofList (cs.extract (i + 1) j).toList)).toList.toArray
            i := k + 1
            continue
    -- `<https://…>`: an autolink, unwrapped.
    if c == '<' then
      if let some j := closeOf cs i '>' then
        let inner := String.ofList (cs.extract (i + 1) j).toList
        if inner.startsWith "http://" || inner.startsWith "https://" then
          out := out ++ inner.toList.toArray
          i := j + 1
          continue
    if c == '*' || c == '`' then
      i := i + 1
      continue
    out := out.push c
    i := i + 1
  return collapseWhitespace (String.ofList out.toList)
where
  /-- The index of the `close` that ends the bracket opened at `i`, on the same text. -/
  closeOf (cs : Array Char) (i : Nat) (close : Char) : Option Nat := Id.run do
    let opener := cs[i]!
    let mut depth := 0
    let mut j := i
    while j < cs.size do
      if cs[j]! == opener then depth := depth + 1
      else if cs[j]! == close then
        depth := depth - 1
        if depth == 0 then return some j
      j := j + 1
    return none

/-- A block that carries no prose: lines of pictures and badges only, HTML, tables and rules. -/
private def isDecoration (block : Array String) : Bool :=
  block.all fun line =>
    let t := trimText line
    t.startsWith "<" || t.startsWith "|" || isSetextUnderline t || (plainText t).isEmpty

/-- The longest description kept, in characters; a longer one is cut at a word. -/
def maxDescriptionLength : Nat := 600

private def shorten (s : String) : String :=
  if s.length ≤ maxDescriptionLength then s
  else
    let cut := (s.take maxDescriptionLength).copy
    let words := cut.splitOn " "
    let kept := if words.length > 1 then " ".intercalate words.dropLast else cut
    kept ++ "…"

/-- The first heading and the first paragraph of prose of a Markdown README. Headings, fenced
and indented code, HTML, tables and badge lines are skipped; the paragraph is plain text. -/
def summarize (text : String) : Option String × Option String := Id.run do
  let lines := (text.splitOn "\n").map fun l =>
    String.ofList (l.toList.reverse.dropWhile (· == '\r')).reverse
  let mut title : Option String := none
  let mut block : Array String := #[]
  let mut inFence := false
  let mut rest := lines
  -- Walk the lines, closing a block at each blank line, heading or fence.
  let mut blocks : Array (Array String) := #[]
  while true do
    match rest with
    | [] => break
    | line :: tail =>
      rest := tail
      if inFence then
        if isFence line then inFence := false
        continue
      if isFence line then
        if !block.isEmpty then blocks := blocks.push block
        block := #[]
        inFence := true
        continue
      if isHeading line then
        if !block.isEmpty then blocks := blocks.push block
        block := #[]
        if title.isNone then title := some (plainText (headingText line))
        continue
      if trimText line |>.isEmpty then
        if !block.isEmpty then blocks := blocks.push block
        block := #[]
        continue
      -- A setext heading: the block so far is a heading, not prose.
      if isSetextUnderline line && block.size == 1 then
        if title.isNone then title := some (plainText (trimText block[0]!))
        block := #[]
        continue
      -- Indented code outside a paragraph.
      if block.isEmpty && (line.startsWith "    " || line.startsWith "\t") then
        continue
      block := block.push line
  if !block.isEmpty then blocks := blocks.push block
  let paragraph? := blocks.find? (!isDecoration ·)
  let description := paragraph?.bind fun paragraph =>
    let lines := paragraph.map fun line =>
      let t := trimText line
      if t.startsWith ">" then trimText ((t.drop 1).copy) else t
    let text := shorten (plainText (" ".intercalate lines.toList))
    if text.isEmpty then none else some text
  return (title, description)

end Readme

/-! ## License -/

/-- The SPDX identifier a license text most likely carries, from phrases every copy of that
license contains. An `SPDX-License-Identifier:` line wins. GNU licenses get the version's
identifier without `-only` or `-or-later`, since the license text alone does not say which. -/
def guessSpdx (text : String) : Option String := Id.run do
  for line in text.splitOn "\n" do
    let t := trimText line
    if t.startsWith "SPDX-License-Identifier:" then
      let id := trimText ((t.drop "SPDX-License-Identifier:".length).copy)
      if !id.isEmpty then return some id
  let t := collapseWhitespace text.toLower
  let has (phrase : String) := (t.splitOn phrase).length > 1
  if has "apache license" && has "version 2.0" then return some "Apache-2.0"
  if has "permission is hereby granted, free of charge" then return some "MIT"
  if has "gnu affero general public license" then return some "AGPL-3.0"
  if has "gnu lesser general public license" then
    return some (if has "version 3" then "LGPL-3.0" else "LGPL-2.1")
  if has "gnu general public license" then
    return some (if has "version 3" then "GPL-3.0" else "GPL-2.0")
  if has "mozilla public license" && has "2.0" then return some "MPL-2.0"
  if has "eclipse public license" && has "2.0" then return some "EPL-2.0"
  if has "redistribution and use in source and binary forms" then
    return some (if has "neither the name" || has "may be used to endorse or promote" then
      "BSD-3-Clause" else "BSD-2-Clause")
  if has "this is free and unencumbered software released into the public domain" then
    return some "Unlicense"
  if has "permission to use, copy, modify, and/or distribute this software for any purpose" then
    return some "ISC"
  if has "cc0 1.0 universal" then return some "CC0-1.0"
  if has "attribution 4.0 international" then return some "CC-BY-4.0"
  return none

/-! ## Lake manifest -/

/-- A repository address without the user name or password it may carry. -/
def stripUserInfo (url : String) : String :=
  match url.splitOn "://" with
  | [scheme, rest] =>
    let (host, path) :=
      match rest.splitOn "/" with
      | [] => ("", "")
      | host :: path => (host, "/".intercalate path)
    let host := (host.splitOn "@").getLast!
    let path := if path.isEmpty && !rest.contains '/' then "" else "/" ++ path
    s!"{scheme}://{host}{path}"
  | _ => url

/-- The root package name and the locked packages of a Lake manifest. -/
def parseManifest (text : String) : Option String × Array ManifestPackage := Id.run do
  let .ok json := Json.parse text | return (none, #[])
  let str (j : Json) (field : String) : Option String :=
    match j.getObjValAs? String field with
    | .ok value => if value.isEmpty then none else some value
    | .error _ => none
  let packages := match json.getObjVal? "packages" with
    | .ok (.arr packages) => packages
    | _ => #[]
  let packages := packages.filterMap fun pkg => do
    let name ← str pkg "name"
    let source := (str pkg "type").getD "git"
    some {
      name, source
      rev := str pkg "rev"
      inputRev := str pkg "inputRev"
      url := (str pkg "url").map stripUserInfo
      dir := str pkg "dir"
      inherited := (pkg.getObjValAs? Bool "inherited").toOption.getD false
    }
  return (str json "name", packages)

/-! ## Reading a project root -/

/-- README file names, most preferred first; matched without regard to case. -/
def readmeNames : Array String := #["README.md", "README.markdown", "README", "README.txt"]

/-- License file names, most preferred first; matched without regard to case. -/
def licenseNames : Array String :=
  #["LICENSE", "LICENSE.md", "LICENSE.txt", "LICENCE", "LICENCE.md", "LICENCE.txt", "COPYING",
    "COPYING.md", "COPYING.txt", "UNLICENSE"]

/-- The first file of `root` whose name matches one of `names` without regard to case. -/
private def findRootFile (root : System.FilePath) (names : Array String) :
    IO (Option String) := do
  let entries ← try root.readDir catch _ => pure #[]
  let files ← entries.filterM fun entry => do
    try return (← entry.path.metadata).type == .file catch _ => return false
  for name in names do
    if let some entry := files.find? (·.fileName.toLower == name.toLower) then
      return some entry.fileName
  return none

private def readFile? (path : System.FilePath) : IO (Option String) := do
  try some <$> IO.FS.readFile path catch _ => pure none

/-- Read a project's identity from the files at `root`. Missing or unreadable files leave
their fields empty. -/
def ProjectIdentity.read (root : System.FilePath) : IO ProjectIdentity := do
  let readme ← findRootFile root readmeNames
  let (title, description) ← match readme with
    | some file => pure <| ((← readFile? (root / file)).map Readme.summarize).getD (none, none)
    | none => pure (none, none)
  let license ← match ← findRootFile root licenseNames with
    | some file => pure <| some { file, spdx := (← readFile? (root / file)).bind guessSpdx }
    | none => pure none
  let toolchain := (← readFile? (root / "lean-toolchain")).map trimText |>.filter (!·.isEmpty)
  let (name, packages) :=
    ((← readFile? (root / "lake-manifest.json")).map parseManifest).getD (none, #[])
  return { name, readme, title, description, license, toolchain, packages }

end Informal.Stats
