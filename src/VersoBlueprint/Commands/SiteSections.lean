/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

import VersoManual
import VersoBlueprint.Meaning

/-!
The sections of a site as Verso's section domain records them after traversal, and the addresses
of the site's own pages read from them: the Project Stats page and the explanation of the marks
on it (`meaningHref?`), which any page may link to.
-/

namespace Informal.Commands

open Lean
open Verso Genre Manual

/-- The title of the Project Stats page in the table of contents. -/
def statsPageTitle : String := "Project Stats"

/-- A section of the site as Verso's section domain records it. -/
structure SiteSection where
  title : String
  number : Option String := none
  link : Verso.Multi.Link
  /-- How many headers enclose it, itself and the document's root included. -/
  depth : Nat
deriving Inhabited

/-- Every section of the site that has an address. -/
def siteSections (state : TraverseState) : Array SiteSection :=
  match state.domains.get? sectionDomain with
  | Option.none => #[]
  | some domain => domain.objects.foldl (init := #[]) fun acc _ obj =>
    let title? := (obj.data.getObjValAs? String "title").toOption
    let number := (obj.data.getObjValAs? String "sectionNum").toOption
    let depth := ((obj.data.getObjValAs? (Array Json) "context").toOption.map (·.size)).getD 0
    let link? := obj.ids.toArray.foldl (init := none) fun found id =>
      found <|> state.externalTags[id]?
    match title?, link? with
    | some title, some link => acc.push { title, number, link, depth }
    | _, _ => acc

/-- The outermost section of the page in directory `dir` (a chapter's own heading). -/
def chapterSection? (sections : Array SiteSection) (dir : String) : Option SiteSection :=
  sections.foldl (init := none) fun best s =>
    if s.link.path != #[dir] then best
    else match best with
      | some b => if s.depth < b.depth then some s else some b
      | Option.none => some s

/-- The outermost section with the given title, such as the summary page. -/
def pageSection? (sections : Array SiteSection) (title : String) : Option SiteSection :=
  sections.foldl (init := none) fun best s =>
    if s.title != title then best
    else match best with
      | some b => if s.depth < b.depth then some s else some b
      | Option.none => some s

/-- The address of the explanation of the marks, the Project Stats page's anchor, when the site
has the page. Pages resolve it against their `<base href>`, the site's root, so it serves every
page, the Project Stats page included. -/
def meaningHref? (state : TraverseState) : Option String :=
  (pageSection? (siteSections state) statsPageTitle).map fun s =>
    String.join (s.link.path.toList.map (· ++ "/")) ++ "#" ++ Informal.Meaning.anchor

end Informal.Commands
