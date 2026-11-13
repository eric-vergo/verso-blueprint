/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

import VersoManual

/-!
Search entries for the declarations of a site generated from compiled code.

A generated site renders each declaration from data (`Informal.CodeSite`), not from a
`{docstring}` block, so neither Verso's quick search nor its full-text index would see the
declarations. `Block.declSearch` gives each declaration the entries a documented Lean constant
has on a Verso manual site: its name in the documentation domain (the search box's
"Documentation" results, jumping to the declaration on its module's page) and its name,
signature and docstring in the full-text index (the block's contents, which are indexed but
not rendered: the declaration's card shows them).
-/

namespace Informal.CodeSite

open Lean
open Verso Doc Genre Manual

-- A declaration's search entries (see the module docstring); `name` is the declaration. The
-- contents are indexed for full-text search and not rendered; the block renders as an anchor the
-- quick search jumps to.
open Verso Doc Elab Genre Manual in
block_extension Block.declSearch (name : Name) where
  data := toJson name
  traverse id data _contents := do
    let .ok (name : Name) := fromJson? data | return none
    let path ← (·.path) <$> read
    let _ ← Verso.Genre.Manual.externalTag id path name.toString
    modify (·.saveDomainObject docstringDomain name.toString id)
    return none
  toTeX := some fun _goI _goB _id _data _contents => pure .empty
  toHtml := some fun _goI _goB id _data _contents => do
    let xref ← Verso.Doc.Html.HtmlT.state
    return .tag "span" ((xref.htmlId id).push ("class", "bp_code_site_anchor")) .empty

end Informal.CodeSite
