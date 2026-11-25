/- 
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Emilio J. Gallego Arias
-/

import Lean
import VersoManual
import VersoBlueprint.PreviewCache

/-!
Shared link-resolution policies for Blueprint renderers.

Most callers should not need to know which Verso traversal domain stores a
target. This module gives them small, named policies instead: resolve a plain
domain object, resolve an inline Lean declaration, or resolve the best link for
an informal block's Lean declaration.
-/

namespace Informal.Resolve

open Lean

def informalDomainName : Name := Name.mkSimple "Informal.Block.informal"
def informalCodeDomainName : Name := Name.mkSimple "Informal.Block.informalCode"
def informalRustCodeDomainName : Name := Name.mkSimple "Informal.Block.informalRustCode"
/-- Traversal domain for declared source documents. -/
def sourceDocumentDomainName : Name := Name.mkSimple "Informal.Source.document"
/--
Traversal domain for external-markup attachments.

This is a semantic domain, not a rendered-preview cache. `Block.externalMarkup`
stores one object per Blueprint label here so later `tex`/`md` witness blocks
can merge by label during traversal. Manifest construction reads this domain to
attach markup to preview-backed block entries, or to emit semantic-only
`externalMarkup` entries for witness-only labels.
-/
def externalMarkupDomainName : Name := Name.mkSimple "Informal.Block.externalMarkup"
def informalPreviewDomainName : Name := Name.mkSimple "Informal.Block.informalPreview"
def informalGroupDomainName : Name := Name.mkSimple "Informal.Block.group"
def graphDomainName : Name := Name.mkSimple "Informal.Block.graph"
/- 
Domain that stores anchors for rendered external declaration rows.

We intentionally keep this separate from `inlineLeanDeclDomainName`: inline Lean links are
declaration-anchor-centric (one destination per declaration), while rendered external rows are
occurrence-centric (one destination per visible code occurrence and canonical declaration).
A label-level fallback names the first visible code row when the selected statement
does not display code. This allows summary/graph UI to jump to a rendered instance, even when the same declaration
is referenced by many blueprint entries. A declaration attached to a proof that shows no rows of
its declarations (the side-by-side layout), and not to the node's statement, has as fallback the
declaration's one place in the site (`Informal.TraversalIndex.ExternalDeclAnchors.placeTarget?`),
so that the first of a declaration's fallback keys in string order that resolves names that place.
Inline preview bodies themselves are keyed by the owning source code-block identity.
-/
def externalRenderedDeclDomainName : Name := Name.mkSimple "Informal.Block.externalRenderedDecl"
def bibliographyDomainName : Name := Name.mkSimple "Informal.Block.bpCitations"
def citationPreviewDomainName : Name := Name.mkSimple "Informal.Inline.bpCite.previews"
def citationUsageDomainName : Name := Name.mkSimple "Informal.Inline.bpCite.usages"
/--
Domain that stores declaration anchors for inline Lean code.

Blueprint code blocks currently elaborate via `Verso.Genre.Manual.InlineLean.Block.lean`,
which registers defined declarations in the Manual `example` domain through
`Verso.Genre.Manual.saveExampleDefs`. We intentionally reuse that index here.
-/
def inlineLeanDeclDomainName : Name := ``Verso.Genre.Manual.example

/--
Key for one rendered external declaration target.

The `decl` input should be canonicalized by callers (for example using `ExternalRef.canonical`).
-/
def externalRenderedDeclTargetKey (occurrence : Verso.Multi.InternalId) (decl : Name) : String :=
  s!"{(toJson occurrence).compress}|{decl}"

/-- First visible code row, independent of the selected prose occurrence. -/
def externalRenderedDeclFallbackKey (label decl : Name) : String :=
  s!"label:{label}|{decl}"

def resolveDomainHref? (s : Verso.Genre.Manual.TraverseState) (domain : Name) (label : String) :
    Option String :=
  match s.resolveDomainObject domain label with
  | .ok dest => some dest.relativeLink
  | .error _ => none

def resolveDomainHrefs (s : Verso.Genre.Manual.TraverseState) (domain : Name) (label : String) :
    Array String :=
  match s.getDomainObject? domain label with
  | none => #[]
  | some obj =>
    let hrefs := obj.ids.toArray.filterMap fun id =>
      (s.externalTags[id]?).map (·.relativeLink)
    hrefs.qsort (fun a b => a < b)

/--
The key of the inline Lean anchor of `decl`: its own name, else the one key of the form
`decl (in …)` (a declaration defined in a named example).
-/
def inlineLeanDeclKey? (s : Verso.Genre.Manual.TraverseState) (decl : Name) : Option String := do
  let dom ← s.domains.get? inlineLeanDeclDomainName
  if dom.objects.contains decl.toString then return decl.toString
  let pref := decl.toString ++ " (in "
  let cands := dom.objects.foldl (init := #[]) fun acc key _obj =>
    if key.startsWith pref then acc.push key else acc
  if cands.size = 1 then cands[0]? else none

def resolveInlineLeanDeclHref? (s : Verso.Genre.Manual.TraverseState) (decl : Name) : Option String :=
  (inlineLeanDeclKey? s decl).bind (resolveDomainHref? s inlineLeanDeclDomainName ·)

/-- The one target of the inline Lean anchor of `decl` (`inlineLeanDeclKey?`). -/
def inlineLeanDeclId? (s : Verso.Genre.Manual.TraverseState) (decl : Name) :
    Option Verso.Multi.InternalId := do
  let obj ← s.getDomainObject? inlineLeanDeclDomainName (← inlineLeanDeclKey? s decl)
  match obj.ids.toList with
  | [id] => some id
  | _ => none

def resolveRenderedExternalDeclHref? (s : Verso.Genre.Manual.TraverseState)
    (label decl : Name) : Option String :=
  (do
    let selected ← s.getDomainObject? informalPreviewDomainName (PreviewCache.key label .statement)
    let occurrence ← (selected.data.getObjValAs? (Option Verso.Multi.InternalId) "target").toOption.join
    resolveDomainHref? s externalRenderedDeclDomainName (externalRenderedDeclTargetKey occurrence decl)) <|>
  resolveDomainHref? s externalRenderedDeclDomainName (externalRenderedDeclFallbackKey label decl)

/--
Resolve a Lean declaration link as seen from one informal block.

If the block rendered the declaration in its external-code panel, prefer that
row: it lands the reader on the concrete code that the block is discussing.
If no row was registered, fall back to the ordinary inline-Lean declaration
anchor shared by the rest of the document. Renderers use
`Informal.TraversalIndex.ExternalDeclAnchors.declHref?`, which adds the declaration's one place in
the site.
-/
def resolveInformalDeclHref? (s : Verso.Genre.Manual.TraverseState)
    (label decl : Name) : Option String :=
  match resolveRenderedExternalDeclHref? s label decl with
  | some href => some href
  | none => resolveInlineLeanDeclHref? s decl

end Informal.Resolve
