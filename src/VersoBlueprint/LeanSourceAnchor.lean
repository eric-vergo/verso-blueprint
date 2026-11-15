/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

import VersoBlueprint.Data

/-!
Machine-readable Lean source anchors in generated Blueprint HTML.

Embedding viewers (an editor that shows the Blueprint next to the code, for
example) need to go from a rendered node to the Lean declarations behind it and
back, without scraping presentation markup. The anchors are plain HTML
attributes and links:

* `data-lean-decls="<Name1> <Name2>"` on the root element of every node facet
  that has associated Lean declarations;
* `data-lean-decl="<Name>"` and, when the source location is known,
  `data-lean-source="<path>:<startLine>:<startCol>-<endLine>:<endCol>"` on the
  element that renders one declaration;
* jump links `lean:decl/<Name>` in the Lean code panel heading (the only form
  generated pages contain: a name survives edits of the Lean file after the
  build, a position does not). `sourceHref` builds the
  `lean:source/<path>:<line>:<col>` form from a `data-lean-source` location for
  custom generators and viewers.

`<path>` is the declaring module's source path relative to its package source
directory (`Mathlib/Order/Basic.lean` for `Mathlib.Order.Basic`), lines are
1-based and columns are 0-based UTF-16 code units, as in the Language Server
Protocol. Names are printed as Lean prints them.
-/

namespace Informal.LeanSourceAnchor

open Lean

/-- The source path of a module relative to its package source directory. -/
def modulePath (moduleName : Name) : String :=
  String.intercalate "/" (moduleName.components.map (·.toString (escape := false))) ++ ".lean"

/-- A declaration name as it appears in anchors. -/
def declText (decl : Name) : String :=
  decl.toString

/-- Format a range as `<path>:<startLine>:<startCol>-<endLine>:<endCol>`. -/
def formatSource (path : String) (range : DeclarationRange) : String :=
  s!"{path}:{range.pos.line}:{range.charUtf16}-{range.endPos.line}:{range.endCharUtf16}"

/-- The `data-lean-source` value of a declaration, when its module and range are known. -/
def source? (decl : Data.ExternalRef) : Option String := do
  guard decl.present
  let moduleName ← decl.provenance.moduleName?
  let range ← decl.range?
  guard (range.pos.line > 0)
  pure <| formatSource (modulePath moduleName) range

private def isUnreserved (c : Char) : Bool :=
  c.isAlphanum || c == '.' || c == '_' || c == '~' || c == '-' || c == '\'' || c == '!' ||
    c == '/' || c == ':'

private def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (55 + n)

/-- Percent-encode everything outside the unreserved ASCII set (UTF-8 for non-ASCII). -/
def percentEncode (text : String) : String :=
  text.foldl (init := "") fun out c =>
    if c.toNat < 128 && isUnreserved c then
      out.push c
    else
      (String.singleton c).toUTF8.foldl (init := out) fun out byte =>
        (out.push '%').push (hexDigit (byte.toNat / 16)) |>.push (hexDigit (byte.toNat % 16))

/-- The jump link to a declaration: `lean:decl/<Name>` (percent-encoded). -/
def declHref (decl : Name) : String :=
  "lean:decl/" ++ percentEncode (declText decl)

/-- The jump link to a source position: `lean:source/<path>:<line>:<col>` (percent-encoded). -/
def sourceHref (path : String) (line col : Nat) : String :=
  "lean:source/" ++ percentEncode s!"{path}:{line}:{col}"

/-- The jump link to the start of a declaration's source, when known. -/
def declSourceHref? (decl : Data.ExternalRef) : Option String := do
  guard decl.present
  let moduleName ← decl.provenance.moduleName?
  let range ← decl.range?
  guard (range.pos.line > 0)
  pure <| sourceHref (modulePath moduleName) range.pos.line range.charUtf16

/-- Attributes for the element that renders one declaration. -/
def declAttrs (decl : Data.ExternalRef) : Array (String × String) :=
  let attrs := #[("data-lean-decl", declText decl.canonical)]
  match source? decl with
  | some source => attrs.push ("data-lean-source", source)
  | none => attrs

/--
Attributes for a node facet's root element: `data-lean-decls` with every associated declaration,
including declarations that were missing when the Blueprint was built.
-/
def rootAttrs (decls : Array Data.ExternalRef) : Array (String × String) :=
  let names := decls.map (declText ·.canonical)
  let names := names.foldl (init := #[]) fun acc n => if acc.contains n then acc else acc.push n
  if names.isEmpty then #[] else #[("data-lean-decls", String.intercalate " " names.toList)]

end Informal.LeanSourceAnchor
