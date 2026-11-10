/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

import VersoBlueprintTests.Blueprint.Support
import VersoBlueprint.LeanSourceAnchor

namespace Verso.VersoBlueprintTests.BlueprintLeanSourceAnchors

open Lean
open Verso
open Verso.Genre.Manual
open Informal
open Verso.VersoBlueprintTests.Blueprint.Support

set_option doc.verso true

private def manualImpls : ExtensionImpls := extension_impls%

/-- A definition whose source range is known to the anchor test. -/
def anchorSquare (n : Nat) : Nat := n * n

/-- A theorem with a non-ASCII name, to check percent-encoding of jump links. -/
theorem anchorSquare_nonneg' (n : Nat) : 0 ≤ anchorSquare n := Nat.zero_le _

#docs (Genre.Manual) anchorDoc "Anchor Doc" :=
:::::::
:::definition "def:anchor.square" (lean := "Verso.VersoBlueprintTests.BlueprintLeanSourceAnchors.anchorSquare")
The square.
:::

:::theorem "thm:anchor.nonneg" (lean := "Verso.VersoBlueprintTests.BlueprintLeanSourceAnchors.anchorSquare_nonneg'") (uses := "def:anchor.square")
Squares are nonnegative.
:::

:::proof "thm:anchor.nonneg"
Trivial.
:::
:::::::

private def squareName : String := "Verso.VersoBlueprintTests.BlueprintLeanSourceAnchors.anchorSquare"

private def nonnegName : String := "Verso.VersoBlueprintTests.BlueprintLeanSourceAnchors.anchorSquare_nonneg'"

/-- The module path of the test module itself (the declarations are in the main module). -/
private def modulePath : String := "VersoBlueprintTests/BlueprintLeanSourceAnchors.lean"

/-- info: true -/
#guard_msgs in
#eval
  LeanSourceAnchor.modulePath `Mathlib.Order.Basic == "Mathlib/Order/Basic.lean" &&
  LeanSourceAnchor.declHref `Foo.bar == "lean:decl/Foo.bar" &&
  LeanSourceAnchor.declHref `Foo.«bar≤» == "lean:decl/Foo.%C2%ABbar%E2%89%A4%C2%BB" &&
  LeanSourceAnchor.sourceHref "A/B.lean" 3 4 == "lean:source/A/B.lean:3:4" &&
  LeanSourceAnchor.formatSource "A/B.lean"
      { pos := ⟨2, 4⟩, charUtf16 := 3, endPos := ⟨5, 1⟩, endCharUtf16 := 1 } ==
    "A/B.lean:2:3-5:1"

/-- info: true -/
#guard_msgs in
#eval
  let missing : Data.ExternalRef := { Data.ExternalRef.ofName `Missing.decl with present := false }
  let located : Data.ExternalRef := {
    Data.ExternalRef.ofName `Located.decl with
      provenance := .inWorkspace `Located.Module "/abs/Located/Module.lean"
      range? := some { pos := ⟨10, 0⟩, charUtf16 := 0, endPos := ⟨12, 7⟩, endCharUtf16 := 7 } }
  LeanSourceAnchor.rootAttrs #[missing, located, located] ==
      #[("data-lean-decls", "Missing.decl Located.decl")] &&
    LeanSourceAnchor.declAttrs missing == #[("data-lean-decl", "Missing.decl")] &&
    LeanSourceAnchor.declAttrs located ==
      #[("data-lean-decl", "Located.decl"), ("data-lean-source", "Located/Module.lean:10:0-12:7")] &&
    LeanSourceAnchor.rootAttrs #[] == #[]

-- The rendered page carries the anchors on node roots, declaration rows, and the panel heading.
-- The source range of a declaration starts at its doc comment (line 22 of this file).
/-- info: true -/
#guard_msgs in
#eval
  show IO Bool from do
    let out ← renderManualDocHtmlString manualImpls anchorDoc
    pure (
      hasSubstr out s!"data-lean-decls=\"{squareName}\"" &&
      hasSubstr out s!"data-lean-decls=\"{nonnegName}\"" &&
      countSubstr out s!"data-lean-decl=\"{squareName}\"" == 2 &&
      hasSubstr out s!"data-lean-source=\"{modulePath}:22:0-23:41\"" &&
      hasSubstr out s!"data-lean-source=\"{modulePath}:25:0-26:76\"" &&
      hasSubstr out s!"href=\"lean:decl/{squareName}\"" &&
      hasSubstr out s!"href=\"lean:decl/{nonnegName}\"" &&
      countSubstr out "class=\"bp_lean_jumps\"" == 2 &&
      -- only `lean:decl/` links are generated (positions live in `data-lean-source`)
      !hasSubstr out "lean:source/"
    )

end Verso.VersoBlueprintTests.BlueprintLeanSourceAnchors
