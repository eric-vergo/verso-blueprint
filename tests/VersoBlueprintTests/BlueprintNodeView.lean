/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

import VersoBlueprintTests.Blueprint.Support
import VersoBlueprint.DeclarationSource
import VersoBlueprint.Informal.NodeView
import VersoBlueprint.PreviewManifest

namespace Verso.VersoBlueprintTests.BlueprintNodeView

open Lean
open Verso
open Verso.Genre.Manual
open Informal
open SubVerso.Highlighting
open Verso.VersoBlueprintTests.Blueprint.Support

set_option doc.verso true

private def manualImpls : ExtensionImpls := extension_impls%

private def view : NodeView.NodeView := {
  label := "thm:x"
  title := "Theorem 1.2"
  href? := some "Chapter/#thm-x"
  status := (.proved, "Proved in Lean")
  informal? := some (.text true "Every x is fine.")
  lean := #[.tag "div" #[("class", "card")] (.text true "theorem x : True")]
  leanDecls := #[`Foo.x, `Foo.x]
  uses := #[{ label := "def:y", title := "Definition 1.1", href? := some "Chapter/#def-y" }]
  usedBy := #[{ label := "thm:z", title := "Theorem 2.1" }]
}

-- Both columns: the statement on the left, the Lean column on the right.
/-- info: true -/
#guard_msgs in
#eval
  let out := view.render.asString
  hasSubstr out "data-bp-node-view=\"thm:x\"" &&
    hasSubstr out "data-bp-node-view-layout=\"both\"" &&
    hasSubstr out "data-lean-decls=\"Foo.x\"" &&
    hasSubstr out "class=\"bp_sbs bp_node_view_body\"" &&
    appearsBefore out "class=\"bp_sbs_informal\"" "class=\"bp_sbs_formal\"" &&
    hasSubstr out "Every x is fine." && hasSubstr out "theorem x : True" &&
    hasSubstr out "href=\"Chapter/#thm-x\"" &&
    hasSubstr out "bp_status_glyph_proved" && hasSubstr out "Proved in Lean" &&
    hasSubstr out "data-bp-node-link=\"def:y\"" && hasSubstr out "href=\"Chapter/#def-y\"" &&
    hasSubstr out "data-bp-node-link=\"thm:z\"" &&
    appearsBefore out ">Uses<" ">Used by<" &&
    -- no `header` or `footer` elements: page styles position those
    !hasSubstr out "<header" && !hasSubstr out "<footer"

-- No prose: the Lean column alone, full width; never an empty informal column.
/-- info: true -/
#guard_msgs in
#eval
  let leanOnly := { view with informal? := none }.render.asString
  let blank := { view with informal? := some (.text true "  ") }.render.asString
  hasSubstr leanOnly "data-bp-node-view-layout=\"lean\"" &&
    hasSubstr leanOnly "class=\"bp_sbs bp_sbs_single bp_node_view_body\"" &&
    hasSubstr leanOnly "class=\"bp_sbs_formal\"" && !hasSubstr leanOnly "bp_sbs_informal" &&
    -- a proof without a statement is not shown on its own
    !hasSubstr { view with informal? := none, proof? := some (.text true "P") }.render.asString
      "bp_node_view_proof" &&
    -- a blank statement counts as none when the caller says what blank is
    hasSubstr ({ view with informal? := some (.text true "  ") }.render
        (isBlank := fun h => h.asString.trimAscii.isEmpty)).asString
      "data-bp-node-view-layout=\"lean\"" &&
    hasSubstr blank "data-bp-node-view-layout=\"both\""

-- No Lean declaration: the statement alone; axioms listed when the generator knows them.
/-- info: true -/
#guard_msgs in
#eval
  let prose := { view with lean := #[], leanDecls := #[], uses := #[], usedBy := #[] }.render.asString
  let axioms := { view with axioms := #["propext", "Classical.choice"] }.render.asString
  hasSubstr prose "data-bp-node-view-layout=\"informal\"" && !hasSubstr prose "bp_sbs_formal" &&
    !hasSubstr prose "data-lean-decls" && !hasSubstr prose "bp_node_view_relations" &&
    hasSubstr axioms ">Axioms<" && hasSubstr axioms "<code>Classical.choice</code>"

/-- A theorem stated in prose and in Lean. -/
theorem nodeViewTheorem : True := by
  trivial

-- A definition with no prose (no docstring): its node shows Lean only.
@[blueprint "def:nv.code"]
def nodeViewCodeOnly : Nat := 3

#docs (Genre.Manual) nodeViewDoc "Node View Doc" :=
:::::::
{blueprint_node "def:nv.code"}

:::theorem "thm:nv.both" (lean := "Verso.VersoBlueprintTests.BlueprintNodeView.nodeViewTheorem") (uses := "def:nv.code")
A true statement about $`3`.
:::

:::proof "thm:nv.both"
Immediate from the definition.
:::

:::lemma_ "lem:nv.prose" (uses := "thm:nv.both")
A statement with no Lean declaration yet.
:::

{blueprint_graph}
:::::::

private def thisModule : Name := `VersoBlueprintTests.BlueprintNodeView

private def theoremName : Name := `Verso.VersoBlueprintTests.BlueprintNodeView.nodeViewTheorem

private def tok (s : String) : Highlighted := .token ⟨.keyword none none none, s⟩

/-- The highlighted module data the generator would load from the Lake facet. -/
private def fakeModule : SubVerso.Module.Module := {
  items := #[{
    range := some (⟨74, 0⟩, ⟨76, 9⟩)
    kind := `Lean.Parser.Command.declaration
    defines := #[theoremName]
    code := .seq #[tok "theorem", .text " ", tok "nodeViewTheorem", .text " ", tok ":", .text " ",
      tok "True", .text " ", tok ":=", .text " ", tok "by", .text "\n  ", tok "trivial"]
  }]
}

private def viewOf (files : PreviewManifest.Files) (label : String) : String :=
  ((files.nodeViews.entries.find? (·.label == label)).map (·.html)).getD ""

-- The generator renders one view per graph node, with the highlighted source in the Lean column.
/-- info: true -/
#guard_msgs in
#eval
  show IO Bool from do
    DeclarationSource.clear
    DeclarationSource.insert thisModule fakeModule
    let files ← buildManualPreviewDataFiles manualImpls nodeViewDoc
    DeclarationSource.clear
    let both := viewOf files "«thm:nv.both»"
    let code := viewOf files "«def:nv.code»"
    let prose := viewOf files "«lem:nv.prose»"
    let cache := files.htmlCache.hoverDocs.map (·.id)
    pure (
      files.nodeViews.entries.size == 3 &&
      -- statement and Lean side by side: the source card, its hovers in the cache's table
      hasSubstr both "data-bp-node-view-layout=\"both\"" &&
      hasSubstr both "A true statement" &&
      -- the informal proof, folded below the statement
      appearsBefore both "A true statement" "<details class=\"bp_node_view_proof\">" &&
      hasSubstr both "Immediate from the definition." &&
      hasSubstr both "class=\"bp_decl_source bp_decl_source_theorem\"" &&
      hasSubstr both ">nodeViewTheorem<" &&
      hasSubstr both s!"data-lean-decls=\"{theoremName}\"" &&
      hasSubstr both "href=\"lean:decl/Verso.VersoBlueprintTests.BlueprintNodeView.nodeViewTheorem\"" &&
      hasSubstr both "data-bp-node-link=\"«def:nv.code»\"" &&
      hasSubstr both "data-bp-node-link=\"«lem:nv.prose»\"" &&
      !cache.isEmpty &&
      -- a code-only node: Lean alone (its signature row: no highlighted source loaded for it)
      hasSubstr code "data-bp-node-view-layout=\"lean\"" &&
      hasSubstr code "data-lean-decl=\"Verso.VersoBlueprintTests.BlueprintNodeView.nodeViewCodeOnly\"" &&
      !hasSubstr code "bp_sbs_informal" &&
      -- a statement without Lean: prose alone
      hasSubstr prose "data-bp-node-view-layout=\"informal\"" &&
      hasSubstr prose "A statement with no Lean declaration yet." &&
      !hasSubstr prose "bp_sbs_formal"
    )

end Verso.VersoBlueprintTests.BlueprintNodeView
