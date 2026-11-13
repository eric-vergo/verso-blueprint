/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

import VersoManual
import VersoBlueprint.Axioms
import VersoBlueprint.Informal.Block.Render
import VersoBlueprint.LeanSourceAnchor

/-!
The node view: one Blueprint node as a unit, the informal statement beside its
Lean declarations.

The dependency graph shows it when a node is clicked. It is built from plain
data (`NodeView`), so any generator can render the same view: a Blueprint site
fills it from its traversal, a site generated from compiled Lean code fills it
from the environment.

Layout rules:

* the informal statement is the left column when the node has one, with its
  informal proof folded below it;
* the Lean column is on the right whenever the node has Lean declarations;
* a node with only one of the two shows it full width (`bp_sbs_single`), never
  an empty column;
* the header carries the node's title (a link to the node in its chapter), its
  status glyph and status text, and a link to the node's neighbourhood in the
  dependency graph (`#ego=<label>`, the graph page's ego view); a footer lists the nodes it uses and the nodes
  that use it, each a link carrying `data-bp-node-link` so a viewer can switch
  to that node's view in place, and the axioms its declarations depend on,
  each marked with its class (`Informal.Data.AxiomClass`): a `sorry`, an extra
  axiom and a proof that trusts compiled code come first, the standard axioms
  last, and "none" when the declarations use no axiom at all.

The markup reuses the side-by-side classes (`bp_sbs`, `bp_sbs_grid`,
`bp_sbs_informal`, `bp_sbs_formal`), so the view looks like a side-by-side node
on a chapter page and follows the page's light and dark theme. It uses plain
`div` elements only: page styles position `header` and `footer` elements.
-/

namespace Informal.NodeView

open Verso.Output.Html

/-- A link from a node view to another node. -/
structure Link where
  /-- The other node's label (`data-bp-node-link`). -/
  label : String
  /-- Display text, such as `Lemma 2.3`. -/
  title : String
  /-- The other node on its chapter page (site-relative), if it has one. -/
  href? : Option String := none
deriving Inhabited, Repr

/-- One node, ready to render. -/
structure NodeView where
  /-- The node's label (`data-bp-node-view`). -/
  label : String
  /-- Display title, such as `Theorem 5.2.3`. -/
  title : String
  /-- The node on its chapter page (site-relative), if it has one. -/
  href? : Option String := none
  /-- Status glyph and its meaning, with details (for example where the `sorry` is). -/
  status : StatusGlyphKind × String := (.noLean, StatusGlyphKind.noLean.meaning)
  /-- The informal statement; `none` (or blank) when the node has no prose. -/
  informal? : Option Verso.Output.Html := none
  /-- The informal proof, shown folded below the statement. -/
  proof? : Option Verso.Output.Html := none
  /-- The Lean column: one part per defining command or declaration. -/
  lean : Array Verso.Output.Html := #[]
  /-- The node's Lean declarations, in authoring order (`data-lean-decls`). -/
  leanDecls : Array Lean.Name := #[]
  /-- Axioms the node's declarations depend on, when the generator knows them (`none`: unknown,
  no row; `some #[]`: the row says none). -/
  axioms? : Option (Array Lean.Name) := none
  /-- Nodes this node uses (statement and proof). -/
  uses : Array Link := #[]
  /-- Nodes that use this node. -/
  usedBy : Array Link := #[]
deriving Inhabited

/-- The link to a node's neighbourhood on the dependency graph's page (its ego view):
`#ego=<label>`, the label percent-encoded. -/
def egoHref (label : String) : String :=
  "#ego=" ++ LeanSourceAnchor.percentEncode label

/-- Whether the view has an informal column (prose that is not blank). -/
def NodeView.hasInformal (v : NodeView) (isBlank : Verso.Output.Html → Bool) : Bool :=
  v.informal?.any (!isBlank ·)

private def linkHtml (l : Link) : Verso.Output.Html :=
  let attrs := #[("class", "bp_node_view_link"), ("data-bp-node-link", l.label), ("title", l.label)]
  match l.href? with
  | some href => .tag "a" (#[("href", href)] ++ attrs) (.text true l.title)
  | none => .tag "span" attrs (.text true l.title)

private def relationRow (caption : String) (links : Array Link) : Verso.Output.Html :=
  if links.isEmpty then .empty else
  let items : Array Verso.Output.Html := links.map fun l => {{<li>{{linkHtml l}}</li>}}
  {{<div class="bp_node_view_relation"><span class="bp_node_view_relation_caption">{{caption}}</span><ul>{{items}}</ul></div>}}

/-- The visible tag beside an axiom that limits trust; the standard axioms have none. -/
private def axiomTag : Data.AxiomClass → Option String
  | .standard => none
  | .sorryAx => some "sorry"
  | .compilerTrusted => some "trusts compiled code"
  | .other => some "extra axiom"

private def axiomItem (a : Lean.Name) : Verso.Output.Html :=
  let cls := Data.AxiomClass.ofName a
  let tag : Verso.Output.Html := match axiomTag cls with
    | some t => .seq #[.text true " ", .tag "span" #[("class", "bp_axiom_tag")] (.text true t)]
    | none => .empty
  .tag "li" #[("class", s!"bp_axiom bp_axiom_{cls.token}"), ("data-bp-axiom-class", cls.token),
      ("title", cls.description)]
    (.seq #[.tag "code" #[] (.text true a.toString), tag])

private def axiomsRow : Option (Array Lean.Name) → Verso.Output.Html
  | none => .empty
  | some axioms =>
    let items : Array Verso.Output.Html := if axioms.isEmpty then
        #[.tag "li" #[("class", "bp_axiom bp_axiom_none")] (.text true "none")]
      else (Data.sortAxioms axioms).map axiomItem
    {{<div class="bp_node_view_relation bp_node_view_axioms"><span class="bp_node_view_relation_caption">"Axioms"</span><ul>{{items}}</ul></div>}}

/--
Render a node view. `isBlank` decides whether the informal statement counts as
prose (generators pass their own blank test for rendered fragments).
-/
def NodeView.render (v : NodeView) (isBlank : Verso.Output.Html → Bool := fun _ => false) :
    Verso.Output.Html :=
  let (glyph, statusText) := v.status
  let titleHtml : Verso.Output.Html :=
    match v.href? with
    | some href => {{<a class="bp_node_view_title" href={{href}}>{{v.title}}</a>}}
    | none => {{<span class="bp_node_view_title">{{v.title}}</span>}}
  let glyphHtml : Verso.Output.Html :=
    .tag "span" #[("class", s!"bp_status_glyph bp_status_glyph_{glyph.modifier}"),
      ("title", statusText), ("aria-hidden", "true")] (.text true glyph.glyph)
  let egoHtml : Verso.Output.Html :=
    .tag "a" #[("class", "bp_node_view_ego"), ("href", egoHref v.label),
      ("data-bp-ego-link", v.label),
      ("title", "Show what this node uses and what uses it in the dependency graph")]
      (.text true "Neighbourhood")
  let header := {{
    <div class="bp_node_view_header">
      {{titleHtml}}{{glyphHtml}}<span class="bp_node_view_status">{{statusText}}</span>{{egoHtml}}
    </div>}}
  let proof := v.proof?.bind fun h => if isBlank h then none else some h
  let informal := if v.hasInformal isBlank then v.informal?.map fun h =>
      match proof with
      | some p => .seq #[h, {{<details class="bp_node_view_proof"><summary>"Proof"</summary>{{p}}</details>}}]
      | none => h
    else none
  let lean := if v.lean.isEmpty then none else some (Verso.Output.Html.seq v.lean)
  let columns : Array Verso.Output.Html :=
    (informal.map fun h => {{<div class="bp_sbs_informal">{{h}}</div>}}).toArray ++
    (lean.map fun h => {{<div class="bp_sbs_formal">{{h}}</div>}}).toArray
  let layout :=
    if informal.isSome && lean.isSome then "both"
    else if lean.isSome then "lean" else "informal"
  let bodyClass := if columns.size == 2 then "bp_sbs bp_node_view_body"
    else "bp_sbs bp_sbs_single bp_node_view_body"
  let names := v.leanDecls.foldl (init := #[]) fun acc n =>
    let t := LeanSourceAnchor.declText n
    if acc.contains t then acc else acc.push t
  let declAttrs := if names.isEmpty then #[] else
    #[("data-lean-decls", String.intercalate " " names.toList)]
  let footer :=
    if v.uses.isEmpty && v.usedBy.isEmpty && v.axioms?.isNone then .empty
    else {{<div class="bp_node_view_relations">{{relationRow "Uses" v.uses}}{{
      relationRow "Used by" v.usedBy}}{{axiomsRow v.axioms?}}</div>}}
  .tag "article" (#[("class", "bp_node_view"), ("data-bp-node-view", v.label),
      ("data-bp-node-view-layout", layout)] ++ declAttrs)
    (.seq #[header,
      {{<div class={{bodyClass}}><div class="bp_sbs_grid">{{columns}}</div></div>}}, footer])

end Informal.NodeView
