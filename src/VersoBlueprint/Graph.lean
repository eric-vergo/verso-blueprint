/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Emilio J. Gallego Arias
-/

import VersoBlueprint.Environment
import VersoBlueprint.Informal.Block.Model
import VersoBlueprint.Lib.HtmlId
import VersoBlueprint.Lib.PreviewKey
import VersoBlueprint.PreviewCache
import VersoBlueprint.CodeHealth
import VersoBlueprint.Replay
import VersoBlueprint.StatusColors

namespace Informal.Graph

open Lean
open Informal Data Environment

/-!
See `doc/DESIGN_RATIONALE.md` for the human-readable graph
status/completion and warning/color mapping rationale.
-/

/-- Upstream-aligned statement-track status (node border). -/
inductive StatementStatus where
  | blocked
  | ready
  | formalized
  | mathlib
deriving Inhabited, Repr, DecidableEq, ToJson, FromJson, Quote

/-- Upstream-aligned background status (proof-track for theorem-like nodes). -/
inductive ProofStatus where
  | none
  | ready
  | incomplete
  | formalized
  | formalizedWithAncestors
  /-- The node's Lean source is not known to be the text that was compiled (its module's source
  changed since the build, or no build record says which text it was): nothing is shown as known
  of its Lean code, and the node is not complete. -/
  | sourceChanged
deriving Inhabited, Repr, DecidableEq, ToJson, FromJson, Quote

/--
The formalization track whose next step is currently actionable.

For theorem-like nodes, ready or incomplete proof work takes precedence over a
ready statement. Other node kinds expose only a ready statement step.
-/
def actionableStageForStatuses? (kind : Data.NodeKind)
    (statementStatus : StatementStatus) (proofStatus : ProofStatus) : Option String :=
  if kind.isTheoremLike then
    if proofStatus == .ready || proofStatus == .incomplete then
      some "proof"
    else if statementStatus == .ready then
      some "statement"
    else
      none
  else if statementStatus == .ready then
    some "statement"
  else
    none

structure WarningFlags where
  unknownRef : Bool := false
  leanOnlyNoStatement : Bool := false
  missingExternalDecl : Bool := false
deriving Inhabited, Repr, DecidableEq, ToJson, FromJson, Quote

/-- What the kernel replay made while the site is generated establishes for a node of the graph
(`Informal.Replay`). A node is drawn in a success colour only by it: the fill and border of
`sorry`-free Lean code are neutral for `none`. -/
inductive NodeReplay where
  /-- Nothing: no replay, no verdict, a rejected build, or Lean code the replay does not cover. -/
  | none
  /-- An accepted replay covers the node's Lean code. -/
  | accepted
  /-- An accepted replay covers the node's Lean code and that of every node it depends on. -/
  | acceptedWithDependencies
deriving Inhabited, Repr, DecidableEq, ToJson, FromJson, Quote

/-- Whether an accepted replay covers the node's Lean code. -/
def NodeReplay.isAccepted : NodeReplay → Bool
  | .none => false
  | _ => true

/-- The proof status a node is drawn with. The darker fill says "dependencies too": under a
replay that covers the node and not everything it depends on, the node is drawn as complete on
its own. -/
def NodeReplay.shownProofStatus : NodeReplay → ProofStatus → ProofStatus
  | .accepted, .formalizedWithAncestors => .formalized
  | _, status => status

/-- SVG class of a node's proof status, which picks its fill and label colour tokens. -/
def proofStatusClass (kind : Data.NodeKind) : ProofStatus → String
  | .none => if kind.isTheoremLike then "bp_graph_status_not_ready" else "bp_graph_status_definition"
  | .ready => "bp_graph_status_ready"
  | .incomplete => "bp_graph_status_incomplete"
  | .formalized => "bp_graph_status_formalized"
  | .formalizedWithAncestors => "bp_graph_status_formalized_with_ancestors"
  | .sourceChanged => "bp_graph_status_source_changed"

/-- SVG class of a node's statement status, which picks its border colour token. -/
def statementStatusClass : StatementStatus → String
  | .blocked => "bp_graph_statement_blocked"
  | .ready => "bp_graph_statement_ready"
  | .formalized => "bp_graph_statement_formalized"
  | .mathlib => "bp_graph_statement_mathlib"

/-- SVG class of a placeholder node for an unknown reference. -/
def unresolvedClass : String := "bp_graph_status_unresolved"

/-- The SVG classes of a status node (see `GraphNode.svgClass`). -/
def nodeStatusClasses (kind : Data.NodeKind) (statement : StatementStatus) (proof : ProofStatus)
    (warnings : WarningFlags) (replay : NodeReplay := .none) : String :=
  if warnings.unknownRef then unresolvedClass
  else
    let classes :=
      s!"{proofStatusClass kind (replay.shownProofStatus proof)} {statementStatusClass statement}"
    -- the class that turns the success colours inside the node green (`StatusColors.replayScopeCss`)
    if replay.isAccepted then s!"{classes} {StatusColors.replayAcceptedClass}" else classes

structure GraphNode (Ref : Type) where
  label : Name
  displayLabel? : Option String := none
  /-- The node's numbered title in the document (`Theorem 6.5`), when it has one: drawings label
  the node with it, and keep the label for the node's tooltip and accessible name. -/
  caption? : Option String := none
  deps : Array Name
  proofDeps : Array Name := #[]
  parent? : Option Name := none
  shape : String := "box"
  style : String := "filled"
  fillcolor : String
  color : String := "#6b7280"
  penwidth : String := "1.8"
  fontcolor : String := StatusColors.fillText.light
  peripheries : Nat := 1
  gradientangle? : Option String := none
  tooltip? : Option String := none
  ref? : Option Ref := none
  /--
  Space-separated classes written onto the node's SVG group. The graph stylesheet
  repaints status nodes from the status colour tokens by these classes, so the colours above
  only matter where no stylesheet applies.
  -/
  svgClass : String := ""
deriving Inhabited, Repr, ToJson, FromJson

instance [Quote Ref] : Quote (GraphNode Ref) where
  quote n := Syntax.mkCApp ``GraphNode.mk
    #[
      quote n.label, quote n.displayLabel?, quote n.caption?, quote n.deps, quote n.proofDeps, quote n.parent?, quote n.shape,
      quote n.style, quote n.fillcolor, quote n.color, quote n.penwidth, quote n.fontcolor, quote n.peripheries,
      quote n.gradientangle?, quote n.tooltip?, quote n.ref?, quote n.svgClass
    ]

abbrev Graph (Ref : Type) := Array (GraphNode Ref)

def GraphNode.displayLabel (node : GraphNode Ref) : String :=
  node.displayLabel?.getD (toString node.label)

/-- The direction the layers of a rendered Blueprint graph follow. -/
inductive GraphDirection where
  | LR
  | RL
  | TB
  | BT
deriving Inhabited, Repr, BEq, FromJson, ToJson, Quote

/-- The token of a graph direction in options, controls and drawings. -/
def GraphDirection.rankdir : GraphDirection → String
  | .LR => "LR"
  | .RL => "RL"
  | .TB => "TB"
  | .BT => "BT"

/-- Parse user-facing direction aliases accepted by `blueprint_graph`. -/
def GraphDirection.parse? (s : String) : Option GraphDirection :=
  match s.toLower with
  | "lr" | "left-right" | "horizontal" => some .LR
  | "rl" | "right-left" => some .RL
  | "tb" | "top-bottom" | "vertical" => some .TB
  | "bt" | "bottom-top" => some .BT
  | _ => none

/-- How the edges of a rendered Blueprint graph are drawn. -/
inductive GraphRouting where
  /-- Horizontal and vertical lanes: the edges that leave a node share one stem, the edges that
  enter it share one stem and one arrowhead, and parallel edges run as bundles of lanes. -/
  | bundled
  /-- One smooth curve per edge, each with its own arrowhead. -/
  | spline
deriving Inhabited, Repr, BEq, FromJson, ToJson, Quote

/-- The token of a routing in options and drawings. -/
def GraphRouting.token : GraphRouting → String
  | .bundled => "bundled"
  | .spline => "spline"

/-- Parse a routing token (`bundled` or `spline`). -/
def GraphRouting.parse? (s : String) : Option GraphRouting :=
  match s.toLower with
  | "bundled" => some .bundled
  | "spline" => some .spline
  | _ => none

/--
Options that affect the layout of rendered Blueprint graphs.

These options are stored in graph block payloads and serialized with render
variants, so update Lean producers and browser consumers together when their
shape changes.
-/
structure GraphOptions where
  /-- The direction the layers follow. -/
  direction : GraphDirection := .TB
  /--
  Lay each connected component out on its own and pack the drawings into rows,
  instead of one row of layers for the whole graph.
  -/
  pack : Bool := true
  /-- How the edges are drawn; a view too large for bundled lanes is drawn with curves
  (`Informal.GraphLayout.routingFor`). -/
  routing : GraphRouting := .bundled
deriving Inhabited, Repr, BEq, FromJson, ToJson, Quote

/--
One rendered graph view.

The bundled renderer uses variants for the full graph, the synthetic group
overview, and per-group subgraphs. Each is drawn while the site is built
(`Informal.GraphLayout`). The `selectOnNodeId` and `hoverOnNodeId`
arrays describe variant transitions keyed by SVG node id, and
`previewKeyByNodeId` maps SVG nodes to manifest/cache-backed preview keys.
-/
structure GraphRenderVariant where
  /-- Stable key used by the graph view selector and variant links. -/
  key : String
  /-- Human-readable view label. -/
  label : String
  /-- The layout options the view is shown with first. -/
  options : GraphOptions := {}
  /-- Node ids that switch to another variant when selected. -/
  selectOnNodeId : Array (String × String) := #[]
  /-- Node ids that preview another variant on hover. -/
  hoverOnNodeId : Array (String × String) := #[]
  /-- Node ids that open manifest/cache-backed previews; nodes without such previews are omitted. -/
  previewKeyByNodeId : Array (String × String) := #[]
deriving Inhabited, Repr, BEq, ToJson, FromJson, Quote

/-- Direction order used by the bundled graph controls. -/
def allGraphDirections : Array GraphDirection := #[.TB, .LR, .RL, .BT]

/--
Public visual metadata for a graph node.

This mirrors the render-facing node attributes without exposing the generic
`GraphNode Ref` type in cached/public JSON schemas.
-/
structure NodeVisual where
  shape : String := "box"
  style : String := "filled"
  fillcolor : String
  color : String := "#6b7280"
  penwidth : String := "1.8"
  fontcolor : String := StatusColors.fillText.light
  peripheries : Nat := 1
  gradientangle? : Option String := none
  tooltip? : Option String := none
deriving Inhabited, Repr, DecidableEq, ToJson, FromJson, Quote

def NodeVisual.ofGraphNode (node : GraphNode Ref) : NodeVisual := {
  shape := node.shape
  style := node.style
  fillcolor := node.fillcolor
  color := node.color
  penwidth := node.penwidth
  fontcolor := node.fontcolor
  peripheries := node.peripheries
  gradientangle? := node.gradientangle?
  tooltip? := node.tooltip?
}

/-- Axis represented by a dependency edge in the public graph API. -/
inductive EdgeAxis where
  | statement
  | proof
deriving Inhabited, Repr, DecidableEq, ToJson, FromJson, Quote

/-- Finalized public dependency edge data. Edges point from dependency source to dependent target. -/
structure EdgeData where
  source : Name
  target : Name
  axes : Array EdgeAxis := #[]
deriving Inhabited, Repr, DecidableEq, ToJson, FromJson, Quote

/-- Group metadata carried by a semantic graph model before membership is derived. -/
structure GroupMetadata where
  label : Name
  title : String
  declared : Bool := false
deriving Inhabited, Repr, DecidableEq, ToJson, FromJson, Quote

/-- Finalized public group metadata and its node-derived membership projection. -/
structure GroupData where
  label : Name
  title : String
  declared : Bool := false
  children : Array Name := #[]
deriving Inhabited, Repr, DecidableEq, ToJson, FromJson, Quote

/--
Public per-node graph data for Lean, manifest, and browser consumers.

Use `statementStatus`, `proofStatus`, and `warnings` for semantics. `visual`
is provided only for renderers that want to reuse Blueprint's current graph
styling without reverse-engineering colors into statuses.
-/
structure NodeData where
  label : Name
  title : String
  displayLabel : String
  kind : Option Data.NodeKind := none
  parent : Option Name := none
  href : Option String := none
  /-- Selected manifest/cache-backed preview key for this node, if available. -/
  previewKey : Option PreviewKey := none
  /-- Authoritative statement-side dependency data for this graph node. -/
  statementUses : Array Data.UseRef := #[]
  /-- Authoritative proof-side dependency data for this graph node. -/
  proofUses : Array Data.UseRef := #[]
  statementStatus : StatementStatus := .blocked
  proofStatus : ProofStatus := .none
  warnings : WarningFlags := {}
  visual : NodeVisual
  /-- What the kernel replay establishes for the node. The statuses above say what the compiled
  files report; a renderer draws a success colour only for a node this field accepts. -/
  replay : NodeReplay := .none
deriving Inhabited, Repr, ToJson, FromJson, Quote

/-- The next actionable formalization stage represented by this finalized graph node. -/
def NodeData.actionableStage? (node : NodeData) : Option String := do
  let kind ← node.kind
  actionableStageForStatuses? kind node.statementStatus node.proofStatus

/-- Canonicalize duplicate dependency refs on each dependency axis. -/
private def NodeData.normalizeDependencies (node : NodeData) : NodeData :=
  {
    node with
      statementUses := Data.UseRef.mergeByLabel #[] node.statementUses
      proofUses := Data.UseRef.mergeByLabel #[] node.proofUses
  }

/--
Semantic graph input used before traversal finishes.

Topology exists only in `nodes`: dependencies live in `statementUses` and
`proofUses`, and membership lives in `parent`. Group records carry metadata but
no child projection. Select, filter, or merge this model, then cross the single
`finish` materialization boundary to obtain immutable public `GraphData`.
Traversal-aware callers use `GraphApi.finishData`, which enriches the model and
then delegates to `finish`.
-/
structure GraphModel where
  nodes : Array NodeData := #[]
  groupMetadata : Array GroupMetadata := #[]
deriving Inhabited, Repr, ToJson, FromJson, Quote

private def graphDataSchemaVersion : Nat := 4

/--
Finished graph data shared by Lean, generated manifests, and browser clients.

The private constructor makes this a materialized final value rather than a
second mutable graph model. `edges`, group `children`, and topology-dependent
variant data are built together exactly once from a `GraphModel`. Public callers
can inspect them or convert back to `GraphModel`, but cannot update topology
while retaining stale projections. Preview keys may subsequently be filtered
against the emitted manifest/cache pair by `filterPreviewReferences`; that
synchronized post-pass does not reopen topology or change a drawing.

`schemaVersion` is bumped for incompatible public JSON shapes or semantic
contracts.
-/
structure GraphData where
  private mk ::
  schemaVersion : Nat := graphDataSchemaVersion
  /-- Stable key identifying this graph block. -/
  key : String := "graph"
  nodes : Array NodeData := #[]
  edges : Array EdgeData := #[]
  groups : Array GroupData := #[]
  /--
  The render variants of the bundled browser graph renderer: the views a page
  offers, with their node-to-view and node-to-preview tables. The drawings are
  made from them while the site is built. The semantic fields above are the current data
  interface for dashboards and audits. The private `GraphData` constructor ties
  these variants to the same finalized topology. The first variant is `full`;
  variant keys are unique, and select/hover mappings target keys in this array.
  -/
  variants : Array GraphRenderVariant := #[]
deriving Repr, ToJson

/-- Graph occurrence selection and options; project topology is stored once in RenderOverviews. -/
structure CachedGraphData where
  /-- `none` selects the captured project graph; `some` supplies a custom graph. -/
  model : Option GraphModel := none
  options : GraphOptions
deriving Inhabited, Repr, ToJson, FromJson, Quote

/-- The numbered title of a node (`Theorem 6.5`, `Lemma A.2`): a title whose last word is a
number, digits and capital letters joined by dots with at least one digit. A title of a node of a
document numbered `none` ends with the node's label instead (`Theorem Project.main`), and the
title of a node outside the document is its label: neither numbers the node. -/
def numberedCaption? (title : String) : Option String :=
  let title := title.trimAscii.toString
  let last := ((title.splitOn " ").getLast?).getD ""
  let isNumber := last.any Char.isDigit &&
    last.all (fun c => c.isDigit || c.isUpper || c == '.') && !last.startsWith "." &&
    !last.endsWith "."
  if title.contains ' ' && isNumber then some title else none

private def NodeData.toGraphNode (node : NodeData) : GraphNode String :=
  {
    label := node.label
    displayLabel? := some node.displayLabel
    caption? := numberedCaption? node.title
    deps := node.statementUses.map (fun useRef => (useRef.label : Name))
    proofDeps := node.proofUses.map (fun useRef => (useRef.label : Name))
    parent? := node.parent
    shape := node.visual.shape
    style := node.visual.style
    fillcolor := node.visual.fillcolor
    color := node.visual.color
    penwidth := node.visual.penwidth
    fontcolor := node.visual.fontcolor
    peripheries := node.visual.peripheries
    gradientangle? := node.visual.gradientangle?
    tooltip? := node.visual.tooltip?
    ref? := node.href
    svgClass :=
      match node.kind with
      | some kind =>
        nodeStatusClasses kind node.statementStatus node.proofStatus node.warnings node.replay
      | none => if node.warnings.unknownRef then unresolvedClass else ""
  }

/-- Build render topology exclusively from the authoritative node fields. -/
private def GraphModel.toGraph (model : GraphModel) : Graph String :=
  model.nodes.map NodeData.toGraphNode

/-- Recover a semantic model when finalized graph nodes must be selected or merged again. -/
def GraphData.toModel (data : GraphData) : GraphModel := {
  nodes := data.nodes
  groupMetadata := data.groups.map fun group => {
    label := group.label
    title := group.title
    declared := group.declared
  }
}

/-- A legend sample. Colours are CSS values; status colours are token references with the light
value as fallback, so a swatch follows the page theme and still shows where no token is defined. -/
structure LegendSwatch where
  background : String := StatusColors.definition.cssVarOr
  borderColor : String := "var(--bp-color-graph-edge, #6b7280)"
  borderWidth : Nat := 1
  borderStyle : String := "solid"
  borderRadius : String := "0.2rem"
deriving Inhabited, Repr, ToJson, FromJson

structure LegendItem where
  label : String
  swatch? : Option LegendSwatch := none
deriving Inhabited, Repr, ToJson, FromJson

structure LegendGroup where
  key : String
  title : String
  summary? : Option String := none
  items : Array LegendItem
deriving Inhabited, Repr, ToJson, FromJson

def LegendSwatch.inlineStyle (swatch : LegendSwatch) : String :=
  String.intercalate "; " [
    s!"background: {swatch.background}",
    s!"border-color: {swatch.borderColor}",
    s!"border-width: {swatch.borderWidth}px",
    s!"border-style: {swatch.borderStyle}",
    s!"border-radius: {swatch.borderRadius}"
  ]

/-! The light values of the status colour tokens, which the drawings carry. -/

def statementBorderBlockedColor : String := StatusColors.blockedBorder.light
def statementBorderReadyColor : String := StatusColors.readyBorder.light
def statementBorderFormalizedColor : String := StatusColors.formalizedBorder.light
def statementBorderMathlibColor : String := StatusColors.mathlibBorder.light

def proofBackgroundNeutralColor : String := StatusColors.notReady.light
def proofBackgroundReadyColor : String := StatusColors.ready.light
def proofBackgroundIncompleteColor : String := StatusColors.incomplete.light
def proofBackgroundFormalizedColor : String := StatusColors.formalized.light
def proofBackgroundFormalizedAncColor : String := StatusColors.formalizedWithAncestors.light

def definitionBackgroundColor : String := StatusColors.definition.light

def unresolvedFillColor : String := StatusColors.unresolved.light
def unresolvedBorderColor : String := StatusColors.unresolvedBorder.light
def unresolvedFontColor : String := StatusColors.unresolvedText.light

def statementStatusBlockedText : String := "blocked"
def statementStatusReadyText : String := "ready to formalize"
def statementStatusFormalizedText : String := "formalized"
def statementStatusMathlibText : String := "in Mathlib"

def proofStatusNoneText : String := "not ready"
def proofStatusReadyText : String := "ready to formalize"
def proofStatusIncompleteText : String := "Lean code incomplete"
def proofStatusFormalizedText : String := "locally formalized"
def proofStatusFormalizedAncestorsText : String := "locally formalized + dependencies complete"
def proofStatusSourceChangedText : String :=
  "Lean source changed since the build, in its module or a project module it imports"

/-! The status texts above are also values of the query interface (`StatementStatus.toText`,
`ProofStatus.toText`) and stay as they are. What a page shows a reader is the wording below,
which says what was looked at: the Lean code, for `sorry`. "Formalized" alone would say that an
informal statement was turned into Lean, which no status knows. -/

def statementStatusFormalizedLabel : String := "in Lean, no sorry"
def proofStatusFormalizedLabel : String := "Lean code without sorry"
def proofStatusFormalizedAncestorsLabel : String := "Lean code without sorry, dependencies too"

def warningLeanOnlyText : String := "Lean code present but informal statement is missing"
def warningMissingExternalText : String := "Associated Lean declaration is missing from the current environment"
def warningHiddenInGroupViewText : String := "Warning markers are not shown individually in Group View"
def edgeMixedText : String := "Thicker solid/dashed: statement + proof deps"
def groupEdgeMixedText : String := "Thicker solid: statement + proof deps"
def graphLegendFullViewNote : String :=
  "Shape shows declaration kind, border shows the status of the Lean statement, fill shows the status of the Lean proof or definition, and edge style separates statement from proof dependencies. A status is about Lean code: no tool checks that a Lean statement says what its informal statement says. Green is drawn only for Lean code a kernel replay accepted and that rests on no axiom outside Lean's standard three; otherwise the same status is grey."

private def legendItem (label : String) (swatch? : Option LegendSwatch := none) : LegendItem :=
  { label, swatch? }

/-- The legend of the full graph. The entries of `sorry`-free Lean code are drawn in a success
colour only on a site whose kernel replay accepted the build and covers every node (`site`);
otherwise their swatches are neutral and each label says what it rests on. -/
def graphLegendGroups (includeMathlib : Bool := false)
    (site : Replay.SiteState := .none Replay.noReplayText) : Array LegendGroup :=
  let noted (label : String) : String :=
    match site.note? with
    | some note => s!"{label} ({note})"
    | none => label
  let statementItems :=
    #[
      legendItem "Blocked" (some { borderColor := StatusColors.blockedBorder.cssVarOr }),
      legendItem "Ready to formalize" (some { borderColor := StatusColors.readyBorder.cssVarOr }),
      legendItem (noted "In Lean, no sorry")
        (some { borderColor := StatusColors.formalizedBorder.cssVarOr })
    ]
  let statementItems :=
    if includeMathlib then
      statementItems.push (legendItem (noted "In Mathlib")
        (some { borderColor := StatusColors.mathlibBorder.cssVarOr }))
    else
      statementItems
  #[
    {
      key := "shape"
      title := "Shapes"
      summary? := some "Node outline shows whether the item is definition-like or theorem-like."
      items := #[
        legendItem "Definition" (some { borderRadius := "0.2rem" }),
        legendItem "Theorem / lemma / corollary" (some { borderRadius := "999px" })
      ]
    },
    {
      key := "statement"
      title := "Statement Border"
      summary? := some "Border color tracks whether the statement is blocked, ready, or already formalized."
      items := statementItems
    },
    {
      key := "proof"
      title := "Proof Status"
      summary? := some "Fill color tracks proof readiness independently from statement progress."
      items := #[
        legendItem proofStatusNoneText (some { background := StatusColors.notReady.cssVarOr }),
        legendItem proofStatusReadyText (some { background := StatusColors.ready.cssVarOr }),
        legendItem proofStatusIncompleteText (some { background := StatusColors.incomplete.cssVarOr }),
        legendItem (noted proofStatusFormalizedLabel)
          (some { background := StatusColors.formalized.cssVarOr }),
        legendItem (noted proofStatusFormalizedAncestorsLabel)
          (some {
            background := StatusColors.formalizedWithAncestors.cssVarOr
            borderColor := StatusColors.mathlibBorder.cssVarOr
          }),
        legendItem s!"{proofStatusSourceChangedText} (or not known to match it): not shown as \
          checked" (some { background := StatusColors.sourceChanged.cssVarOr })
      ]
    },
    {
      key := "warning"
      title := "Warning Markers"
      summary? := some "Border treatments flag missing references, missing declarations, or Lean-only nodes without an informal statement."
      items := #[
        legendItem "Unknown reference"
          (some {
            background := StatusColors.unresolved.cssVarOr
            borderColor := StatusColors.unresolvedBorder.cssVarOr
          }),
        legendItem "Lean code, informal statement missing"
          (some {
            borderStyle := "dashed"
          }),
        legendItem "Missing external Lean declaration"
          (some {
            borderStyle := "dotted"
          })
      ]
    },
    {
      key := "edge"
      title := "Edges"
      summary? := some "Line style distinguishes statement dependencies from proof-only dependencies."
      items := #[
        legendItem "Solid: statement deps from theorem-like sources",
        legendItem "Dashed: statement deps from box-shaped sources",
        legendItem "Dotted: proof-only deps",
        legendItem edgeMixedText
      ]
    }
  ]

def graphLegendGroupViewNote : String :=
  "Group View uses tab-shaped aggregate group nodes; labels use group titles, colors are averaged over child nodes, and individual warning markers are hidden."

def groupGraphLegendGroups : Array LegendGroup :=
  #[
    {
      key := "group-view"
      title := "Group View"
      summary? := some "Group nodes summarize children instead of showing each declaration separately."
      items := #[
        legendItem "Tab nodes summarize grouped children",
        legendItem "Border/fill colors average child node status colors",
        legendItem warningHiddenInGroupViewText
      ]
    },
    {
      key := "group-edge"
      title := "Edges"
      summary? := some "Grouped edges compress many child edges into one aggregate connection."
      items := #[
        legendItem "Solid: at least one statement dep",
        legendItem "Dotted: proof-only deps",
        legendItem groupEdgeMixedText
      ]
    }
  ]

def statementUses (node : Data.Node) : Array Data.UseRef :=
  (node.statement.map (·.deps)).getD #[]

def proofUses (node : Data.Node) : Array Data.UseRef :=
  (node.proof.map (·.deps)).getD #[]

def statementDeps (node : Data.Node) : Array Name :=
  (statementUses node).map (fun useRef => (useRef.label : Name))

def proofDeps (node : Data.Node) : Array Name :=
  (proofUses node).map (fun useRef => (useRef.label : Name))

def allDeps (node : Data.Node) : Array Name :=
  statementDeps node ++ proofDeps node

def nodeExternalDecls (node : Data.Node) : Array Data.ExternalRef :=
  node.summaryExternalRefs

def nodeHasAssociatedCode (node : Data.Node) : Bool :=
  node.hasAssociatedCode

def nodeHasMissingExternalDecls (external : ExternalCodeStatus) (node : Data.Node) : Bool :=
  (nodeCodeHealth external node).hasMissingExternalDecls

def nodeHasStatementBlockers (external : ExternalCodeStatus) (node : Data.Node) : Bool :=
  (nodeCodeHealth external node).hasStatementGaps

def nodeHasProofBlockers (external : ExternalCodeStatus) (node : Data.Node) : Bool :=
  (nodeCodeHealth external node).hasAnyGaps

def nodeHasIncompleteCode (external : ExternalCodeStatus) (node : Data.Node) : Bool :=
  (nodeCodeHealth external node).hasAnyGaps

def nodeLocalStatementFormalized (external : ExternalCodeStatus) (node : Data.Node) : Bool :=
  (nodeCodeHealth external node).localStatementFormalized

def nodeLocalProofFormalized (external : ExternalCodeStatus) (node : Data.Node) : Bool :=
  (nodeCodeHealth external node).localProofFormalized

def nodeLocalFormalized (external : ExternalCodeStatus) (node : Data.Node) : Bool :=
  (nodeCodeHealth external node).localFormalized node.kind

def eraseDups (xs : Array Name) : Array Name :=
  xs.foldl (init := #[]) fun acc x => if acc.contains x then acc else acc.push x

/-- Placeholder branch for future `(lean := "...")` Mathlib integration. -/
def nodeInMathlib (_state : Environment.State) (_label : Name) (_node : Data.Node) : Bool :=
  false

inductive DepTraversal where
  | statement
  | proof
  | both
deriving Inhabited, Repr

def depsForTraversal (mode : DepTraversal) (node : Data.Node) : Array Name :=
  match mode with
  | .statement => statementDeps node
  | .proof => proofDeps node
  | .both => allDeps node

/-- For the dependencies of `mode`, the nodes of `state` that do not have every node they depend
on, directly or not, present and formalized on its own (`nodeLocalFormalized`), themselves
included, and the labels used that have no node: found for every node at once, by one walk over
the reversed dependencies from the nodes that are not formalized on their own and the labels
without a node. Linear in the nodes and dependencies; a cycle of formalized nodes is complete. -/
def unfinishedClosures (external : ExternalCodeStatus) (state : Environment.State)
    (mode : DepTraversal) : NameSet := Id.run do
  let mut users : Std.HashMap Name (Array Name) := {}
  let mut todo : Array Name := #[]
  for (label, node) in state.data do
    for dep in depsForTraversal mode node.toNode do
      users := users.insert dep ((users.getD dep #[]).push label)
      if !state.data.contains dep then todo := todo.push dep
    if !nodeLocalFormalized external node.toNode then todo := todo.push label
  let mut unfinished : NameSet := {}
  while !todo.isEmpty do
    let label := todo.back!
    todo := todo.pop
    if unfinished.contains label then continue
    unfinished := unfinished.insert label
    todo := todo ++ (users.getD label #[]).filter (!unfinished.contains ·)
  return unfinished

/-- `unfinishedClosures` for each kind of dependency, computed once for a whole graph. -/
structure Closures where
  statement : NameSet := {}
  proof : NameSet := {}
  both : NameSet := {}
deriving Inhabited

/-- The closures of every node of `state`. -/
def Closures.of (external : ExternalCodeStatus) (state : Environment.State) : Closures where
  statement := unfinishedClosures external state .statement
  proof := unfinishedClosures external state .proof
  both := unfinishedClosures external state .both

/-- Whether every node of `roots`, and every node they depend on through the dependencies of
`mode`, directly or not, is present and formalized on its own. -/
def Closures.complete (closures : Closures) (mode : DepTraversal) (roots : Array Name) : Bool :=
  let unfinished := match mode with
    | .statement => closures.statement
    | .proof => closures.proof
    | .both => closures.both
  roots.all (!unfinished.contains ·)

/-- Whether every node of `roots`, and every node they depend on through the dependencies of
`mode`, directly or not, is present and formalized on its own (`Closures.complete`). A caller
that asks this of many nodes computes `Closures.of` once and passes it. -/
def depsClosureComplete (external : ExternalCodeStatus) (state : Environment.State)
    (mode : DepTraversal) (roots : Array Name)
    (closures : Closures := Closures.of external state) : Bool :=
  closures.complete mode roots

def nodeAncestorsFormalized (external : ExternalCodeStatus) (state : Environment.State)
    (node : Data.Node) (closures : Closures := Closures.of external state) : Bool :=
  closures.complete .both (allDeps node)

def statementStatus (external : ExternalCodeStatus) (state : Environment.State) (label : Name)
    (node : Data.Node) (closures : Closures := Closures.of external state) : StatementStatus :=
  if nodeInMathlib state label node then
    .mathlib
  else if nodeLocalStatementFormalized external node then
    .formalized
  else if closures.complete .statement (statementDeps node) then
    .ready
  else
    .blocked

def proofStatus (external : ExternalCodeStatus) (state : Environment.State) (_label : Name)
    (node : Data.Node) (closures : Closures := Closures.of external state) : ProofStatus :=
  let health := nodeCodeHealth external node
  if health.hasChangedSource then .sourceChanged
  else if !node.kind.isTheoremLike then
    if health.localStatementFormalized then
      if closures.complete .both (allDeps node) then .formalizedWithAncestors else .formalized
    else if health.incompleteAssociatedCode then
      .incomplete
    else if closures.complete .statement (statementDeps node) then
      .ready
    else
      .none
  else if health.localProofFormalized then
    if closures.complete .both (allDeps node) then .formalizedWithAncestors else .formalized
  else if health.incompleteAssociatedCode then
    .incomplete
  else
    let stmtDepsDone := closures.complete .statement (statementDeps node)
    let proofDepsDone := closures.complete .proof (proofDeps node)
    if stmtDepsDone && proofDepsDone then .ready else .none

def nodeWarnings (external : ExternalCodeStatus) (_state : Environment.State) (_label : Name)
    (node : Data.Node) : WarningFlags :=
  let health := nodeCodeHealth external node
  {
    unknownRef := false
    leanOnlyNoStatement := health.hasAssociatedCode && node.statement.isNone
    missingExternalDecl := health.hasAssociatedCode && health.hasMissingExternalDecls
  }

def statementStatusBorderColor : StatementStatus → String
  | .blocked => statementBorderBlockedColor
  | .ready => statementBorderReadyColor
  | .formalized => statementBorderFormalizedColor
  | .mathlib => statementBorderMathlibColor

def proofStatusFillColor (kind : Data.NodeKind) : ProofStatus → String
  | .none =>
    if kind.isTheoremLike then proofBackgroundNeutralColor else definitionBackgroundColor
  | .ready => proofBackgroundReadyColor
  | .incomplete => proofBackgroundIncompleteColor
  | .formalized => proofBackgroundFormalizedColor
  | .formalizedWithAncestors => proofBackgroundFormalizedAncColor
  | .sourceChanged => StatusColors.sourceChanged.light

def proofStatusFontColor : ProofStatus → String
  | .formalizedWithAncestors => StatusColors.formalizedWithAncestorsText.light
  | _ => StatusColors.fillText.light

private def graphFillRules : List (String × StatusColors.ColorToken × StatusColors.ColorToken) := [
  (proofStatusClass .definition .none, StatusColors.definition, StatusColors.fillText),
  (proofStatusClass .theorem .none, StatusColors.notReady, StatusColors.fillText),
  (proofStatusClass .theorem .ready, StatusColors.ready, StatusColors.fillText),
  (proofStatusClass .theorem .incomplete, StatusColors.incomplete, StatusColors.fillText),
  (proofStatusClass .theorem .formalized, StatusColors.formalized, StatusColors.fillText),
  (proofStatusClass .theorem .formalizedWithAncestors, StatusColors.formalizedWithAncestors,
    StatusColors.formalizedWithAncestorsText),
  (proofStatusClass .theorem .sourceChanged, StatusColors.sourceChanged, StatusColors.fillText),
  (unresolvedClass, StatusColors.unresolved, StatusColors.unresolvedText)
]

private def graphBorderRules : List (String × StatusColors.ColorToken) := [
  (statementStatusClass .blocked, StatusColors.blockedBorder),
  (statementStatusClass .ready, StatusColors.readyBorder),
  (statementStatusClass .formalized, StatusColors.formalizedBorder),
  (statementStatusClass .mathlib, StatusColors.mathlibBorder),
  (unresolvedClass, StatusColors.unresolvedBorder)
]

/--
Stylesheet rules that paint graph nodes from the status colour tokens by their SVG classes.
The drawing carries the light colours; these rules override them in either theme.
-/
def graphStatusCss : String :=
  let node (cls : String) :=
    s!":is(.bp_graph_canvas, .bp_group_hover_preview_graph) svg g.node.{cls}"
  let fills := graphFillRules.map fun (cls, fill, text) =>
    s!"{node cls} :is(ellipse, path) \{ fill: {fill.cssVar}; }\n" ++
      s!"{node cls} text \{ fill: {text.cssVar}; }\n"
  let borders := graphBorderRules.map fun (cls, border) =>
    s!"{node cls} :is(ellipse, path) \{ stroke: {border.cssVar}; }\n"
  "\n/* Status colours of graph nodes, from the status tokens. */\n" ++
    String.join fills ++ String.join borders

/-- The node with what the kernel replay establishes for it. Its concrete colours, which a
drawing without the stylesheet shows, follow: the success colours of `sorry`-free Lean code only
when the replay accepted it, the neutral ones otherwise. -/
def NodeData.withReplay (node : NodeData) (replay : NodeReplay) : NodeData :=
  if node.warnings.unknownRef then { node with replay := .none } else
  let proof := replay.shownProofStatus node.proofStatus
  let pick (color : StatusColors.SuccessColor) : String :=
    if replay.isAccepted then color.accepted.1 else color.reported.1
  let fillcolor := match proof with
    | .formalized => pick StatusColors.formalizedColor
    | .formalizedWithAncestors => pick StatusColors.formalizedWithAncestorsColor
    | _ => node.visual.fillcolor
  let color := match node.statementStatus with
    | .formalized => pick StatusColors.formalizedBorderColor
    | .mathlib => pick StatusColors.mathlibBorderColor
    | _ => node.visual.color
  { node with
    replay, visual := { node.visual with fillcolor, color, fontcolor := proofStatusFontColor proof } }

def kindShape (kind : Data.NodeKind) : String :=
  if kind.isTheoremLike then "ellipse" else "box"

def StatementStatus.toText : StatementStatus → String
  | .blocked => statementStatusBlockedText
  | .ready => statementStatusReadyText
  | .formalized => statementStatusFormalizedText
  | .mathlib => statementStatusMathlibText

def ProofStatus.toText : ProofStatus → String
  | .none => proofStatusNoneText
  | .ready => proofStatusReadyText
  | .incomplete => proofStatusIncompleteText
  | .formalized => proofStatusFormalizedText
  | .formalizedWithAncestors => proofStatusFormalizedAncestorsText
  | .sourceChanged => proofStatusSourceChangedText

/-- The status as a page shows it (`statementStatusFormalizedLabel`). -/
def StatementStatus.label : StatementStatus → String
  | .formalized => statementStatusFormalizedLabel
  | status => status.toText

/-- The status as a page shows it (`proofStatusFormalizedLabel`). -/
def ProofStatus.label : ProofStatus → String
  | .formalized => proofStatusFormalizedLabel
  | .formalizedWithAncestors => proofStatusFormalizedAncestorsLabel
  | status => status.toText

def warningTooltipParts (warnings : WarningFlags) : List String :=
  (if warnings.leanOnlyNoStatement then [warningLeanOnlyText] else []) ++
  (if warnings.missingExternalDecl then [warningMissingExternalText] else [])

private def styleTokensForWarnings (warnings : WarningFlags) : Array String :=
  let tokens : Array String := #["filled"]
  let tokens :=
    if warnings.leanOnlyNoStatement then tokens.push "dashed" else tokens
  let tokens :=
    if warnings.missingExternalDecl then tokens.push "dotted" else tokens
  tokens

def mkStyledNode (kind : Data.NodeKind) (label : Name) (deps proofDeps : Array Name)
    (parent? : Option Name)
    (statement : StatementStatus) (proof : ProofStatus) (warnings : WarningFlags)
    (ref? : Option Ref) : GraphNode Ref :=
  if warnings.unknownRef then
    {
      label
      deps
      proofDeps
      parent?
      shape := "box"
      style := "filled"
      fillcolor := unresolvedFillColor
      color := unresolvedBorderColor
      penwidth := "2.2"
      fontcolor := unresolvedFontColor
      peripheries := 1
      gradientangle? := none
      tooltip? := some s!"Unknown reference: {label}"
      ref?
      svgClass := unresolvedClass
    }
  else
    let shape := kindShape kind
    let baseFill := proofStatusFillColor kind proof
    let styleTokens := styleTokensForWarnings warnings
    let style := String.intercalate "," styleTokens.toList
    let tooltipParts :=
      [s!"Lean statement: {statement.label}",
        s!"{if kind.isTheoremLike then "Lean proof" else "Lean code"}: {proof.label}"] ++
        warningTooltipParts warnings
    let tooltip? :=
      if tooltipParts.isEmpty then none else some (String.intercalate " | " tooltipParts)
    {
      label
      deps
      proofDeps
      parent?
      shape
      style
      fillcolor := baseFill
      color := statementStatusBorderColor statement
      penwidth := "2.2"
      fontcolor := proofStatusFontColor proof
      peripheries := 1
      gradientangle? := none
      tooltip?
      ref?
      svgClass := nodeStatusClasses kind statement proof warnings
    }

/-- The node with these statuses, and the colours, classes and tooltip that go with them. -/
def NodeData.withStatuses (node : NodeData) (statement : StatementStatus) (proof : ProofStatus) :
    NodeData :=
  if node.warnings.unknownRef then node else
  let kind := node.kind.getD .theorem
  let drawn : GraphNode String :=
    mkStyledNode kind node.label #[] #[] node.parent statement proof node.warnings none
  { node with statementStatus := statement, proofStatus := proof
              visual := NodeVisual.ofGraphNode drawn }

/-- The graph with the Lean code of the nodes `changed` not known to be what was compiled (its
module's source changed since the build): such a node gets the status `sourceChanged` and is not
complete, and a node that depends on one, directly or not, is not complete with its dependencies.
One walk over the reversed dependencies. -/
def GraphModel.withSourceChanged (model : GraphModel) (changed : NameSet) : GraphModel := Id.run do
  if changed.isEmpty then return model
  let mut users : Std.HashMap Name (Array Name) := {}
  for n in model.nodes do
    for dep in n.statementUses ++ n.proofUses do
      users := users.insert dep.label ((users.getD dep.label #[]).push n.label)
  -- every node that depends on a changed node, directly or not, and the changed nodes
  let mut tainted : NameSet := {}
  let mut todo : Array Name := changed.toArray
  while !todo.isEmpty do
    let label := todo.back!
    todo := todo.pop
    if tainted.contains label then continue
    tainted := tainted.insert label
    todo := todo ++ (users.getD label #[]).filter (!tainted.contains ·)
  let nodes := model.nodes.map fun n =>
    if changed.contains n.label then
      let statement := if n.statementStatus == .formalized then .ready else n.statementStatus
      n.withStatuses statement .sourceChanged
    else if tainted.contains n.label && n.proofStatus == .formalizedWithAncestors then
      n.withStatuses n.statementStatus .formalized
    else n
  return { model with nodes }

def expandLabels (state : Environment.State) (roots : Array Name) : Array Name :=
  Id.run <| do
    let mut queue : Array Name := eraseDups roots
    let mut enqueued : NameSet := queue.foldl (init := {}) fun acc label => acc.insert label
    let mut seen : NameSet := {}
    let mut idx : Nat := 0
    while idx < queue.size do
      let label := queue[idx]!
      idx := idx + 1
      if seen.contains label then
        continue
      seen := seen.insert label
      match state.data.get? label with
      | none => pure ()
      | some node =>
        for dep in allDeps node do
          if !enqueued.contains dep then
            queue := queue.push dep
            enqueued := enqueued.insert dep
    return queue

def mkNode (external : ExternalCodeStatus) (state : Environment.State)
    (resolveRef? : Name → Option Ref) (label : Name)
    (closures : Closures := Closures.of external state) : GraphNode Ref :=
  match state.data.get? label with
  | some node =>
    let deps := statementDeps node
    let nodeProofDeps := proofDeps node
    let statement := statementStatus external state label node closures
    let proof := proofStatus external state label node closures
    let warnings := nodeWarnings external state label node
    let ref? := resolveRef? label
    mkStyledNode node.kind label deps nodeProofDeps node.parent statement proof warnings ref?
  | none =>
    let unresolvedWarnings : WarningFlags := { unknownRef := true }
    mkStyledNode Data.NodeKind.definition label #[] #[] none .blocked .none unresolvedWarnings none

def build (state : Environment.State) (roots : Array Name) (resolveRef? : Name → Option Ref := fun _ => none) :
    Graph Ref :=
  let labels := expandLabels state roots
  let external : ExternalCodeStatus := {}
  let closures := Closures.of external state
  labels.map (mkNode external state resolveRef? · closures)

def buildWithExternal (state : Environment.State) (roots : Array Name)
    (external : ExternalCodeStatus) (resolveRef? : Name → Option Ref := fun _ => none)
    (closures : Closures := Closures.of external state) : Graph Ref :=
  let labels := expandLabels state roots
  labels.map (mkNode external state resolveRef? · closures)

private def edgeAxes (isStatement isProof : Bool) : Array EdgeAxis :=
  let axes := #[]
  let axes := if isStatement then axes.push .statement else axes
  if isProof then axes.push .proof else axes

private def edgesForNode (node : GraphNode Ref) : Array EdgeData :=
  let stmtDeps := eraseDups node.deps
  let proofDeps := eraseDups node.proofDeps
  let deps := proofDeps.foldl (init := stmtDeps) fun deps dep =>
    if deps.contains dep then deps else deps.push dep
  deps.map fun dep => {
    source := dep
    target := node.label
    axes := edgeAxes (stmtDeps.contains dep) (proofDeps.contains dep)
  }

/--
Project the graph's semantic edges, combining duplicate dependencies and
dropping dependencies whose source endpoint is not present in the graph.
-/
private def edgesForGraph (graph : Graph Ref) : Array EdgeData :=
  let known : NameSet := graph.foldl (init := {}) fun acc node => acc.insert node.label
  let (_, edges) := graph.foldl
    (init := (({} : Std.HashMap (Name × Name) Nat), (#[] : Array EdgeData)))
    fun (edgeIndex, edges) node =>
      (edgesForNode node).foldl (init := (edgeIndex, edges)) fun (edgeIndex, edges) edge =>
        if !known.contains edge.source then
          (edgeIndex, edges)
        else
          let endpoints := (edge.source, edge.target)
          match edgeIndex.get? endpoints with
          | none => (edgeIndex.insert endpoints edges.size, edges.push edge)
          | some index =>
            let current := edges[index]!
            let merged := {
              current with
                axes := edgeAxes
                  (current.axes.contains .statement || edge.axes.contains .statement)
                  (current.axes.contains .proof || edge.axes.contains .proof)
            }
            (edgeIndex, edges.set! index merged)
  edges

private def graphParentChildren (graph : Graph Ref) : Lean.NameMap (Array Name) :=
  graph.foldl (init := ({} : Lean.NameMap (Array Name))) fun acc node =>
    match node.parent? with
    | none => acc
    | some parent =>
      let children := acc.getD parent #[]
      if children.contains node.label then acc else acc.insert parent (children.push node.label)

private def graphNodeParents (graph : Graph Ref) : Lean.NameMap Name :=
  graph.foldl (init := ({} : Lean.NameMap Name)) fun acc node =>
    match node.parent? with
    | none => acc
    | some parent => acc.insert node.label parent

private def groupTitle (groupTitles : Lean.NameMap String) (parent : Name) : String :=
  let title := (groupTitles.getD parent parent.toString).trimAscii.toString
  if title.isEmpty then parent.toString else title

private def groupMetadataFromTitles (groupTitles : Array (Name × String)) : Array GroupMetadata :=
  groupTitles.map fun (label, title) => {
    label
    title
    declared := true
  }

private def normalizeGroupMetadata (group : GroupMetadata) : GroupMetadata :=
  let title := group.title.trimAscii.toString
  {
    group with
      title := if title.isEmpty then group.label.toString else title
  }

/--
Merge duplicate group metadata records without consulting their derived child
arrays. The first declared record wins; a later declared record replaces an
earlier undeclared fallback.
-/
private def groupMetadataMap (groups : Array GroupMetadata) : Lean.NameMap GroupMetadata :=
  groups.foldl (init := ({} : Lean.NameMap GroupMetadata)) fun acc incoming =>
    let incoming := normalizeGroupMetadata incoming
    match acc.get? incoming.label with
    | none => acc.insert incoming.label incoming
    | some current =>
      let preferred := if !current.declared && incoming.declared then incoming else current
      acc.insert incoming.label {
        preferred with
          declared := current.declared || incoming.declared
      }

private def canonicalNodes (nodes : Array NodeData) : Array NodeData :=
  let (_, nodes) := nodes.foldl
    (init := (({} : Lean.NameSet), (#[] : Array NodeData))) fun (seen, nodes) node =>
      if seen.contains node.label then
        (seen, nodes)
      else
        (seen.insert node.label, nodes.push node.normalizeDependencies)
  nodes

/--
Canonicalize only the authoritative semantic model before caching or finishing.

The first node for a label is retained, dependency refs are deduplicated, and
group metadata is merged by label. No edge, child, or render projection exists
at this stage.
-/
def GraphModel.canonicalize (model : GraphModel) : GraphModel := {
  nodes := canonicalNodes model.nodes
  groupMetadata := (groupMetadataMap model.groupMetadata).toArray.map (·.2)
}

/--
Merge two semantic graph models, selecting the preferred model's complete node
record whenever both models contain the same label.

Dependencies and parent membership are deliberately not merged field by field:
they are topology owned by the selected node. Group metadata is combined by
label, preferring declared metadata over an undeclared fallback, and every
derived projection is left to the later `finish` boundary.
-/
def GraphModel.mergePreferLeft (preferred fallback : GraphModel) : GraphModel :=
  ({
    nodes := preferred.nodes ++ fallback.nodes
    groupMetadata := preferred.groupMetadata ++ fallback.groupMetadata
  } : GraphModel).canonicalize

private def GraphModel.groupTitleMap (model : GraphModel) : Lean.NameMap String :=
  (groupMetadataMap model.groupMetadata).foldl (init := ({} : Lean.NameMap String))
    fun acc label metadata => acc.insert label metadata.title

/--
Derive group membership from node parents while retaining group title and
declaration metadata. Metadata for groups with no selected children is omitted.
-/
private def groupDataForGraphFromMetadata (graph : Graph Ref) (groups : Array GroupMetadata) :
    Array GroupData :=
  let metadata := groupMetadataMap groups
  graphParentChildren graph |>.toArray
    |>.map (fun (parent, children) =>
      match metadata.get? parent with
      | some group => {
          label := group.label
          title := group.title
          declared := group.declared
          children
        }
      | none => {
          label := parent
          title := parent.toString
          declared := false
          children
        })
    |>.qsort fun a b =>
      a.title < b.title || (a.title == b.title && a.label.toString < b.label.toString)

private def nodeTitle (resolveTitle? : Name → Option String) (label : Name) : String :=
  match resolveTitle? label with
  | some title =>
    let title := title.trimAscii.toString
    if title.isEmpty then label.toString else title
  | none => label.toString

def nodeDataWithExternal
    (external : ExternalCodeStatus)
    (state : Environment.State)
    (resolveHref? : Name → Option String)
    (resolveTitle? : Name → Option String)
    (graphNode : GraphNode String) (closures : Closures := Closures.of external state) :
    NodeData :=
  let label := graphNode.label
  match state.data.get? label with
  | some node =>
    let statement := statementStatus external state label node closures
    let proof := proofStatus external state label node closures
    let warnings := nodeWarnings external state label node
    {
      label
      title := nodeTitle resolveTitle? label
      displayLabel := graphNode.displayLabel
      kind := some node.kind
      parent := node.parent
      href := resolveHref? label
      previewKey := PreviewKey.ofString? (PreviewCache.statementKey label)
      statementUses := statementUses node
      proofUses := proofUses node
      statementStatus := statement
      proofStatus := proof
      warnings
      visual := NodeVisual.ofGraphNode graphNode
    }
  | none =>
    {
      label
      title := nodeTitle resolveTitle? label
      displayLabel := graphNode.displayLabel
      kind := none
      parent := none
      href := resolveHref? label
      previewKey := PreviewKey.ofString? (PreviewCache.statementKey label)
      statementUses := #[]
      proofUses := #[]
      statementStatus := .blocked
      proofStatus := .none
      warnings := { unknownRef := true }
      visual := NodeVisual.ofGraphNode graphNode
    }

def buildModelWithExternal
    (state : Environment.State)
    (roots : Array Name)
    (external : ExternalCodeStatus)
    (resolveHref? : Name → Option String := fun _ => none)
    (resolveTitle? : Name → Option String := fun _ => none)
    (groupTitles : Array (Name × String) := #[]) : GraphModel :=
  let closures := Closures.of external state
  let graph := buildWithExternal state roots external resolveHref? closures
  {
    nodes := graph.map (nodeDataWithExternal external state resolveHref? resolveTitle? · closures)
    groupMetadata := groupMetadataFromTitles groupTitles
  }

def buildModel
    (state : Environment.State)
    (roots : Array Name)
    (resolveHref? : Name → Option String := fun _ => none)
    (resolveTitle? : Name → Option String := fun _ => none)
    (groupTitles : Array (Name × String) := #[]) : GraphModel :=
  buildModelWithExternal state roots {} resolveHref? resolveTitle? groupTitles

def graphNodeSvgId (label : Name) : String :=
  Informal.HtmlId.prefixed "bp-node" (toString label)

/-- Stable key for the synthetic group overview variant. -/
def groupVariantKey : String := "group"
private def parentVariantKey (parent : Name) : String := s!"parent:{parent}"

private partial def wrapGraphLabelWords (words : List String) (lineWidth maxLines : Nat)
    (current : String) (lines : Array String) : Array String :=
  match words with
  | [] =>
    if current.isEmpty then lines else lines.push current
  | word :: rest =>
    if lines.size + 1 == maxLines then
      let finalLine :=
        if current.isEmpty then
          String.intercalate " " (word :: rest)
        else
          String.intercalate " " (current :: word :: rest)
      lines.push finalLine
    else
      let candidate := if current.isEmpty then word else current ++ " " ++ word
      if !current.isEmpty && candidate.length > lineWidth then
        wrapGraphLabelWords words lineWidth maxLines "" (lines.push current)
      else
        wrapGraphLabelWords rest lineWidth maxLines candidate lines

private def wrapGraphLabel (title : String) (lineWidth : Nat := 26) (maxLines : Nat := 3) : String :=
  let words :=
    (title.splitOn " ").foldr (init := ([] : List String)) fun word acc =>
      let word := word.trimAscii.toString
      if word.isEmpty then acc else word :: acc
  match words with
  | [] => title.trimAscii.toString
  | _ =>
    let lines := wrapGraphLabelWords words lineWidth maxLines "" #[]
    String.intercalate "\n" lines.toList

private def graphParentDisplayLabel (groupTitles : Lean.NameMap String) (parent : Name) : String :=
  wrapGraphLabel (groupTitle groupTitles parent)

private def hexNibble? (c : Char) : Option Nat :=
  match c with
  | '0' => some 0
  | '1' => some 1
  | '2' => some 2
  | '3' => some 3
  | '4' => some 4
  | '5' => some 5
  | '6' => some 6
  | '7' => some 7
  | '8' => some 8
  | '9' => some 9
  | 'a' | 'A' => some 10
  | 'b' | 'B' => some 11
  | 'c' | 'C' => some 12
  | 'd' | 'D' => some 13
  | 'e' | 'E' => some 14
  | 'f' | 'F' => some 15
  | _ => none

private def parseHexByte? (c1 c2 : Char) : Option Nat := do
  let hi ← hexNibble? c1
  let lo ← hexNibble? c2
  return hi * 16 + lo

private def parseHexColor? (s : String) : Option (Nat × Nat × Nat) := do
  let chars :=
    match s.trimAscii.toString.toList with
    | '#' :: rest => rest
    | xs => xs
  match chars with
  | r1 :: r2 :: g1 :: g2 :: b1 :: b2 :: [] =>
    return (← parseHexByte? r1 r2, ← parseHexByte? g1 g2, ← parseHexByte? b1 b2)
  | _ => none

private def hexChar (n : Nat) : Char :=
  if n < 10 then
    Char.ofNat ('0'.toNat + n)
  else
    Char.ofNat ('a'.toNat + (n - 10))

private def byteToHex (n : Nat) : String :=
  let n := n % 256
  let hi := n / 16
  let lo := n % 16
  String.ofList [hexChar hi, hexChar lo]

private def rgbToHex (r g b : Nat) : String :=
  "#" ++ byteToHex r ++ byteToHex g ++ byteToHex b

private def primaryColorToken (s : String) : String :=
  match s.splitOn ":" with
  | token :: _ => token.trimAscii.toString
  | [] => s.trimAscii.toString

private def averageHexColor (colors : Array (Nat × Nat × Nat)) (fallback : String) : String :=
  if colors.isEmpty then
    fallback
  else
    let (sumR, sumG, sumB) := colors.foldl (init := (0, 0, 0)) fun (r, g, b) (r', g', b') =>
      (r + r', g + g', b + b')
    let n := colors.size
    rgbToHex (sumR / n) (sumG / n) (sumB / n)

private def mixedNodeColor (nodes : Array (GraphNode String)) (colorOf : GraphNode String → String)
    (fallback : String) : String :=
  let colors := nodes.foldl (init := (#[] : Array (Nat × Nat × Nat))) fun acc node =>
    match parseHexColor? (primaryColorToken (colorOf node)) with
    | some rgb => acc.push rgb
    | none => acc
  averageHexColor colors fallback

private def fontColorForFill (fillColor : String) : String :=
  match parseHexColor? fillColor with
  | some (r, g, b) =>
    -- Relative luminance approximation, keeps labels readable on dark mixes.
    if (299 * r + 587 * g + 114 * b) < 140000 then "#f8fafc" else "#0f172a"
  | none => "#0f172a"

private def nodeHasAncestorParent (parentMap : Lean.NameMap Name) (label ancestor : Name) : Bool :=
  Id.run <| do
    let mut current := label
    let mut seen : Lean.NameSet := {}
    let mut fuel := parentMap.toArray.size + 1
    while fuel > 0 do
      fuel := fuel - 1
      match parentMap.get? current with
      | none => return false
      | some parent =>
        if parent == ancestor then
          return true
        if seen.contains parent then
          return false
        seen := seen.insert parent
        current := parent
    return false

private def subgraphForParent (graph : Graph Ref) (parent : Name) : Graph Ref :=
  let parentMap := graphNodeParents graph
  graph.filter fun node =>
    node.label == parent || nodeHasAncestorParent parentMap node.label parent

/--
Build the synthetic group overview graph used by graph view variants.

Each parent with multiple children becomes one aggregate node whose colors are
derived from its children and whose edges summarize cross-group dependencies.
-/
def mkParentOverviewGraph (graph : Graph String) (parents : Array Name)
    (groupTitles : Lean.NameMap String) : Graph String :=
  let parentChildren := graphParentChildren graph
  let nodeByLabel : Lean.NameMap (GraphNode String) :=
    graph.foldl (init := ({} : Lean.NameMap (GraphNode String))) fun acc node =>
      acc.insert node.label node
  let parentSet : Lean.NameSet :=
    parents.foldl (init := ({} : Lean.NameSet)) fun acc parent => acc.insert parent
  let parentMap := graphNodeParents graph
  let addParentDep (acc : Lean.NameMap (Array Name)) (target source : Name) : Lean.NameMap (Array Name) :=
    let deps := acc.getD target #[]
    if deps.contains source then
      acc
    else
      acc.insert target (deps.push source)
  let collectParentDeps (depsOf : GraphNode String → Array Name) :=
    graph.foldl (init := ({} : Lean.NameMap (Array Name))) fun acc node =>
      match node.parent? with
      | none => acc
      | some target =>
        if !parentSet.contains target then
          acc
        else
          (depsOf node).foldl (init := acc) fun acc dep =>
            match parentMap.get? dep with
            | some source =>
              if parentSet.contains source && source != target then
                addParentDep acc target source
              else
                acc
            | none => acc
  let parentStatementDeps := collectParentDeps (·.deps)
  let parentProofDeps := collectParentDeps (·.proofDeps)
  parents.map fun parent =>
    let childNodes :=
      (parentChildren.getD parent #[]).foldl (init := (#[] : Array (GraphNode String))) fun acc child =>
        match nodeByLabel.get? child with
        | some node => acc.push node
        | none => acc
    let mixedFillColor := mixedNodeColor childNodes (·.fillcolor) "#e2e8f0"
    let mixedBorderColor := mixedNodeColor childNodes (·.color) "#475569"
    let title := groupTitle groupTitles parent
    {
      label := parent
      displayLabel? := some (graphParentDisplayLabel groupTitles parent)
      deps := parentStatementDeps.getD parent #[]
      proofDeps := parentProofDeps.getD parent #[]
      shape := "tab"
      style := "filled"
      fillcolor := mixedFillColor
      color := mixedBorderColor
      penwidth := "2.4"
      fontcolor := fontColorForFill mixedFillColor
      tooltip? := some s!"Group View: {title} ({childNodes.size} nodes)"
      ref? := none
    }

/-- The groups with more than one node, by title: each has a view of its own. -/
private def variantParents (graph : Graph String) (groupTitles : Lean.NameMap String) :
    Array Name :=
  (graphParentChildren graph).toArray
    |>.filter (fun (_, children) => children.size > 1)
    |>.map (·.1)
    |>.qsort (fun a b => groupTitle groupTitles a < groupTitle groupTitles b)

/--
Build the render variants for the bundled graph UI.

Graphs without multi-child groups produce just the full graph variant. Grouped
graphs additionally produce a synthetic group overview and one focused subgraph
per parent group.
-/
private def mkGraphVariants (graph : Graph String) (options : GraphOptions)
    (groupTitles : Lean.NameMap String)
    (previewKeyForLabel : Name → Option PreviewKey := fun _ => none) :
    Array GraphRenderVariant :=
  let previewKeyByNodeId (graph : Graph String) : Array (String × String) :=
    graph.filterMap fun node =>
      previewKeyForLabel node.label |>.map fun previewKey =>
        (graphNodeSvgId node.label, toString previewKey)
  let parents := variantParents graph groupTitles
  if parents.isEmpty then
    #[{
      key := "full"
      label := "Full Graph"
      options
      selectOnNodeId := #[]
      hoverOnNodeId := #[]
      previewKeyByNodeId := previewKeyByNodeId graph
    }]
  else
    let parentVariantRefs := parents.map (fun parent => (graphNodeSvgId parent, parentVariantKey parent))
    let groupVariant : GraphRenderVariant := {
      key := groupVariantKey
      label := "Group View"
      options
      selectOnNodeId := parentVariantRefs
      hoverOnNodeId := parentVariantRefs
      previewKeyByNodeId := #[]
    }
    let fullVariant : GraphRenderVariant := {
      key := "full"
      label := "Full Graph"
      options
      selectOnNodeId := #[]
      hoverOnNodeId := #[]
      previewKeyByNodeId := previewKeyByNodeId graph
    }
    let parentVariants := parents.map fun parent =>
      let parentSubgraph := subgraphForParent graph parent
      let title := groupTitle groupTitles parent
      {
        key := parentVariantKey parent
        label := title
        options
        selectOnNodeId := #[]
        hoverOnNodeId := #[]
        previewKeyByNodeId := previewKeyByNodeId parentSubgraph
      }
    #[fullVariant, groupVariant] ++ parentVariants

/-- Finish a semantic model by materializing every public projection and render variant once. -/
def GraphModel.finish (model : GraphModel) (key : String) (options : GraphOptions) : GraphData :=
  let model := model.canonicalize
  let graph := model.toGraph
  let groups := groupDataForGraphFromMetadata graph model.groupMetadata
  let groupTitles := groups.foldl (init := ({} : Lean.NameMap String)) fun acc group =>
    acc.insert group.label group.title
  let previewKeys := model.nodes.foldl (init := ({} : Lean.NameMap PreviewKey)) fun acc node =>
    match node.previewKey with
    | some key => acc.insert node.label key
    | none => acc
  {
    schemaVersion := graphDataSchemaVersion
    key
    nodes := model.nodes
    edges := edgesForGraph graph
    groups
    variants := mkGraphVariants graph options groupTitles previewKeys.get?
  }

/-- What a variant shows: its nodes, the titles of its groups, and whether groups are drawn as
boxes around their nodes. -/
structure VariantGraph where
  key : String
  graph : Graph String
  groupTitle : Name → Option String
  clusters : Bool

/-- The graph of every render variant, in the order of `variants`: the full graph with its
groups as boxes, the group overview, and each group's own nodes (the view is the group, so no
box is drawn around it). -/
def GraphData.variantGraphs (data : GraphData) : Array VariantGraph :=
  let model := data.toModel.canonicalize
  let graph := model.toGraph
  let titles := data.groups.foldl (init := ({} : Lean.NameMap String)) fun acc group =>
    acc.insert group.label group.title
  let parents := variantParents graph titles
  let full : VariantGraph := { key := "full", graph, groupTitle := titles.get?, clusters := true }
  if parents.isEmpty then #[full]
  else
    #[full, { key := groupVariantKey, graph := mkParentOverviewGraph graph parents titles,
              groupTitle := fun _ => none, clusters := false }] ++
      parents.map fun parent =>
        let sub := subgraphForParent graph parent
        { key := parentVariantKey parent
          graph := sub.map fun node =>
            if node.parent? == some parent then { node with parent? := none } else node
          groupTitle := titles.get?, clusters := true }

/-- The graph the neighbourhood views are cut from: every node, without groups. -/
def GraphData.renderGraph (data : GraphData) : Graph String :=
  data.toModel.canonicalize.toGraph

/--
Filter preview references without reopening finalized topology.

This is the only supported post-finish update: unavailable node preview keys
and their variant lookup entries are removed together, while topology and the
drawings remain unchanged. Preview keys cannot be rewritten after finalization.
-/
def GraphData.filterPreviewReferences
    (data : GraphData)
    (keep : PreviewKey → Bool) : GraphData :=
  {
    data with
      nodes := data.nodes.map fun node => { node with previewKey := node.previewKey.filter keep }
      variants := data.variants.map fun variant => {
        variant with
          previewKeyByNodeId := variant.previewKeyByNodeId.filterMap fun (nodeId, key) =>
            (PreviewKey.ofString? key).filter keep |>.map fun key => (nodeId, toString key)
      }
  }

private structure GraphDataJson where
  schemaVersion : Nat
  key : String
  nodes : Array NodeData
  edges : Array EdgeData
  groups : Array GroupData
  variants : Array GraphRenderVariant
deriving FromJson

/-- Decode only finalized graph records whose materialized projections agree. -/
instance : FromJson GraphData where
  fromJson? json := do
    let decoded ← fromJson? (α := GraphDataJson) json
    if decoded.schemaVersion != graphDataSchemaVersion then
      throw s!"unsupported graph schema version {decoded.schemaVersion}; expected {graphDataSchemaVersion}"
    let metadata : Array GroupMetadata := decoded.groups.map fun group => {
      label := group.label
      title := group.title
      declared := group.declared
    }
    let model : GraphModel := { nodes := decoded.nodes, groupMetadata := metadata }
    let canonical := model.canonicalize
    if canonical.nodes.size != decoded.nodes.size then
      throw "finalized graph contains duplicate node labels"
    let dependenciesAreCanonical := decoded.nodes.all fun node =>
      let normalized := node.normalizeDependencies
      node.statementUses == normalized.statementUses && node.proofUses == normalized.proofUses
    if !dependenciesAreCanonical then
      throw "finalized graph contains duplicate dependency refs"
    let some firstVariant := decoded.variants[0]?
      | throw "finalized graph contains no render variants"
    let expected := model.finish decoded.key firstVariant.options
    if decoded.edges != expected.edges then
      throw "finalized graph edges disagree with node dependencies"
    if decoded.groups != expected.groups then
      throw "finalized graph group children disagree with node parents"
    if decoded.variants != expected.variants then
      throw "finalized graph variants disagree with node topology or preview references"
    pure {
      schemaVersion := decoded.schemaVersion
      key := decoded.key
      nodes := decoded.nodes
      edges := decoded.edges
      groups := decoded.groups
      variants := decoded.variants
    }

end Informal.Graph
