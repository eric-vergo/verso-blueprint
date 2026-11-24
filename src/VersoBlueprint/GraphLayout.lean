/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

import PILean.Graph.Web
import VersoBlueprint.Graph

/-!
Graph layout and drawing at build time.

Every view of the dependency graph is laid out and drawn while the site is generated, in Lean,
by PILean's layered layout (the method of Sugiyama, Tagawa and Toda as refined by Gansner,
Koutsofios, North and Vo): layers by network simplex, a graph with groups from the inside out so
that every group has layers of its own, crossing reduction by weighted medians, transposition
and sifting from several starts, coordinates after Brandes and Köpf improved by network simplex,
every edge the shortest route through the free space beside the nodes it passes, drawn as one
smooth curve, components packed on shelves. The result is deterministic: the same graph gives
the same bytes.

* `drawings` draws one view (`View`) for every direction a reader can choose and with its
  components packed or in one row of layers, as inert SVG (no script, link or event handler)
  whose nodes carry the ids and status classes the page's stylesheet and script use. The graph
  block puts the first drawing into the page, and the others beside the graph data when the
  site has no folder of drawings
  (`<script type="image/svg+xml" class="bp-graph-drawing" data-variant data-direction data-pack>`).
* `writeDrawings` writes the drawings of every view into a folder of the site, and with them the
  neighbourhood views (the nodes within one to three steps of a node): one drawing per distinct
  set of nodes, within a limit on their total size; `index.json` there says which drawing shows
  which view and neighbourhood and which were left out. A page fetches a drawing when it is
  first shown.
-/

namespace Informal.GraphLayout

open Lean
open Informal.Graph

/-- A view to draw: its nodes, the titles of its groups, whether groups are drawn as boxes
around their nodes, and how its edges are drawn. -/
structure View where
  graph : Graph String
  groupTitle : Name → Option String := fun _ => none
  clusters : Bool := true
  routing : GraphRouting := .bundled

/-- The size of node labels. -/
def fontSize : Float := 12

/-- The most characters of a line of a label before a dotted name is broken. -/
def labelWidth : Nat := 28

/-- A dotted name over several lines of at most `width` characters where its components allow:
broken after a dot, never inside a component. A text without a dot, or one that fits, is one
line. -/
def wrapDotted (text : String) (width : Nat := labelWidth) : Array String := Id.run do
  if text.length ≤ width then return #[text]
  let parts := text.splitOn "."
  let mut lines : Array String := #[]
  let mut line := ""
  for part in parts, i in [0:parts.length] do
    let piece := if i + 1 < parts.length then part ++ "." else part
    if !line.isEmpty && line.length + piece.length > width then
      lines := lines.push line
      line := piece
    else line := line ++ piece
  return if line.isEmpty then lines else lines.push line

/-- The lines of a node's label: its own lines, each long dotted name (a module, a declaration
in its namespaces) broken after dots, so that a node is not much wider than the others. -/
def labelLines (node : GraphNode Ref) : Array String :=
  (((node.caption?.getD node.displayLabel).splitOn "\n").toArray).flatMap wrapDotted

/-- The accessible name of a drawn node: the text of its label, followed by its name (the
node's label) when the label shows something else, as a numbered title does
(`Theorem 6.5 (critical_radius)`), then its tooltip, which says the node's state in the words of
its mark ("Theorem 6.5 (critical_radius): Lean proof without sorry, as the compiled files
report; …"). -/
def accessibleName (node : PILean.Graph.WebNode) : String :=
  let shown := String.join node.lines.toList
  let named := if shown == node.name || node.name.isEmpty then shown
    else s!"{" ".intercalate node.lines.toList} ({node.name})"
  if node.tooltip.isEmpty then named else s!"{named}: {node.tooltip}"

/-- The outline of a node. -/
def webShape (node : GraphNode Ref) : PILean.Graph.WebShape :=
  if node.shape == "ellipse" then .ellipse else if node.shape == "tab" then .tab else .box

/-- The width and height of a node's box: its label in the page's sans-serif face (measured with
Helvetica's metrics and a small reserve) with room around it. -/
def nodeSize (node : GraphNode Ref) : Float × Float :=
  let lines := labelLines node
  let width := lines.foldl (fun w s => max w (PILean.Graph.sansWidth s fontSize)) 0 * 1.06
  let extra := fontSize * 1.2 * ((lines.size : Nat) - 1).toFloat
  match webShape node with
  | .ellipse => (max 56 (width * 1.12 + 20), 32 + extra)
  | .tab => (max 60 (width + 22), 30 + extra)
  | _ => (max 48 (width + 16), 26 + extra)

private def styleTokens (node : GraphNode Ref) : List String :=
  (node.style.splitOn ",").map (·.trimAscii.toString)

/-- Whether XML can carry the character `c`: tab, line feed, carriage return, and everything
from the space up, except `U+FFFE` and `U+FFFF` (Lean's characters are never surrogates). -/
def xmlChar (c : Char) : Bool :=
  c == '\t' || c == '\n' || c == '\r' || (c.val ≥ 0x20 && c.val != 0xFFFE && c.val != 0xFFFF)

/-- The page's side of a node: its id, status classes, name, tooltip (without the
characters XML cannot carry), label and colours. -/
def webNode (node : GraphNode Ref) : PILean.Graph.WebNode :=
  let tokens := styleTokens node
  { id := graphNodeSvgId node.label
    classes := node.svgClass
    name := toString node.label
    tooltip := String.ofList ((node.tooltip?.getD "").toList.filter xmlChar)
    lines := labelLines node
    shape := webShape node
    fill := node.fillcolor
    stroke := node.color
    ink := node.fontcolor
    strokeWidth := if node.penwidth == "2.4" then 2 else 1.6
    dash := if tokens.contains "dashed" then "5 3" else if tokens.contains "dotted" then "1.5 3"
      else "" }

/-- A view as a graph to lay out, with the page's side of its nodes and edges. An edge runs from
a dependency to the node that uses it: dashed from a definition, thicker when both the statement
and the proof use it, dotted when only the proof does. Groups with more than one member become
clusters, nested as the groups are. -/
def toLayoutGraph (view : View) :
    PILean.Graph × Array PILean.Graph.WebNode × Array PILean.Graph.WebEdge := Id.run do
  let g := view.graph
  let index : NameMap Nat := Id.run do
    let mut m : NameMap Nat := {}
    for i in [0:g.size] do
      if !m.contains g[i]!.label then m := m.insert g[i]!.label i
    return m
  let nodes : Array PILean.Graph.Node := g.map fun node =>
    { label := node.displayLabel
      style := { shape := if node.shape == "ellipse" then some .ellipse else some .box }
      size := some (nodeSize node) }
  let mut edges : Array PILean.Graph.Edge := #[]
  let mut webEdges : Array PILean.Graph.WebEdge := #[]
  for i in [0:g.size] do
    let node := g[i]!
    let statement := eraseDups node.deps
    let proof := eraseDups node.proofDeps
    for dep in statement do
      if let some j := index.get? dep then
        let mixed := proof.contains dep
        let fromDefinition := g[j]!.shape == "box"
        edges := edges.push { src := j, dst := i }
        webEdges := webEdges.push
          { classes := if mixed then "bp_graph_edge_mixed" else ""
            width := if mixed then 1.7 else if fromDefinition then 1.2 else 1
            dash := if fromDefinition then "5 3" else "" }
    for dep in proof do
      if let some j := index.get? dep then
        if !statement.contains dep then
          edges := edges.push { src := j, dst := i }
          webEdges := webEdges.push
            { classes := "bp_graph_edge_proof", width := 1.2, dash := "1.5 3" }
  let mut clusters : Array PILean.Graph.Cluster := #[]
  if view.clusters then
    let mut members : NameMap (Array Nat) := {}
    let mut order : Array Name := #[]
    for i in [0:g.size] do
      if let some parent := g[i]!.parent? then
        if !members.contains parent then order := order.push parent
        members := members.insert parent ((members.getD parent #[]).push i)
    let groups := order.filter fun parent => (members.getD parent #[]).size > 1
    -- a group whose own node lies in another group is drawn inside it; parents come first
    let parentOf := fun (group : Name) => (index.get? group).bind fun i =>
      g[i]!.parent?.filter groups.contains
    let depth := fun (group : Name) => Id.run do
      let mut d := 0
      let mut cur := group
      for _ in [0:groups.size] do
        match parentOf cur with
        | some p => d := d + 1; cur := p
        | none => break
      return d
    let sorted := groups.qsort fun a b => depth a < depth b
    for group in sorted do
      let title := match view.groupTitle group with
        | some title => if title.trimAscii.isEmpty then toString group else title.trimAscii.toString
        | none => toString group
      clusters := clusters.push
        { name := title, members := members.getD group #[]
          parent := (parentOf group).bind fun p => sorted.idxOf? p }
  return ({ nodes, edges, clusters }, g.map webNode, webEdges)

/-- The width from which the nodes of one layer are split over rows: wide enough for a row of
ten nodes, and for a large graph the width that would make its nodes fill a drawing about twice
as wide as tall. -/
def layerWidth (graph : PILean.Graph) : Float :=
  let area := graph.nodes.foldl (init := 0) fun sum node =>
    let (width, height) := node.size.getD (0, 0)
    sum + (width + 18) * (height + 36)
  max 1800 (2.5 * area).sqrt

/-- The look of bundled routes: neighbouring lanes 8 pixels apart, the innermost corner of a
turning bundle of radius 10 (each lane further out turning about the same centre), a straight
stem of 14 pixels at every port, and at least 16 pixels between two runs on one track. -/
def bundleStyle : PILean.Graph.BundleStyle :=
  { laneGap := 8, radius := 10, stemLength := 14, trackGap := 16 }

/-- The most edges of a view drawn with bundled lanes. -/
def bundledEdgeLimit : Nat := 2000

/-- The most edges at one node of a view drawn with bundled lanes: the lanes of a node with many
more edges than its neighbours run side by side round the whole drawing. -/
def bundledDegreeLimit : Nat := 60

/-- The largest number of edges at one node of `graph` (an edge from a node to itself counted
once). -/
def maxDegree (graph : PILean.Graph) : Nat := Id.run do
  let mut degree : Array Nat := Array.replicate graph.nodes.size 0
  for e in graph.edges do
    if e.src < degree.size then degree := degree.modify e.src (· + 1)
    if e.dst != e.src && e.dst < degree.size then degree := degree.modify e.dst (· + 1)
  return degree.foldl max 0

/-- How the edges of a view of `graph` are drawn when `asked` is asked for: bundled lanes up to
`bundledEdgeLimit` edges in all and `bundledDegreeLimit` at one node, curves beyond, with the
sentence that says so. -/
def routingFor (asked : GraphRouting) (graph : PILean.Graph) : GraphRouting × Option String :=
  match asked with
  | .spline => (.spline, none)
  | .bundled =>
    let degree := maxDegree graph
    if graph.edges.size > bundledEdgeLimit then
      (.spline, some s!"This view has {graph.edges.size} edges, so it is drawn with curved \
        edges: edges are drawn in bundled lanes in views of up to {bundledEdgeLimit} edges.")
    else if degree > bundledDegreeLimit then
      (.spline, some s!"A node of this view has {degree} edges, so the view is drawn with \
        curved edges: edges are drawn in bundled lanes when no node has more than \
        {bundledDegreeLimit}.")
    else (.bundled, none)

/-- The options of the layout: the gaps between nodes and layers, how much the width of a layer
counts against the straightness of the edges (a drawing of a written blueprint then fits a page
with its labels readable), the width from which a layer is split into rows, how many extra
starts the crossing reduction makes, and how the edges are drawn. -/
def layoutOptions (leftToRight : Bool) (starts : Nat := 16) (maxLayerWidth : Float := 0)
    (routing : GraphRouting := .bundled) : PILean.Graph.LayeredOptions :=
  { direction := if leftToRight then .leftToRight else .topToBottom
    layerGap := 36, nodeGap := 18, edgeGap := 10, portStep := 10, compact := 4
    maxLayerWidth, starts
    routing := match routing with | .bundled => .bundled | .spline => .spline
    bundle := bundleStyle }

/-- The style of the layout: the margin around the drawing and the size of cluster titles. -/
def layoutStyle : PILean.Style := { margin := 12, noteSize := fontSize }

/-- The layout of a graph with its layers from the top down or from left to right, its
components packed or in one row of layers, its edges drawn as `routing` says. -/
def layoutOf (graph : PILean.Graph) (leftToRight pack : Bool) (starts : Nat := 16)
    (routing : GraphRouting := .bundled) : PILean.Graph.Layout :=
  let options := layoutOptions leftToRight starts (layerWidth graph) routing
  if pack then graph.layoutPacked options layoutStyle else graph.layout options layoutStyle

/-- One drawing of a view. -/
structure Drawing where
  /-- The view's key. -/
  variant : String
  direction : GraphDirection
  /-- Whether components are packed; `none` when the view has one component, so both are this
  drawing. -/
  pack : Option Bool
  /-- The `svg` element. -/
  svg : String
  /-- Why the drawing's edges are not drawn as the view asked (`routingFor`), when they are not. -/
  note : Option String := none

/-- Text for an attribute value: `&`, `<`, `>` and `"` escaped, and the characters XML cannot
carry (`xmlChar`) left out, since a drawing with one is not a well-formed SVG document. -/
def escapeAttribute (text : String) : String :=
  let text := String.ofList (text.toList.filter xmlChar)
  (((text.replace "&" "&amp;").replace "<" "&lt;").replace ">" "&gt;").replace "\"" "&quot;"

/-- A drawing whose nodes are images named for a reader of the page (`role="img"` and their
`accessibleName` as `aria-label`), found by the nodes' ids. -/
def withAccessibleNames (nodes : Array PILean.Graph.WebNode) (svg : String) : String :=
  let names : Std.HashMap String String := nodes.foldl (init := {}) fun m n =>
    if n.id.isEmpty then m else m.insert n.id (accessibleName n)
  match svg.splitOn "<g id=\"" with
  | [] | [_] => svg
  | first :: rest =>
    let rest := rest.map fun piece =>
      let id := (piece.splitOn "\"").head?.getD ""
      let after := (piece.drop (id.length + 1)).toString
      match names.get? id, after.splitOn ">" with
      | some name, attrs :: rest@(_ :: _) =>
        if attrs.startsWith " class=\"node" then
          s!"{id}\"{attrs} role=\"img\" aria-label=\"{escapeAttribute name}\">" ++ ">".intercalate rest
        else piece
      | _, _ => piece
    "<g id=\"".intercalate (first :: rest)

/-! ## Routes for the page

A page highlights an edge's whole route, from the port it leaves to the arrowhead it reaches,
when a reader points at the edge or at one of its nodes. The drawing carries what that needs,
computed here from the layout, so the page draws nothing of its own:

* every `path.edge` has `data-edge` (its number in the drawing), `data-from` and `data-to` (the
  ids of its nodes) and, when it shares a stem with other edges, `data-stems`: the path data of
  the part of each shared stem that is its own route (from the port to where it leaves the stem,
  and from where it joins a stem to the arrowhead);
* every `path.stem` has `data-node` and `data-port` (`out` or `in`);
* every arrowhead has `data-node` and `data-port="in"` when it is a port's (bundled routes), or
  `data-edge` when it is an edge's own (curves). -/

/-- The first and the last point of a path. -/
def pathEnds (path : PILean.Path) : Option (PILean.Point × PILean.Point) := do
  let pointOf : PILean.PathCmd → Option PILean.Point
    | .move p | .line p => some p
    | .quad _ p | .cubic _ _ p => some p
    | .close => none
  let first ← path.cmds.findSome? pointOf
  let last ← path.cmds.reverse.findSome? pointOf
  return (first, last)

/-- A segment as path data, or nothing when its ends are less than a tenth of a pixel apart. -/
def segmentData (a b : PILean.Point) : String :=
  if (a.x - b.x).abs < 0.1 && (a.y - b.y).abs < 0.1 then ""
  else s!"M{PILean.fmtNum a.x 1} {PILean.fmtNum a.y 1} L{PILean.fmtNum b.x 1} {PILean.fmtNum b.y 1}"

/-- The path data of the parts of shared stems that belong to edge `e`'s route: from its source's
exit stem's port to the start of its own path, and from the end of its own path to its target's
entry stem's end at the arrowhead. -/
def ownStems (layout : PILean.Graph.Layout) (e : PILean.Graph.RoutedEdge) : String :=
  let stemOf := fun (node : Nat) (entry : Bool) =>
    (layout.ports.find? fun p => p.node == node && p.entry == entry).bind (·.stem) |>.bind pathEnds
  match pathEnds e.path with
  | none => ""
  | some (start, stop) =>
    let out := match stemOf e.src false with
      | some (port, _) => segmentData port start
      | none => ""
    let into := match stemOf e.dst true with
      | some (_, base) => segmentData stop base
      | none => ""
    " ".intercalate ([out, into].filter (!·.isEmpty))

/-- `text` with the attributes `attrs[i]` written into the `i`-th element that starts with
`opening ++ rest` (each attribute text starts with a space): after `opening`, before `rest`. -/
def tagElements (text opening rest : String) (attrs : Array String) : String :=
  match text.splitOn (opening ++ rest) with
  | [] => text
  | first :: pieces =>
    let tagged := pieces.toArray.mapIdx fun i piece => opening ++ attrs.getD i "" ++ rest ++ piece
    first ++ String.join tagged.toList

/-- The drawing of `layout` with the attributes a page reads to highlight routes (see above);
`ids` are the nodes' element ids by number. -/
def withRouteData (layout : PILean.Graph.Layout) (ids : Array String) (svg : String) : String :=
  let id := fun (n : Nat) => escapeAttribute (ids.getD n "")
  let edgeAttrs := layout.edges.mapIdx fun i e =>
    let stems := ownStems layout e
    s!" data-edge=\"{i}\" data-from=\"{id e.src}\" data-to=\"{id e.dst}\"" ++
      (if stems.isEmpty then "" else s!" data-stems=\"{stems}\"")
  let stemAttrs := (layout.ports.filter (·.stem.isSome)).map fun p =>
    s!" data-node=\"{id p.node}\" data-port=\"{if p.entry then "in" else "out"}\""
  let headAttrs :=
    ((layout.edges.mapIdx fun i e => (i, e)).filter (·.2.head.isSome)).map (fun (i, _) =>
      s!" data-edge=\"{i}\"") ++
    (layout.ports.filter (·.head.isSome)).map fun p =>
      s!" data-node=\"{id p.node}\" data-port=\"in\""
  let svg := tagElements svg "<path" " class=\"edge" edgeAttrs
  let svg := tagElements svg "<path" " class=\"stem\"" stemAttrs
  match svg.splitOn "<g class=\"heads\"" with
  | [before, after] =>
    match after.splitOn "</g>" with
    | heads :: rest =>
      before ++ "<g class=\"heads\"" ++ tagElements heads "<path" "" headAttrs ++ "</g>" ++
        "</g>".intercalate rest
    | [] => svg
  | _ => svg

/-- A layout written for a direction: the layout of the top-down or left-to-right direction,
mirrored for the opposite one, with how its edges are drawn (`data-bp-routing`), the sentence
that says why when that is not what the view asked for (`data-bp-routing-note`), and what a page
needs to highlight routes (`withRouteData`). -/
def svgFor (layout : PILean.Graph.Layout) (nodes : Array PILean.Graph.WebNode)
    (edges : Array PILean.Graph.WebEdge) (direction : GraphDirection)
    (routing : GraphRouting := .bundled) (note : Option String := none) : String :=
  let mirrored := match direction with
    | .BT => layout.mirror true
    | .RL => layout.mirror false
    | _ => layout
  let attrs := #[("data-bp-direction", direction.rankdir), ("data-bp-routing", routing.token)] ++
    (note.map fun n => #[("data-bp-routing-note", n)]).getD #[]
  withRouteData mirrored (nodes.map (·.id)) <| withAccessibleNames nodes <|
    mirrored.toWebSvg nodes edges
      { classes := "bp_graph_drawing", fontSize, titlesBelow := direction == .BT, attrs }

/-- The directions drawn from one layout. -/
def directionsOf (leftToRight : Bool) : Array GraphDirection :=
  if leftToRight then #[.LR, .RL] else #[.TB, .BT]

/-- The text of a drawing's packing in file names and attributes: `true`, `false`, or `any` for
a view of one component. -/
def packToken : Option Bool → String
  | some true => "true" | some false => "false" | none => "any"

/-- The graph of a view with whether it has more than one component. -/
def severalComponents (graph : PILean.Graph) : Bool :=
  (PILean.Graph.components graph).any (· != 0)

/-- Every drawing of a view: the four directions, with the components packed and in one row of
layers when the view has more than one. The layouts are computed in parallel. -/
def drawings (key : String) (view : View) : Array Drawing :=
  let (graph, nodes, edges) := toLayoutGraph view
  let (routing, note) := routingFor view.routing graph
  let packs : Array (Option Bool) :=
    if severalComponents graph then #[some true, some false] else #[none]
  let jobs := #[false, true].flatMap fun leftToRight => packs.map fun pack => (leftToRight, pack)
  let tasks := jobs.map fun (leftToRight, pack) => Task.spawn fun _ =>
    let layout := layoutOf graph leftToRight (pack.getD false) (routing := routing)
    (directionsOf leftToRight).map fun direction =>
      ({ variant := key, direction, pack,
         svg := svgFor layout nodes edges direction routing note, note } : Drawing)
  tasks.flatMap (·.get)

/-- The one drawing of a view for a direction and a packing. -/
def drawing (key : String) (view : View) (direction : GraphDirection) (pack : Bool) : Drawing :=
  let (graph, nodes, edges) := toLayoutGraph view
  let (routing, note) := routingFor view.routing graph
  let pack? := if severalComponents graph then some pack else none
  let layout := layoutOf graph (direction == .LR || direction == .RL) pack (routing := routing)
  { variant := key, direction, pack := pack?, svg := svgFor layout nodes edges direction routing note
    note }

/-! ## Neighbourhood views -/

/-- The most steps of a neighbourhood view. -/
def egoMaxHops : Nat := 3

/-- The node sets of the neighbourhood views of a graph, up to `limit` nodes each: the distinct
sets (each in node order), for every node the set of its neighbourhood of one, two and three
steps along edges in either direction, and for every set whether it stands for neighbourhoods of
more than `limit` nodes; with the number of steps of the search. A search stops as soon as a
neighbourhood has more than `limit` nodes, and every such neighbourhood is the one set marked as
too large (it is never drawn), so the work for one node is at most about `3 * (limit + 1)²`
steps, whatever the graph: a hub does not make every node's search visit the whole graph. -/
def egoSetsWithin (graph : Graph Ref) (limit : Nat) :
    Array (Array Nat) × Array (Array Nat) × Array Bool × Nat := Id.run do
  let n := graph.size
  let index : NameMap Nat := Id.run do
    let mut m : NameMap Nat := {}
    for i in [0:n] do
      if !m.contains graph[i]!.label then m := m.insert graph[i]!.label i
    return m
  let mut neighbours : Array (Std.HashSet Nat) := Array.replicate n {}
  for i in [0:n] do
    for dep in graph[i]!.deps ++ graph[i]!.proofDeps do
      if let some j := index.get? dep then
        if j != i then
          neighbours := neighbours.modify i (·.insert j)
          neighbours := neighbours.modify j (·.insert i)
  let adjacent := neighbours.map fun set => set.toArray.qsort (· < ·)
  let mut sets : Array (Array Nat) := #[]
  let mut over : Array Bool := #[]
  let mut seenSets : Std.HashMap (Array Nat) Nat := {}
  let mut overId : Option Nat := none
  let mut perNode : Array (Array Nat) := Array.mkEmpty n
  let mut steps := 0
  for v in [0:n] do
    let mut inside : Std.HashSet Nat := {}
    inside := inside.insert v
    let mut frontier : Array Nat := #[v]
    let mut ids : Array Nat := #[]
    let mut tooLarge := false
    for _ in [0:egoMaxHops] do
      if !tooLarge then
        let mut next : Array Nat := #[]
        for u in frontier do
          if tooLarge then break
          for w in adjacent[u]! do
            steps := steps + 1
            if !inside.contains w then
              inside := inside.insert w
              next := next.push w
              if inside.size > limit then
                tooLarge := true
                break
        frontier := next
      if tooLarge then
        if overId.isNone then
          overId := some sets.size
          sets := sets.push #[]
          over := over.push true
        ids := ids.push (overId.getD 0)
      else
        let set := inside.toArray.qsort (· < ·)
        match seenSets.get? set with
        | some id => ids := ids.push id
        | none =>
          seenSets := seenSets.insert set sets.size
          ids := ids.push sets.size
          sets := sets.push set
          over := over.push false
    perNode := perNode.push ids
  return (sets, perNode, over, steps)

/-- `egoSetsWithin` without a limit: every neighbourhood with all its nodes. -/
def egoSets (graph : Graph Ref) : Array (Array Nat) × Array (Array Nat) :=
  let (sets, perNode, _, _) := egoSetsWithin graph graph.size
  (sets, perNode)

/-- The bit of a direction in the index's record of what is drawn. -/
def directionBit : GraphDirection → Nat
  | .TB => 1 | .BT => 2 | .LR => 4 | .RL => 8

/-- The most nodes of a neighbourhood that is drawn: a larger one is a picture of most of the
graph around a hub, slow to lay out and hard to read, and the page says that it was left out. -/
def egoNodeLimit : Nat := 150

/-- The default limit on the total size of a graph's neighbourhood drawings, in bytes. -/
def egoByteLimit : Nat := 192 * 1024 * 1024

/-- The folder of a graph's drawings inside the site's data folder. -/
def drawingsFolder (graphKey : String) : String :=
  "blueprint-graph/" ++ String.ofList (graphKey.toList.map fun c =>
    if c.isAlphanum then c else '-')

/-- Draws a graph into `dir`, for a page to read on demand:

* `v<i>-<direction>-<packing>.svg` for variant `i` of `views`, every direction, and the packings
  `true` and `false` (or `any` for a view of one component);
* `e<set>-<direction>.svg` for each distinct node set of the neighbourhood views of `graph`,
  with the layers from the top down (`TB`) and from left to right (`LR`); a page mirrors them for
  the two opposite directions. The sets are drawn smallest first, first along `direction`, then
  across; a set of more than `nodeLimit` nodes is not drawn, nor is a drawing that would take
  the neighbourhood drawings past `limit` bytes in all;
* `index.json`: for every variant key its file stem and packings; for every node the sets of its
  one, two and three step neighbourhoods; for every set its size, whether it stands for
  neighbourhoods of more than `nodeLimit` nodes (`over`, whose size is then not counted) and the
  directions drawn; how
  many drawings were left out, and the two limits.

Returns the number of neighbourhood drawings written and left out. -/
def writeDrawings (dir : System.FilePath) (views : Array (String × View))
    (graph : Graph String) (direction : GraphDirection) (routing : GraphRouting := .bundled)
    (limit : Nat := egoByteLimit) (nodeLimit : Nat := egoNodeLimit) (jobs : Nat := 8) :
    IO (Nat × Nat) := do
  IO.FS.createDirAll dir
  let mut variants : Array (String × Json) := #[]
  for (key, view) in views, i in [0:views.size] do
    let all := drawings key view
    for d in all do
      IO.FS.writeFile (dir / s!"v{i}-{d.direction.rankdir}-{packToken d.pack}.svg") d.svg
    let packs := (all.map (packToken ·.pack)).foldl
      (fun acc p => if acc.contains p then acc else acc.push p) #[]
    variants := variants.push (key, Json.mkObj [("file", s!"v{i}"), ("packs", toJson packs)])
  let (sets, perNode, over, _) := egoSetsWithin graph nodeLimit
  let small := (Array.range sets.size).filter fun id => !over[id]! && sets[id]!.size ≤ nodeLimit
  let bySize := small.qsort fun a b =>
    sets[a]!.size < sets[b]!.size || (sets[a]!.size == sets[b]!.size && a < b)
  let defaultAcross := direction == .LR || direction == .RL
  let mut drawn : Array Nat := Array.replicate sets.size 0
  let mut bytes := 0
  let mut written := 0
  let mut omitted := 2 * (sets.size - small.size)
  for leftToRight in #[defaultAcross, !defaultAcross] do
    let mut i := 0
    while i < bySize.size do
      let batch := bySize.extract i (i + jobs)
      i := i + jobs
      if bytes ≥ limit then
        omitted := omitted + batch.size
        continue
      let tasks := batch.map fun id => Task.spawn fun _ =>
        let view : View := { graph := sets[id]!.map (graph[·]!), clusters := false, routing }
        let (g, nodes, edges) := toLayoutGraph view
        let (routing, note) := routingFor view.routing g
        -- thousands of these are drawn: fewer starts each
        let layout := layoutOf g leftToRight false
          (starts := if sets[id]!.size ≤ 40 then 4 else 1) (routing := routing)
        let d : GraphDirection := if leftToRight then .LR else .TB
        (d, svgFor layout nodes edges d routing note)
      for id in batch, task in tasks do
        let (d, svg) := task.get
        if bytes + svg.utf8ByteSize > limit then
          omitted := omitted + 1
        else
          IO.FS.writeFile (dir / s!"e{id}-{d.rankdir}.svg") svg
          bytes := bytes + svg.utf8ByteSize
          written := written + 1
          drawn := drawn.modify id (· ||| directionBit d)
  let nodes := Json.mkObj <| (Array.range graph.size).toList.map fun v =>
    (toString graph[v]!.label, toJson perNode[v]!)
  let index := Json.mkObj [("version", toJson (1 : Nat)), ("variants", Json.mkObj variants.toList),
    ("hops", toJson egoMaxHops), ("nodes", nodes), ("sizes", toJson (sets.map (·.size))),
    ("over", toJson over), ("drawn", toJson drawn), ("omitted", toJson omitted),
    ("limit", toJson limit),
    ("nodeLimit", toJson nodeLimit)]
  IO.FS.writeFile (dir / "index.json") index.compress
  return (written, omitted)

end Informal.GraphLayout
