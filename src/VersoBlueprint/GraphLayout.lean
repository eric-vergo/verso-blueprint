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
Koutsofios, North and Vo): layers by network simplex, crossing reduction by weighted medians,
transposition and sifting from several starts, coordinates after Brandes and Köpf improved by
network simplex, clusters as in Sander's compound layout, components packed on shelves. The
result is deterministic: the same graph gives the same bytes.

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

/-- A view to draw: its nodes, the titles of its groups, and whether groups are drawn as
boxes around their nodes. -/
structure View where
  graph : Graph String
  groupTitle : Name → Option String := fun _ => none
  clusters : Bool := true

/-- The size of node labels. -/
def fontSize : Float := 11

/-- The lines of a node's label. -/
def labelLines (node : GraphNode Ref) : Array String :=
  (node.displayLabel.splitOn "\n").toArray

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
  | .ellipse => (max 56 (width * 1.18 + 22), 32 + extra)
  | .tab => (max 60 (width + 24), 30 + extra)
  | _ => (max 48 (width + 18), 26 + extra)

private def styleTokens (node : GraphNode Ref) : List String :=
  (node.style.splitOn ",").map (·.trimAscii.toString)

/-- The page's side of a node: its id, status classes, name, tooltip, label and colours. -/
def webNode (node : GraphNode Ref) : PILean.Graph.WebNode :=
  let tokens := styleTokens node
  { id := graphNodeSvgId node.label
    classes := node.svgClass
    name := toString node.label
    tooltip := node.tooltip?.getD ""
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

/-- The options of the layout: the gaps between nodes and layers, and how many extra starts the
crossing reduction makes. -/
def layoutOptions (leftToRight : Bool) (starts : Nat := 16) : PILean.Graph.LayeredOptions :=
  { direction := if leftToRight then .leftToRight else .topToBottom
    layerGap := 40, nodeGap := 22, edgeGap := 12, portStep := 10, starts }

/-- The style of the layout: the margin around the drawing and the size of cluster titles. -/
def layoutStyle : PILean.Style := { margin := 12, noteSize := fontSize }

/-- The layout of a graph with its layers from the top down or from left to right, its
components packed or in one row of layers. -/
def layoutOf (graph : PILean.Graph) (leftToRight pack : Bool) (starts : Nat := 16) :
    PILean.Graph.Layout :=
  let options := layoutOptions leftToRight starts
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

/-- A layout written for a direction: the layout of the top-down or left-to-right direction,
mirrored for the opposite one. -/
def svgFor (layout : PILean.Graph.Layout) (nodes : Array PILean.Graph.WebNode)
    (edges : Array PILean.Graph.WebEdge) (direction : GraphDirection) : String :=
  let mirrored := match direction with
    | .BT => layout.mirror true
    | .RL => layout.mirror false
    | _ => layout
  mirrored.toWebSvg nodes edges
    { classes := "bp_graph_drawing", fontSize, titlesBelow := direction == .BT
      attrs := #[("data-bp-direction", direction.rankdir)] }

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
  let packs : Array (Option Bool) :=
    if severalComponents graph then #[some true, some false] else #[none]
  let jobs := #[false, true].flatMap fun leftToRight => packs.map fun pack => (leftToRight, pack)
  let tasks := jobs.map fun (leftToRight, pack) => Task.spawn fun _ =>
    let layout := layoutOf graph leftToRight (pack.getD false)
    (directionsOf leftToRight).map fun direction =>
      ({ variant := key, direction, pack, svg := svgFor layout nodes edges direction } : Drawing)
  tasks.flatMap (·.get)

/-- The one drawing of a view for a direction and a packing. -/
def drawing (key : String) (view : View) (direction : GraphDirection) (pack : Bool) : Drawing :=
  let (graph, nodes, edges) := toLayoutGraph view
  let pack? := if severalComponents graph then some pack else none
  let layout := layoutOf graph (direction == .LR || direction == .RL) pack
  { variant := key, direction, pack := pack?, svg := svgFor layout nodes edges direction }

/-! ## Neighbourhood views -/

/-- The most steps of a neighbourhood view. -/
def egoMaxHops : Nat := 3

/-- The node sets of the neighbourhood views of a graph: the distinct sets (each in node order)
and, for every node, the set of its neighbourhood of one, two and three steps along edges in
either direction. -/
def egoSets (graph : Graph Ref) : Array (Array Nat) × Array (Array Nat) := Id.run do
  let n := graph.size
  let index : NameMap Nat := Id.run do
    let mut m : NameMap Nat := {}
    for i in [0:n] do
      if !m.contains graph[i]!.label then m := m.insert graph[i]!.label i
    return m
  let mut adjacent : Array (Array Nat) := Array.replicate n #[]
  for i in [0:n] do
    for dep in graph[i]!.deps ++ graph[i]!.proofDeps do
      if let some j := index.get? dep then
        if j != i then
          adjacent := adjacent.modify i (·.push j)
          adjacent := adjacent.modify j (·.push i)
  let mut sets : Array (Array Nat) := #[]
  let mut seenSets : Std.HashMap (Array Nat) Nat := {}
  let mut perNode : Array (Array Nat) := Array.mkEmpty n
  for v in [0:n] do
    let mut inside : Std.HashSet Nat := {}
    inside := inside.insert v
    let mut frontier : Array Nat := #[v]
    let mut ids : Array Nat := #[]
    for _ in [0:egoMaxHops] do
      let mut next : Array Nat := #[]
      for u in frontier do
        for w in adjacent[u]! do
          if !inside.contains w then
            inside := inside.insert w
            next := next.push w
      frontier := next
      let set := inside.toArray.qsort (· < ·)
      match seenSets.get? set with
      | some id => ids := ids.push id
      | none =>
        seenSets := seenSets.insert set sets.size
        ids := ids.push sets.size
        sets := sets.push set
    perNode := perNode.push ids
  return (sets, perNode)

/-- The bit of a direction in the index's record of what is drawn. -/
def directionBit : GraphDirection → Nat
  | .TB => 1 | .BT => 2 | .LR => 4 | .RL => 8

/-- The most nodes of a neighbourhood that is drawn: a larger one is a picture of most of the
graph around a hub, slow to lay out and hard to read, and the page says that it was left out. -/
def egoNodeLimit : Nat := 150

/-- The default limit on the total size of a graph's neighbourhood drawings, in bytes. -/
def egoByteLimit : Nat := 128 * 1024 * 1024

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
  one, two and three step neighbourhoods; for every set its size and the directions drawn; how
  many drawings were left out, and the two limits.

Returns the number of neighbourhood drawings written and left out. -/
def writeDrawings (dir : System.FilePath) (views : Array (String × View))
    (graph : Graph String) (direction : GraphDirection)
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
  let (sets, perNode) := egoSets graph
  let small := (Array.range sets.size).filter fun id => sets[id]!.size ≤ nodeLimit
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
        let view : View := { graph := sets[id]!.map (graph[·]!), clusters := false }
        let (g, nodes, edges) := toLayoutGraph view
        -- thousands of these are drawn: fewer starts each
        let layout := layoutOf g leftToRight false (starts := if sets[id]!.size ≤ 40 then 4 else 1)
        let d : GraphDirection := if leftToRight then .LR else .TB
        (d, svgFor layout nodes edges d)
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
    ("drawn", toJson drawn), ("omitted", toJson omitted), ("limit", toJson limit),
    ("nodeLimit", toJson nodeLimit)]
  IO.FS.writeFile (dir / "index.json") index.compress
  return (written, omitted)

end Informal.GraphLayout
