/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

import PILean.Svg.Inert
import PILean.Graph.Check
import VersoBlueprint.GraphLayout
import VersoBlueprintTests.Blueprint.Support
import VersoBlueprintTests.BlueprintGraph.Shared

/-!
The dependency graph is laid out and drawn while the site is built: the layout graph a view
becomes (nodes, edges and groups with the page's side of each), the drawings of a view (one per
direction and packing, deterministic, inert, escaping what a label says), the mirrored directions,
the routes of the edges (clear of nodes and of groups they do not end in, never back across the
layers), the neighbourhood sets, and the folder of drawings with its index and limit.
-/

namespace Verso.VersoBlueprintTests.BlueprintGraph.Layout

open Lean
open Informal.Graph
open Informal.GraphLayout
open Verso.VersoBlueprintTests.Blueprint.Support
open Verso.VersoBlueprintTests.BlueprintGraph.Shared

private def mk (label : Name) (deps : Array Name := #[]) (proofDeps : Array Name := #[])
    (parent? : Option Name := none) (shape : String := "ellipse") (style : String := "filled")
    (svgClass : String := "") (display? : Option String := none)
    (tooltip? : Option String := none) : GraphNode String :=
  { label, displayLabel? := display?, deps, proofDeps, parent?, shape, style,
    fillcolor := "#ffffff", svgClass, tooltip? }

/-- A graph with a group of two nodes, a definition, a node that exists only in Lean (dashed), a
node using all of them with a tooltip, an unknown reference and an isolated node. -/
private def sample : Graph String := #[
  mk `a1 (parent? := some `g),
  mk `a2 #[`a1] (parent? := some `g),
  mk `defn (shape := "box"),
  mk `lean_only (shape := "box") (style := "filled,dashed"),
  mk `user #[`defn, `a2] #[`defn, `lean_only] (tooltip? := some "Tooltip text"),
  mk `unknown (svgClass := "bp_graph_status_unresolved"),
  mk `iso #[`not_in_view]]

private def sampleView : View :=
  { graph := sample, groupTitle := fun n => if n == `g then some "Group G" else none }

/-- A graph of one component. -/
private def chain : Graph String := #[mk `p, mk `q #[`p], mk `r #[`q]]

private def chainView : View := { graph := chain }

private def count (s needle : String) : Nat := (s.splitOn needle).length - 1

private def sortedDirections (ds : Array Drawing) : Array String :=
  (ds.map (·.direction.rankdir)).qsort (· < ·)

private def allInert (ds : Array Drawing) : Bool := ds.all (PILean.Svg.isInert ·.svg)

/-- The layout graph of a view, with the page's side of its nodes and of its edges. -/
private def layoutGraph (view : View) : PILean.Graph :=
  (toLayoutGraph view).1

private def webNodes (view : View) : Array PILean.Graph.WebNode :=
  (toLayoutGraph view).2.1

private def webEdges (view : View) : Array PILean.Graph.WebEdge :=
  (toLayoutGraph view).2.2

/-! ## The layout graph -/

-- Edges run from a dependency to the node that uses it: dashed from a definition, thicker with
-- a class when statement and proof both use it, dotted with a class when only the proof does;
-- a dependency outside the view makes no edge.
/-- info: true -/
#guard_msgs in
#eval
  let g := layoutGraph sampleView
  let edges := webEdges sampleView
  g.edges.map (fun e => (e.src, e.dst)) == #[(0, 1), (2, 4), (1, 4), (3, 4)] &&
  edges.map (·.classes) == #["", "bp_graph_edge_mixed", "", "bp_graph_edge_proof"] &&
  edges.map (·.dash) == #["", "5 3", "", "1.5 3"] &&
  edges[1]!.width > edges[0]!.width && edges[1]!.width > edges[3]!.width

-- Groups of more than one node are boxes with their title; a group of one node is none; nested
-- groups are drawn inside their parents.
/-- info: true -/
#guard_msgs in
#eval
  let g := layoutGraph sampleView
  let lone := layoutGraph { sampleView with graph := #[mk `solo (parent? := some `h)] }
  let nested : Graph String := #[
    mk `inner (parent? := some `outer), mk `peer (parent? := some `outer),
    mk `leaf1 (parent? := some `inner), mk `leaf2 (parent? := some `inner)]
  let ng := layoutGraph { graph := nested }
  g.clusters.size == 1 && g.clusters[0]!.name == "Group G" && g.clusters[0]!.members == #[0, 1] &&
  lone.clusters.isEmpty &&
  ng.clusters.map (·.name) == #["outer", "inner"] &&
  ng.clusters[1]!.parent == some 0 && ng.clusters[0]!.parent.isNone &&
  (layoutGraph { sampleView with clusters := false }).clusters.isEmpty

-- The page's side of a node: its id, its status classes and name, its tooltip, a dashed outline
-- for a node that exists only in Lean, and the lines of its label.
/-- info: true -/
#guard_msgs in
#eval
  let nodes := webNodes sampleView
  nodes[3]!.dash == "5 3" && nodes[0]!.dash.isEmpty &&
  nodes[5]!.classes == "bp_graph_status_unresolved" &&
  nodes[4]!.tooltip == "Tooltip text" && nodes[0]!.tooltip.isEmpty &&
  nodes[4]!.id == graphNodeSvgId `user && nodes[4]!.name == "user" &&
  nodes[2]!.shape == .box && nodes[4]!.shape == .ellipse &&
  nodes[0]!.lines == #["a1"]

/-- info: true -/
#guard_msgs in
#eval
  let multi : GraphNode String := mk `m (display? := some "first line\nsecond line")
  let nodes := webNodes { graph := #[multi, mk `n] }
  nodes[0]!.lines == #["first line", "second line"] &&
  (nodeSize multi).2 > (nodeSize (mk `n)).2

-- A long dotted name is broken after dots into lines of at most 28 characters where its
-- components allow; other labels keep their lines, and nothing of a label is lost.
/-- info: true -/
#guard_msgs in
#eval
  let long := "Project.Analysis.SpecialFunctions.Complex.LogBounds"
  let node := mk `long (display? := some long)
  labelLines node == #["Project.Analysis.", "SpecialFunctions.Complex.", "LogBounds"] &&
  String.join (labelLines node).toList == long &&
  wrapDotted "a_label_without_any_dot_that_is_longer_than_a_line" ==
    #["a_label_without_any_dot_that_is_longer_than_a_line"] &&
  wrapDotted "Short.name" == #["Short.name"] &&
  wrapDotted "A.ComponentLongerThanALineIsNeverBrokenInside.b" 20 ==
    #["A.", "ComponentLongerThanALineIsNeverBrokenInside.", "b"] &&
  (webNodes { graph := #[node] })[0]!.lines.size == 3 &&
  (nodeSize node).1 < (PILean.Graph.sansWidth long fontSize)

/-! ## The drawings -/

-- A drawing is the same on every call, and every node is in it exactly once under its id.
/-- info: true -/
#guard_msgs in
#eval
  let first := drawings "full" sampleView
  let again := drawings "full" sampleView
  first.map (·.svg) == again.map (·.svg) &&
  first.all fun d => d.svg.startsWith "<svg " &&
    sample.all fun node => count d.svg s!"id=\"{graphNodeSvgId node.label}\"" == 1

-- The one drawing of a view for a direction and packing is its entry in `drawings`.
/-- info: true -/
#guard_msgs in
#eval
  let all := drawings "full" sampleView
  [GraphDirection.TB, .BT, .LR, .RL].all fun direction =>
    [true, false].all fun pack =>
      match all.find? (fun d => d.direction == direction && d.pack == some pack) with
      | some d => (drawing "full" sampleView direction pack).svg == d.svg
      | none => false

-- Every drawing of every kind of view is inert: no script, link or handler.
/-- info: true -/
#guard_msgs in
#eval
  let groupView : View := { graph := mkParentOverviewGraph sample #[`g] {}, clusters := false }
  allInert (drawings "full" sampleView) && allInert (drawings "group" groupView) &&
  allInert (drawings "chain" chainView) &&
  (drawings "full" sampleView).size > 0

-- Labels, tooltips and titles are text: markup in them is escaped.
/-- info: true -/
#guard_msgs in
#eval
  let hostile := "</script><img src=x onerror=alert(1)> \"q\" 'a' & <b>"
  let graph : Graph String := #[
    mk `h1 (display? := some hostile) (tooltip? := some hostile) (parent? := some `grp),
    mk `h2 #[`h1] (parent? := some `grp)]
  let view : View := { graph, groupTitle := fun _ => some hostile }
  let ds := drawings "hostile" view
  ds.size > 0 && allInert ds &&
  ds.all fun d =>
    !hasSubstr d.svg "</script" && !hasSubstr d.svg "<img" && !hasSubstr d.svg "<b>" &&
    hasSubstr d.svg "&lt;/script&gt;&lt;img src=x onerror=alert(1)&gt;" &&
    hasSubstr d.svg "&amp;"

-- A view gets the four directions; with several components, each both packed and unpacked; with
-- one component, one drawing of each direction for both settings.
/-- info: true -/
#guard_msgs in
#eval
  let several := drawings "full" sampleView
  let one := drawings "chain" chainView
  several.size == 8 &&
  (several.filter (·.pack == some true)).size == 4 &&
  (several.filter (·.pack == some false)).size == 4 &&
  sortedDirections (several.filter (·.pack == some true)) == #["BT", "LR", "RL", "TB"] &&
  one.size == 4 && one.all (·.pack.isNone) &&
  sortedDirections one == #["BT", "LR", "RL", "TB"] &&
  several.all (·.variant == "full") && one.all (·.variant == "chain") &&
  packToken (some true) == "true" && packToken (some false) == "false" && packToken none == "any"

-- Each direction is drawn as such, and the layers of the top-down drawing run downwards.
/-- info: true -/
#guard_msgs in
#eval
  (drawings "chain" chainView).all fun d =>
    hasSubstr d.svg s!"data-bp-direction=\"{d.direction.rankdir}\""

-- The bottom-up layout is the top-down layout mirrored: every node box has its size, at the
-- height turned upside down; left to right and right to left likewise.
/-- info: true -/
#guard_msgs in
#eval
  let g := layoutGraph sampleView
  [false, true].all fun leftToRight =>
    [false, true].all fun pack =>
      let l := layoutOf g leftToRight pack
      [true, false].all fun vertical =>
        let m := l.mirror vertical
        m.width == l.width && m.height == l.height && m.nodes.size == l.nodes.size &&
        (l.nodes.zip m.nodes).all fun (a, b) =>
          a.box.width == b.box.width && a.box.height == b.box.height &&
          if vertical then
            b.box.x0 == a.box.x0 && b.box.y0 == l.height - a.box.y1
          else
            b.box.y0 == a.box.y0 && b.box.x0 == l.width - a.box.x1

-- The drawing of a mirrored direction has the same nodes as the other (with the same boxes
-- sizes, hence the same bytes in length, as the mirrored layout is a reflection).
/-- info: true -/
#guard_msgs in
#eval
  let ds := drawings "chain" chainView
  match ds.find? (·.direction == .TB), ds.find? (·.direction == .BT) with
  | some tb, some bt =>
    tb.svg != bt.svg && count tb.svg "<text" == count bt.svg "<text" &&
    count tb.svg "class=\"node" == count bt.svg "class=\"node"
  | _, _ => false

-- A node whose replay is not accepted does not get the class the success colours hang on.
/-- info: true -/
#guard_msgs in
#eval
  let classes := fun (replay : NodeReplay) =>
    nodeStatusClasses .theorem .formalized .formalizedWithAncestors {} replay
  let graph : Graph String := #[
    mk `accepted (svgClass := classes .accepted),
    mk `plain (svgClass := classes .none),
    mk `dependent #[`accepted, `plain] (svgClass := classes .acceptedWithDependencies)]
  let nodeGroup := fun (svg : String) (label : Name) =>
    ((svg.splitOn s!"id=\"{graphNodeSvgId label}\"")[1]!.splitOn "</g>")[0]!
  (drawings "replay" { graph }).all fun d =>
    hasSubstr (nodeGroup d.svg `accepted) "bp_replay_accepted" &&
    !hasSubstr (nodeGroup d.svg `plain) "bp_replay_accepted" &&
    hasSubstr (nodeGroup d.svg `dependent) "bp_replay_accepted"

-- Node classes, names and tooltips reach the drawing; a dashed node has dashed lines.
/-- info: true -/
#guard_msgs in
#eval
  let d := (drawing "full" sampleView .TB true).svg
  hasSubstr d "<title>user</title>" && hasSubstr d "<desc>Tooltip text</desc>" &&
  hasSubstr d "class=\"node bp_graph_status_unresolved\"" &&
  hasSubstr d "stroke-dasharray=\"5 3\"" && hasSubstr d "class=\"edge bp_graph_edge_mixed\"" &&
  hasSubstr d "class=\"edge bp_graph_edge_proof\"" && hasSubstr d "Group G" &&
  hasSubstr d "class=\"cluster\""

/-! ## The routes of the edges -/

/-- Two groups joined through a third node, a node used across both, and a long edge past
them: the edges have groups to go round. -/
private def grouped : Graph String := #[
  mk `top,
  mk `u1 #[`top] (parent? := some `upper), mk `u2 #[`u1] (parent? := some `upper),
  mk `between #[`u2],
  mk `l1 #[`between] (parent? := some `lower), mk `l2 #[`l1, `u1] (parent? := some `lower),
  mk `side #[`top], mk `last #[`l2, `top, `side]]

private def points (path : PILean.Path) : Array PILean.Point :=
  (path.flatten 0.5).foldl (fun acc line => acc ++ line.points) #[]

-- No edge passes a node it does not end at, or through a group that holds neither of its ends,
-- and the boxes of the groups hold exactly their nodes, in every direction and packing.
/-- info: true -/
#guard_msgs in
#eval
  [sampleView, { graph := grouped }].all fun view =>
    let g := layoutGraph view
    [false, true].all fun leftToRight =>
      [false, true].all fun pack =>
        let l := layoutOf g leftToRight pack
        (PILean.Graph.clearanceProblems g l).isEmpty && (PILean.Graph.clusterProblems g l).isEmpty

-- An edge never turns back across the layers (no edge runs round the outside of the drawing),
-- and an edge between neighbouring layers with nothing in its way is one straight line.
/-- info: true -/
#guard_msgs in
#eval
  let g := layoutGraph { graph := grouped }
  let down := (layoutOf g false false).edges.all fun e =>
    let ps := points e.path
    (Array.range (ps.size - 1)).all fun i => ps[i]!.y ≤ ps[i + 1]!.y + 1e-6
  let across := (layoutOf g true false).edges.all fun e =>
    let ps := points e.path
    (Array.range (ps.size - 1)).all fun i => ps[i]!.x ≤ ps[i + 1]!.x + 1e-6
  let straight := (layoutOf (layoutGraph chainView) false false).edges.all fun e =>
    e.points.size == 2
  down && across && straight

-- The check sees a fault: an edge drawn through the middle of another node is reported.
/-- info: true -/
#guard_msgs in
#eval
  let g := layoutGraph { graph := grouped }
  let l := layoutOf g false false
  let box := l.nodes[3]!.box
  let through := ((PILean.Path.empty.moveTo ⟨box.x0 - 5, (box.y0 + box.y1) / 2⟩).lineTo
    ⟨box.x1 + 5, (box.y0 + box.y1) / 2⟩)
  let bad := { l with edges := l.edges.modify 0 fun e => { e with path := through } }
  (PILean.Graph.clearanceProblems g l).isEmpty && !(PILean.Graph.clearanceProblems g bad).isEmpty

-- The options: the width of a layer counts in the coordinates, and a layer is split into rows
-- from a width that grows with the graph and is never less than a row of about ten nodes.
/-- info: true -/
#guard_msgs in
#eval
  let small := layoutGraph sampleView
  let wide : Graph String := (Array.range 120).map fun i => mk (Name.mkSimple s!"leaf{i}") #[`hub]
  let star := layoutGraph { graph := #[mk `hub] ++ wide }
  let unsplit := star.layout (layoutOptions false) layoutStyle
  (layoutOptions false).compact == 4 && (layoutOptions true (maxLayerWidth := 7)).maxLayerWidth == 7 &&
  layerWidth small == 1800 && layerWidth star ≥ 1800 &&
  (layoutOf star false false).width < unsplit.width / 2 &&
  (layoutOf star false false).height > unsplit.height

/-! ## Neighbourhoods -/

/-- A path `a → b → c → d → e` and a node `f` apart, one edge through a proof dependency. -/
private def pathGraph : Graph String := #[
  mk `a, mk `b #[`a], mk `c #[`b], mk `d #[] #[`c], mk `e #[`d], mk `f]

-- The neighbourhoods of one, two and three steps along edges in either direction; sets that are
-- equal are one set.
/-- info: true -/
#guard_msgs in
#eval
  let sets : Array (Array Nat) := (egoSets pathGraph).1
  let perNode : Array (Array Nat) := (egoSets pathGraph).2
  let set := fun (v k : Nat) => sets[perNode[v]![k]!]!
  perNode.size == 6 && perNode.all (·.size == egoMaxHops) &&
  set 0 0 == #[0, 1] && set 0 1 == #[0, 1, 2] && set 0 2 == #[0, 1, 2, 3] &&
  set 2 0 == #[1, 2, 3] && set 2 1 == #[0, 1, 2, 3, 4] && set 2 2 == #[0, 1, 2, 3, 4] &&
  set 4 0 == #[3, 4] && set 4 2 == #[1, 2, 3, 4] &&
  set 5 0 == #[5] && set 5 2 == #[5] &&
  -- shared sets
  perNode[2]![1]! == perNode[2]![2]! && perNode[1]![2]! == perNode[2]![1]! &&
  perNode[5]![0]! == perNode[5]![2]! &&
  -- no two sets are equal
  sets.toList.eraseDups.length == sets.size

/-! ## The folder of drawings -/

/-- The names of the files of a folder. -/
private def fileNames (dir : System.FilePath) : IO (Array String) := do
  return (← dir.readDir).map (·.fileName)

private def packsOf (index : Json) (key : String) : Array String :=
  ((index.getObjVal? "variants").toOption.bind (·.getObjVal? key |>.toOption)
    |>.bind (·.getObjValAs? (Array String) "packs" |>.toOption)).getD #[]

-- The folder holds the drawings the index names, and the index says what is drawn.
/-- info: true -/
#guard_msgs in
#eval IO.FS.withTempDir fun tmp => do
  let dir := tmp / "drawings"
  let views := #[("full", sampleView), ("chain", chainView)]
  let (written, omitted) ← writeDrawings dir views sample .TB
  let some index := (Json.parse (← IO.FS.readFile (dir / "index.json"))).toOption
    | return false
  let names ← fileNames dir
  let fullPacks := packsOf index "full"
  let chainPacks := packsOf index "chain"
  let drawn := (index.getObjValAs? (Array Nat) "drawn").toOption.getD #[]
  let sizes := (index.getObjValAs? (Array Nat) "sizes").toOption.getD #[]
  let sets : Array (Array Nat) := (egoSets sample).1
  let mut egoFiles := 0
  for id in [0:sets.size] do
    for (bit, name) in [(1, "TB"), (4, "LR")] do
      let there := names.contains s!"e{id}-{name}.svg"
      if there != (drawn[id]! &&& bit != 0) then return false
      if there then egoFiles := egoFiles + 1
  let mut variantsOk := true
  for (stem, packs) in [("v0", fullPacks), ("v1", chainPacks)] do
    for pack in packs do
      for direction in ["TB", "BT", "LR", "RL"] do
        variantsOk := variantsOk && names.contains s!"{stem}-{direction}-{pack}.svg"
  let svgText ← IO.FS.readFile (dir / "v0-TB-true.svg")
  return omitted == 0 && written == egoFiles && written == 2 * sets.size &&
    (index.getObjValAs? Nat "omitted").toOption == some 0 &&
    (index.getObjValAs? Nat "limit").toOption == some egoByteLimit &&
    fullPacks == #["true", "false"] && chainPacks == #["any"] && variantsOk &&
    sizes == sets.map (fun (set : Array Nat) => set.size) && drawn.size == sets.size && drawn.all (· == 5) &&
    svgText == (drawing "full" sampleView .TB true).svg &&
    ((index.getObjVal? "nodes").toOption.bind (·.getObjVal? "user" |>.toOption)).isSome &&
    names.contains "index.json"

-- A limit on the neighbourhood drawings leaves some out, says so in the index, and keeps the
-- total size of the drawings written within it; the drawings of the views are not limited.
/-- info: true -/
#guard_msgs in
#eval IO.FS.withTempDir fun tmp => do
  let views := #[("full", sampleView)]
  let (fullWritten, _) ← writeDrawings (tmp / "all") views sample .TB
  let mut total := 0
  for f in ← (tmp / "all").readDir do
    if f.fileName.startsWith "e" then total := total + (← IO.FS.readFile f.path).utf8ByteSize
  let limit := total / 2
  let (written, omitted) ← writeDrawings (tmp / "some") views sample .TB (limit := limit)
  let some index := (Json.parse (← IO.FS.readFile (tmp / "some" / "index.json"))).toOption
    | return false
  let drawn := (index.getObjValAs? (Array Nat) "drawn").toOption.getD #[]
  let mut bytes := 0
  let mut files := 0
  for f in ← (tmp / "some").readDir do
    if f.fileName.startsWith "e" then
      bytes := bytes + (← IO.FS.readFile f.path).utf8ByteSize
      files := files + 1
  let tinyWritten ← writeDrawings (tmp / "tiny") views sample .TB (limit := 1)
  let tinyEntries : Array IO.FS.DirEntry ← (tmp / "tiny").readDir
  let tinyFiles := tinyEntries.filter fun (e : IO.FS.DirEntry) => e.fileName.startsWith "e"
  return omitted > 0 && written > 0 && written + omitted == fullWritten &&
    (index.getObjValAs? Nat "omitted").toOption == some omitted &&
    (index.getObjValAs? Nat "limit").toOption == some limit &&
    bytes ≤ limit && files == written &&
    (drawn.foldl (fun n m => n + (if m &&& 1 != 0 then 1 else 0) +
      (if m &&& 4 != 0 then 1 else 0)) 0) == written &&
    (← (tmp / "some" / "v0-TB-true.svg").pathExists) &&
    tinyWritten.1 == 0 && tinyWritten.2 == fullWritten && tinyFiles.isEmpty

-- A neighbourhood of more than `nodeLimit` nodes is not drawn, and the index says so with the
-- limit: all such neighbourhoods are the one set marked `over`, whose search stopped at the limit.
/-- info: true -/
#guard_msgs in
#eval IO.FS.withTempDir fun tmp => do
  let views := #[("full", sampleView)]
  let big := (egoSets sample).1.filter fun (set : Array Nat) => set.size > 3
  let (sets, _, over, _) := egoSetsWithin sample 3
  let (written, omitted) ← writeDrawings (tmp / "d") views sample .TB (nodeLimit := 3)
  let some index := (Json.parse (← IO.FS.readFile (tmp / "d" / "index.json"))).toOption
    | return false
  let drawn := (index.getObjValAs? (Array Nat) "drawn").toOption.getD #[]
  let overs := (index.getObjValAs? (Array Bool) "over").toOption.getD #[]
  let overCount := (over.filter id).size
  return !big.isEmpty && overCount == 1 && overs == over &&
    omitted == 2 * overCount && written == 2 * (sets.size - overCount) &&
    (index.getObjValAs? Nat "nodeLimit").toOption == some 3 &&
    (index.getObjValAs? Nat "omitted").toOption == some omitted &&
    (Array.range sets.size).all fun id =>
      (drawn[id]! == 0) == over[id]! && (over[id]! || (sets[id]!.size ≤ 3 && drawn[id]! == 5))

-- The folder of a graph is named from its key with every character that is not a letter or a
-- digit replaced.
/-- info: true -/
#guard_msgs in
#eval
  drawingsFolder "graph:a/b c" == "blueprint-graph/graph-a-b-c" &&
  drawingsFolder "Plain1" == "blueprint-graph/Plain1"

-- The neighbourhood search is bounded by the size of what can be drawn: on a star of 10,000
-- leaves every leaf's two-step neighbourhood is the whole graph, and the search stops at the
-- node limit instead of visiting it, for every leaf. Those neighbourhoods are one set marked as
-- too large, and the small ones are as before.
/-- info: (true, true, true, true) -/
#guard_msgs in
#eval
  let leaves := 10000
  let star : Graph String := #[mk `hub] ++
    (Array.range leaves).map fun i => mk (.mkSimple s!"leaf{i}") #[`hub]
  let (sets, perNode, over, steps) := egoSetsWithin star 150
  let overIds := (Array.range sets.size).filter (over[·]!)
  (decide (steps < (leaves + 1) * 3 * 160), overIds.size == 1,
   -- a leaf: itself and the hub after one step, then too large
   (perNode[1]!.extract 1 3).all (overIds.contains ·) && sets[perNode[1]![0]!]!.size == 2,
   (egoSetsWithin pathGraph 150).1 == (egoSets pathGraph).1)

end Verso.VersoBlueprintTests.BlueprintGraph.Layout
