/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude (Anthropic)
-/

import PILean.Svg.Inert
import VersoBlueprint.GraphLayout
import VersoBlueprint.GraphNames
import VersoBlueprintTests.Blueprint.Support
import VersoBlueprintTests.BlueprintGraph.Shared

/-!
A node of the dependency graph with a Lean statement shows the short name of one declaration of
its statement in the code face, on up to two lines, with the count of further declarations after
it; a node without a Lean statement shows its number. The names: which declaration a node shows,
their shortening and disambiguation over a graph, which declarations they come from, and how the
drawings carry them with the number beside them and the full names in the node's title.
-/

namespace Verso.VersoBlueprintTests.BlueprintGraph.LeanNames

open Lean
open Informal
open Informal.Data
open Informal.Graph
open Informal.GraphLayout
open Informal.GraphNames
open Verso.VersoBlueprintTests.Blueprint.Support
open Verso.VersoBlueprintTests.BlueprintGraph.Shared

/-- A node whose statement has the declarations `names` (theorems unless `theorems := false`). -/
private def node (names : List Name) (theorems : Bool := true) (number : String := "Theorem 1.1") :
    Input :=
  { decls := names.toArray.map ({ name := ·, isTheorem := theorems }), theoremNode := theorems
    number }

private def linesOf (labels : Array (Option GraphNames.Label)) : Array (Option (Array String)) :=
  labels.map (·.map (·.lines))

private def count (s needle : String) : Nat := (s.splitOn needle).length - 1

/-- Whether no two labels of `labels` read alike: neither the same text nor the same text around
their ellipses, unless they carry different numbers under them. -/
private def distinct (labels : Array (Option GraphNames.Label)) : Bool :=
  let shown := labels.filterMap id |>.map fun l => (l.text, l.quiet)
  shown.all fun (a, qa) => shown.all fun (b, qb) =>
    (a, qa) == (b, qb) || qa.isSome && qb.isSome && qa != qb ||
      (alikeKeys a).all fun k => !(alikeKeys b).contains k

/-! ## Names -/

-- One declaration: its last component; a node without declarations has no name.
/-- info: true -/
#guard_msgs in
#eval
  linesOf (labels #[node [`Project.Analysis.rho_irrational], node []]) ==
    #[some #["rho_irrational"], none]

-- Several declarations: the shown one with the count of the others; a declaration given twice
-- counts once.
/-- info: true -/
#guard_msgs in
#eval
  labels #[node [`P.first, `P.second, `Q.third, `P.second]] ==
    #[some { lines := #["first"], name := `P.first, more := 2 }]

-- Two nodes whose names end alike show as many trailing components as tell them apart; a
-- node's own further declarations count too; a name whose components run out is shown whole.
/-- info: true -/
#guard_msgs in
#eval
  linesOf (labels #[node [`A.B.foo], node [`A.C.foo], node [`D.foo], node [`bar]]) ==
      #[some #["B.foo"], some #["C.foo"], some #["D.foo"], some #["bar"]] &&
    linesOf (labels #[node [`A.x.foo], node [`B.x.foo]]) == #[some #["A.x.foo"], some #["B.x.foo"]] &&
    linesOf (labels #[node [`M.same, `K.same]]) == #[some #["M.same"]] &&
    linesOf (labels #[node [`A.foo], node [`foo]]) == #[some #["A.foo"], some #["foo"]]

-- A last component that does not name a declaration to a reader (a number, a name that starts
-- with `_`) keeps the components before it; the prefix of a private declaration and macro
-- scopes are not shown; an anonymous name is no name.
/-- info: true -/
#guard_msgs in
#eval
  let priv := Name.mkNum (`_private ++ `Project.Module) 0 ++ `Project.hidden
  linesOf (labels #[node [Name.mkNum `Project.lemma 3], node [`Project.thm._proof_1], node [priv],
      node [Name.anonymous], node [Name.anonymous, `Project.real]]) ==
    #[some #["lemma.3"], some #["thm._proof_1"], some #["hidden"], none, some #["real"]] &&
  readableLength (Name.mkNum (Name.mkNum `a 1) 2) == 3 &&
  readableLength (Name.mkSimple "_x") == 1

-- Names that are not identifiers are written with guillemets; other non-ASCII names as they are.
/-- info: true -/
#guard_msgs in
#eval
  linesOf (labels #[node [Name.str `Project "α-lemma"], node [`Project.ρ_irrational]]) ==
    #[some #["«α-lemma»"], some #["ρ_irrational"]]

-- A long name takes two lines of at most `maxLineLength` characters, broken after a `.`, else a
-- `_`, else between camel-case words, as evenly as it can; a longer one is cut in its last
-- component at `_` boundaries, keeping its beginning and its end; a name without such
-- boundaries is broken or cut in characters, never repeating any.
/-- info: true -/
#guard_msgs in
#eval
  let ls := linesOf (labels #[node [`P.differentiableOn_abelSeries_chi4],
    node [`P.eventuallyPeriodic_of_tsum_div_two_pow_mem_range_ratCast],
    node [`P.instFGSubtypePermMemSubgroupCompoundSymmetryGroupOfFiniteOfIsometryEquivElemClosedBall]])
  ls == #[some #["differentiableOn_", "abelSeries_chi4"],
      some #["eventuallyPeriodic_", "of…mem_range_ratCast"],
      some #["instFGSubtypePermMem", "…EquivElemClosedBall"]] &&
    ls.all (·.all (·.all (·.length ≤ maxLineLength))) &&
    fitLines "short" == some #["short"] && cutMiddle "short" 10 == "short" &&
    -- a camel-case name breaks between its words; a name too long for that, in characters
    fitLines "previewExternalMissing" == some #["preview", "ExternalMissing"] &&
    layoutName `P.abcdefghijklmnopqrstuvwxyz 1 == #["abcdefghijklmnopqrst", "uvwxyz"] &&
    (layoutName (Name.mkSimple (String.ofList (List.replicate 50 'a'))) 1).map (·.length) == #[20, 20]

-- Two nodes that a namespace tells apart show it in full on both, even when their last
-- components must be cut, and their labels never read alike.
/-- info: true -/
#guard_msgs in
#eval
  let ls := labels #[node [`RokickiConstant.PNT.not_exists_abs_sum_chi4_sub_mul_le],
    node [`RokickiConstant.not_exists_abs_sum_chi4_sub_mul_le]]
  linesOf ls == #[some #["PNT.not_exists_abs_", "sum_chi4_sub_mul_le"],
      some #["RokickiConstant.not…", "sum_chi4_sub_mul_le"]] &&
    distinct ls

-- Nodes that show the same declaration show their numbers under their names; so do nodes whose
-- cut labels would read alike.
/-- info: true -/
#guard_msgs in
#eval
  let same := labels #[node [`Nat.add] false "Definition 1.3", node [`Nat.add] false "Definition 6.1",
    node [`Nat.mul] false "Definition 6.2"]
  let cut := labels #[node [`P.sum_range_succ_mul_alpha_beta_gamma_eq_sum_mul_sub],
    node [`P.sum_range_succ_mul_delta_epsilon_zeta_eq_sum_mul_sub] (number := "Lemma 2.4")]
  same == #[some { lines := #["add"], name := `Nat.add, more := 0, quiet := some "Definition 1.3" },
      some { lines := #["add"], name := `Nat.add, more := 0, quiet := some "Definition 6.1" },
      some { lines := #["mul"], name := `Nat.mul, more := 0 }] &&
    cut.all (·.any (·.quiet.isSome)) && distinct same && distinct cut

/-! ## The declaration a node shows -/

private def decl (name : Name) (isTheorem : Bool := false) : LeanName := { name, isTheorem }

-- A theorem-like node shows its first theorem, also after a helper definition; a definition
-- shows its first definition that is not a constructor, field or recursor of another of its
-- declarations, nor an instance; without one, the first declaration.
/-- info: true -/
#guard_msgs in
#eval
  chooseShown true #[decl `P.helper, decl `P.main true] == 1 &&
    chooseShown false #[decl `P.Stage, decl `P.Stage.initial, decl `P.Stage.rec] == 0 &&
    chooseShown false #[decl `P.Stage.initial, decl `P.Stage] == 1 &&
    chooseShown false #[decl `P.instFGFoo, decl `P.foo_fg] == 1 &&
    chooseShown false #[decl `P.instFGFoo] == 0 &&
    shownFirst #[decl `P.a, decl `P.b, decl `P.c] 1 == #[decl `P.b, decl `P.a, decl `P.c]

/-! ## The declarations of a node -/

private def attached (n : Name) (present : Bool := true) (kind := NodeKind.definition) :
    ExternalRef :=
  { written := n, canonical := n, present, kind }

private def codeOf (defs : Array (Name × Nat)) (thms : Array (Name × Nat)) : Code :=
  { stx := .missing
    definedDefs := defs.map fun (name, commandIndex) => { name, commandIndex }
    definedTheorems := thms.map fun (name, commandIndex) => { name, commandIndex } }

-- The statement's declarations in the order the author wrote them: attached ones (present or
-- missing, theorem-like by their kind), then each code block's in source order, a type before the
-- constructors and fields its command declares too, whatever order they were recorded in. A node
-- whose Lean code is attached only to its proof, or whose code block defines no named
-- declaration, has none.
/-- info: true -/
#guard_msgs in
#eval
  let both : Node := {
    kind := NodeKind.theorem
    externalRefs := #[attached `P.b (kind := .theorem), attached `P.a (present := false)]
    literateCodes := #[codeOf #[(`P.d, 2)] #[(`P.c, 1)], codeOf #[] #[(`P.e, 0)]] }
  let structure_ : Node := {
    kind := NodeKind.definition
    literateCodes := #[codeOf #[(`P.Pair.fst, 0), (`P.Pair.mk, 0), (`P.Pair, 0), (`P.Pair.snd, 0),
      (`P.helper, 1)] #[]] }
  let proofOnly : Node := { kind := NodeKind.theorem, proofExternalRefs := #[attached `P.helper] }
  let examples : Node := { kind := NodeKind.theorem, literateCodes := #[codeOf #[] #[]] }
  let names := statementDeclarationNames both
  names.map (·.name) == #[`P.b, `P.a, `P.c, `P.d, `P.e] &&
    names.map (·.isTheorem) == #[true, false, true, false, true] &&
    names.map (·.present) == #[true, false, true, true, true] &&
    (statementDeclarationNames structure_).map (·.name) ==
      #[`P.Pair, `P.Pair.fst, `P.Pair.mk, `P.Pair.snd, `P.helper] &&
    chooseShown false (statementDeclarationNames structure_) == 0 &&
    statementDeclarationNames proofOnly == #[] &&
    statementDeclarationNames examples == #[]

private def state : Environment.State :=
  mkState [
    (`stmt, {
      kind := NodeKind.theorem
      externalRefs := #[attached `Project.aux, attached `Project.rho_irrational (kind := .theorem),
        attached `Project.gone (present := false)] }),
    (`proof_only, {
      kind := NodeKind.theorem
      proofExternalRefs := #[attached `Project.helper]
      statement := some (mkInformal #[`stmt]) }),
    (`other, { kind := NodeKind.definition, externalRefs := #[attached `Other.rho_irrational] })]

private def titles : Name → Option String
  | `stmt => some "Theorem 1.1"
  | `proof_only => some "Theorem 1.2"
  | `other => some "Definition 1.3"
  | _ => none

private def graphOf (nodeText : GraphNodeText := .name) : GraphData :=
  (buildModel state #[`stmt, `proof_only, `other] (resolveTitle? := titles)).finish "g"
    { nodeText }

-- The graph data carries every declaration of each node's statement in the author's order; the
-- drawn nodes get a label for the whole graph: the theorem node shows its theorem, not the helper
-- attached first, `Project.rho_irrational` and `Other.rho_irrational` tell each other apart, and
-- the node whose Lean code is attached only to its proof keeps its number.
/-- info: true -/
#guard_msgs in
#eval
  let g := graphOf
  let drawn := g.renderGraph
  hasGraphDataNodeWith g `stmt
      (·.leanNames.map (·.name) == #[`Project.aux, `Project.rho_irrational, `Project.gone]) &&
    hasGraphDataNodeWith g `proof_only (·.leanNames.isEmpty) &&
    hasNodeWith drawn `stmt (fun n => n.leanLines == #["Project.", "rho_irrational"] &&
      n.leanMore == 2 &&
      n.leanNames.map (·.name) == #[`Project.rho_irrational, `Project.aux, `Project.gone]) &&
    hasNodeWith drawn `other (·.leanLines == #["Other.rho_irrational"]) &&
    hasNodeWith drawn `proof_only (fun n => n.leanLines.isEmpty && n.caption? == some "Theorem 1.2")

/-! ## Drawings -/

private def drawingOf (nodeText : GraphNodeText) : String :=
  let g := graphOf nodeText
  (drawing "full" { graph := g.renderGraph, nodeText } .TB true).svg

-- A drawn node with a Lean label holds its lines in the code face with the count after the last,
-- and its number as `text.bp_graph_label_number`; the one the site does not show first is
-- hidden. Its title lists its number and the full names of its declarations, the shown one first
-- and a missing one marked; the group keeps the node's name. A node without a Lean statement
-- shows its number as before. The drawing stays inert.
/-- info: true -/
#guard_msgs in
#eval
  let byName := drawingOf .name
  let byNumber := drawingOf .number
  count byName "class=\"bp_graph_label_name\"" == 3 &&
    count byName "class=\"bp_graph_label_number\" display=\"none\"" == 2 &&
    hasSubstr byName ">Project.</text>" &&
    hasSubstr byName ">rho_irrational<tspan class=\"bp_graph_label_more\"" &&
    hasSubstr byName ">+2</tspan></text>" &&
    hasSubstr byName s!"font-family=\"{codeFontFamily}\"" &&
    hasSubstr byName ">Theorem 1.2</text>" &&
    hasSubstr byName "<title>Theorem 1.1 (stmt)\nProject.rho_irrational\nProject.aux\nProject.gone (not found)</title>" &&
    hasSubstr byName "data-bp-node-name=\"stmt\" data-bp-node-hover=\"\" class=\"node" &&
    hasSubstr byName "<title>proof_only</title>" &&
    count byNumber "class=\"bp_graph_label_number\" x=" == 2 &&
    count byNumber "display=\"none\">rho_irrational" == 1 &&
    PILean.Svg.isInert byName && PILean.Svg.isInert byNumber

-- The accessible name keeps the number, the label and the status words, and names the full
-- Lean declarations, the shown one first.
/-- info: true -/
#guard_msgs in
#eval
  let web : PILean.Graph.WebNode :=
    { name := "stmt", lines := #["Theorem 1.1"], tooltip := "Lean proof complete" }
  accessibleName web #[`Project.rho_irrational] ==
      "Theorem 1.1 (stmt), Lean name Project.rho_irrational: Lean proof complete" &&
    accessibleName web #[`P.a, `P.b] == "Theorem 1.1 (stmt), Lean names P.a, P.b: Lean proof complete" &&
    accessibleName web == "Theorem 1.1 (stmt): Lean proof complete" &&
    hasSubstr (drawingOf .name)
      "aria-label=\"Theorem 1.1 (stmt), Lean names Project.rho_irrational, Project.aux, Project.gone"

-- A node's box holds the wider and taller of its two labels, so it fits whichever a reader
-- shows: a long name widens it, a second line makes it taller, a short one leaves the number's
-- size.
/-- info: true -/
#guard_msgs in
#eval
  let base : GraphNode String :=
    { label := `n, caption? := some "Theorem 1.1", fillcolor := "#fff", deps := #[] }
  let named := { base with leanLines := #["a_rather_long_name"], leanMore := 2 }
  let twoLines := { base with leanLines := #["differentiableOn_", "abelSeries_chi4"] }
  let quiet := { base with leanLines := #["add"], leanQuiet? := some "Definition 6.1" }
  let shortNamed := { base with leanLines := #["f"] }
  (nodeSize named).1 > (nodeSize base).1 &&
    (nodeSize named).1 ≥ monoWidth "a_rather_long_name" leanFontSize +
      PILean.Graph.sansWidth "+2" moreFontSize &&
    (nodeSize twoLines).2 > (nodeSize base).2 && (nodeSize quiet).2 == (nodeSize twoLines).2 &&
    (nodeSize shortNamed) == (nodeSize base) &&
    (nodeSize named).2 == (nodeSize base).2 &&
    (nodeSize named 10).1 < (nodeSize named 11).1

end Verso.VersoBlueprintTests.BlueprintGraph.LeanNames
