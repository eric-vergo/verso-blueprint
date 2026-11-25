/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

import PILean.Svg.Inert
import VersoBlueprint.GraphLayout
import VersoBlueprint.GraphNames
import VersoBlueprintTests.Blueprint.Support
import VersoBlueprintTests.BlueprintGraph.Shared

/-!
A node of the dependency graph with a Lean statement shows the short name of its statement's first
declaration in the code face, with the count of further declarations after it; a node without a
Lean statement shows its number. The names: their shortening and disambiguation over a graph, which
declarations they come from, and how the drawings carry them with the number beside them.
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

private def texts (labels : Array (Option GraphNames.Label)) : Array (Option String) :=
  labels.map (·.map (·.text))

private def count (s needle : String) : Nat := (s.splitOn needle).length - 1

/-! ## Names -/

-- One declaration: its last component; a node without declarations has no name.
/-- info: true -/
#guard_msgs in
#eval
  texts (labels #[#[`Project.Analysis.rho_irrational], #[]]) == #[some "rho_irrational", none]

-- Several declarations: the first, in the order given, with the count of the others; a
-- declaration given twice counts once.
/-- info: true -/
#guard_msgs in
#eval
  let ls := labels #[#[`P.first, `P.second, `Q.third, `P.second]]
  ls == #[some { text := "first", name := `P.first, more := 2 }]

-- Two nodes whose names end alike show as many trailing components as tell them apart; a
-- node's own further declarations count too; a name whose components run out is shown whole.
/-- info: true -/
#guard_msgs in
#eval
  texts (labels #[#[`A.B.foo], #[`A.C.foo], #[`D.foo], #[`bar]]) ==
      #[some "B.foo", some "C.foo", some "D.foo", some "bar"] &&
    texts (labels #[#[`A.x.foo], #[`B.x.foo]]) == #[some "A.x.foo", some "B.x.foo"] &&
    texts (labels #[#[`M.same, `K.same]]) == #[some "M.same"] &&
    texts (labels #[#[`A.foo], #[`foo]]) == #[some "A.foo", some "foo"] &&
    -- one declaration on two nodes is no collision
    texts (labels #[#[`A.foo], #[`A.foo]]) == #[some "foo", some "foo"]

-- A last component that does not name a declaration to a reader (a number, a name that starts
-- with `_`) keeps the components before it; the prefix of a private declaration and macro
-- scopes are not shown; an anonymous name is no name.
/-- info: true -/
#guard_msgs in
#eval
  let priv := Name.mkNum (`_private ++ `Project.Module) 0 ++ `Project.hidden
  texts (labels #[#[Name.mkNum `Project.lemma 3], #[`Project.thm._proof_1], #[priv],
      #[Name.anonymous], #[Name.anonymous, `Project.real]]) ==
    #[some "lemma.3", some "thm._proof_1", some "hidden", none, some "real"] &&
  readableLength (Name.mkNum (Name.mkNum `a 1) 2) == 3 &&
  readableLength (Name.mkSimple "_x") == 1

-- Names that are not identifiers are written with guillemets; other non-ASCII names as they are.
/-- info: true -/
#guard_msgs in
#eval
  texts (labels #[#[Name.str `Project "α-lemma"], #[`Project.ρ_irrational]]) ==
    #[some "«α-lemma»", some "ρ_irrational"]

-- A long label is shortened with an ellipsis in the middle of its last component, and at the
-- namespace side where its namespaces take more than half of it; it never has more than
-- `maxLabelLength` characters.
/-- info: true -/
#guard_msgs in
#eval
  let long := `Project.an_extremely_long_lemma_name_about_irrationality_of_things
  let short := (labels #[#[long]])[0]!.get!.text
  let collide := labels #[#[`Very.Long.Namespace.part.lemma_name_in_namespace], #[`other.lemma_name_in_namespace]]
  short == "an_extremely_l…ality_of_things" && short.length == maxLabelLength &&
    shorten `Abcdefghij.Klmnopqrst.uvwxyz_uvwxyz 3 20 == "…uvwxyz_uvwxyz" &&
    shorten `Abcdefghij.Klmnopqrst.uvwxyz_uvwxyz 3 26 == "…Klmnopqrst.uvwxyz_uvwxyz" &&
    -- the component that tells two long names apart stays
    texts (labels #[#[`Project.not_exists_abs_sum_chi4_sub_mul_le],
        #[`Project.PNT.not_exists_abs_sum_chi4_sub_mul_le]]) ==
      #[some "Project.not_exists…_sub_mul_le", some "PNT.not_exists_a…i4_sub_mul_le"] &&
    (texts collide).all (·.all (·.length ≤ maxLabelLength)) &&
    cutMiddle "short" == "short"

/-! ## The declarations of a node -/

private def attached (n : Name) (present : Bool := true) : ExternalRef :=
  { written := n, canonical := n, present }

private def codeOf (defs : Array (Name × Nat)) (thms : Array (Name × Nat)) : Code :=
  { stx := .missing
    definedDefs := defs.map fun (name, commandIndex) => { name, commandIndex }
    definedTheorems := thms.map fun (name, commandIndex) => { name, commandIndex } }

-- The statement's declarations in the order the author wrote them: attached ones (present or
-- missing), then each code block's in source order. A node whose Lean code is attached only to
-- its proof, or whose code block defines no named declaration, has none.
/-- info: true -/
#guard_msgs in
#eval
  let both : Node := {
    kind := NodeKind.theorem
    externalRefs := #[attached `P.b, attached `P.a (present := false)]
    literateCodes := #[codeOf #[(`P.d, 2)] #[(`P.c, 1)], codeOf #[] #[(`P.e, 0)]] }
  let proofOnly : Node := { kind := NodeKind.theorem, proofExternalRefs := #[attached `P.helper] }
  let examples : Node := { kind := NodeKind.theorem, literateCodes := #[codeOf #[] #[]] }
  statementDeclarationNames both == #[`P.b, `P.a, `P.c, `P.d, `P.e] &&
    statementDeclarationNames proofOnly == #[] &&
    statementDeclarationNames examples == #[]

private def state : Environment.State :=
  mkState [
    (`stmt, { kind := NodeKind.theorem, externalRefs := #[attached `Project.rho_irrational, attached `Project.aux] }),
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

-- The graph data carries every declaration of each node's statement; the drawn nodes get a label
-- for the whole graph: `Project.rho_irrational` and `Other.rho_irrational` tell each other apart,
-- and the node whose Lean code is attached only to its proof keeps its number.
/-- info: true -/
#guard_msgs in
#eval
  let g := graphOf
  let drawn := g.renderGraph
  hasGraphDataNodeWith g `stmt (·.leanNames == #[`Project.rho_irrational, `Project.aux]) &&
    hasGraphDataNodeWith g `proof_only (·.leanNames.isEmpty) &&
    hasNodeWith drawn `stmt (fun n => n.leanLabel? == some "Project.rho_irrational" && n.leanMore == 1) &&
    hasNodeWith drawn `other (·.leanLabel? == some "Other.rho_irrational") &&
    hasNodeWith drawn `proof_only (fun n => n.leanLabel?.isNone && n.caption? == some "Theorem 1.2")

/-! ## Drawings -/

private def drawingOf (nodeText : GraphNodeText) : String :=
  let g := graphOf nodeText
  (drawing "full" { graph := g.renderGraph, nodeText } .TB true).svg

-- A drawn node with a Lean label holds it in the code face with the count after it, and its
-- number as `text.bp_graph_label_number`; the one the site does not show first is hidden. A node
-- without a Lean statement shows its number as before. The drawing stays inert.
/-- info: true -/
#guard_msgs in
#eval
  let byName := drawingOf .name
  let byNumber := drawingOf .number
  count byName "class=\"bp_graph_label_name\"" == 2 &&
    count byName "class=\"bp_graph_label_number\" display=\"none\"" == 2 &&
    hasSubstr byName ">Project.rho_irrational<tspan class=\"bp_graph_label_more\"" &&
    hasSubstr byName ">+1</tspan></text>" &&
    hasSubstr byName s!"font-family=\"{codeFontFamily}\"" &&
    hasSubstr byName ">Theorem 1.2</text>" &&
    count byNumber "class=\"bp_graph_label_number\" x=" == 2 &&
    count byNumber "display=\"none\">Project.rho_irrational" == 1 &&
    PILean.Svg.isInert byName && PILean.Svg.isInert byNumber

-- The accessible name keeps the number, the label and the status words, and names the full
-- Lean declarations.
/-- info: true -/
#guard_msgs in
#eval
  let web : PILean.Graph.WebNode :=
    { name := "stmt", lines := #["Theorem 1.1"], tooltip := "Lean proof complete" }
  accessibleName web #[`Project.rho_irrational] ==
      "Theorem 1.1 (stmt), Lean name Project.rho_irrational: Lean proof complete" &&
    accessibleName web #[`P.a, `P.b] == "Theorem 1.1 (stmt), Lean names P.a, P.b: Lean proof complete" &&
    accessibleName web == "Theorem 1.1 (stmt): Lean proof complete" &&
    hasSubstr (drawingOf .name) "aria-label=\"Theorem 1.1 (stmt), Lean names Project.rho_irrational, Project.aux"

-- A node's box holds the wider of its two labels, so it fits whichever a reader shows; a long
-- name widens the box, a short one leaves the number's width.
/-- info: true -/
#guard_msgs in
#eval
  let base : GraphNode String :=
    { label := `n, caption? := some "Theorem 1.1", fillcolor := "#fff", deps := #[] }
  let named := { base with leanLabel? := some "a_rather_long_lemma_name_here", leanMore := 2 }
  let shortNamed := { base with leanLabel? := some "f" }
  (nodeSize named).1 > (nodeSize base).1 &&
    (nodeSize named).1 ≥ monoWidth "a_rather_long_lemma_name_here" leanFontSize +
      PILean.Graph.sansWidth "+2" moreFontSize &&
    (nodeSize shortNamed).1 == (nodeSize base).1 &&
    (nodeSize named).2 == (nodeSize base).2

end Verso.VersoBlueprintTests.BlueprintGraph.LeanNames
