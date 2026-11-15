/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary.Html
import VersoBlueprintTests.BlueprintGraph.NodeStatus
import VersoBlueprintTests.Blueprint.Support

/-!
The status colours come from one set of theme tokens: the token stylesheet declares each with
a light and a dark value, graph nodes carry SVG classes that the graph stylesheet paints from
the tokens, and legend swatches and summary cards refer to the same tokens.
-/

namespace Verso.VersoBlueprintTests.BlueprintGraph.StatusColors

open Lean
open Informal
open Informal.Graph
open Verso.VersoBlueprintTests.BlueprintGraph.Shared
open Verso.VersoBlueprintTests.BlueprintGraph.NodeStatus
open Verso.VersoBlueprintTests.Blueprint.Support

private def isHexDigit (c : Char) : Bool :=
  c.isDigit || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')

/-- Whether `s` contains a hexadecimal colour literal such as `#16a34a`. -/
private def hasHexColor (s : String) : Bool :=
  let rec go : List Char → Bool
    | '#' :: a :: b :: c :: rest =>
      (isHexDigit a && isHexDigit b && isHexDigit c) || go (a :: b :: c :: rest)
    | _ :: rest => go rest
    | [] => false
  go s.toList

-- Every status token is declared with its light value in the light block and with its dark
-- value in the dark theme, once.
/-- info: true -/
#guard_msgs in
#eval
  StatusColors.all.all fun token =>
    hasSubstr Informal.Commands.blueprintLightTokensCss s!"  {token.name}: {token.light};\n" &&
    (Informal.Commands.darkTokens.filter (·.1 == token.name)) == [(token.name, token.dark)]

-- Token names are distinct.
/-- info: true -/
#guard_msgs in
#eval
  let names := StatusColors.all.map (·.name)
  names.eraseDups.length == names.length

-- The graph's status colours are the tokens' light values (what DOT carries).
/-- info: true -/
#guard_msgs in
#eval
  statementBorderBlockedColor == StatusColors.blockedBorder.light &&
  proofBackgroundFormalizedAncColor == StatusColors.formalizedWithAncestors.light &&
  proofStatusFontColor .formalizedWithAncestors == StatusColors.formalizedWithAncestorsText.light &&
  unresolvedFillColor == StatusColors.unresolved.light

-- Styled nodes carry their status classes, and so does the DOT made from finished graph data.
/-- info: true -/
#guard_msgs in
#eval
  hasNodeWith graphStatus `thm_ready (fun n =>
    n.svgClass == "bp_graph_status_ready bp_graph_statement_ready") &&
  hasNodeWith graphStatus `def_formal (fun n =>
    n.svgClass ==
      "bp_graph_status_formalized_with_ancestors bp_graph_statement_formalized") &&
  hasNodeWith graphStatus `missing_dep (fun n => n.svgClass == "bp_graph_status_unresolved") &&
  match graphDataStatus.variants[0]? with
  | none => false
  | some full =>
    hasSubstr full.dot "class=\"bp_graph_status_ready bp_graph_statement_ready\"" &&
    hasSubstr full.dot "class=\"bp_graph_status_unresolved\""

-- The graph stylesheet paints every status class from a token and names no colour itself.
/-- info: true -/
#guard_msgs in
#eval
  let css := graphStatusCss
  !hasHexColor css &&
  hasSubstr Informal.Commands.graphCss css &&
  hasSubstr css
    (".bp_graph_canvas svg g.node.bp_graph_status_ready :is(ellipse, polygon, path) " ++
      "{ fill: var(--bp-color-status-ready); }") &&
  hasSubstr css
    (".bp_graph_canvas svg g.node.bp_graph_status_formalized_with_ancestors text " ++
      "{ fill: var(--bp-color-status-formalized-with-ancestors-text); }") &&
  hasSubstr css
    (".bp_graph_canvas svg g.node.bp_graph_statement_mathlib :is(ellipse, polygon, path) " ++
      "{ stroke: var(--bp-color-status-mathlib-border); }") &&
  StatusColors.all.all fun token => hasSubstr css token.cssVar

-- Legend swatches use the tokens (with the light value as fallback), never a bare colour.
/-- info: true -/
#guard_msgs in
#eval
  (graphLegendGroups (includeMathlib := true)).all fun group =>
    group.items.all fun item =>
      match item.swatch? with
      | none => true
      | some swatch => swatch.background.startsWith "var(--" && swatch.borderColor.startsWith "var(--"

-- A summary card about a status carries that status's token.
/-- info: true -/
#guard_msgs in
#eval
  let html := (Informal.Commands.summaryCard "Ready now" "3"
    (accent? := StatusColors.readyBorder)).asString
  hasSubstr html "bp_summary_card bp_summary_card_status" &&
  hasSubstr html "--bp-summary-status: var(--bp-color-status-ready-border)" &&
  !hasSubstr (Informal.Commands.summaryCard "Total" "3").asString "bp_summary_card_status"

end Verso.VersoBlueprintTests.BlueprintGraph.StatusColors
