/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

import VersoBlueprintTests.Blueprint.Support
import VersoBlueprint.DeclarationSource
import VersoBlueprint.PreviewManifest

namespace Verso.VersoBlueprintTests.BlueprintSideBySide

open Lean
open Verso
open Verso.Genre.Manual
open Informal
open SubVerso.Highlighting
open Verso.VersoBlueprintTests.Blueprint.Support

set_option doc.verso true

private def manualImpls : ExtensionImpls := extension_impls%

private def tok (s : String) : Highlighted := .token ⟨.keyword none none none, s⟩

private def txt (s : String) : Highlighted := .text s

private def leavesText (hls : Array Highlighted) : String :=
  hls.foldl (init := "") fun out hl =>
    match hl with
    | .token t => out ++ t.content
    | .text s | .unparsed s => out ++ s
    | _ => out

/-- `theorem foo (h : x := 1) : True := by` / `  trivial`, with a proof state and a message span. -/
private def theoremCode : Highlighted :=
  .seq #[tok "theorem", txt " ", tok "foo", txt " ", tok "(", tok "h", txt " ", tok ":", txt " ",
    tok "x", txt " ", tok ":=", txt " ", tok "1", tok ")", txt " ", tok ":", txt " ", tok "True",
    txt " ", tok ":=", txt " ", tok "by", txt "\n  ",
    .tactics #[] 0 1 (.span #[(.warning, .text "w")] (tok "trivial")), txt "\n\n"]

/-- info: true -/
#guard_msgs in
#eval
  match DeclarationSource.splitStatement? (DeclarationSource.presentation theoremCode) with
  | some (statement, proof) =>
    leavesText statement == "theorem foo (h : x := 1) : True := by" &&
      leavesText proof == "  trivial" &&
      -- proof states and message spans are dropped
      proof.all fun | .tactics .. | .span .. => false | _ => true
  | none => false

-- A top-level `:=` without a following `by` splits right after it.
/-- info: true -/
#guard_msgs in
#eval
  let code : Highlighted := .seq #[tok "theorem", txt " ", tok "t", txt " ", tok ":", txt " ",
    tok "True", txt " ", tok ":=", txt " ", tok "trivial", txt "\n"]
  match DeclarationSource.splitStatement? (DeclarationSource.presentation code) with
  | some (statement, proof) => leavesText statement == "theorem t : True :=" && leavesText proof == "trivial"
  | none => false

-- Commands without a top-level `:=` (or with nothing after it) are not split.
/-- info: true -/
#guard_msgs in
#eval
  let structureCode : Highlighted := .seq #[tok "structure", txt " ", tok "P", txt " ", tok "where",
    txt "\n  ", tok "x", txt " ", tok ":", txt " ", tok "Nat"]
  let nothingAfter : Highlighted := .seq #[tok "def", txt " ", tok "d", txt " ", tok ":=", txt "  \n"]
  let documented : Highlighted := .seq #[txt "\n\n", .token ⟨.docComment, "/-- Doc. -/"⟩, txt "\n",
    tok "def", txt " ", tok "d", txt " ", tok ":=", txt " ", tok "1", txt "\n"]
  (DeclarationSource.splitStatement? (DeclarationSource.presentation structureCode)).isNone &&
    (DeclarationSource.splitStatement? (DeclarationSource.presentation nothingAfter)).isNone &&
    leavesText (DeclarationSource.presentation theoremCode) ==
      "theorem foo (h : x := 1) : True := by\n  trivial" &&
    leavesText (DeclarationSource.presentation documented) == "def d := 1"

-- Source lines are split at line breaks inside text leaves, keeping indentation.
/-- info: true -/
#guard_msgs in
#eval
  let ls := DeclarationSource.lines (DeclarationSource.presentation theoremCode)
  ls.map leavesText == #["theorem foo (h : x := 1) : True := by", "  trivial"] &&
    (DeclarationSource.lines #[txt "a\n\nb"]).map leavesText == #["a", "", "b"] &&
    -- the indentation that wrapped lines hang from
    ls.map DeclarationSource.lineIndent == #[0, 2]

-- The site default style ships the legend of every status glyph, once.
/-- info: true -/
#guard_msgs in
#eval
  let cfg := PreviewManifest.withSideBySideDefaultStyle (PreviewManifest.withSideBySideDefaultStyle {})
  let head := String.join (cfg.toHtmlConfig.extraHead.map (·.asString)).toList
  countSubstr head "<template id=\"bp-status-legend\">" == 1 &&
    countSubstr head "name=\"verso-blueprint-default-style\"" == 1 &&
    Informal.StatusGlyphKind.all.all fun kind =>
      hasSubstr head kind.glyph && hasSubstr head kind.meaning &&
        hasSubstr head s!"bp_status_glyph_{kind.modifier}"

/-- info: true -/
#guard_msgs in
#eval
  (DeclarationSource.highlightedJsonPath "/p" `A.B.C).toString == "/p/.lake/build/highlighted/A/B/C.json" &&
    DeclarationSource.wantsSource { Data.ExternalRef.ofName `x with
      provenance := .inWorkspace `A.B "/p/A/B.lean" } == some `A.B &&
    DeclarationSource.wantsSource { Data.ExternalRef.ofName `x with
      provenance := .inWorkspace `M "/p/.lake/packages/mathlib/M.lean" } == none &&
    DeclarationSource.wantsSource { Data.ExternalRef.ofName `x with
      present := false
      provenance := .inWorkspace `A.B "/p/A/B.lean" } == none

/-- A theorem whose source the side-by-side layout shows. -/
theorem sbsTheorem : True := by
  trivial

#docs (Genre.Manual) sbsDoc "Side by Side Doc" :=
:::::::
:::theorem "thm:sbs" (lean := "Verso.VersoBlueprintTests.BlueprintSideBySide.sbsTheorem, Nat.add")
A true statement.
:::

:::proof "thm:sbs"
Obvious.
:::
:::::::

private def thisModule : Name := `VersoBlueprintTests.BlueprintSideBySide

private def sbsTheoremName : Name := `Verso.VersoBlueprintTests.BlueprintSideBySide.sbsTheorem

/-- The highlighted module data the generator would load from the Lake facet. -/
private def fakeModule : SubVerso.Module.Module := {
  items := #[{
    range := some (⟨100, 0⟩, ⟨102, 9⟩)
    kind := `Lean.Parser.Command.declaration
    defines := #[sbsTheoremName]
    code := .seq #[tok "theorem", txt " ", tok "sbsTheorem", txt " ", tok ":", txt " ",
      tok "True", txt " ", tok ":=", txt " ", tok "by", txt "\n  ", tok "trivial"]
  }]
}

/-- info: true -/
#guard_msgs in
#eval
  show IO Bool from do
    DeclarationSource.clear
    DeclarationSource.insert thisModule fakeModule
    let out ← DeclarationSource.withEnabled true <| renderManualDocHtmlString manualImpls sbsDoc
    let plain ← renderManualDocHtmlString manualImpls sbsDoc
    DeclarationSource.clear
    pure (
      hasSubstr out "class=\"bp_sbs\"" &&
      hasSubstr out "data-bp-node=\"«thm:sbs»\"" &&
      hasSubstr out "data-bp-facet=\"statement\"" &&
      hasSubstr out "data-bp-facet=\"proof\"" &&
      hasSubstr out "class=\"bp_sbs_informal\"" &&
      hasSubstr out "class=\"bp_sbs_formal\"" &&
      -- the theorem's source card: statement, folded Lean proof, anchors
      hasSubstr out "class=\"bp_decl_source bp_decl_source_theorem\"" &&
      hasSubstr out s!"data-lean-decl=\"{sbsTheoremName}\"" &&
      hasSubstr out "class=\"bp_decl_source_proof\"" &&
      hasSubstr out ">sbsTheorem<" &&
      hasSubstr out "class=\"bp_code_line\"" &&
      hasSubstr out ">trivial<" &&
      -- the indented proof line carries its indentation for the hanging indent
      hasSubstr out "style=\"--bp-indent: 2\"" &&
      appearsBefore out ">sbsTheorem<" "class=\"bp_decl_source_proof\"" &&
      -- `Nat.add` has no workspace source: it keeps its signature row
      hasSubstr out "data-lean-decl=\"Nat.add\"" &&
      hasSubstr out "bp_external_decl_item" &&
      -- the status glyph, whose tooltip starts with its meaning, and the folded proof
      hasSubstr out "class=\"bp_status_glyph" &&
      Informal.StatusGlyphKind.all.any (fun kind => hasSubstr out s!"title=\"{kind.meaning}") &&
      hasSubstr out "<details class=\"bp_wrapper bp_kind_proof_wrapper" &&
      -- no separate Lean code panel for the statement
      !hasSubstr out "Lean code for Theorem" &&
      -- without the layout, nothing changes
      !hasSubstr plain "bp_sbs" && !hasSubstr plain "bp_status_glyph" &&
      hasSubstr plain "Lean code for Theorem"
    )

/-! Runs: consecutive Blueprint blocks share one `div.bp_sbs_run`. -/

#docs (Genre.Manual) runsDoc "Runs Doc" :=
:::::::
:::theorem "thm:runA" (lean := "Nat.add")
First statement.
:::

:::proof "thm:runA"
First proof.
:::

:::definition "def:runB" (lean := "Nat.mul")
Second statement.
:::

:::lemma_ "lem:runNoLean"
A statement without Lean.
:::

Prose between the blocks.

:::theorem "thm:runC" (lean := "Nat.sub")
A block alone.
:::
:::::::

/-- The text of `s` from the `n`-th (from 0) occurrence of `needle` up to the next one. -/
private def segment (s needle : String) (n : Nat) : String :=
  ((s.splitOn needle)[n + 1]?).getD ""

/-- info: true -/
#guard_msgs in
#eval
  show IO Bool from do
    let out ← DeclarationSource.withEnabled true <|
      renderManualDocHtmlString manualImpls runsDoc (prepare := Informal.SideBySideRuns.groupRuns)
    let ungrouped ← DeclarationSource.withEnabled true <| renderManualDocHtmlString manualImpls runsDoc
    let run := "<div class=\"bp_sbs_run\">"
    let first := segment out run 0
    let second := segment out run 1
    pure (
      -- prose ends the first run; the block after it is a run of its own
      countSubstr out run == 2 &&
      hasSubstr first "data-bp-node=\"«thm:runA»\"" &&
      hasSubstr first "data-bp-node=\"«def:runB»\"" &&
      -- a statement without Lean stays in the run, in one column
      hasSubstr first "class=\"bp_sbs bp_sbs_single\" data-bp-node=\"«lem:runNoLean»\"" &&
      appearsBefore out "Prose between the blocks." run &&
      -- the run element is closed before the prose: one more `</div>` than `<div` up to it
      (let pre := (first.splitOn "Prose between the blocks.").headD ""
       countSubstr pre "</div>" == countSubstr pre "<div" + 1) &&
      hasSubstr second "data-bp-node=\"«thm:runC»\"" &&
      -- the proof sits in its node's informal column, before the Lean column
      appearsBefore first "First proof." "class=\"bp_sbs_formal\"" &&
      -- without grouping (other layouts and renderers) nothing changes
      !hasSubstr ungrouped "bp_sbs_run" &&
      appearsBefore ungrouped "class=\"bp_sbs_formal\"" "First proof."
    )

/-! A block that renders nothing (here hidden external markup, the default display) between two
Blueprint blocks does not end their run. -/

#docs (Genre.Manual) hiddenBetweenDoc "Hidden Between Doc" :=
:::::::
:::theorem "thm:hiddenA" (lean := "Nat.add")
Statement before the hidden block.
:::

```tex "thm:hiddenA" (slot := statement)
\begin{theorem}Hidden source text.\end{theorem}
```

:::definition "def:hiddenB" (lean := "Nat.mul")
Statement after the hidden block.
:::
:::::::

/-- info: true -/
#guard_msgs in
#eval
  show IO Bool from do
    let out ← DeclarationSource.withEnabled true <|
      renderManualDocHtmlString manualImpls hiddenBetweenDoc
        (prepare := Informal.SideBySideRuns.groupRuns)
    let run := "<div class=\"bp_sbs_run\">"
    pure (
      countSubstr out run == 1 &&
      hasSubstr (segment out run 0) "data-bp-node=\"«thm:hiddenA»\"" &&
      hasSubstr (segment out run 0) "data-bp-node=\"«def:hiddenB»\"" &&
      !hasSubstr out "Hidden source text.")

open Verso.Output in
/-- A side-by-side node and a proof of it, as rendered (attributes only). -/
private def node (label : String) : Html :=
  .tag "div" #[("class", "bp_sbs"), ("data-bp-node", label)] <|
    .tag "div" #[("class", "bp_sbs_grid")] <| .seq #[
      .tag "div" #[("class", "bp_sbs_informal")] (.text true "statement"),
      .tag "div" #[("class", "bp_sbs_formal")] (.text true "lean")]

open Verso.Output in
private def proof (label : String) : Html :=
  .tag "details" #[("data-bp-node", label), ("data-bp-facet", "proof")] (.text true s!"proof {label}")

open Verso.Output in
private def panel : Html := .tag "div" #[("class", "bp_wrapper bp_code_panel_wrapper")] .empty

-- Proofs move into the node they directly follow, with their references panel; a proof of
-- another node stays where it is.
/-- info: true -/
#guard_msgs in
#eval
  open Verso.Output in
  let out := Informal.SideBySideRuns.renderRun <| #[node "a", .seq #[proof "a", panel], node "b",
    proof "c", proof "b"].map (true, ·)
  let s := out.asString
  countSubstr s "<div class=\"bp_sbs_run\">" == 1 &&
    appearsBefore s "proof a" "class=\"bp_sbs_formal\"" &&
    appearsBefore s "bp_code_panel_wrapper" "data-bp-node=\"b\"" &&
    appearsBefore s "data-bp-node=\"b\"" "proof c" &&
    -- `b`'s proof follows another node's proof, so it is not attached
    appearsBefore s "proof c" "proof b" &&
    appearsBefore (segment s "data-bp-node=\"b\"" 0) "class=\"bp_sbs_formal\"" "proof c"

-- Between Blueprint blocks, a block that renders nothing (or only whitespace) is dropped and the
-- run goes on, so a proof after it is still attached; one that shows something ends the run.
/-- info: true -/
#guard_msgs in
#eval
  open Verso.Output in
  let out := Informal.SideBySideRuns.renderRun #[(true, node "a"), (false, .empty),
    (false, .seq #[.text true "\n  ", .seq #[]]), (true, proof "a"), (false, .text true "prose"),
    (true, node "b")]
  let s := out.asString
  countSubstr s "<div class=\"bp_sbs_run\">" == 2 &&
    appearsBefore s "proof a" "class=\"bp_sbs_formal\"" &&
    appearsBefore s "proof a" "prose" && appearsBefore s "prose" "data-bp-node=\"b\"" &&
    -- the first run element is closed before the prose
    (let pre := (s.splitOn "prose").headD ""
     countSubstr pre "</div>" == countSubstr pre "<div")

/-- A stand-in for a block of the given extension (only its name matters for grouping). -/
private def blockOf (name : Name) (contents : Array (Doc.Block Genre.Manual) := #[]) :
    Doc.Block Genre.Manual :=
  .other { name } contents

private def shape : Doc.Block Genre.Manual → String
  | .other b contents =>
    let inner := String.intercalate "," (contents.map shape).toList
    if b.name == ``Informal.SideBySideRuns.Block.sideBySideRun then s!"run[{inner}]"
    else if b.name == Informal.SideBySideRuns.informalBlockName then "n"
    else if b.name == `Informal.Block.groupMetadata then "g"
    else s!"o[{inner}]"
  | .para _ => "p"
  | _ => "?"

-- Grouping: each stretch from one Blueprint block to another, whatever lies between (whether
-- that ends the run is decided when it renders); blocks before the first and after the last stay
-- outside; containers are searched for runs of their own.
/-- info: "g,run[n,g,n,p,g,n,o[run[n,n]],n],p" -/
#guard_msgs in
#eval
  let n := blockOf Informal.SideBySideRuns.informalBlockName
  let g := blockOf `Informal.Block.groupMetadata
  let p : Doc.Block Genre.Manual := .para #[]
  String.intercalate "," ((Informal.SideBySideRuns.groupBlocks
    #[g, n, g, n, p, g, n, blockOf `Other #[n, n], .concat #[n], p]).toList.map shape)

-- Concatenations are flattened at any depth, and the blocks inside them are searched too.
/-- info: "run[n,n,n,?,o[run[n,n]],n]" -/
#guard_msgs in
#eval
  let n := blockOf Informal.SideBySideRuns.informalBlockName
  String.intercalate "," ((Informal.SideBySideRuns.groupBlocks
    #[n, .concat #[.concat #[n, .concat #[n]]],
      .concat #[.blockquote #[] , blockOf `Other #[.concat #[n, .concat #[n]]]], n]).toList.map
    shape)

end Verso.VersoBlueprintTests.BlueprintSideBySide
