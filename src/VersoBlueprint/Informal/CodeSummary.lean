/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Emilio J. Gallego Arias
-/

import Lean
import Verso
import VersoManual
import VersoBlueprint.Axioms
import VersoBlueprint.Graph
import VersoBlueprint.Informal.Block.Common
import VersoBlueprint.Informal.Block.StatusGlyph
import VersoBlueprint.Informal.LeanCodePreviewKey
import VersoBlueprint.Informal.LeanCodeLink
import VersoBlueprint.Lib.HoverRender
import VersoBlueprint.Meaning
import VersoBlueprint.Replay

namespace Informal
namespace CodeSummary

open Verso Doc Elab
open Lean Elab

/-!
`CodeSummary` computes the heading-level Lean status/summary fragments for informal blocks.

This module intentionally owns the high-level overview for one informal node:
status marks, declaration-summary tooltips, and code-panel indicators.

It does not own HTML-cache-backed code-preview hovers for explicit links to code;
that narrower responsibility lives in `Informal.LeanCodeLink` /
`Informal.LeanCodePreview`.

Public API:
- `ComputedData`: normalized code inputs for one block heading.
- `RenderParts`: rendered heading fragments consumed by callers.
- `renderParts`: main entry point that derives status badge + Lean link node.
-/

/-- All associated Lean inputs for a heading, or the inputs owned by an individual panel. -/
structure ComputedData where
  codeHref : Option String := none
  source : Option BlockCodeData := none
  /-- Traversed panels supply preview keys, independently of project declaration facts. -/
  inlineBlocks : InlineCodeBlocks := #[]

def ComputedData.ofInlineBlocks (blocks : InlineCodeBlocks) : ComputedData :=
  { source := (BlockCodeData.ofInlineBlocks blocks).nonempty?, inlineBlocks := blocks }

/--
Rendered fragments produced by `CodeSummary.renderParts` for an informal block heading.
-/
structure RenderParts where
  /-- Optional status icon rendered next to the statement heading. -/
  statusMark : Option BlockStatusMark := none
  /-- Optional Lean badge/link node (`L∃∀N`) with tooltip wrapper. -/
  codeEntry : Output.Html := .empty

structure PanelIndicatorParts where
  /-- Summary text exposed on the enclosing code-panel `<summary>` title. -/
  summaryTitle : String := ""
  /-- Top-right indicator node for the code panel summary row. -/
  indicator : Output.Html := .empty

inductive DeclSummaryKind where
  | definition
  | theoremLike
deriving Inhabited, Repr, BEq

/--
Normalized declaration summary row shared by inline and external Lean summary UI.

`present = false` is used only for external references that failed to resolve.
-/
structure DeclSummaryItem where
  /-- Name shown in the code-summary panel. -/
  displayName : Name
  /--
  Canonical declaration name used for the default Lean-code preview lookup.

  External references may be written with an opened or namespace-local name, but
  traversal stores rendered Lean-code previews under the resolved canonical name.
  -/
  previewName : Name
  /-- Explicit HTML-cache preview lookup key, when it differs from `previewName`. -/
  previewLookupKey? : Option String := none
  href : Option String := none
  kind : DeclSummaryKind := .definition
  status : Data.ProvedStatus := .incomplete {}
  present : Bool := true
deriving Inhabited, Repr

private structure SummaryTooltipSection where
  title : String := ""
  items : Array DeclSummaryItem := #[]
  emptyText : String := "No associated Lean declarations."

private def declSummaryStatusText (item : DeclSummaryItem) : String :=
  (item.status.presentation (present := item.present)).summaryText

private def declSummaryStatusClass (item : DeclSummaryItem) : String :=
  (item.status.presentation (present := item.present)).codeDeclClass

private def renderDeclSummaryItems (items : Array DeclSummaryItem) : Array Output.Html :=
  open Verso.Output.Html in
  items.map fun item =>
    let nameNode : Output.Html :=
      let txt := html%{<code>{.text s!"{item.displayName}"}</code>}
      match item.href with
      | some href =>
        Informal.LeanCodeLink.renderResolved
          item.previewName txt "" (some href)
          (previewTitle := s!"{item.displayName}")
          (previewLookupKey? := item.previewLookupKey?)
      | none => txt
    html%{
      <li class="bp_code_decl_item">
        <span class="bp_code_decl_name">{nameNode}</span>
        <span class={s!"bp_code_decl_status {declSummaryStatusClass item}"}>
          {.text s!"[{declSummaryStatusText item}]"}
        </span>
      </li>
    }

private def summaryTooltipSection (tooltipSection : SummaryTooltipSection) : Output.Html :=
  let items :=
    if tooltipSection.items.isEmpty then
      #[codeHoverEmptyItem tooltipSection.emptyText]
    else
      renderDeclSummaryItems tooltipSection.items
  codeHoverSection tooltipSection.title items

private def renderSummaryPreviewBody (sections : Array SummaryTooltipSection) : Output.Html :=
  open Verso.Output.Html in
  html%{
    <div class="bp_code_summary_preview_content">
      {.seq (sections.map summaryTooltipSection)}
    </div>
  }

private def renderExternalRenderFailureItems (failures : Array ExternalRenderFailure)
    (hrefOf : Name → Option String) : Array Output.Html :=
  open Verso.Output.Html in
  failures.map fun failure =>
    let href :=
      if failure.decl.present then
        match hrefOf failure.decl.canonical with
        | some href => some href
        | none => hrefOf failure.decl.written
      else
        hrefOf failure.decl.written
    let declNode :=
      let txt := html%{<code>{.text s!"{failure.decl.written}"}</code>}
      match href with
      | some href =>
        Informal.LeanCodeLink.renderResolved
          failure.decl.canonical txt "" (some href)
          (previewTitle := s!"{failure.decl.canonical}")
      | none => txt
    codeHoverListItem html%{
      <span>{declNode}{": "}{.text failure.message}</span>
    }

private def inlineDeclSummaryItems (definedDefs definedTheorems : Array CodeDeclData)
    (hrefOf : Name → Option String) (previewLookupKey? : Option String := none) :
    Array DeclSummaryItem :=
  let defs := definedDefs.map fun decl =>
    {
      displayName := decl.name
      previewName := decl.name
      previewLookupKey?
      href := hrefOf decl.name
      kind := .definition
      status := decl.provedStatus
    }
  let theoremLikes := definedTheorems.map fun decl =>
    {
      displayName := decl.name
      previewName := decl.name
      previewLookupKey?
      href := hrefOf decl.name
      kind := .theoremLike
      status := decl.provedStatus
    }
  defs ++ theoremLikes

private def incompleteSummaryItems (items : Array DeclSummaryItem) : Array DeclSummaryItem :=
  items.filter fun item => !item.present || item.status.isIncomplete

def externalDeclKindText? (decl : Data.ExternalRef) : Option String :=
  if !decl.present then
    none
  else
    match decl.kind with
    | .definition => some "definition"
    | .proposition => some "proposition"
    | .lemma => some "lemma"
    | .theorem => some "theorem"
    | .corollary => some "corollary"

private def externalSummaryKind (decl : Data.ExternalRef) : DeclSummaryKind :=
  match decl.kind with
  | .definition => .definition
  | .proposition | .lemma | .theorem | .corollary => .theoremLike

private def externalDeclHref (decl : Data.ExternalRef) (hrefOf : Name → Option String) : Option String :=
  if decl.present then
    match hrefOf decl.canonical with
    | some href => some href
    | none => hrefOf decl.written
  else
    hrefOf decl.written

private def externalDeclSummaryItems (decls : Array Data.ExternalRef)
    (hrefOf : Name → Option String) : Array DeclSummaryItem :=
  decls.map fun decl =>
    {
      displayName := decl.written
      previewName := decl.canonical
      href := externalDeclHref decl hrefOf
      kind := externalSummaryKind decl
      status := decl.provedStatus
      present := decl.present
    }

private def summaryPreviewItems (cdata : ComputedData)
    (hrefOf : Name → Option String) : Array DeclSummaryItem :=
  let source := cdata.source.getD {}
  let declarations := source.summaryLiterateDeclarations
  let previewKeys := cdata.inlineBlocks.foldl (init := ({} : Lean.NameMap String)) fun keys block =>
    let key := Informal.LeanCodePreviewKey.inlineLookupKey block.blockId
    block.declarations.foldl (fun keys decl => keys.insert decl.name key) keys
  let inlineItems := (inlineDeclSummaryItems declarations.definedDefs declarations.definedTheorems hrefOf).map fun item =>
    { item with previewLookupKey? := previewKeys.get? item.previewName }
  inlineItems ++ externalDeclSummaryItems source.summaryExternalDecls hrefOf

private def renderSummaryPreview (cdata : ComputedData)
    (hrefOf : Name → Option String) (proofDecls : Array Data.ExternalRef := #[]) : Output.Html :=
  let items := summaryPreviewItems cdata hrefOf
  let sectionTitle :=
    if items.isEmpty then "Lean status" else "Associated Lean declarations"
  let sections : Array SummaryTooltipSection := #[{
    title := sectionTitle
    items
    emptyText := "No associated Lean code or declarations."
  }]
  -- what the mark also counts, with the statuses that lower it
  let sections := if proofDecls.isEmpty then sections else sections.push {
    title := Informal.Meaning.proofDeclsTitle
    items := externalDeclSummaryItems (Data.ExternalRef.mergeSnapshots #[] proofDecls) hrefOf }
  let failures := externalRenderFailures (cdata.source.getD {}).externalDecls
  if failures.isEmpty then
    renderSummaryPreviewBody sections
  else
    let failureSection := codeHoverSection "Render diagnostics" (renderExternalRenderFailureItems failures hrefOf)
    open Verso.Output.Html in
    html%{
      <div class="bp_code_summary_preview_content">
        {.seq (sections.map summaryTooltipSection)}
        {failureSection}
      </div>
    }

private structure CodeEntryVisual where
  classSuffix : String
  symbol : String
  absent : Bool := false
deriving Inhabited

/-- The symbol of the Lean link in a block's header. Code without `sorry` gets the check mark
only when the kernel replay `replay?` accepted its declarations with everything they depend on
and neither the replay nor the compiled files found an axiom outside Lean's standard three under
them; otherwise the diamond (what the compiled files report), the warning mark (such an axiom),
or the mark of a rejected replay. -/
private def codeEntryVisual (hasSource : Bool) (statusMark : BlockStatusMark)
    (replay? : Option Replay.Result := none) : CodeEntryVisual :=
  if !hasSource then
    { classSuffix := "absent", symbol := "X", absent := true }
  else
    let view := statusMark.status.presentation
    -- the class says what the symbol says: `proved` only beside the check mark
    let (classSuffix, symbol) :=
      if !statusMark.status.isProved then (view.codeEntryClassSuffix, view.codeEntrySymbol)
      else match Replay.provedStanding replay? statusMark.declarations statusMark.unplaced
          statusMark.sourceChange? with
        | .rejected => ("rejected", "⊘")
        | .sourceChanged _ => ("changed", "◌")
        | .notChecked _ => ("warning", "⚠")
        -- an axiom outside Lean's standard three that the compiled files report: the heading's
        -- warning mark (`statusGlyph`), whatever the replay
        | _ => if !statusMark.extraAxioms.isEmpty then ("warning", "⚠") else
          match Replay.provedStanding replay? statusMark.declarations statusMark.unplaced
              statusMark.sourceChange? with
          | .accepted => (view.codeEntryClassSuffix, view.codeEntrySymbol)
          | _ => ("reported", "◇")
    { classSuffix, symbol }

private structure ExternalRenderHealth where
  failureCount : Nat := 0
deriving Inhabited

private def ExternalRenderHealth.hasFailures (health : ExternalRenderHealth) : Bool :=
  health.failureCount > 0

private def ExternalRenderHealth.summaryText (health : ExternalRenderHealth) : String :=
  externalRenderFailureSummaryText health.failureCount

private def externalRenderHealth (decls : Array Data.ExternalRef) : ExternalRenderHealth :=
  { failureCount := externalRenderFailureCount decls }

private def appendRenderHealthSummary (title : String) (health : ExternalRenderHealth) : String :=
  appendExternalRenderFailureSummary title health.failureCount

private def renderCodeHeadingRenderHealthBadge (health : ExternalRenderHealth) : Output.Html :=
  open Verso.Output.Html in
  if !health.hasFailures then
    .empty
  else
    html%{
      <span class="bp_render_warning_badge bp_code_render_warning_badge"
          title={health.summaryText}>!</span>
    }

private def renderCodeEntryNode (href : Option String) (title : String) (visual : CodeEntryVisual)
    (renderHealth : ExternalRenderHealth := {}) : Output.Html :=
  open Verso.Output.Html in
  let linkClass := s!"bp_code_link bp_code_link_status bp_code_link_status_{visual.classSuffix}" ++
    (if visual.absent then " bp_code_link_empty" else "")
  let body : Output.Html := html%{
    {renderCodeHeadingRenderHealthBadge renderHealth}
    <span class="bp_code_status_symbol">{.text visual.symbol}</span>
    <span class="bp_code_link_label">L∃∀N</span>
  }
  match href with
  | some href =>
      html%{<a class={linkClass} href={href} title={title} aria-label={title}>{body}</a>}
  | none =>
      html%{<span class={linkClass} title={title}>{body}</span>}

private def codeSummaryPreviewId : String := "bp-code-summary"

private def renderCodeSummaryPreview (previewTitle : String) (trigger : Output.Html)
    (body : Output.Html) (focusable : Bool := false) (ariaLabel? : Option String := none) : Output.Html :=
  Informal.HoverRender.templatePreviewRoot
    "bp_code_summary_preview_root"
    "bp_code_summary_preview_wrap"
    "bp_code_summary_preview_wrap_active"
    "bp_code_summary_preview_tpl"
    "data-bp-preview-id"
    codeSummaryPreviewId
    previewTitle
    ".bp_code_summary_preview_panel"
    ".bp_code_summary_preview_title"
    ".bp_code_summary_preview_body"
    ".bp_code_summary_preview_close"
    (titleAttr? := some "data-bp-preview-title")
    trigger
    body
    Informal.HoverRender.codeSummaryPreviewPanel
    (focusable := focusable)
    (ariaLabel? := ariaLabel?)

private def renderCodeEntryWrap (href : Option String) (title previewTitle : String)
    (previewBody : Output.Html) (visual : CodeEntryVisual)
    (renderHealth : ExternalRenderHealth := {}) : Output.Html :=
  renderCodeSummaryPreview previewTitle
    (renderCodeEntryNode href title visual renderHealth)
    previewBody
    (focusable := href.isNone)
    (ariaLabel? := if href.isNone then some title else none)

/-- Axis wording follows the same semantic evidence as the completion mark.
Zero observed reference counts cannot establish verified coverage. The words are about the Lean
code alone: "no sorry" says that the inspection found none in the statement (or the proof) or in
anything it uses, and nothing about an informal statement. A definition's second axis is its
body. -/
private def completionAxisText (kind : Data.NodeKind) (health : Informal.Graph.CodeHealth) :
    String :=
  let status := health.provedStatus
  let axisText (complete hasGap unverified : Bool) (otherAxisBlocker : String) :=
    if !health.hasAssociatedCode then "unassociated"
    else if status.isMissing then "missing declaration"
    else if status.isAxiomLike then "axiom-like (no body)"
    else if complete then "no sorry"
    else if hasGap then "blocked by sorry"
    else if status.hasUnlocalizedSorry then "unknown (sorry location unavailable)"
    else if unverified then "unverified"
    else if status.hasKnownSorry then otherAxisBlocker
    else "unverified"
  let statement := axisText health.localStatementFormalized status.hasTypeGap status.hasUnverifiedType
    "blocked by sorry in body"
  let proof := axisText health.localProofFormalized status.hasProofGap status.hasUnverifiedProof
    "blocked by sorry in statement"
  let second := if kind.isTheoremLike then "Lean proof" else "Lean body"
  s!"Lean statement: {statement}; {second}: {proof}"

/--
Use the observed declaration evidence for the completion mark. Axis counts
cannot distinguish inherited, direct, or unknown origins.
-/
private def completionStatusMark (kind : Data.NodeKind) (extraAxioms : Array Name)
    (health : Informal.Graph.CodeHealth) : BlockStatusMark :=
  let status := health.provedStatus
  let title := completionAxisText kind health
  if status.isProved then
    { status, title, kind, extraAxioms }
  else
    { status, title, kind, extraAxioms, symbolOverride? := some "⚠" }

private def statusMarkOfHealth (kind : Data.NodeKind) (extraAxioms : Array Name)
    (health : Informal.Graph.CodeHealth) (declarations : Array Name)
    (unplaced : Option Name) : BlockStatusMark :=
  if health.hasMissingExternalDecls then
    {
      status := .missing
      title := s!"{completionAxisText kind health}; Lean declarations: {health.presentDecls} present, {health.missingDecls} missing"
      kind, extraAxioms, declarations, unplaced
    }
  else
    if health.hasAxiomLike then
      { status := .axiomLike, title := completionAxisText kind health, kind, extraAxioms
        declarations, unplaced }
    else
      { completionStatusMark kind extraAxioms health with declarations, unplaced }

private def statusMarkFromHealth (kind : Data.NodeKind) (extraAxioms : Array Name)
    (health : Informal.Graph.CodeHealth) (declarations : Array Name := #[])
    (unplaced : Option Name := none) (sourceChange? : Option String := none) : BlockStatusMark :=
  { statusMarkOfHealth kind extraAxioms health declarations unplaced with sourceChange? }

/-- A Lean declaration of `source` whose module is not known (`BlockCodeData.unplaced`). -/
def unplacedOf (source : BlockCodeData) : Option Name := source.unplaced

/-- The Lean declarations of `source` (`BlockCodeData.declarations`). -/
def declarationsOf (source : BlockCodeData) : Array Name := source.declarations

/-- The axioms the present declarations of `source` depend on other than `sorryAx` and Lean's
standard three, each once, in display order. -/
def extraAxiomsOf (source : BlockCodeData) : Array Name :=
  let all := (source.externalDecls.filter (·.present)).flatMap (·.axioms) ++
    source.literateDeclarations.declarations.flatMap (·.axioms)
  Data.sortAxioms <| all.filter fun a =>
    let cls := Data.AxiomClass.ofName a
    cls == .other || cls == .compilerTrusted

private def sortDeclsByCommand (decls : Array CodeDeclData) : Array CodeDeclData :=
  decls.qsort (fun a b =>
    a.commandIndex < b.commandIndex ||
    (a.commandIndex == b.commandIndex && a.name.toString < b.name.toString))

private def progressSegmentClass (missing hasSorry : Bool) : String :=
  if missing then
    "bp_code_progress_segment bp_code_progress_segment_missing"
  else if hasSorry then
    "bp_code_progress_segment bp_code_progress_segment_sorry"
  else
    "bp_code_progress_segment bp_code_progress_segment_ok"

private def codeSummaryText (label : Data.Label)
    (definedDefs definedTheorems : Array CodeDeclData) : String :=
  if definedDefs.isEmpty && definedTheorems.isEmpty then
    s!"{label}"
  else
    let definedDefNames := definedDefs.map (·.name)
    let definedTheoremNames := definedTheorems.map (·.name)
    let defs :=
      if definedDefNames.isEmpty then
        "none"
      else
        String.intercalate ", " (definedDefNames.toList.map toString)
    let thms :=
      if definedTheoremNames.isEmpty then
        "none"
      else
        String.intercalate ", " (definedTheoremNames.toList.map toString)
    let summaryItems := inlineDeclSummaryItems definedDefs definedTheorems (fun _ => none)
    let sorries := incompleteSummaryItems summaryItems
    let sorriesTxt :=
      if sorries.isEmpty then
        "none"
      else
        String.intercalate ", " (sorries.toList.map fun item => s!"{item.displayName} [{declSummaryStatusText item}]")
    s!"{label}\nLean definitions: {defs}\nLean theorems/lemmas: {thms}\nIncomplete declarations: {sorriesTxt}"

private def wrapPanelIndicator (label : Data.Label) (summaryTitle : String)
    (node previewBody : Output.Html) : Output.Html :=
  open Verso.Output.Html in
  html%{
    <span class="bp_code_summary_indicator">
      {renderCodeSummaryPreview
        s!"{label}"
        node
        previewBody
        (focusable := true)
        (ariaLabel? := some summaryTitle)}
    </span>
  }

private def renderInlinePanelIndicator (label : Data.Label) (cdata : ComputedData)
    (hrefOf : Name → Option String) : PanelIndicatorParts :=
  open Verso.Output.Html in
  let codeData := (cdata.source.getD {}).literateDeclarations
  let orderedDecls := if cdata.inlineBlocks.isEmpty then codeData.declarations else
    cdata.inlineBlocks.flatMap fun block => sortDeclsByCommand block.declarations
  let previewBody := renderSummaryPreview cdata hrefOf
  let summaryTitle := s!"Lean code for {label}: {codeSummaryText label codeData.definedDefs codeData.definedTheorems}"
  let indicator : Output.Html :=
    if orderedDecls.isEmpty then
      .empty
    else
      let segments := orderedDecls.map fun decl =>
        let hasSorry := decl.provedStatus.isIncomplete
        let statusView := decl.provedStatus.presentation
        let cls := progressSegmentClass false hasSorry
        let weight := max decl.weight 1
        let title :=
          if hasSorry then
            if decl.provedStatus.containsExplicitSorry then
              s!"{decl.name}: {statusView.externalPanelText}"
            else
              s!"{decl.name}: {statusView.summaryText}"
          else
            s!"{decl.name}: no sorry"
        html%{
          <span class={cls} title={title} style={s!"flex: {weight} 1 0%"}></span>
        }
      let bar := html%{
        <span class="bp_code_progress" aria-label="Lean declaration progress">{segments}</span>
      }
      wrapPanelIndicator label summaryTitle bar previewBody
  {
    summaryTitle
    indicator
  }

private def pluralizeKindText (kind : String) : String :=
  match kind with
  | "lemma" => "lemmas"
  | "theorem" => "theorems"
  | "definition" => "definitions"
  | "corollary" => "corollaries"
  | _ => kind ++ "s"

private def externalIndicatorKindText?
    (decls : Array Data.ExternalRef) (health : Informal.Graph.CodeHealth) : Option String :=
  if health.missingDecls > 0 || decls.isEmpty then
    none
  else
    let kinds := decls.filterMap externalDeclKindText?
    if kinds.size != decls.size || kinds.isEmpty then
      none
    else
      let first := kinds[0]!
      if kinds.all (· == first) then
        some first
      else
        none

private def externalIndicatorText
    (decls : Array Data.ExternalRef) (health : Informal.Graph.CodeHealth) : String :=
  let declText :=
    match externalIndicatorKindText? decls health with
    | some kind =>
      if health.totalDecls == 1 then
        s!"1 {kind}"
      else
        s!"{health.totalDecls} {pluralizeKindText kind}"
    | none =>
      if health.totalDecls == 1 then
        "1 declaration"
      else
        s!"{health.totalDecls} declarations"
  if health.missingDecls > 0 then
    s!"{declText}, {health.missingDecls} missing"
  else if health.hasChangedSource then
    if health.totalDecls == 1 then s!"{declText}, {health.sourceChangeWords}"
    else s!"{declText}, {health.changedDecls} with {health.sourceChangeWords}"
  else if health.anyGapCount > 0 then
    if health.totalDecls == 1 then
      s!"{declText}, incomplete"
    else
      s!"{declText}, {health.anyGapCount} incomplete"
  else
    declText

private structure ExternalIndicatorPresentation where
  className : String
  iconText : String := "●"
  title : String
  badgeText : String
deriving Inhabited

private def externalIndicatorPresentation
    (decls : Array Data.ExternalRef) (health : Informal.Graph.CodeHealth) :
    ExternalIndicatorPresentation :=
  let badgeText := externalIndicatorText decls health
  if health.missingDecls > 0 then
    {
      className := "bp_external_status_missing"
      title := s!"Lean declarations: {health.presentDecls}/{health.totalDecls} present ({health.missingDecls} missing)"
      badgeText
    }
  else if health.hasChangedSource then
    {
      className := "bp_external_status_changed"
      iconText := "◌"
      title := s!"Lean declarations: all present, {health.changedDecls} with \
        {health.sourceChangeWords}: not shown as checked"
      badgeText
    }
  else if health.anyGapCount > 0 then
    {
      className := "bp_external_status_sorry"
      title := s!"Lean declarations: all present, {health.anyGapCount} incomplete"
      badgeText
    }
  else
    {
      className := "bp_external_status_ok"
      title := s!"Lean declarations: all {health.totalDecls} present"
      badgeText
    }

private def renderExternalPanelIndicator (decls : Array Data.ExternalRef)
    (label : Data.Label) (hrefOf : Name → Option String) : PanelIndicatorParts :=
  open Verso.Output.Html in
  let health := Informal.Graph.codeHealthOfBlockSource .definition {} (some { externalDecls := decls })
  let renderHealth := externalRenderHealth decls
  let previewBody := renderSummaryPreview { source := some { externalDecls := decls } } hrefOf
  let presentation := externalIndicatorPresentation decls health
  let summaryTitle :=
    s!"Lean code for {label}: " ++ appendRenderHealthSummary
      (externalCodeEntryTitle health.presentDecls health.totalDecls health.missingDecls
        health.anyGapCount health.changedDecls health.sourceChangeWords)
      renderHealth
  let badgeTitle :=
    appendRenderHealthSummary presentation.title renderHealth
  let badge : Output.Html := html%{
    <span class={s!"bp_external_status_badge bp_external_status_badge_summary \
        {presentation.className}"} title={badgeTitle}>
      <span class={s!"bp_external_status_icon {presentation.className}"}>
        {.text presentation.iconText}
      </span>
      <span class="bp_external_status_badge_text">{.text presentation.badgeText}</span>
    </span>
  }
  {
    summaryTitle
    indicator := wrapPanelIndicator label summaryTitle badge previewBody
  }

/--
Render the top-right code-panel indicator from canonical code-source data.

Inline blocks use the weighted progress bar; external references keep the pill-style
indicator for now, but both paths share the same normalized declaration summary model
for hover content.
-/
def renderPanelIndicator (label : Data.Label) (cdata : ComputedData)
    (hrefOf : Name → Option String) : PanelIndicatorParts :=
  match cdata.source with
  | none => { summaryTitle := s!"Lean code for {label}: no associated Lean declarations" }
  | some source =>
    let inlinePanel := renderInlinePanelIndicator label cdata hrefOf
    let externalPanel := renderExternalPanelIndicator source.externalDecls label hrefOf
    if source.literateDeclarations.isEmpty then externalPanel else
    if source.externalDecls.isEmpty then inlinePanel else
      { summaryTitle := inlinePanel.summaryTitle ++ "\n" ++ externalPanel.summaryTitle
        indicator := .seq #[inlinePanel.indicator, externalPanel.indicator] }

/-- The summary's closing line: a link to the explanation of the marks, when the site has one. -/
private def withMeaningLink (body : Output.Html) (meaningHref? : Option String) : Output.Html :=
  match meaningHref? with
  | some href =>
    .seq #[body, .element "p" #[("class", "bp_code_summary_meaning")]
      (.element "a" #[("class", "bp_meaning_link"), ("href", href)]
        (.text Informal.Meaning.linkText))]
  | none => body

/-- The mark of Lean code `source` of a node of kind `kind`, whatever it is. -/
private def markOfSource (kind : Data.NodeKind) (source : BlockCodeData) : BlockStatusMark :=
  statusMarkFromHealth kind (extraAxiomsOf source)
    (Informal.Graph.codeHealthOfBlockSource kind {} (some source)) (declarationsOf source)
    (unplacedOf source) source.sourceChange?

/--
The Lean code a node's mark is about, from the Lean code of its statement (`statement?`) and the
declarations attached to its proof (`proof`); every mark, chip, glyph, success colour and kernel
replay standing of a node is derived from it.

The proof's declarations can only lower the mark, never raise it. With Lean code on the
statement, they join it, each declaration once with every observation of it merged
conservatively (`Data.ExternalRef.mergeSnapshots`): a `sorry`, a missing declaration, an axiom
outside Lean's standard three or a changed source in them shows in the mark. Without Lean code on
the statement the mark is about the Lean statement, of which there is none: the result is `none`
(no Lean declaration) however complete the proof's declarations are, unless they show one of those
problems, and then it is their code.
-/
def markSource? (kind : Data.NodeKind) (statement? : Option BlockCodeData)
    (proof : Array Data.ExternalRef) : Option BlockCodeData :=
  let statement? := statement?.bind (·.nonempty?)
  if proof.isEmpty then statement? else
  -- each declaration once, its statuses merged conservatively and every axiom any observation
  -- of it reports kept
  let merge (refs : Array Data.ExternalRef) : Array Data.ExternalRef :=
    (Data.ExternalRef.mergeSnapshots #[] refs).map fun ref =>
      let canonical := ref.canonical
      { ref with axioms := Data.sortAxioms <| refs.foldl (init := #[]) fun acc r =>
          if r.canonical.eraseMacroScopes == canonical then
            r.axioms.foldl (fun acc a => if acc.contains a then acc else acc.push a) acc
          else acc }
  match statement? with
  | some statement =>
    some { statement with externalDecls := merge (statement.externalDecls ++ proof) }
  | none =>
    let code : BlockCodeData := { externalDecls := merge proof }
    let mark := markOfSource kind code
    if mark.status.isProved && mark.extraAxioms.isEmpty && mark.sourceChange?.isNone then none
    else some code

/-- The heading status of a node of kind `kind` whose statement's Lean code is `source?` and whose
proof has the declarations `proof` (`markSource?`); `none` when the mark is "no Lean
declaration". -/
def statusMark? (kind : Data.NodeKind) (source? : Option BlockCodeData)
    (proof : Array Data.ExternalRef := #[]) : Option BlockStatusMark :=
  (markSource? kind source? proof).map (markOfSource kind)

/-- Heading status and tooltip: the mark is about `markSource?` of the statement's code (`cdata`)
and the declarations attached to the proof (`proofDecls`); the summary lists the statement's
declarations and, under "Attached to the proof", the proof's, with their statuses, so that the
page says what the mark counts. The tooltip is headed `heading` (the statement's numbered title)
and ends with a link to the explanation of the marks at `meaningHref?`. -/
def renderParts (data : BlockData) (cdata : ComputedData) (hrefOf : Name → Option String)
    (replay? : Option Replay.Result := none) (heading : String := toString data.label)
    (meaningHref? : Option String := none) (proofDecls : Array Data.ExternalRef := #[]) :
    RenderParts :=
  if data.isProof then {} else
  let source? := markSource? data.kind cdata.source proofDecls
  let source := source?.getD {}
  let health := Informal.Graph.codeHealthOfBlockSource data.kind {} source?
  let renderHealth := externalRenderHealth (cdata.source.getD {}).externalDecls
  let statusMark := markOfSource data.kind source
  let title := if source.isEmpty then "No associated Lean declarations" else
    -- the state first, in the words of the heading's mark, so that what a reader hears or sees
    -- on the link is the verdict, then what the declarations are
    s!"{(statusGlyph (some statusMark) replay?).2}. " ++ appendRenderHealthSummary
      (externalCodeEntryTitle health.presentDecls health.totalDecls health.missingDecls
        health.anyGapCount health.changedDecls health.sourceChangeWords)
      renderHealth
  { statusMark := if source.isEmpty then none else some statusMark
    codeEntry := renderCodeEntryWrap cdata.codeHref title heading
      (withMeaningLink (renderSummaryPreview cdata hrefOf proofDecls) meaningHref?)
      (codeEntryVisual (!source.isEmpty) statusMark replay?)
      renderHealth }

end CodeSummary
end Informal
