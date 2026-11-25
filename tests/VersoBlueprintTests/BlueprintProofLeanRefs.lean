/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Emilio J. Gallego Arias
-/

import VersoBlueprintTests.Blueprint.Support
import VersoBlueprint.Vbp
import VersoBlueprint.PreviewManifest.BlockRender
import VersoBlueprintTests.BlueprintProofLeanRefs.Provider

open Lean Verso Genre Manual Informal
open Verso.VersoBlueprintTests.Blueprint.Support

namespace Verso.VersoBlueprintTests.BlueprintProofLeanRefs

@[blueprint "proof.inferred.dep"]
theorem inferredDependency : True := True.intro

theorem attachedResult : True := inferredDependency

theorem admittedAttachedResult : True := by sorry

-- Synthetic status observations exercise the reducer independently of the
-- classifier. Neither facet, input order, batching nor exact replay may discard
-- observed incompleteness before the canonical node projection sees it.
#eval show IO Unit from do
  let good : Data.ExternalRef := { Data.ExternalRef.ofName `Example.repeated with
    present := true, kind := .theorem, provedStatus := .proved }
  let known : Data.ProvedStatus := .incomplete { knownSorry := #[{
    location := .proof, origin := .dependency, refs? := some 2 }] }
  let unverified : Data.ProvedStatus := .incomplete { unverified := #[{
    location := .proof, declaration := good.canonical, reason := .bodyUnavailable }] }
  for isProof in #[false, true] do
    for status in #[known, unverified] do
      let gap := { good with provedStatus := status }
      for refs in #[#[good, gap], #[gap, good]] do
        -- Keep producer identities fixed across batching and exact replay.
        -- Both facets enter the identified slice and retain their authored side.
        let assemble := fun (indices : Array Nat) =>
          let records := indices.toList.map fun index =>
            ({ id := { moduleName := `Repeated, producer := `test, subject := `repeated,
                       site := index, slot := 0 },
               label := `repeated,
               references := if isProof then #[] else #[refs[index]!],
               proofReferences := if isProof then #[refs[index]!] else #[],
               priority := none, source := none }
              : Contributions.Record)
          (NodeAssembly.assemble `repeated #[] records).map (·.node)
        let indices := (List.range refs.size).toArray
        let .ok batched := assemble indices
          | throw <| IO.userError "Repeated associations were rejected"
        let .ok (_, incremental) := indices.foldlM
            (fun (state : Array Nat × Data.Node) index => do
              let accumulated := state.1.push index
              return (accumulated, ← assemble accumulated)) (#[], ({} : Data.Node))
          | throw <| IO.userError "Incremental associations were rejected"
        let .ok replayed := assemble (indices ++ indices)
          | throw <| IO.userError "Replayed associations were rejected"
        for node in #[batched, incremental, replayed] do
          let refs := node.associatedExternalRefs
          unless refs.size == 1 && refs[0]!.provedStatus == status &&
              node.leanDecls == #[good.canonical] &&
              !(Graph.nodeCodeHealth {} node).localProofFormalized do
            throw <| IO.userError "Same-facet deduplication discarded status evidence"
  for status in #[known, unverified, Data.ProvedStatus.incomplete {}, .missing, .axiomLike] do
    let ref := { good with provedStatus := status, present := status != .missing }
    let code : Data.Code := { stx := .missing, definedTheorems := #[{
      name := good.canonical, provedStatus := .proved }] }
    let node : Data.Node := { kind := .theorem, proofExternalRefs := #[ref], literateCodes := #[code] }
    let health := Graph.nodeCodeHealth {} node
    unless node.summaryExternalRefs.isEmpty && health.totalDecls == 1 &&
        health.hasAnyGaps == (!status.isMissing && status.isIncomplete) &&
        health.hasMissingExternalDecls == status.isMissing &&
        health.hasAxiomLike == status.isAxiomLike && !health.localProofFormalized &&
        health.provedStatus.reportJson == status.reportJson &&
        node.summaryLiterateCodes[0]!.definedTheorems[0]!.provedStatus.reportJson == status.reportJson do
      throw <| IO.userError "Inline display precedence discarded external status evidence"
    let source : BlockCodeData := { externalDecls := #[ref], literateDeclarations := {
      definedTheorems := #[{ name := good.canonical, provedStatus := .proved }] } }
    let panel := Graph.codeHealthOfBlockSource .theorem {} (some source)
    unless source.summaryExternalDecls.isEmpty && panel.totalDecls == 1 &&
        panel.hasAnyGaps == (!status.isMissing && status.isIncomplete) &&
        panel.hasMissingExternalDecls == status.isMissing &&
        panel.hasAxiomLike == status.isAxiomLike && !panel.localProofFormalized &&
        panel.provedStatus.reportJson == status.reportJson do
      throw <| IO.userError "Panel display precedence discarded external status evidence"
    let data : BlockData := { label := `overlap, kind := .theorem, count := 1, codeData := some source }
    let rendered := CodeSummary.renderParts data { source := some source } (fun _ => none)
    unless !hasSubstr rendered.codeEntry.render "bp_code_decl_status_ok" do
      throw <| IO.userError "Summary preview presented the selected inline declaration as complete"
  let code : Data.Code := { stx := .missing, definedTheorems := #[{
    name := good.canonical, provedStatus := .proved }] }
  let node : Data.Node := { kind := .theorem, proofExternalRefs := #[good], literateCodes := #[code] }
  let external : Graph.ExternalCodeStatus := { provedStatus := fun _ => unverified }
  unless !(Graph.nodeCodeHealth external node).localProofFormalized do
    throw <| IO.userError "Inline display precedence discarded external lookup evidence"

#docs (Manual) proofReferencesDoc "Proof references" :=
:::::::
:::lemma_ "proof.helper.owner" (lean := "Nat.add_comm")
A separately owned helper.
:::
:::lemma_ "proof.references" (lean := "Nat.add_assoc")
A statement with its own implementation.
:::
:::proof "proof.references" (lean := "Nat.add_comm, Nat.add_left_comm") (autoDeps := true) (uses := "proof.helper.owner")
A proof with two associated declarations.
:::
:::lemma_ "proof.attachments.only"
A statement whose Lean association is on the proof.
:::
:::proof "proof.attachments.only" (lean := "attachedResult") (autoDeps := true)
The attached theorem contributes to this node and infers its proof dependency.
:::
:::lemma_ "proof.attachments.admitted"
A statement with an incomplete associated proof.
:::
:::proof "proof.attachments.admitted" (lean := "admittedAttachedResult") (autoDeps := false)
The attached proof hole must remain visible in progress and summaries.
:::
:::lemma_ "proof.attachments.both" (lean := "attachedResult")
The same declaration can be mentioned on both facets.
:::
:::proof "proof.attachments.both" (lean := "attachedResult")
Both mentions retain their facet while contributing one canonical declaration.
:::
:::lemma_ "proof.without.references" (lean := "Nat.add_assoc")
A statement with implementation metadata.
:::
:::proof "proof.without.references"
A proof with no attached references.
:::
:::proof "proof.imported.crossFacet" (lean := "Provider.crossFacetProof")
This imported statement association also has a proof-facet occurrence.
:::
:::::::

/- Both facets contribute to node membership, inference, and conservative status. -/
#eval show CoreM Unit from do
  let state := Environment.informalExt.getState (← getEnv)
  let some node := state.data.get? (Name.mkSimple "proof.references")
    | throwError "Missing proof-reference node"
  unless node.externalRefs.map (·.canonical) == #[`Nat.add_assoc] &&
      node.proofExternalRefs.map (·.canonical) == #[`Nat.add_comm, `Nat.add_left_comm] do
    throwError "A declaration lost its authored facet"
  unless node.leanDecls == #[`Nat.add_assoc, `Nat.add_comm, `Nat.add_left_comm] do
    throwError "Proof declarations were excluded from node membership"
  unless node.proof.any (·.dependencyLabels == #[Name.mkSimple "proof.helper.owner"]) &&
      node.statement.any (·.dependencyLabels.isEmpty) do
    throwError "Proof attachments changed authored dependency axes"
  unless state.leanNameLabels.getD `Nat.add_comm #[] ==
      #[Name.mkSimple "proof.helper.owner", Name.mkSimple "proof.references"] do
    throwError "Proof declarations were excluded from the accepted index"
  let some proofOnly := state.data.get? (Name.mkSimple "proof.attachments.only")
    | throwError "Missing proof-only association node"
  unless proofOnly.hasAssociatedCode && proofOnly.leanDecls == #[``attachedResult] &&
      (Graph.nodeCodeHealth {} proofOnly).localProofFormalized &&
      proofOnly.proof.any (·.dependencyLabels == #[Name.mkSimple "proof.inferred.dep"]) &&
      proofOnly.statement.any (·.dependencyLabels.isEmpty) do
    throwError "Proof association did not contribute membership, status, or inferred proof dependencies"
  -- its declarations are complete, but the node has no Lean statement: nothing counts it as
  -- formalized, not its statement nor its proof nor its dependents' closures
  let onlyLabel := Name.mkSimple "proof.attachments.only"
  unless !proofOnly.hasLeanStatement && !Graph.nodeLocalFormalized {} proofOnly &&
      !Graph.nodeLocalStatementFormalized {} proofOnly &&
      Graph.statementStatus {} state onlyLabel proofOnly != .formalized &&
      Graph.proofStatus {} state onlyLabel proofOnly != .formalized &&
      Graph.proofStatus {} state onlyLabel proofOnly != .formalizedWithAncestors do
    throwError "A node without a Lean statement was counted as formalized"
  let some admitted := state.data.get? (Name.mkSimple "proof.attachments.admitted")
    | throwError "Missing admitted proof association"
  unless Graph.proofStatus {} state (Name.mkSimple "proof.attachments.admitted") admitted == .incomplete do
    throwError "An admitted proof association appeared complete"
  let some both := state.data.get? (Name.mkSimple "proof.attachments.both")
    | throwError "Missing shared-facet association"
  unless both.leanDecls == #[``attachedResult] &&
      (Graph.nodeCodeHealth {} both).totalDecls == 1 do
    throwError "The same declaration on two facets was counted twice"
  let proofGap : Data.ProvedStatus := .incomplete {
    knownSorry := #[{ location := .proof, origin := .dependency }] }
  let crossFacetGap := { both.toNode with
    proofExternalRefs := both.proofExternalRefs.map fun ref => { ref with provedStatus := proofGap } }
  unless (Graph.nodeCodeHealth {} crossFacetGap).hasAnyGaps &&
      !(Graph.nodeCodeHealth {} crossFacetGap).localProofFormalized do
    throwError "Canonical deduplication erased proof-facet status evidence"
  for status in #[Data.ProvedStatus.proved, .axiomLike, .missing,
      proofGap, .incomplete { knownSorry := #[{ location := .unknown, origin := .unknown }] },
      .incomplete { unverified := #[{ location := .proof, reason := .bodyUnavailable }] }] do
    let refs := proofOnly.proofExternalRefs.map fun ref =>
      { ref with provedStatus := status, present := status != .missing }
    let changed := { proofOnly.toNode with proofExternalRefs := refs }
    unless (Graph.nodeCodeHealth {} changed).localProofFormalized == status.isProved &&
        (Graph.nodeWarnings {} state (Name.mkSimple "proof.attachments.only") changed).missingExternalDecl ==
          (status == .missing) do
      throwError "Proof association status did not contribute conservatively"

-- Add a second proof association to a compiled imported node. Export only this
-- local contribution and check both associations again after another import.
private def contributeProofReferences (label : Data.Label) (references : Array Data.ExternalRef)
    (payload : Data.NodeContribution := {}) :
    CoreM (Option Data.Node) := do
  let fact : Contributions.Record := {
    id := ⟨← getMainModule, `test.proofAssociations, label, 0, 0⟩
    label, proofReferences := references
    priority := none, source := none }
  Environment.contributeRecord fact payload

run_meta do
  let ref ← externalRefSnapshotAtCurrentDir {}
    (Data.ExternalRef.ofName ``Provider.secondProof)
  let some _ ← contributeProofReferences (Name.mkSimple "proof.imported.associations") #[ref]
    | throwError "Could not extend the imported proof associations"
  let some node ← Environment.getNode? (Name.mkSimple "proof.imported.associations")
    | throwError "Missing imported proof node"
  unless node.leanDecls == #[``Provider.firstProof, ``Provider.secondProof] do
    throwError "Local proof association discarded imported membership"

-- Re-observe a compiled admitted proof with a synthetic neutral snapshot.
-- This is a projection/replay control, not a claim about classifier output.
run_meta do
  let ref ← externalRefSnapshotAtCurrentDir {}
    (Data.ExternalRef.ofName ``Provider.admittedProof)
  let neutral := { ref with provedStatus := .proved }
  let some _ ← contributeProofReferences (Name.mkSimple "proof.imported.repeated") #[neutral, ref]
    | throwError "Could not repeat the imported proof association"
  let some node ← Environment.getNode? (Name.mkSimple "proof.imported.repeated")
    | throwError "Missing repeated imported proof node"
  unless node.proofExternalRefs.size == 1 &&
      node.associatedExternalRefs[0]!.provedStatus.isIncomplete &&
      !(Graph.nodeCodeHealth {} node).localProofFormalized do
    throwError "Repeated compiled proof association erased incompleteness"

-- Synthetic neutral inline evidence tests display precedence. The external
-- snapshot supplies the actual admitted proof's classification.
run_meta do
  let ref ← externalRefSnapshotAtCurrentDir {}
    (Data.ExternalRef.ofName ``Provider.admittedProof)
  let code : Data.Code := { stx := .missing, definedTheorems := #[{
    name := ``Provider.admittedProof, provedStatus := .proved }] }
  let some _ ← contributeProofReferences (Name.mkSimple "proof.inline.overlap") #[ref] {
    kind := some .theorem, literateCodes := #[code] }
    | throwError "Could not register inline/external overlap"

#eval show CoreM Unit from do
  let some node ← Environment.getNode? (Name.mkSimple "proof.inline.overlap")
    | throwError "Missing inline/external overlap"
  unless (Graph.nodeCodeHealth {} node).totalDecls == 1 &&
      !(Graph.nodeCodeHealth {} node).localProofFormalized do
    throwError "Inline/external overlap was counted twice or appeared complete"
  let summary ← Commands.buildSummary
  let details := summary.incompleteDetails.filter (·.label == Name.mkSimple "proof.inline.overlap")
  unless details.length == 1 && details[0]!.status.hasKnownSorry do
    throwError "Summary discarded the proof association's incompleteness"

/- Page HTML, cached proof previews, manifest facets, and node queries retain the same proof refs. -/
#eval show IO Unit from do
  let (html, state) ← renderManualDocHtmlStringAndState extension_impls% proofReferencesDoc
  unless hasSubstr html "Lean declarations attached to this proof" do
    throw <| IO.userError "Proof declaration panel missing from page HTML"
  let files ← PreviewManifest.buildPreviewDataFiles extension_impls%
    (fun message => throw <| IO.userError message)
    (PreviewManifest.PreparedPreviewState.prepare state)
    ({ mode := .none } : ExternalMarkupRender.Config)
  let label := Name.mkSimple "proof.references"
  let some statement := files.manifest.findEntry? (PreviewCache.statementKey label)
    | throw <| IO.userError "Missing statement facet"
  let some proof := files.manifest.findEntry? (PreviewCache.proofKey label)
    | throw <| IO.userError "Missing proof facet"
  unless statement.codeData.any (·.externalDecls.map (·.canonical) == #[`Nat.add_assoc]) &&
      proof.codeData.any (·.externalDecls.map (·.canonical) == #[`Nat.add_comm, `Nat.add_left_comm]) &&
      proof.leanCodePreviewKeys.size == 2 do
    throw <| IO.userError "Manifest borrowed declarations from the other facet"
  let noRefs := Name.mkSimple "proof.without.references"
  unless (files.manifest.findEntry? (PreviewCache.proofKey noRefs)).any
      (fun entry => entry.codeData.isNone && entry.leanCodePreviewKeys.isEmpty) do
    throw <| IO.userError "An unattached proof borrowed statement code"
  let some proofBody := files.htmlCache.findHtml? (PreviewCache.proofKey label)
    | throw <| IO.userError "Missing cached proof HTML"
  let rendered := PreviewManifest.BlockRender.renderWithRenderedContent {} proof {
    body := .raw proofBody
    codeBodies := #[.raw "Supporting declaration preview"]
    codeData := proof.codeData.getD {}
  }
  unless hasSubstr rendered.render "Lean declarations attached to this proof" &&
      hasSubstr rendered.render "Supporting declaration preview" do
    throw <| IO.userError "Cached proof rendering dropped its supporting declarations"
  let .ok (some query) := VersoBlueprint.Vbp.parseQueryPlan ["node", "proof.references"]
    | throw <| IO.userError "Node query failed to parse"
  let result := query.run files.manifest
  let .ok proofJson := result.getObjVal? "proof"
    | throw <| IO.userError "Node query omitted the proof facet"
  unless (proofJson.getObjVal? "codeData").toOption == some (toJson proof.codeData) do
    throw <| IO.userError "Node query dropped proof reference metadata"
  let .ok (some codeQuery) := VersoBlueprint.Vbp.parseQueryPlan ["code", "attachedResult"]
    | throw <| IO.userError "Code query failed to parse"
  let .ok matchingLabels := (codeQuery.run files.manifest).getObjValAs? (Array Json) "labels"
    | throw <| IO.userError "Code query omitted its labels"
  unless matchingLabels.any (fun entry => (entry.getObjValAs? String "label").toOption ==
      some "proof.attachments.only") do
    throw <| IO.userError "Code query omitted a proof-only association"
  for (label, complete) in #[("proof.attachments.only", true), ("proof.attachments.admitted", false)] do
    let .ok (some statusQuery) := VersoBlueprint.Vbp.parseQueryPlan ["status", label]
      | throw <| IO.userError "Status query failed to parse"
    let status := statusQuery.run files.manifest
    -- neither node has a Lean statement: neither is complete, and the evidence of the declarations
    -- attached to its proof is `proofComplete`, with a verdict naming the missing statement
    unless (status.getObjValAs? Bool "complete").toOption == some false &&
        (status.getObjValAs? Bool "statementComplete").toOption == some false &&
        (status.getObjValAs? Bool "proofComplete").toOption == some complete &&
        ((status.getObjValAs? String "verdict").toOption == some "no-lean-statement") == complete do
      throw <| IO.userError "Status query ignored the proof association"
    let .ok declarations := status.getObjValAs? (Array Json) "declarations"
      | throw <| IO.userError "Status query omitted declarations"
    unless declarations.size == 1 &&
        (declarations[0]!.getObjValAs? String "facet").toOption == some "proof" do
      throw <| IO.userError "Status query lost proof association provenance"

/- The side-by-side layout shows no panel of a proof's declarations on the page, while the node's data keeps them: the same proof facet, status and queries. -/
#eval show IO Unit from do
  let (plain, plainState) ← renderManualDocHtmlStringAndState extension_impls% proofReferencesDoc
  let (html, state) ← DeclarationSource.withEnabled true <|
    renderManualDocHtmlStringAndState extension_impls% proofReferencesDoc
  unless hasSubstr html "class=\"bp_sbs\"" &&
      !hasSubstr html "Lean declarations attached to this proof" &&
      !hasSubstr html "data-lean-decl=\"Nat.add_left_comm\"" &&
      hasSubstr html "data-lean-decls=\"Nat.add_comm Nat.add_left_comm\"" do
    throw <| IO.userError "A side-by-side page showed a proof's declarations"
  -- the mark of a node counts its proof's declarations: one with `sorry` is incomplete; complete
  -- ones do not give a statement without Lean code a mark
  let glyphOf (label : String) : String :=
    let marker := "data-bp-node=\"«" ++ label ++ "»\""
    let after := marker.intercalate ((html.splitOn marker).drop 1)
    toString (((after.splitOn "bp_status_glyph bp_status_glyph_").getD 1 "").takeWhile (· != '"'))
  unless glyphOf "proof.attachments.admitted" == "partial" &&
      glyphOf "proof.attachments.only" == "none" do
    throw <| IO.userError s!"A side-by-side mark ignored the proof's declarations: \
      {glyphOf "proof.attachments.admitted"} / {glyphOf "proof.attachments.only"}"
  let build (state : TraverseState) := PreviewManifest.buildPreviewDataFiles extension_impls%
    (fun message => throw <| IO.userError message)
    (PreviewManifest.PreparedPreviewState.prepare state)
    ({ mode := .none } : ExternalMarkupRender.Config)
  let plainFiles ← build plainState
  let files ← DeclarationSource.withEnabled true <| build state
  for label in #["proof.references", "proof.attachments.only", "proof.attachments.admitted"] do
    let key := PreviewCache.proofKey (Name.mkSimple label)
    let some proof := files.manifest.findEntry? key
      | throw <| IO.userError s!"Missing proof facet of {label}"
    unless (plainFiles.manifest.findEntry? key).any (toJson · == toJson proof) &&
        proof.codeData.any (!·.externalDecls.isEmpty) do
      throw <| IO.userError s!"The side-by-side layout changed the proof facet of {label}"
  for (label, complete) in #[("proof.attachments.only", true), ("proof.attachments.admitted", false)] do
    let .ok (some statusQuery) := VersoBlueprint.Vbp.parseQueryPlan ["status", label]
      | throw <| IO.userError "Status query failed to parse"
    unless ((statusQuery.run files.manifest).getObjValAs? Bool "proofComplete").toOption ==
        some complete do
      throw <| IO.userError "A side-by-side status ignored the proof association"

#docs (Manual) proofPlacementsDoc "Proof placements" :=
:::::::
:::lemma_ "proof.placed"
A statement whose proof is placed again below.
:::
:::proof "proof.placed" (lean := "admittedAttachedResult")
The attached proof hole is placed with the proof.
:::

{blueprint_node "proof.placed" (facet := "proof")}

{blueprint_summary}
:::::::

/-- The values of `attr="…"` in `html`. -/
private def attrValues (html attr : String) : List String :=
  (html.splitOn s!"{attr}=\"").drop 1 |>.map fun rest => (rest.splitOn "\"").headD ""

/-- The `href` values of the links whose text mentions `text`. -/
private def linksMentioning (html text : String) : List String :=
  (html.splitOn "href=\"").drop 1 |>.filterMap fun rest =>
    let href := (rest.splitOn "\"").headD ""
    if hasSubstr ((rest.splitOn "</a>").headD "") text then some href else none

/- A placement of a proof shows no panel of its declarations (a placement shows code only for a
statement), so the panel is the proof's own: in the standard layout only. In the side-by-side
layout the summary's link to the proof's declaration with `sorry`, which has no row of its own,
lands on the node, and every link to a place on the page finds it. -/
#eval show IO Unit from do
  let (plain, _) ← renderManualDocHtmlStringAndState extension_impls% proofPlacementsDoc
  let (html, _) ← DeclarationSource.withEnabled true <|
    renderManualDocHtmlStringAndState extension_impls% proofPlacementsDoc
  unless countSubstr plain "Lean declarations attached to this proof" == 1 &&
      hasSubstr plain "data-bp-facet=\"proof\" data-bp-preview-key" do
    throw <| IO.userError "A placed proof changed its declaration panels in the standard layout"
  if hasSubstr html "Lean declarations attached to this proof" then
    throw <| IO.userError "A placed proof showed its declaration panel in the side-by-side layout"
  let ids := attrValues html "id"
  let fragments := (attrValues html "href").filterMap fun href =>
    match href.splitOn "#" with
    | [_, fragment] => if fragment.isEmpty || hasSubstr fragment "=" then none else some fragment
    | _ => none
  let missing := fragments.filter (!ids.contains ·)
  unless missing.isEmpty do
    throw <| IO.userError s!"Links to places missing from the page: {missing}"
  let declLinks := linksMentioning html "admittedAttachedResult"
  -- the target is the node's placement: the element carrying the id names the node
  let landsOnNode (href : String) : Bool :=
    match href.splitOn "#" with
    | [_, fragment] =>
      match html.splitOn s!"id=\"{fragment}\"" with
      | before :: after :: _ =>
        hasSubstr (((before.splitOn "<").getLast?.getD "") ++ ((after.splitOn ">").headD ""))
          "proof.placed"
      | _ => false
    | _ => false
  unless !declLinks.isEmpty && declLinks.all landsOnNode do
    throw <| IO.userError s!"The summary's link to the open proof declaration misses its node: {declLinks}"

theorem placeShown : True := trivial
theorem placeShared : True := trivial
theorem placeKeyOrder : True := trivial

#docs (Manual) proofDeclTargetsDoc "Proof declaration targets" :=
:::::::
:::lemma_ "proof.targets.only"
A statement without a Lean declaration of its own.
:::
:::proof "proof.targets.only" (lean := "admittedAttachedResult")
Its declaration is named by the proof alone.
:::
:::lemma_ "proof.targets.both" (lean := "attachedResult")
A statement whose declaration its proof names as well.
:::
:::proof "proof.targets.both" (lean := "attachedResult, inferredDependency")
The proof names the statement's declaration and one of its own.
:::

```Verso.Genre.Manual.InlineLean.lean
theorem proofTargetsInline : True := trivial
```

:::lemma_ "proof.targets.inline"
A statement whose proof names a declaration of the text.
:::
:::proof "proof.targets.inline" (lean := "proofTargetsInline")
The declaration is defined in a Lean block of the text.
:::

:::lemma_ "place.zeta" (lean := "placeShown")
A statement that shows the declaration.
:::
:::lemma_ "place.alpha"
A node whose key comes first and whose proof attaches the declaration another statement shows.
:::
:::proof "place.alpha" (lean := "placeShown")
The proof names it too.
:::
:::lemma_ "place.p.a"
The first of two nodes whose proofs alone attach a declaration.
:::
:::proof "place.p.a" (lean := "placeShared")
Attached here.
:::
:::lemma_ "place.p.b"
The second of them.
:::
:::proof "place.p.b" (lean := "placeShared")
And here.
:::
:::lemma_ "place.k"
A node whose label comes first, and whose key comes second.
:::
:::proof "place.k" (lean := "placeKeyOrder")
Attached here.
:::
:::lemma_ "place.k.b"
A node whose label comes second, and whose key comes first.
:::
:::proof "place.k.b" (lean := "placeKeyOrder")
And here.
:::

{blueprint_summary}
:::::::

/-- The fragment of `href`, if it has one. -/
private def fragmentOf? (href : String) : Option String :=
  match href.splitOn "#" with
  | [_, fragment] => if fragment.isEmpty then none else some fragment
  | _ => none

/-- The opening tag of the element of `html` whose `id` is `fragment`. -/
private def tagWithId (html fragment : String) : String :=
  match html.splitOn s!"id=\"{fragment}\"" with
  | before :: after :: _ => ((before.splitOn "<").getLast?.getD "") ++ ((after.splitOn ">").headD "")
  | _ => ""

/-- Where a reader of the traversal store of rendered declarations finds `decl` without asking the
Blueprint's resolver: the first fallback key of a node (by key) that names it, else an inline Lean
block that defines it. This is how a library that draws figures with links into the site looks a
declaration up. -/
private def storeTarget? (state : TraverseState) (decl : Name) : Option String :=
  let dom := Resolve.externalRenderedDeclDomainName
  let keys := match state.domains.get? dom with
    | some d => d.objects.foldl (init := (#[] : Array String)) fun (acc : Array String) (k : String) _ =>
        if k.startsWith "label:" && k.endsWith ("|" ++ decl.toString) then acc.push k else acc
    | none => #[]
  (keys.qsort (· < ·)).findSome? (Resolve.resolveDomainHref? state dom ·) <|>
    Resolve.resolveInlineLeanDeclHref? state decl

/-- The place a declaration's links should lead to. -/
private inductive Place where
  /-- The Lean row of the declaration that node `label` shows. -/
  | row (label : String)
  /-- The node `label`. -/
  | node (label : String)
  /-- The Lean block of the text that defines it. -/
  | inline

/-- The place of `decl`, the nodes that name it, and where its links lead in the side-by-side and
the standard layout. -/
private def placeCases : List (Name × List String × Place × Place) := [
  (``admittedAttachedResult, ["proof.targets.only"], .node "proof.targets.only",
    .row "proof.targets.only"),
  (``attachedResult, ["proof.targets.both"], .row "proof.targets.both", .row "proof.targets.both"),
  (``inferredDependency, ["proof.targets.both"], .node "proof.targets.both",
    .row "proof.targets.both"),
  (``proofTargetsInline, ["proof.targets.inline"], .inline, .row "proof.targets.inline"),
  -- a row of another node's statement, though the node whose proof attaches it comes first
  (``placeShown, ["place.alpha", "place.zeta"], .row "place.zeta", .row "place.alpha"),
  -- two proofs alone attach it: the first node in key order
  (``placeShared, ["place.p.a", "place.p.b"], .node "place.p.a", .row "place.p.a"),
  -- key order, not label order: `«place.k.b»|` comes before `«place.k»|`
  (``placeKeyOrder, ["place.k", "place.k.b"], .node "place.k.b", .row "place.k.b")]

/-- Checks that every resolver of the site leads `decl` to one place of `html`, of the kind
`place`. A node's own links (its chip, its summary entry) may lead to its own row of the
declaration instead, in the standard layout, where each proof shows its rows. -/
private def checkPlace (layout html : String) (state : TraverseState) (sideBySide : Bool)
    (decl : Name) (labels : List String) (place : Place) : IO Unit := do
  let ids := attrValues html "id"
  let some global := storeTarget? state decl
    | throw <| IO.userError s!"{layout}: the store has no place for {decl}"
  let inPage (href : String) : Bool :=
    (fragmentOf? href).any fun f => ids.contains f ||
      -- this test's renderer gives the defining name of a Lean block of the text no `id` (a site
      -- does, `TraverseState.definitionIds`); the name is on the page, under its link target
      (some href == Resolve.resolveInlineLeanDeclHref? state decl &&
        hasSubstr html s!"data-binding=\"const-{decl}\"")
  unless inPage global do
    throw <| IO.userError s!"{layout}: {decl} leads to {global}, missing from the page"
  let site := (LeanCodeLinks.siteTargets state).get? decl
  unless site == some global do
    throw <| IO.userError s!"{layout}: Lean code leads {decl} to {site}, the store to {global}"
  let mut own : List String := []
  for label in labels do
    let label := Name.mkSimple label
    let some href := TraversalIndex.ExternalDeclAnchors.declHref? state label decl
      | throw <| IO.userError s!"{layout}: {decl} of {label} has no place in the site"
    unless href == global ||
        (!sideBySide && some href == Resolve.resolveRenderedExternalDeclHref? state label decl) do
      throw <| IO.userError s!"{layout}: {decl} of {label} leads to {href}, the store to {global}"
    unless inPage href do
      throw <| IO.userError s!"{layout}: {decl} of {label} leads to {href}, missing from the page"
    own := href :: own
  let links := (linksMentioning html decl.toString).filter (fragmentOf? · |>.isSome)
  unless !links.isEmpty && links.all (fun h => h == global || own.contains h) do
    throw <| IO.userError s!"{layout}: the page's links to {decl} are {links}, not {global}"
  let tag := tagWithId html ((fragmentOf? global).getD "")
  let right : Bool := match place with
    | .row label => hasSubstr tag s!"data-lean-decl=\"{decl}\"" &&
        some global == Resolve.resolveRenderedExternalDeclHref? state (Name.mkSimple label) decl
    | .node label => hasSubstr tag s!"data-bp-node=\"«{label}»\""
    | .inline => some global == Resolve.resolveInlineLeanDeclHref? state decl
  unless right do
    throw <| IO.userError s!"{layout}: {decl} leads to the wrong place: <{tag}>"

/- Every resolver of the site leads a declaration attached to a proof to one place of the page: in
the standard layout a proof's panel row; in the side-by-side layout, which shows no row of a
proof's declarations, a row of any node that shows it, else the Lean block of the text that defines
it, else the first node (in the store's key order) whose proof attaches it. -/
#eval show IO Unit from do
  for sideBySide in [false, true] do
    let layout := if sideBySide then "side-by-side" else "standard"
    let (html, state) ← DeclarationSource.withEnabled sideBySide <|
      renderManualDocHtmlStringAndState extension_impls% proofDeclTargetsDoc
    for (decl, labels, sbs, std) in placeCases do
      checkPlace layout html state sideBySide decl labels (if sideBySide then sbs else std)

/--
warning: Label «place.later»: external Lean name 'Verso.VersoBlueprintTests.BlueprintProofLeanRefs.placeLaterInline' could not be resolved in current namespace/open declarations; keeping parsed name
-/
#guard_msgs in
#docs (Manual) proofDeclLaterBlockDoc "A Lean block after the proof" :=
:::::::
:::lemma_ "place.later"
A statement whose proof names a declaration that a later Lean block of the text defines.
:::
:::proof "place.later" (lean := "Verso.VersoBlueprintTests.BlueprintProofLeanRefs.placeLaterInline")
The block comes after this proof.
:::

```Verso.Genre.Manual.InlineLean.lean
theorem placeLaterInline : True := trivial
```

{blueprint_summary}
:::::::

/- The place of a declaration does not depend on the order of the document: a Lean block of the
text that defines a proof's declaration is its place in the side-by-side layout also when it comes
after the proof. -/
#eval show IO Unit from do
  let (html, state) ← DeclarationSource.withEnabled true <|
    renderManualDocHtmlStringAndState extension_impls% proofDeclLaterBlockDoc
  checkPlace "side-by-side" html state true `Verso.VersoBlueprintTests.BlueprintProofLeanRefs.placeLaterInline
    ["place.later"] .inline

/--
error: Label «proof.duplicate» has duplicate external Lean reference 'Nat.add' (canonical 'Nat.add'); previously declared as 'Nat.add'
-/
#guard_msgs in
#docs (Manual) duplicateProofRefs "Duplicate proof refs" :=
:::::::
:::lemma_ "proof.duplicate"
Statement.
:::
:::proof "proof.duplicate" (lean := "Nat.add, Nat.add")
Proof.
:::
:::::::

/--
error: Label «proof.missing»: external Lean name 'No.Such.ProofHelper' could not be resolved in current namespace/open declarations
-/
#guard_msgs in
set_option verso.blueprint.externalCode.strictResolve true in
#docs (Manual) missingProofRef "Missing proof ref" :=
:::::::
:::lemma_ "proof.missing"
Statement.
:::
:::proof "proof.missing" (lean := "No.Such.ProofHelper")
Proof.
:::
:::::::

end Verso.VersoBlueprintTests.BlueprintProofLeanRefs
