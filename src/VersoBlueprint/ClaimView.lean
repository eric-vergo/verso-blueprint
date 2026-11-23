/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

import Verso.Output.Html
import VersoBlueprint.Meaning

/-!
An author's claim about a Lean declaration, as pages show it.

The claim is data the project's author supplies (`Informal.Stats.Claims`): which result of which
source the declaration is meant to state, the informal statement, and the people who say they
compared the two. `ClaimView` is that data as plain text, so the Project Stats page and the node
view render it the same way. Every string is written as text; a source address becomes a link
only when the caller found it to be a web address.

The block always says whose words these are ("Author's claim"), says that no tool compared them
with the Lean statement, and shows an attestation as a person's statement with their name and
date, never with a check mark.
-/

namespace Informal.ClaimView

open Verso.Output

/-- A person's statement that they compared the claim with the Lean statement. -/
structure Attestation where
  who : String
  date : Option String := none
  note : Option String := none
deriving Inhabited, Repr, BEq

/-- A claim, ready to render. -/
structure ClaimView where
  /-- The result's own name in the source ("Theorem 2.2"). -/
  reference : Option String := none
  sourceTitle : Option String := none
  sourceAuthors : Option String := none
  sourceVersion : Option String := none
  /-- A web address of the source, already checked to be one. -/
  sourceLink : Option String := none
  /-- The informal statement. -/
  statement : Option String := none
  attestations : Array Attestation := #[]
deriving Inhabited, Repr, BEq

private def txt (s : String) : Html := .text s

private def el (tag cls : String) (content : Html) (attrs : Array (String × String) := #[]) :
    Html :=
  .element tag (#[("class", cls)] ++ attrs) content

/-- What the claim refers to, in words: "Theorem 2.2 of Title (authors; version)". -/
def ClaimView.citation (c : ClaimView) : String :=
  let detail := "; ".intercalate (c.sourceAuthors.toList ++ c.sourceVersion.toList)
  let source := match c.sourceTitle with
    | some t => if detail.isEmpty then t else s!"{t} ({detail})"
    | none => detail
  match c.reference, source.isEmpty with
  | some r, false => s!"{r} of {source}"
  | some r, true => r
  | none, false => source
  | none, true => ""

/-- The line an attestation is shown as: who, when, what they say, and that it is a person's
statement. -/
def Attestation.text (a : Attestation) : String :=
  let date := (a.date.map (s!", {·}")).getD ""
  let note := (a.note.map (s!": {·}")).getD ""
  s!"Attested by {a.who}{date}{note}"

/-- The sentence that closes a list of attestations. -/
def attestationNote : String := "An attestation is a person's statement, not a check."

/-- The sentence under a claim nobody has attested. -/
def noAttestationNote : String := "Nobody has recorded comparing it with the Lean statement."

/-- The block. `meaningHref?` is the address of the explanation of the marks, when the site has
one. -/
def ClaimView.render (c : ClaimView) (meaningHref? : Option String := none) : Html :=
  let citation := c.citation
  let cite : Html :=
    if citation.isEmpty then .empty
    else match c.sourceLink with
      | some href => .element "a" #[("href", href), ("class", "bp_claim_cite")] (txt citation)
      | none => el "span" "bp_claim_cite" (txt citation)
  let meaning : Html := match meaningHref? with
    | some href => .seq #[txt " ", .element "a" #[("href", href), ("class", "bp_meaning_link")]
        (txt Informal.Meaning.linkText)]
    | none => .empty
  let attestations : Html :=
    if c.attestations.isEmpty then
      el "p" "bp_claim_note" (.seq #[txt s!"{Informal.Meaning.uncheckedNote} {noAttestationNote}",
        meaning])
    else .seq #[
      el "ul" "bp_claim_attestations" (.seq <| c.attestations.map fun a =>
        el "li" "bp_claim_attestation" (txt a.text) #[("data-bp-attested-by", a.who)]),
      el "p" "bp_claim_note" (.seq #[txt s!"{Informal.Meaning.uncheckedNote} {attestationNote}",
        meaning])]
  el "div" "bp_claim" (.seq #[
    el "p" "bp_claim_head" (.seq #[el "span" "bp_claim_caption" (txt "Author's claim"),
      if citation.isEmpty then .empty else txt " ", cite]),
    match c.statement with
    | some s => el "p" "bp_claim_statement" (txt s)
    | none => .empty,
    attestations])
    #[("data-bp-claim", c.reference.getD ""),
      ("data-bp-attestations", toString c.attestations.size)]

end Informal.ClaimView
