/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

import VersoBlueprint.ClaimView
import VersoBlueprint.Stats.Data

/-!
Author-supplied claims: what a project's author says its Lean declarations state.

A Lean check establishes a Lean statement. Whether that statement is the theorem of a manuscript
is a judgement a person makes by reading both; no tool here makes it. A project can still say
which result it means, so a reader knows what to compare: `informal-claims.json` at the project
root names the source and, per Lean declaration, the result's own number in that source, its
informal statement and the people who say they compared the two.

```json
{
  "source": { "title": "…", "authors": "…", "version": "…", "url": "…" },
  "claims": [
    { "declaration": "Project.main_theorem",
      "reference": "Theorem 2.2",
      "statement": "…",
      "attestations": [ { "by": "…", "date": "2026-01-31", "note": "…" } ] }
  ]
}
```

Every field but `declaration` is optional. The file is separate from `comparator.json` on
purpose: that file configures a judgement a tool makes, and nothing in this one is judged. Pages
show the data as text, labelled as the author's, never as a check.
-/

namespace Informal.Stats

open Lean

/-- The file at the project root that holds the author's claims. -/
def claimsFile : String := "informal-claims.json"

/-- The longest text kept from one field of the claims file, in characters. -/
def maxClaimTextLength : Nat := 4000

/-- The most claims, and the most attestations of one claim, kept from the file. -/
def maxClaims : Nat := 2000

private def clean (s : String) : Option String :=
  let t := s.trimAscii.copy
  if t.isEmpty then none
  else if t.length ≤ maxClaimTextLength then some t
  else some ((t.take maxClaimTextLength).copy ++ "…")

private def text? (j : Json) (field : String) : Option String :=
  match j.getObjValAs? String field with
  | .ok value => clean value
  | .error _ => none

private def array (j : Json) (field : String) : Array Json :=
  match j.getObjVal? field with
  | .ok (.arr items) => items.extract 0 maxClaims
  | _ => #[]

private def attestationOf? (j : Json) : Option Attestation := do
  let who ← text? j "by"
  return { who, date := text? j "date", note := text? j "note" }

private def claimOf? (j : Json) : Option Claim := do
  let declaration := ((← text? j "declaration")).toName
  guard !declaration.isAnonymous
  return {
    declaration
    reference := text? j "reference"
    statement := text? j "statement"
    attestations := (array j "attestations").filterMap attestationOf? }

/-- Read the text of a claims file. Entries without a declaration name, and attestations without
a name, are left out; a later claim about a declaration that already has one is left out too. -/
def Claims.parse (text : String) : Except String Claims := do
  let json ← Json.parse text
  let .obj _ := json | throw "expected an object"
  let source : ClaimSource := match json.getObjVal? "source" with
    | .ok j => { title := text? j "title", authors := text? j "authors"
                 version := text? j "version", url := text? j "url" }
    | .error _ => {}
  let claims := (array json "claims").filterMap claimOf? |>.foldl (init := #[]) fun acc c =>
    if acc.any (·.declaration == c.declaration) then acc else acc.push c
  return { source, claims }

/-- The claims in `informal-claims.json` at `root`: none without the file, and a record that
carries the error when the file cannot be read. -/
def Claims.atRoot? (root : System.FilePath) : IO (Option Claims) := do
  let file := root / claimsFile
  unless ← file.pathExists do return none
  try
    match Claims.parse (← IO.FS.readFile file) with
    | .ok claims => return some claims
    | .error e => return some { error := some e }
  catch e =>
    return some { error := some (toString e) }

/-- Whether a link target from the claims file may become a link: a web address. Anything else
is shown as text. -/
def claimLink? (url : String) : Option String :=
  let u := url.trimAscii.copy
  if (u.startsWith "https://" || u.startsWith "http://") &&
      !u.any (fun c => c.isWhitespace || c == '"' || c == '<' || c == '>') then some u
  else none

/-- The claim about `declaration` as pages show it, with the source the file names. -/
def Claims.view? (c : Claims) (declaration : Name) : Option Informal.ClaimView.ClaimView :=
  (c.find? declaration).map fun claim => {
    reference := claim.reference
    sourceTitle := c.source.title
    sourceAuthors := c.source.authors
    sourceVersion := c.source.version
    sourceLink := c.source.url.bind claimLink?
    statement := claim.statement
    attestations := claim.attestations.map fun a => { who := a.who, date := a.date, note := a.note } }

end Informal.Stats
