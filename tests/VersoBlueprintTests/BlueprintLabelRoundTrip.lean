/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/
import VersoBlueprintTests.Blueprint.Support

/-!
Labels are arbitrary strings, so a label need not be writable as a Lean name: `»` cannot appear
inside `«…»`. The render model writes every label so that it reads back as the same label, and a
model that does not read back fails with an error that names the text, not a panic.
-/

open Lean Verso Informal
open Verso.Genre
open Verso.VersoBlueprintTests.Blueprint.Support

namespace Verso.VersoBlueprintTests.BlueprintLabelRoundTrip

/-- Labels that `Name.toString` cannot write so that they read back, and some that it can. -/
def hardLabels : List String :=
  ["a»b", "»", "«»", "»»", "x«y»z", "a.b»", "tab\there", "bell\x07", "nul\x00",
   "plain", "thm:main", "a.b", "", "[anonymous]", "«quoted»", "1", "é»ü"]

/-- `label` read back from the JSON the render model writes for it. -/
def roundTrip (label : Data.Label) : Except String Data.Label :=
  Json.parse (toJson label).compress >>= fromJson?

#eval show IO Unit from do
  for s in hardLabels do
    let label : Data.Label := Name.mkSimple s
    match roundTrip label with
    | .ok back =>
      unless back == label do
        throw <| IO.userError s!"label {s.quote} read back as {repr (back : Name)}"
    | .error e => throw <| IO.userError s!"label {s.quote} did not read back: {e}"
  -- names with several components and numeric components, as `Name` builds them
  for label in [(`a.b : Name), Name.mkNum `x 3, Name.mkStr (Name.mkNum .anonymous 3) "y»",
      Name.mkStr (Name.mkStr .anonymous "p»") "q", .anonymous] do
    match roundTrip label with
    | .ok back =>
      unless back == label do throw <| IO.userError s!"label {repr label} read back as {repr back}"
    | .error e => throw <| IO.userError s!"label {repr label} did not read back: {e}"

-- Ordinary labels are written exactly as before: the string `Name.toString` gives.
#eval show IO Unit from do
  for s in ["plain", "thm:main", "a.b", "1", "tab\there"] do
    let label : Data.Label := Name.mkSimple s
    unless toJson label == Json.str (label : Name).toString do
      throw <| IO.userError s!"label {s.quote} is written differently: {(toJson label).compress}"

-- A string that is no label's encoding is refused with an error naming it.
#eval show IO Unit from do
  for bad in ["«a", "«a»»", "a»b»", "«a»b»"] do
    match (fromJson? (Json.str bad) : Except String Data.Label) with
    | .ok l => throw <| IO.userError s!"{bad.quote} was read as the label {repr (l : Name)}"
    | .error e =>
      unless hasSubstr e bad do
        throw <| IO.userError s!"the error for {bad.quote} does not name it: {e}"

-- A serialized model that does not read back gives an error naming the text, not a panic.
#eval show IO Unit from do
  match RenderModel.fromJsonString? "[[{\"label\": \"«a\"}], {}, {}, {}]" with
  | .ok _ => throw <| IO.userError "a model with the label text «a was read"
  | .error e =>
    unless hasSubstr e "«a" do
      throw <| IO.userError s!"the error for an unreadable model does not name the text: {e}"

#docs (Manual) hardLabelDocument "Hard labels" :=
:::::::
:::theorem "a»b"
A theorem whose label holds a closing guillemet.
:::
:::lemma_ "«»"
A lemma whose label is a pair of guillemets.
:::
:::definition "ok_label"
An ordinary label.
:::
{blueprint_summary}
:::::::

def hardLabelBlueprint : BlueprintDocument := .capture hardLabelDocument.toPart

-- The captured model reads back with every label, and the page renders.
#eval show IO Unit from do
  let labels := hardLabelBlueprint.model.nodes.map fun node => (node.label : Name)
  for s in ["a»b", "«»", "ok_label"] do
    unless labels.contains (Name.mkSimple s) do
      throw <| IO.userError s!"the render model lost the label {s.quote}: {repr labels}"
  let html ← renderManualDocHtmlString extension_impls% hardLabelDocument
    (model := hardLabelBlueprint.model)
  unless hasSubstr html "A theorem whose label holds a closing guillemet." do
    throw <| IO.userError "the page with a hard label did not render"

end Verso.VersoBlueprintTests.BlueprintLabelRoundTrip
