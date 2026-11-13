/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

import VersoBlueprintTests.Blueprint.Support
import VersoBlueprint.Axioms
import VersoBlueprint.PreviewManifest

namespace Verso.VersoBlueprintTests.BlueprintAxioms

open Lean
open Verso
open Verso.Genre.Manual
open Informal
open Informal.Data
open Verso.VersoBlueprintTests.Blueprint.Support

set_option doc.verso true

private def manualImpls : ExtensionImpls := extension_impls%

/-- A project axiom. -/
axiom projectAxiom : 2 + 2 = 4

/-- A theorem that rests on the project axiom. -/
theorem fromProjectAxiom : 2 + 2 = 4 := projectAxiom

/-- A theorem left unproved. -/
theorem admitted : 1 + 1 = 3 := by sorry

/-- A theorem proved by running compiled code. -/
theorem byNativeDecide : 10 * 10 = 100 := by native_decide

/-- A classical theorem: the standard axioms only. -/
theorem classical (p : Prop) : p ∨ ¬p := Classical.em p

/-- A theorem with no axioms at all. -/
theorem axiomFree : True := trivial

/-- A theorem that collects every class through the declarations it uses. -/
theorem everything : (2 + 2 = 4) ∧ (1 + 1 = 3) ∧ (10 * 10 = 100) ∧ (True ∨ ¬True) :=
  ⟨fromProjectAxiom, admitted, byNativeDecide, classical True⟩

private def ns : Name := `Verso.VersoBlueprintTests.BlueprintAxioms

private def classesOf (decl : Name) : MetaM (Array (String × AxiomClass)) := do
  let axioms ← declarationAxioms (ns ++ decl)
  return axioms.map fun a => ((a.replacePrefix (ns ++ decl) `decl).toString, AxiomClass.ofName a)

-- The four classes, on the pinned toolchain's own axiom names.
/--
info: #[("propext", Informal.Data.AxiomClass.standard), ("Classical.choice", Informal.Data.AxiomClass.standard),
  ("Quot.sound", Informal.Data.AxiomClass.standard), ("sorryAx", Informal.Data.AxiomClass.sorryAx),
  ("decl._native.native_decide.ax_1_1", Informal.Data.AxiomClass.compilerTrusted),
  ("projectAxiom", Informal.Data.AxiomClass.other)]
-/
#guard_msgs in
#eval
  #[``propext, ``Classical.choice, ``Quot.sound, ``sorryAx, `decl._native.native_decide.ax_1_1,
    `projectAxiom].map fun (a : Name) => (a.toString, AxiomClass.ofName a)

/--
info: #[("Verso.VersoBlueprintTests.BlueprintAxioms.projectAxiom", Informal.Data.AxiomClass.other)]
-/
#guard_msgs in
#eval classesOf `fromProjectAxiom

/-- info: #[("sorryAx", Informal.Data.AxiomClass.sorryAx)] -/
#guard_msgs in
#eval classesOf `admitted

/-- info: #[("decl._native.native_decide.ax_1_1", Informal.Data.AxiomClass.compilerTrusted)] -/
#guard_msgs in
#eval classesOf `byNativeDecide

/--
info: #[("propext", Informal.Data.AxiomClass.standard), ("Classical.choice", Informal.Data.AxiomClass.standard),
  ("Quot.sound", Informal.Data.AxiomClass.standard)]
-/
#guard_msgs in
#eval classesOf `classical

/-- info: #[] -/
#guard_msgs in
#eval classesOf `axiomFree

-- The answer for a name is stored and agrees with Lean's own walk; display order puts what
-- limits trust first.
/-- info: true -/
#guard_msgs in
#eval show MetaM Bool from do
  let name := ns ++ `everything
  let first ← declarationAxioms name
  let some cache := declarationAxiomsCache.getState (← getEnv) | return false
  let stored := (← cache.get).find? name
  let again ← declarationAxioms name
  let sorted := sortAxioms first
  return stored == some first && again == first && first == (← collectAxioms name) &&
    first.size == 6 &&
    sorted.map AxiomClass.ofName ==
      #[.sorryAx, .other, .compilerTrusted, .standard, .standard, .standard]

-- A missing name has no axioms and is not stored.
/-- info: true -/
#guard_msgs in
#eval show MetaM Bool from do
  let name := ns ++ `notDeclaredAnywhere
  let none' := (← declarationAxioms name).isEmpty
  let some cache := declarationAxiomsCache.getState (← getEnv) | return false
  return none' && ((← cache.get).find? name).isNone

#docs (Genre.Manual) axiomsDoc "Axioms Doc" :=
:::::::
:::theorem "thm:ax.project" (lean := "Verso.VersoBlueprintTests.BlueprintAxioms.fromProjectAxiom")
Rests on an axiom of the project.
:::

:::theorem "thm:ax.sorry" (lean := "Verso.VersoBlueprintTests.BlueprintAxioms.admitted")
Not proved yet.
:::

:::theorem "thm:ax.native" (lean := "Verso.VersoBlueprintTests.BlueprintAxioms.byNativeDecide")
Checked by compiled code.
:::

:::theorem "thm:ax.standard" (lean := "Verso.VersoBlueprintTests.BlueprintAxioms.classical, Verso.VersoBlueprintTests.BlueprintAxioms.axiomFree")
Classical logic only.
:::

:::theorem "thm:ax.free" (lean := "Verso.VersoBlueprintTests.BlueprintAxioms.axiomFree")
No axioms at all.
:::

:::theorem "thm:ax.inline"
A proof written in the blueprint itself.
:::

```lean "thm:ax.inline"
open Verso.VersoBlueprintTests.BlueprintAxioms in
theorem inlineAxiomUse : 2 + 2 = 4 :=
  projectAxiom
```

:::lemma_ "lem:ax.prose"
No Lean declaration yet.
:::

{blueprint_graph}
:::::::

private def axiomsBlueprint : BlueprintDocument := .capture axiomsDoc.toPart

private def capturedAxioms? (label : String) : Option (Array Name) := do
  let node ← axiomsBlueprint.model.nodes.find? (·.label == Name.mkSimple label)
  return node.externalRefs.flatMap (·.axioms)

-- Capture stores each declaration's axioms on its reference.
/-- info: true -/
#guard_msgs in
#eval
  capturedAxioms? "thm:ax.project" == some #[ns ++ `projectAxiom] &&
    capturedAxioms? "thm:ax.sorry" == some #[``sorryAx] &&
    (capturedAxioms? "thm:ax.native").any (fun axs =>
      axs.size == 1 && axs.all (AxiomClass.ofName · == .compilerTrusted)) &&
    capturedAxioms? "thm:ax.standard" == some #[``propext, ``Classical.choice, ``Quot.sound] &&
    capturedAxioms? "thm:ax.free" == some #[]

end Verso.VersoBlueprintTests.BlueprintAxioms
