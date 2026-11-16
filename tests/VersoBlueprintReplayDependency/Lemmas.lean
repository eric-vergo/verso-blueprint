/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

import Lean

/-!
A module that stands for a dependency of a project in the tests of the kernel replay
(`BlueprintKernelReplay` puts its compiled file in a directory of its own). It has a sound lemma
and one added without the kernel (`debug.skipKernelTC`): `helper` claims `False` with the value
`True.intro`.
-/

namespace ReplayDependency

/-- A sound lemma. -/
theorem fine : True := trivial

open Lean Elab Command in
set_option debug.skipKernelTC true in
run_cmd liftCoreM do
  addDecl <| .thmDecl {
    name := `ReplayDependency.helper, levelParams := [], type := mkConst ``False
    value := mkConst ``True.intro }

end ReplayDependency
