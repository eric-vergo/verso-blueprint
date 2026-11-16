/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

import Lean

/-!
A child module with a constant added without the kernel (`debug.skipKernelTC`): `ghost` claims
`False` with the value `True.intro`. Only a kernel replay of this module finds it.
-/

namespace ReplayNested

open Lean Elab Command in
set_option debug.skipKernelTC true in
run_cmd liftCoreM do
  addDecl <| .thmDecl {
    name := `ReplayNested.ghost, levelParams := [], type := mkConst ``False
    value := mkConst ``True.intro }

end ReplayNested
