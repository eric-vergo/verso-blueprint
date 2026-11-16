/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

import VersoBlueprintTests.ReplayFixtures.Tree.Leaf
import VersoBlueprintTests.ReplayFixtures.Tree.Mid

/-!
The root of a tree of honest modules: `Tree` has the children `Tree.Leaf` and `Tree.Mid`, and
`Tree.Mid` has the child `Tree.Mid.Leaf`. `leanchecker` replays every module whose name starts
with its argument, so the root and the middle module cannot be named alone on the directory of
compiled modules; `BlueprintKernelReplay` tests that each module is still replayed exactly once.
-/

namespace ReplayTree

/-- The root uses both children. -/
theorem root_sum : leaf + mid = 5 := rfl

end ReplayTree
