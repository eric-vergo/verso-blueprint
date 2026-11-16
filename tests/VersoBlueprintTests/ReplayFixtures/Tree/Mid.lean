/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

import VersoBlueprintTests.ReplayFixtures.Tree.Mid.Leaf

/-! The middle module of the honest tree of `ReplayFixtures.Tree`, itself with a child. -/

namespace ReplayTree

/-- Three. -/
def mid : Nat := midLeaf + 1

end ReplayTree
