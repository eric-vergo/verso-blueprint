/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

import VersoBlueprintTests.ReplayFixtures.Nested.Forged

/-!
An honest root module over a forged child: every constant of `Nested` is sound, and
`Nested.Forged` adds one that no kernel accepts. A replay of `root_true` accepts it, since it
depends on nothing of the child; a replay that is also asked for the child's `ghost` rejects the
build.
-/

namespace ReplayNested

/-- A sound theorem of the root's own. -/
theorem root_true : True := trivial

end ReplayNested
