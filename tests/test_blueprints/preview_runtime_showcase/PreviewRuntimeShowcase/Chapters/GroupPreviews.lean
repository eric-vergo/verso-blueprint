import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Group Previews" =>

:::group "preview_group"
Preview group title.
:::

:::definition "group_target" (parent := "preview_group")
Target statement in a declared group.
:::

:::lemma_ "group_peer_one" (parent := "preview_group")
First peer in the same group.
:::

:::lemma_ "group_peer_two" (parent := "preview_group")
Second peer in the same group.
:::

:::lemma_ "group_user"
Statement depends on {uses "group_target"}[].
:::

:::theorem "ungrouped_theorem"
Standalone theorem without a parent group.
:::

# Groups of $`n + 1` Statements

A section whose title holds a formula.

# Groups Named by {Verso.Genre.Manual.InlineLean.lean}`Nat.succ 0`

A section whose title holds Lean code.
