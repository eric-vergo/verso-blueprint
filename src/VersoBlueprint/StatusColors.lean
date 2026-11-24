/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

/-!
The colours of the Blueprint status vocabulary, as theme tokens.

Each status colour is one CSS custom property with a light and a dark value. The page token
stylesheet declares them next to the other `--bp-color-*` tokens, the dependency graph's CSS
paints nodes with them, and the graph's drawings carry the light values (a drawing needs
concrete colours; the stylesheet then repaints the nodes in the active theme). Pages that show
statuses (the summary, progress bars) use the same properties, so a status reads the same
colour everywhere.

The fill colours follow `Informal.Graph.ProofStatus`, the border colours
`Informal.Graph.StatementStatus`.

A success colour is a statement: green says that a kernel replay accepted the Lean code it is
drawn for (`Informal.Replay`). So every success colour (`successColors`) has two values, the one
it takes where an accepted replay stands behind it and a neutral one, and the property a
stylesheet uses carries the neutral value unless an enclosing element says otherwise
(`replayScopeCss`): `bp_replay_accepted` on a node, a card or a page section switches the
properties inside it to their accepted values, `bp_replay_none` and `bp_replay_rejected` switch
them back. A page that carries no such class shows no green.
-/

namespace Informal.StatusColors

/-- A colour token: a CSS custom property with its value in the light and in the dark theme. -/
structure ColorToken where
  /-- The custom property, including the leading `--`. -/
  name : String
  /-- Value in the light theme (also the value written into the graph's drawings). -/
  light : String
  /-- Value in the dark theme. -/
  dark : String
deriving Inhabited, Repr, BEq

/-- A CSS reference to the token, `var(--name)`. -/
def ColorToken.cssVar (token : ColorToken) : String :=
  s!"var({token.name})"

/-- A CSS reference to the token that falls back to the light value where the token is not
defined (for example in an editor widget without the Blueprint stylesheet). -/
def ColorToken.cssVarOr (token : ColorToken) : String :=
  s!"var({token.name}, {token.light})"

/-- Fill of a theorem-like node whose proof is not ready to be formalized. -/
def notReady : ColorToken :=
  { name := "--bp-color-status-not-ready", light := "#f8fafc", dark := "#262c37" }

/-- Fill of a definition-like node with nothing formalized yet. -/
def definition : ColorToken :=
  { name := "--bp-color-status-definition", light := "#ffffff", dark := "#1b1f27" }

/-- Fill of a node ready to be formalized. -/
def ready : ColorToken :=
  { name := "--bp-color-status-ready", light := "#dbeafe", dark := "#1e3a5f" }

/-- Fill of a node whose Lean code is incomplete. -/
def incomplete : ColorToken :=
  { name := "--bp-color-status-incomplete", light := "#fef3c7", dark := "#42300a" }

/-- A success colour: the property stylesheets use, with its value where a kernel replay accepted
what it is drawn for and its neutral value everywhere else, each in the light and the dark theme. -/
structure SuccessColor where
  /-- The custom property stylesheets use, including the leading `--`. -/
  name : String
  /-- Light and dark value under an accepted replay. -/
  accepted : String × String
  /-- Light and dark value otherwise: what the compiled files report, in a neutral colour. -/
  reported : String × String
deriving Inhabited, Repr, BEq

/-- The property as stylesheets use it. Its own values are the neutral ones. -/
def SuccessColor.token (c : SuccessColor) : ColorToken :=
  { name := c.name, light := c.reported.1, dark := c.reported.2 }

/-- The property that always carries the accepted value. -/
def SuccessColor.acceptedToken (c : SuccessColor) : ColorToken :=
  { name := c.name ++ "-accepted", light := c.accepted.1, dark := c.accepted.2 }

/-- The property that always carries the neutral value. -/
def SuccessColor.reportedToken (c : SuccessColor) : ColorToken :=
  { name := c.name ++ "-reported", light := c.reported.1, dark := c.reported.2 }

/-- Fill of a node whose Lean code has no `sorry` while something it depends on is open. -/
def formalizedColor : SuccessColor :=
  { name := "--bp-color-status-formalized",
    accepted := ("#dcfce7", "#163a24"), reported := ("#e2e8f0", "#334155") }

/-- Fill of a node whose Lean code has no `sorry`, and neither has anything it depends on. -/
def formalizedWithAncestorsColor : SuccessColor :=
  { name := "--bp-color-status-formalized-with-ancestors",
    accepted := ("#166534", "#15803d"), reported := ("#64748b", "#64748b") }

/-- Border of a node whose Lean statement has no `sorry`. -/
def formalizedBorderColor : SuccessColor :=
  { name := "--bp-color-status-formalized-border",
    accepted := ("#16a34a", "#4ade80"), reported := ("#64748b", "#94a3b8") }

/-- Border of a node whose statement is in Mathlib. -/
def mathlibBorderColor : SuccessColor :=
  { name := "--bp-color-status-mathlib-border",
    accepted := ("#14532d", "#bbf7d0"), reported := ("#334155", "#cbd5e1") }

/-- The success colours of the general page tokens (`Informal.Commands.blueprintLightTokensCss`
declares these properties with their neutral values). -/
def pageSuccessColors : List SuccessColor := [
  { name := "--bp-color-accent-success",
    accepted := ("#16a34a", "#4ade80"), reported := ("#64748b", "#94a3b8") },
  { name := "--bp-color-status-success-text",
    accepted := ("#166534", "#86efac"), reported := ("#475569", "#cbd5e1") },
  { name := "--bp-color-tint-success",
    accepted := ("rgba(22, 101, 52, 0.08)", "rgba(74, 222, 128, 0.14)"),
    reported := ("rgba(100, 116, 139, 0.1)", "rgba(148, 163, 184, 0.14)") },
  { name := "--bp-color-tint-success-border",
    accepted := ("rgba(22, 101, 52, 0.18)", "rgba(74, 222, 128, 0.3)"),
    reported := ("rgba(100, 116, 139, 0.25)", "rgba(148, 163, 184, 0.3)") },
  { name := "--bp-color-slide-ok-text",
    accepted := ("#166534", "#86efac"), reported := ("#475569", "#cbd5e1") },
  { name := "--bp-color-slide-ok-icon",
    accepted := ("#16a34a", "#4ade80"), reported := ("#64748b", "#94a3b8") },
  { name := "--bp-color-slide-ok-bg",
    accepted := ("rgba(22, 163, 74, 0.08)", "rgba(74, 222, 128, 0.14)"),
    reported := ("rgba(100, 116, 139, 0.1)", "rgba(148, 163, 184, 0.14)") },
  { name := "--bp-color-slide-ok-border",
    accepted := ("rgba(22, 163, 74, 0.26)", "rgba(74, 222, 128, 0.3)"),
    reported := ("rgba(100, 116, 139, 0.25)", "rgba(148, 163, 184, 0.3)") }
]

/-- Every success colour: the status ones, then the general page ones. -/
def successColors : List SuccessColor :=
  [formalizedColor, formalizedWithAncestorsColor, formalizedBorderColor, mathlibBorderColor] ++
    pageSuccessColors

/-- Fill of a node formalized locally while some of its ancestors are still open: neutral unless
an accepted replay stands behind the node (`formalizedColor`). -/
def formalized : ColorToken := formalizedColor.token

/-- Fill of a node formalized together with all of its ancestors: neutral unless an accepted
replay stands behind the node and what it depends on (`formalizedWithAncestorsColor`). -/
def formalizedWithAncestors : ColorToken := formalizedWithAncestorsColor.token

/-- Label colour on every status fill except `formalizedWithAncestors`. -/
def fillText : ColorToken :=
  { name := "--bp-color-status-fill-text", light := "#111827", dark := "#e5e7eb" }

/-- Label colour on the `formalizedWithAncestors` fill. -/
def formalizedWithAncestorsText : ColorToken :=
  { name := "--bp-color-status-formalized-with-ancestors-text", light := "#ffffff",
    dark := "#ffffff" }

/-- Border of a node whose statement is blocked. -/
def blockedBorder : ColorToken :=
  { name := "--bp-color-status-blocked-border", light := "#f59e0b", dark := "#fbbf24" }

/-- Border of a node whose statement is ready to be formalized. -/
def readyBorder : ColorToken :=
  { name := "--bp-color-status-ready-border", light := "#2563eb", dark := "#60a5fa" }

/-- Border of a node whose statement is formalized (`formalizedBorderColor`). -/
def formalizedBorder : ColorToken := formalizedBorderColor.token

/-- Border of a node whose statement is in Mathlib (`mathlibBorderColor`). -/
def mathlibBorder : ColorToken := mathlibBorderColor.token

/-- Fill of a placeholder node for a reference that names no Blueprint entry. -/
def unresolved : ColorToken :=
  { name := "--bp-color-status-unresolved", light := "#fee2e2", dark := "#450a0a" }

/-- Fill of a node whose Lean source is not known to be the text that was compiled: neutral, since
nothing is shown as known of it. -/
def sourceChanged : ColorToken :=
  { name := "--bp-color-status-source-changed", light := "#e7e5e4", dark := "#3b3734" }

/-- Border of an unresolved-reference node. -/
def unresolvedBorder : ColorToken :=
  { name := "--bp-color-status-unresolved-border", light := "#b91c1c", dark := "#f87171" }

/-- Label colour of an unresolved-reference node. -/
def unresolvedText : ColorToken :=
  { name := "--bp-color-status-unresolved-text", light := "#7f1d1d", dark := "#fecaca" }

/-- The class of an element behind which an accepted kernel replay stands: the success colours
inside it take their accepted values. -/
def replayAcceptedClass : String := "bp_replay_accepted"

/-- The class of an element whose build the kernel checker rejected. -/
def replayRejectedClass : String := "bp_replay_rejected"

/-- The class of an element with no verdict of a kernel replay behind it. -/
def replayNoneClass : String := "bp_replay_none"

/-- The attribute that says the same of an element whose classes are not the generator's to
set: its value is `accepted`, `rejected` or `none`. -/
def replayScopeAttr : String := "data-bp-replay-scope"

/-- Every status colour token, in the order the stylesheets declare them: the status colours,
then each success colour's accepted and neutral value under names of their own. -/
def all : List ColorToken := [
  notReady, definition, ready, incomplete, formalized, formalizedWithAncestors,
  fillText, formalizedWithAncestorsText,
  blockedBorder, readyBorder, formalizedBorder, mathlibBorder,
  unresolved, unresolvedBorder, unresolvedText, sourceChanged
] ++ successColors.flatMap fun c => [c.acceptedToken, c.reportedToken]

/-- The rules that give the success colours their value by the kernel replay behind an element.
Outside every such element a success colour keeps the neutral value the token stylesheet
declares; an element can only be told green by its own class or an enclosing one. -/
def replayScopeCss : String :=
  let block (selector : String) (value : SuccessColor → ColorToken) : String :=
    selector ++ " {\n" ++
      String.join (successColors.map fun c => s!"  {c.name}: {(value c).cssVar};\n") ++ "}\n"
  "\n/* Success colours follow the kernel replay behind an element. */\n" ++
    block s!".{replayAcceptedClass},\n[{replayScopeAttr}=\"accepted\"]" (·.acceptedToken) ++
    block (s!".{replayNoneClass},\n.{replayRejectedClass},\n" ++
      s!"[{replayScopeAttr}]:not([{replayScopeAttr}=\"accepted\"])") (·.reportedToken)

end Informal.StatusColors
