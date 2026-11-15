/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

/-!
The colours of the Blueprint status vocabulary, as theme tokens.

Each status colour is one CSS custom property with a light and a dark value. The page token
stylesheet declares them next to the other `--bp-color-*` tokens, the dependency graph's CSS
paints nodes with them, and the graph's DOT source carries the light values (Graphviz needs
concrete colours; the stylesheet then repaints the nodes in the active theme). Pages that show
statuses (the summary, progress bars) use the same properties, so a status reads the same
colour everywhere.

The fill colours follow `Informal.Graph.ProofStatus`, the border colours
`Informal.Graph.StatementStatus`.
-/

namespace Informal.StatusColors

/-- A colour token: a CSS custom property with its value in the light and in the dark theme. -/
structure ColorToken where
  /-- The custom property, including the leading `--`. -/
  name : String
  /-- Value in the light theme (also the value written into Graphviz DOT). -/
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

/-- Fill of a node formalized locally while some of its ancestors are still open. -/
def formalized : ColorToken :=
  { name := "--bp-color-status-formalized", light := "#dcfce7", dark := "#163a24" }

/-- Fill of a node formalized together with all of its ancestors. -/
def formalizedWithAncestors : ColorToken :=
  { name := "--bp-color-status-formalized-with-ancestors", light := "#166534", dark := "#15803d" }

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

/-- Border of a node whose statement is formalized. -/
def formalizedBorder : ColorToken :=
  { name := "--bp-color-status-formalized-border", light := "#16a34a", dark := "#4ade80" }

/-- Border of a node whose statement is in Mathlib. -/
def mathlibBorder : ColorToken :=
  { name := "--bp-color-status-mathlib-border", light := "#14532d", dark := "#bbf7d0" }

/-- Fill of a placeholder node for a reference that names no Blueprint entry. -/
def unresolved : ColorToken :=
  { name := "--bp-color-status-unresolved", light := "#fee2e2", dark := "#450a0a" }

/-- Border of an unresolved-reference node. -/
def unresolvedBorder : ColorToken :=
  { name := "--bp-color-status-unresolved-border", light := "#b91c1c", dark := "#f87171" }

/-- Label colour of an unresolved-reference node. -/
def unresolvedText : ColorToken :=
  { name := "--bp-color-status-unresolved-text", light := "#7f1d1d", dark := "#fecaca" }

/-- Every status colour token, in the order the stylesheets declare them. -/
def all : List ColorToken := [
  notReady, definition, ready, incomplete, formalized, formalizedWithAncestors,
  fillText, formalizedWithAncestorsText,
  blockedBorder, readyBorder, formalizedBorder, mathlibBorder,
  unresolved, unresolvedBorder, unresolvedText
]

end Informal.StatusColors
