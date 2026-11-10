/- 
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Emilio J. Gallego Arias
-/

import Lean.Data.Options

namespace Informal.Commands

open Lean

register_option verso.blueprint.debug.commands : Bool := {
  defValue := false
  descr := "Emit debug info logs for blueprint graph, summary, and bibliography commands"
}

def blueprintLightTokensCss : String := r##"
:root {
  --bp-color-surface: #ffffff;
  --bp-color-surface-muted: #f8fafc;
  --bp-color-surface-subtle: #f9fafb;
  --bp-color-surface-modern: #f8fbff;
  --bp-color-surface-warn: #fff7ed;
  --bp-color-surface-warn-soft: #ffedd5;
  --bp-color-surface-note: #fffbeb;
  --bp-color-border: #cbd5e1;
  --bp-color-border-soft: #e2e8f0;
  --bp-color-border-muted: #d1d5db;
  --bp-color-border-panel: #dbe4ee;
  --bp-color-border-strong: #94a3b8;
  --bp-color-text-strong: #0f172a;
  --bp-color-text: #111827;
  --bp-color-text-muted: #334155;
  --bp-color-text-subtle: #475569;
  --bp-color-text-faint: #64748b;
  --bp-color-accent-success: #16a34a;
  --bp-color-accent-warning: #ca8a04;
  --bp-color-accent-danger: #dc2626;
  --bp-color-accent-info: #7c3aed;
  --bp-color-status-success-text: #166534;
  --bp-color-status-warning-text: #a16207;
  --bp-color-status-warning-strong: #9a3412;
  --bp-color-status-warning-border: #fdba74;
  --bp-color-status-warning-border-soft: #fed7aa;
  --bp-color-status-error-text: #b91c1c;
  --bp-color-status-error-strong: #991b1b;
  --bp-color-status-error-border-soft: #fecaca;
  --bp-color-status-note-border: #fcd34d;
  --bp-color-status-note-text: #92400e;
  --bp-color-focus-border: #93c5fd;
  --bp-color-focus-surface: #eff6ff;
  --bp-color-focus-ring: rgba(59, 130, 246, 0.12);
  --bp-color-selection: rgba(59, 130, 246, 0.18);
  --bp-color-selection-ring: rgba(59, 130, 246, 0.22);
  --bp-color-selection-surface-strong: rgba(59, 130, 246, 0.28);
  --bp-color-selection-surface-soft: rgba(59, 130, 246, 0.14);
  --bp-color-selection-surface-faint: rgba(59, 130, 246, 0.1);
  --bp-color-selection-shadow-strong: rgba(59, 130, 246, 0.3);
  --bp-color-selection-shadow-soft: rgba(59, 130, 246, 0.24);
  --bp-color-selection-shadow-faint: rgba(59, 130, 246, 0.16);
  --bp-color-target-ring: rgba(37, 99, 235, 0.22);
  --bp-color-target-surface: rgba(37, 99, 235, 0.14);
  --bp-color-target-ring-strong: rgba(37, 99, 235, 0.28);
  --bp-color-modern-border: #d6deea;
  --bp-color-modern-surface-alt: #f5f9ff;
  --bp-color-modern-caption: #e0ecff;
  --bp-color-bold-surface-glow-1: rgba(251, 191, 36, 0.2);
  --bp-color-bold-surface-glow-2: rgba(16, 185, 129, 0.2);
  --bp-color-bold-link: #7c2d12;
  --bp-color-bold-label: #f59e0b;
  --bp-color-biblio-border: #d6ccff;
  --bp-color-biblio-surface: #faf7ff;
  --bp-color-biblio-border-soft: #e9ddff;
  --bp-color-biblio-surface-soft: #fdfbff;
  --bp-color-biblio-link: #4c1d95;
  --bp-color-tint-success: rgba(22, 101, 52, 0.08);
  --bp-color-tint-success-border: rgba(22, 101, 52, 0.18);
  --bp-color-tint-warning: rgba(161, 98, 7, 0.09);
  --bp-color-tint-warning-border: rgba(161, 98, 7, 0.2);
  --bp-color-tint-error: rgba(185, 28, 28, 0.08);
  --bp-color-tint-error-border: rgba(185, 28, 28, 0.18);
  --bp-color-tint-info: rgba(124, 58, 237, 0.08);
  --bp-color-tint-info-border: rgba(124, 58, 237, 0.18);
  --bp-color-tint-danger: rgba(220, 38, 38, 0.08);
  --bp-color-overlay-surface: rgba(255, 255, 255, 0.98);
  --bp-color-overlay-surface-soft: rgba(255, 255, 255, 0.9);
  --bp-color-ink-hairline: rgba(15, 23, 42, 0.14);
  --bp-color-ink-rule: rgba(15, 23, 42, 0.2);
  --bp-color-ink-divider: rgba(15, 23, 42, 0.35);
  --bp-color-badge-highlight: rgba(255, 255, 255, 0.35);
  --bp-color-relation-statement-text: #1d4ed8;
  --bp-color-relation-proof-text: #047857;
  --bp-color-relation-auto-text: #6d28d9;
  --bp-color-relation-auto-prefix: #7c3aed;
  --bp-color-relation-aux-text: #92400e;
  --bp-color-relation-aux-prefix: #b45309;
  --bp-color-relation-tech-text: #4338ca;
  --bp-color-relation-tech-prefix: #4f46e5;
  --bp-color-kind-rule: #000000;
  --bp-color-slide-accent: #075985;
  --bp-color-slide-link: #0e7490;
  --bp-color-slide-math: #164e63;
  --bp-color-slide-ok-text: #166534;
  --bp-color-slide-ok-icon: #16a34a;
  --bp-color-slide-ok-bg: rgba(22, 163, 74, 0.08);
  --bp-color-slide-ok-border: rgba(22, 163, 74, 0.26);
  --bp-color-slide-code-keyword: #8839a0;
  --bp-color-slide-code-const: #1a5fb4;
  --bp-color-slide-code-var: #1a7a6a;
  --bp-color-rust-keyword: #7c2d12;
  --bp-color-rust-type: #0f766e;
  --bp-color-rust-number: #166534;
  --bp-color-rust-string: #9f1239;
  --bp-color-rust-comment: #64748b;
  --bp-color-graph-bg: #ffffff;
  --bp-color-graph-edge: #6b7280;
  --bp-color-graph-cluster: #cbd5e1;
  --bp-color-graph-label: #000000;
  --bp-radius-sm: 0.35rem;
  --bp-radius-md: 0.45rem;
  --bp-radius-lg: 0.5rem;
  --bp-radius-xl: 0.55rem;
  --bp-radius-2xl: 0.7rem;
  --bp-radius-3xl: 0.85rem;
  --bp-radius-pill: 999px;
  --bp-shadow-sm: 0 4px 14px rgba(15, 23, 42, 0.1);
  --bp-shadow-md: 0 10px 24px rgba(15, 23, 42, 0.16);
  --bp-shadow-lg: 0 12px 28px rgba(15, 23, 42, 0.18);
  --bp-shadow-modern: 0 6px 18px rgba(15, 23, 42, 0.08);
  --bp-shadow-xs: 0 1px 2px rgba(15, 23, 42, 0.06);
  --bp-shadow-inset: inset 0 1px 1px rgba(15, 23, 42, 0.08);
  --bp-shadow-popover: 0 8px 20px rgba(15, 23, 42, 0.15);
  --bp-shadow-icon: 0 1px 2px rgba(15, 23, 42, 0.18);
  --bp-shadow-step: 0 3px 0 rgba(15, 23, 42, 0.14);
  --bp-shadow-slide-card: 0 10px 24px rgba(15, 23, 42, 0.12);
  --bp-shadow-slide-panel: 0 18px 42px rgba(15, 23, 42, 0.2);
  --bp-shadow-bold: 0 7px 0 var(--bp-color-text-strong);
  --bp-shadow-bold-lg: 0 9px 0 var(--bp-color-text-strong);
}
"##

/-- Dark values for the `--bp-*` tokens above plus the Verso base variables, as `(name, value)`
pairs. This single list renders both dark triggers (`blueprintDarkTokensCss`); radii are
theme-independent and have no dark value. `--bp-color-link` and the `--bp-code-*` tokens have no
light value here (consumers fall back to their own default). -/
def darkTokens : List (String × String) := [
  ("color-scheme", "dark"),
  ("--bp-color-surface", "#1b1f27"),
  ("--bp-color-surface-muted", "#20252e"),
  ("--bp-color-surface-subtle", "#1e232b"),
  ("--bp-color-surface-modern", "#1c2230"),
  ("--bp-color-surface-warn", "#2a2118"),
  ("--bp-color-surface-warn-soft", "#3a2a1a"),
  ("--bp-color-surface-note", "#2a2615"),
  ("--bp-color-border", "#334155"),
  ("--bp-color-border-soft", "#2a3140"),
  ("--bp-color-border-muted", "#3b4252"),
  ("--bp-color-border-panel", "#2e3646"),
  ("--bp-color-border-strong", "#64748b"),
  ("--bp-color-text-strong", "#f8fafc"),
  ("--bp-color-text", "#e5e7eb"),
  ("--bp-color-text-muted", "#cbd5e1"),
  ("--bp-color-text-subtle", "#a3b1c6"),
  ("--bp-color-text-faint", "#8b9ab0"),
  ("--bp-color-accent-success", "#4ade80"),
  ("--bp-color-accent-warning", "#facc15"),
  ("--bp-color-accent-danger", "#f87171"),
  ("--bp-color-accent-info", "#a78bfa"),
  ("--bp-color-status-success-text", "#86efac"),
  ("--bp-color-status-warning-text", "#fde047"),
  ("--bp-color-status-warning-strong", "#fdba74"),
  ("--bp-color-status-warning-border", "#b45309"),
  ("--bp-color-status-warning-border-soft", "#7c4a1a"),
  ("--bp-color-status-error-text", "#fca5a5"),
  ("--bp-color-status-error-strong", "#fecaca"),
  ("--bp-color-status-error-border-soft", "#7f1d1d"),
  ("--bp-color-status-note-border", "#b45309"),
  ("--bp-color-status-note-text", "#fcd34d"),
  ("--bp-color-focus-border", "#60a5fa"),
  ("--bp-color-focus-surface", "#1a2540"),
  ("--bp-color-focus-ring", "rgba(96, 165, 250, 0.25)"),
  ("--bp-color-selection", "rgba(96, 165, 250, 0.28)"),
  ("--bp-color-selection-ring", "rgba(96, 165, 250, 0.34)"),
  ("--bp-color-selection-surface-strong", "rgba(96, 165, 250, 0.4)"),
  ("--bp-color-selection-surface-soft", "rgba(96, 165, 250, 0.22)"),
  ("--bp-color-selection-surface-faint", "rgba(96, 165, 250, 0.16)"),
  ("--bp-color-selection-shadow-strong", "rgba(96, 165, 250, 0.45)"),
  ("--bp-color-selection-shadow-soft", "rgba(96, 165, 250, 0.36)"),
  ("--bp-color-selection-shadow-faint", "rgba(96, 165, 250, 0.26)"),
  ("--bp-color-target-ring", "rgba(96, 165, 250, 0.34)"),
  ("--bp-color-target-surface", "rgba(96, 165, 250, 0.22)"),
  ("--bp-color-target-ring-strong", "rgba(96, 165, 250, 0.42)"),
  ("--bp-color-modern-border", "#2b3547"),
  ("--bp-color-modern-surface-alt", "#1d2433"),
  ("--bp-color-modern-caption", "#1e3a5f"),
  ("--bp-color-bold-surface-glow-1", "rgba(250, 204, 21, 0.12)"),
  ("--bp-color-bold-surface-glow-2", "rgba(52, 211, 153, 0.12)"),
  ("--bp-color-bold-link", "#fdba74"),
  ("--bp-color-bold-label", "#f59e0b"),
  ("--bp-color-biblio-border", "#4c3d8f"),
  ("--bp-color-biblio-surface", "#211c33"),
  ("--bp-color-biblio-border-soft", "#3a2f66"),
  ("--bp-color-biblio-surface-soft", "#1f1b2e"),
  ("--bp-color-biblio-link", "#c4b5fd"),
  ("--bp-color-tint-success", "rgba(74, 222, 128, 0.14)"),
  ("--bp-color-tint-success-border", "rgba(74, 222, 128, 0.3)"),
  ("--bp-color-tint-warning", "rgba(250, 204, 21, 0.14)"),
  ("--bp-color-tint-warning-border", "rgba(250, 204, 21, 0.3)"),
  ("--bp-color-tint-error", "rgba(248, 113, 113, 0.14)"),
  ("--bp-color-tint-error-border", "rgba(248, 113, 113, 0.3)"),
  ("--bp-color-tint-info", "rgba(167, 139, 250, 0.14)"),
  ("--bp-color-tint-info-border", "rgba(167, 139, 250, 0.3)"),
  ("--bp-color-tint-danger", "rgba(248, 113, 113, 0.14)"),
  ("--bp-color-overlay-surface", "rgba(27, 31, 39, 0.98)"),
  ("--bp-color-overlay-surface-soft", "rgba(27, 31, 39, 0.9)"),
  ("--bp-color-ink-hairline", "rgba(255, 255, 255, 0.18)"),
  ("--bp-color-ink-rule", "rgba(255, 255, 255, 0.2)"),
  ("--bp-color-ink-divider", "rgba(0, 0, 0, 0.5)"),
  ("--bp-color-badge-highlight", "rgba(255, 255, 255, 0.08)"),
  ("--bp-color-relation-statement-text", "#93c5fd"),
  ("--bp-color-relation-proof-text", "#6ee7b7"),
  ("--bp-color-relation-auto-text", "#c4b5fd"),
  ("--bp-color-relation-auto-prefix", "#a78bfa"),
  ("--bp-color-relation-aux-text", "#fcd34d"),
  ("--bp-color-relation-aux-prefix", "#f59e0b"),
  ("--bp-color-relation-tech-text", "#a5b4fc"),
  ("--bp-color-relation-tech-prefix", "#818cf8"),
  ("--bp-color-kind-rule", "#94a3b8"),
  ("--bp-color-slide-accent", "#7dd3fc"),
  ("--bp-color-slide-link", "#67e8f9"),
  ("--bp-color-slide-math", "#a5f3fc"),
  ("--bp-color-slide-ok-text", "#86efac"),
  ("--bp-color-slide-ok-icon", "#4ade80"),
  ("--bp-color-slide-ok-bg", "rgba(74, 222, 128, 0.14)"),
  ("--bp-color-slide-ok-border", "rgba(74, 222, 128, 0.3)"),
  ("--bp-color-slide-code-keyword", "#c792ea"),
  ("--bp-color-slide-code-const", "#7cb7ff"),
  ("--bp-color-slide-code-var", "#5eead4"),
  ("--bp-color-rust-keyword", "#fdba74"),
  ("--bp-color-rust-type", "#5eead4"),
  ("--bp-color-rust-number", "#86efac"),
  ("--bp-color-rust-string", "#fda4af"),
  ("--bp-color-rust-comment", "#8b9ab0"),
  ("--bp-color-graph-bg", "#1b1f27"),
  ("--bp-color-graph-edge", "#94a3b8"),
  ("--bp-color-graph-cluster", "#475569"),
  ("--bp-color-graph-label", "#e5e7eb"),
  ("--bp-shadow-sm", "0 4px 14px rgba(0, 0, 0, 0.45)"),
  ("--bp-shadow-md", "0 10px 24px rgba(0, 0, 0, 0.45)"),
  ("--bp-shadow-lg", "0 12px 28px rgba(0, 0, 0, 0.45)"),
  ("--bp-shadow-modern", "0 6px 18px rgba(0, 0, 0, 0.4)"),
  ("--bp-shadow-bold", "0 7px 0 var(--bp-color-border-strong)"),
  ("--bp-shadow-bold-lg", "0 9px 0 var(--bp-color-border-strong)"),
  ("--bp-shadow-xs", "0 1px 2px rgba(0, 0, 0, 0.4)"),
  ("--bp-shadow-inset", "inset 0 1px 1px rgba(0, 0, 0, 0.4)"),
  ("--bp-shadow-popover", "0 8px 20px rgba(0, 0, 0, 0.5)"),
  ("--bp-shadow-icon", "0 1px 2px rgba(0, 0, 0, 0.5)"),
  ("--bp-shadow-step", "0 3px 0 rgba(0, 0, 0, 0.45)"),
  ("--bp-shadow-slide-card", "0 10px 24px rgba(0, 0, 0, 0.45)"),
  ("--bp-shadow-slide-panel", "0 18px 42px rgba(0, 0, 0, 0.55)"),
  -- Tokens other branches consume; they may have no light value in this branch.
  ("--bp-color-link", "#93c5fd"),
  ("--bp-code-keyword", "#7cb7ff"),
  ("--bp-code-const", "#e5c07b"),
  ("--bp-code-var", "#9cdcfe"),
  ("--bp-code-sort", "#4ec9b0"),
  ("--bp-code-literal", "#b5cea8"),
  ("--bp-code-comment", "#8b949e"),
  ("--bp-code-punctuation", "#d4d4d4"),
  -- Verso base variables, so the whole page is dark even without a Verso dark theme.
  ("--verso-text-color", "#e5e7eb"),
  ("--verso-code-color", "#e5e7eb"),
  ("--verso-structure-color", "#f8fafc"),
  ("--verso-selected-color", "#1e3a5f"),
  ("--verso-tooltip-color", "#e5e7eb"),
  ("--verso-tooltip-bg-color", "#20252e"),
  ("--verso-tooltip-border-color", "#64748b"),
  ("--verso-tooltip-separator-color", "#334155"),
  ("--verso-code-info-hover-bg-color", "#1e3a8a"),
  ("--verso-code-warning-hover-bg-color", "#5c4a14"),
  ("--verso-code-error-hover-bg-color", "#5a2020"),
  ("--verso-message-error-color", "#f87171"),
  ("--verso-tactic-state-color", "#e5e7eb"),
  ("--verso-tactic-state-bg-color", "#1b1f27"),
  ("--verso-tactic-state-border-color", "#475569"),
  ("--verso-tactic-toggle-color", "#64748b"),
  ("--verso-tactic-toggle-checked-color", "#94a3b8"),
  ("--verso-code-hover-bg-color", "#2a3140"),
  ("--verso-toc-background-color", "#171b22"),
  ("--verso-toc-border-color", "#334155"),
  ("--verso-toc-resize-handle-color", "#64748b"),
  ("--verso-burger-toc-visible-color", "#e5e7eb"),
  ("--verso-burger-toc-visible-shadow-color", "#1b1f27"),
  ("--verso-burger-toc-hidden-color", "#e5e7eb"),
  ("--verso-burger-toc-hidden-shadow-color", "#1b1f27"),
  ("background-color", "var(--bp-color-surface)")
]

/-- Page-level rules that Verso's `book.css` hard-codes rather than routing through variables:
`(selector below html, declarations)`. An empty selector means `html` itself. -/
def darkPageRules : List (String × List (String × String)) := [
  ("body", [("background", "var(--bp-color-surface)"), ("color", "var(--verso-text-color)")]),
  ("header", [("background", "var(--bp-color-surface)")]),
  ("#toc .split-toc label.toggle-split-toc::before",
    [("background-color", "var(--verso-text-color)")])
]

private def renderDarkRule (trigger selector : String) (decls : List (String × String)) : String :=
  let sel := if selector.isEmpty then trigger else trigger ++ " " ++ selector
  sel ++ " {\n" ++
    String.join (decls.map fun (name, value) => "  " ++ name ++ ": " ++ value ++ ";\n") ++ "}\n"

private def renderDarkRules (trigger : String) : String :=
  String.join <|
    renderDarkRule trigger "" darkTokens ::
      darkPageRules.map fun (selector, decls) => renderDarkRule trigger selector decls

/-- Dark theme CSS: one block per trigger (the `data-theme="dark"` attribute, and the OS
preference unless `data-theme="light"` opts out), both rendered from `darkTokens`. -/
def blueprintDarkTokensCss : String :=
  "\n" ++ renderDarkRules "html[data-theme=\"dark\"]" ++
  "@media (prefers-color-scheme: dark) {\n" ++
  renderDarkRules "html:not([data-theme=\"light\"])" ++ "}\n"

/-- All token CSS shipped with every blueprint page: light tokens plus the dark theme. -/
def blueprintTokensCss : String :=
  blueprintLightTokensCss ++ blueprintDarkTokensCss

def previewPanelCss : String := r##"
.bp_preview_panel {
  border: 1px solid var(--bp-color-border);
  border-radius: var(--bp-radius-lg);
  background: var(--bp-color-surface);
  box-shadow: var(--bp-shadow-md);
  padding: 0.65rem 0.75rem;
}

.bp_preview_panel[hidden] {
  display: none !important;
}

.bp_preview_panel[data-bp-preview-placement="anchored"]::before {
  content: "";
  position: absolute;
  left: 0;
  right: 0;
  top: -0.85rem;
  height: 0.85rem;
}

.bp_preview_panel[data-bp-preview-placement="anchored"]::after {
  content: "";
  position: absolute;
  left: 0;
  right: 0;
  bottom: -0.85rem;
  height: 0.85rem;
}

.bp_preview_panel_header {
  display: flex;
  align-items: center;
  justify-content: space-between;
  gap: 0.5rem;
  margin-bottom: 0.4rem;
}

.bp_preview_panel_title {
  font-weight: 700;
  color: var(--bp-color-text);
  min-width: 0;
  white-space: nowrap;
  overflow: hidden;
  text-overflow: ellipsis;
}

.bp_preview_panel_close {
  border: 1px solid var(--bp-color-border);
  border-radius: var(--bp-radius-sm);
  background: var(--bp-color-surface);
  color: var(--bp-color-text-strong);
  font-size: 0.72rem;
  font-weight: 600;
  line-height: 1;
  padding: 0.25rem 0.45rem;
  cursor: pointer;
}

.bp_preview_panel[data-bp-preview-mode="hover"] .bp_preview_panel_close {
  display: none;
}

.bp_preview_panel_body {
  border-left: 2px solid var(--bp-color-border-soft);
  overflow: auto;
}
"##

def previewHeaderCss : String := r##"
.bp_preview_header_heading {
  display: flex;
  align-items: baseline;
  flex-wrap: wrap;
  gap: 0.42rem;
  flex: 1 1 auto;
  min-width: 0;
}

.bp_preview_header_heading > *:first-child {
  min-width: 0;
}

.bp_preview_header_label {
  margin-left: auto;
  max-width: 100%;
  color: var(--bp-color-text-muted);
  font-family: var(--bp-font-mono, ui-monospace, SFMono-Regular, Menlo, Consolas, monospace);
  font-size: 0.72rem;
  font-weight: 600;
  overflow-wrap: anywhere;
  text-align: right;
  text-decoration: none;
}

.bp_preview_header_label[href]:hover {
  color: var(--bp-color-link);
  text-decoration: underline;
}

.bp_preview_header_label[hidden] {
  display: none;
}
"##

def inlinePreviewCss : String := r##"
.bp_inline_preview_ref {
  cursor: help;
}

.bp_inline_preview_panel {
  position: fixed;
  display: flex;
  flex-direction: column;
  z-index: 70;
  min-width: 18rem;
  max-width: min(34rem, 86vw);
  max-height: min(26rem, 80vh);
  overflow: hidden;
  border: 1px solid var(--bp-color-border);
  border-radius: var(--bp-radius-md);
  background: var(--bp-color-surface);
  box-shadow: var(--bp-shadow-lg);
}

.bp_inline_preview_panel[hidden] {
  display: none !important;
}

.bp_inline_preview_panel_child {
  z-index: 71;
}

.bp_inline_preview_panel[hidden] {
  display: none;
}

.bp_inline_preview_panel[data-bp-preview-placement="anchored"]::before {
  content: "";
  position: absolute;
  left: 0;
  right: 0;
  top: -0.85rem;
  height: 0.85rem;
}

.bp_inline_preview_panel[data-bp-preview-placement="docked"] {
  top: 0.9rem;
  right: 0.9rem;
  left: auto;
}

.bp_inline_preview_panel_header {
  display: flex;
  align-items: center;
  justify-content: space-between;
  gap: 0.6rem;
  padding: 0.4rem 0.55rem;
  border-bottom: 1px solid var(--bp-color-border-soft);
  background: var(--bp-color-surface-muted);
}

.bp_inline_preview_panel_title {
  font-size: 0.82rem;
  font-weight: 700;
  color: var(--bp-color-text-strong);
}

.bp_inline_preview_panel_close {
  border: 1px solid var(--bp-color-border);
  border-radius: 0.3rem;
  background: var(--bp-color-surface);
  color: var(--bp-color-text-muted);
  font-size: 0.72rem;
  line-height: 1;
  padding: 0.2rem 0.35rem;
  cursor: pointer;
}

.bp_inline_preview_panel_body {
  padding: 0.5rem 0.6rem 0.55rem;
  min-height: 0;
  max-height: min(22rem, 70vh);
  overflow: auto;
  font-size: 0.8rem;
}

.bp_inline_preview_panel_footer {
  display: flex;
  align-items: center;
  flex-wrap: wrap;
  gap: 0.35rem;
  padding: 0.38rem 0.55rem 0.42rem;
  border-top: 1px solid var(--bp-color-border-soft);
  background: var(--bp-color-surface-muted);
  color: var(--bp-color-text-subtle);
  font-size: 0.72rem;
}

.bp_inline_preview_panel_footer[hidden] {
  display: none;
}

.bp_inline_preview_panel_footer code {
  font-size: 0.72rem;
}

.bp_bibliography_hover_entry {
  border: 1px solid var(--bp-color-border-soft);
  border-radius: 0.4rem;
  padding: 0.35rem 0.45rem;
  background: var(--bp-color-surface-muted);
}

.bp_bibliography_hover_entry .citation {
  display: block;
  line-height: 1.35;
}

.bp_bibliography_hover_meta {
  margin-top: 0.42rem;
  display: flex;
  align-items: baseline;
  gap: 0.42rem;
  flex-wrap: wrap;
}

.bp_bibliography_hover_meta_label {
  font-size: 0.68rem;
  font-weight: 700;
  letter-spacing: 0.05em;
  text-transform: uppercase;
  color: var(--bp-color-text-faint);
}

.bp_bibliography_hover_meta_value {
  font-size: 0.76rem;
  font-weight: 600;
  color: var(--bp-color-text-strong);
}

.bp_code_hover_section {
  margin-top: 0.28rem;
}

.bp_code_hover_label {
  font-weight: 600;
  color: var(--bp-color-text-muted);
}

.bp_code_hover_list code {
  font-size: 0.76rem;
}

.bp_code_hover_none {
  color: var(--bp-color-text-faint);
  font-style: italic;
}

.bp_inline_preview_panel[data-bp-preview-mode="hover"] .bp_inline_preview_panel_close {
  display: none;
}
"##

/--
Logical Blueprint browser assets before choosing a physical output mode.

Manual renderers currently inline these lists through Verso `HtmlAssets`.
JavaScript startup is supplied by the generated ESM page runtime instead of
these command-local bundles.
-/
structure BlueprintAssetBundle where
  css : List String := []
  js : List String := []
deriving Inhabited

namespace BlueprintAssetBundle

def append (left right : BlueprintAssetBundle) : BlueprintAssetBundle :=
  { css := left.css ++ right.css
    js := left.js ++ right.js }

def withCss (assets : BlueprintAssetBundle) (extras : List String) : BlueprintAssetBundle :=
  { assets with css := assets.css ++ extras }

def withJs (assets : BlueprintAssetBundle) (before after : List String) : BlueprintAssetBundle :=
  { assets with js := before ++ assets.js ++ after }

end BlueprintAssetBundle

def blueprintCssAssetBundle (extras : List String := []) : BlueprintAssetBundle :=
  ({ css := [blueprintTokensCss] } : BlueprintAssetBundle).withCss extras

def previewPanelCssAssetBundle (extras : List String := []) : BlueprintAssetBundle :=
  (blueprintCssAssetBundle [previewPanelCss]).withCss extras

def inlinePreviewCssAssetBundle (extras : List String := []) : BlueprintAssetBundle :=
  (blueprintCssAssetBundle extras).withCss [previewHeaderCss, inlinePreviewCss]

def previewPanelInlinePreviewCssAssetBundle (extras : List String := []) : BlueprintAssetBundle :=
  (previewPanelCssAssetBundle extras).withCss [previewHeaderCss, inlinePreviewCss]

def previewPanelAssetBundle
    (cssExtras : List String := [])
    (jsBefore : List String := [])
    (jsAfter : List String := []) : BlueprintAssetBundle :=
  (previewPanelCssAssetBundle cssExtras).append
    ({ js := jsBefore ++ jsAfter } : BlueprintAssetBundle)

def inlinePreviewAssetBundle
    (cssExtras : List String := [])
    (jsBefore : List String := [])
    (jsAfter : List String := []) : BlueprintAssetBundle :=
  (inlinePreviewCssAssetBundle cssExtras).append
    ({ js := jsBefore ++ jsAfter } : BlueprintAssetBundle)

def previewPanelInlinePreviewAssetBundle
    (cssExtras : List String := [])
    (jsBefore : List String := [])
    (jsAfter : List String := []) : BlueprintAssetBundle :=
  (previewPanelInlinePreviewCssAssetBundle cssExtras).append
    ({ js := jsBefore ++ jsAfter } : BlueprintAssetBundle)

end Informal.Commands
