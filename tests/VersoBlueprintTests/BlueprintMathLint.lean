/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Emilio J. Gallego Arias
-/

import VersoBlueprint

namespace Verso.VersoBlueprintTests.BlueprintMathLint

open Informal

/-- The source text that `span` covers, for inline code whose lines are the given slices of
`source`, each starting at the byte offset paired with it. -/
private def extractedRaw? (source : String) (lines : Array (Nat × String))
    (span : Informal.MathLint.Span) : Option String := do
  let lines := lines.map fun (offset, text) => ((⟨offset⟩ : String.Pos.Raw), text)
  let (start, stop) ← Informal.MathLint.codeLinesRangeOfDecodedSpan? lines span
  pure <| start.extract source stop

private def localNodeAvailable : IO Bool := do
  try
    let out ← IO.Process.output { cmd := "node", args := #["--version"] }
    pure (out.exitCode == 0)
  catch _ =>
    pure false

/-- info: true -/
#guard_msgs in
#eval
  show IO Bool from do
    let source := r#"\undefinedmacro"#
    let nodeAvailable ← localNodeAvailable
    let report ← Informal.MathLint.lint? {
      mode := .inline
      source
    }
    pure <|
      if !nodeAvailable then
        true
      else
        match report with
        | some failure =>
          failure.reason.contains "Undefined control sequence" &&
          failure.site == .source { start := 0, length := source.length } { start := 0, length := source.length }
        | none => false

/-- info: true -/
#guard_msgs in
#eval
  show IO Bool from do
    let report ← Informal.MathLint.lint? {
      mode := .inline
      source := r#"\foo + 1"#
      texPrelude := r#"\newcommand{\foo}{\mathsf{Foo}}"#
    }
    pure report.isNone

/-- info: true -/
#guard_msgs in
#eval
  show IO Bool from do
    let nodeAvailable ← localNodeAvailable
    let tasks ← (List.range 8).mapM fun i =>
      IO.asTask <| Informal.MathLint.lint? {
        mode := .inline
        source := r#"\undefinedmacro"# ++ toString i
      }
    let reports ← tasks.mapM fun task => IO.ofExcept task.get
    pure <| !nodeAvailable || reports.all (·.isSome)

-- Each character of a line maps onto its own source, backslashes included.
/-- info: true -/
#guard_msgs in
#eval
  show Bool from
    extractedRaw? r#"$`\\x`$"# #[(2, r#"\\x"#)] { start := 0, length := 2 } == some r#"\\"#

/-- info: true -/
#guard_msgs in
#eval
  show Bool from
    extractedRaw? r#"$`\alpha + 1`$"# #[(2, r#"\alpha + 1"#)] { start := 0, length := 6 } ==
      some r#"\alpha"#

-- A span on a later line of the code is found in that line's source, past the indentation that
-- is not part of the code.
/-- info: true -/
#guard_msgs in
#eval
  show Bool from
    extractedRaw? "$`a +\n    \\beta`$" #[(2, "a +\n"), (10, "\\beta")] { start := 4, length := 5 } ==
      some "\\beta"

-- A span across a line break covers the indentation between the lines.
/-- info: true -/
#guard_msgs in
#eval
  show Bool from
    extractedRaw? "$`a +\n    b`$" #[(2, "a +\n"), (10, "b")] { start := 2, length := 3 } ==
      some "+\n    b"

-- Positions count characters, not bytes.
/-- info: true -/
#guard_msgs in
#eval
  show Bool from
    extractedRaw? "$`α + β`$" #[(2, "α + β")] { start := 4, length := 1 } == some "β"

-- A span ending at the end of the code ends at the end of its last line.
/-- info: true -/
#guard_msgs in
#eval
  show Bool from
    extractedRaw? "$`ab`$" #[(2, "ab")] { start := 1, length := 1 } == some "b"

-- A span beyond the code has no source.
/-- info: true -/
#guard_msgs in
#eval
  show Bool from
    extractedRaw? "$`ab`$" #[(2, "ab")] { start := 1, length := 5 } == none

/-- info: true -/
#guard_msgs in
#eval
  show IO Bool from do
    let nodeAvailable ← localNodeAvailable
    let failure? ← Informal.MathLint.lint? {
      mode := .inline
      source := r#"\frac{a}{"#
    }
    pure <| if !nodeAvailable then true else
      match failure? with
      | some failure =>
        failure.site == .source { start := 9, length := 0 } { start := 9, length := 0 }
      | none => false

/-- info: true -/
#guard_msgs in
#eval
  show IO Bool from do
    let nodeAvailable ← localNodeAvailable
    let failure? ← Informal.MathLint.lint? {
      mode := .display
      source := r#"\foo + 1"#
      texPrelude := r#"\newcommand{\foo}{\mathsf{Foo}"#
    }
    pure <| if !nodeAvailable then true else
      match failure? with
      | some failure =>
        failure.reason.contains "expected '}'" &&
        match failure.site with
        | .prelude { start, length } => start > 0 && length == 0
        | _ => false
      | none => false

/-- info: true -/
#guard_msgs in
#eval
  show IO Bool from do
    let invalidPrelude := r#"\newcommand{\foo}{\mathsf{Foo}"#
    let nodeAvailable ← localNodeAvailable
    let first ← Informal.MathLint.lint? {
      mode := .inline
      source := r#"\foo + 1"#
      texPrelude := invalidPrelude
    }
    let second ← Informal.MathLint.lint? {
      mode := .inline
      source := r#"\foo + 2"#
      texPrelude := invalidPrelude
    }
    pure <| !nodeAvailable || (first.isSome && first == second)

end Verso.VersoBlueprintTests.BlueprintMathLint
