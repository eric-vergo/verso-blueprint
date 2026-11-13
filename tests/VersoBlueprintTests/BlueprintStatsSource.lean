/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

import VersoBlueprint.Stats.Source

/-!
The `cloc`-style line scanner of the project statistics, on small Lean sources.
-/

namespace Verso.VersoBlueprintTests.BlueprintStatsSource

open Informal.Stats

private def counts (text : String) : Nat × Nat × Nat :=
  let c := countLeanLines text
  (c.blank, c.comment, c.code)

-- Blank, comment and code lines, and a last line without a final newline.
/-- info: (1, 1, 2) -/
#guard_msgs in
#eval counts "def x := 1\n\n-- a comment\ntheorem t : True := trivial"

-- An empty text has no lines; a lone newline is one blank line.
/-- info: ((0, 0, 0), 1, 0, 0) -/
#guard_msgs in
#eval (counts "", counts "\n")

-- Docstrings and module docstrings are comments; a blank line inside one stays blank.
/-- info: (1, 4, 1) -/
#guard_msgs in
#eval counts "/-! Module\n\ndocs -/\n/-- A docstring\n  over lines. -/\ndef x := 1\n"

-- Block comments nest: the inner `-/` does not end the outer comment.
/-- info: (0, 3, 1) -/
#guard_msgs in
#eval counts "/- outer /- inner -/\n still outer\n-/\ndef y := 2\n"

-- Code followed by a comment on the same line is code; a comment opened after code is too.
/-- info: (0, 1, 2) -/
#guard_msgs in
#eval counts "def z := 3 -- trailing\ndef w := 4 /- opens\n closes -/\n"

-- Comment markers inside string, raw string and character literals are code.
/-- info: (0, 0, 4) -/
#guard_msgs in
#eval counts "def s := \"-- not a comment\"\ndef r := r#\"/- \" -/\"#\ndef c := '\"'\ndef d := \"\\\"--\"\n"

-- A string literal over several lines keeps its lines as code.
/-- info: (0, 0, 3) -/
#guard_msgs in
#eval counts "def m := \"first\n-- inside the string\nlast\"\n"

-- A prime in an identifier is not a character literal, and `f '' s` is not one either.
/-- info: (0, 1, 2) -/
#guard_msgs in
#eval counts "theorem h' : x' = x' := rfl\nexample := f '' s -- image\n-- done\n"

-- A guillemet name may hold comment markers.
/-- info: (0, 0, 1) -/
#guard_msgs in
#eval counts "def «a -- b» := 1\n"

-- Non-ASCII character literals and names: a quote inside `'"'`-like literals of any width does
-- not open a string.
/-- info: (0, 1, 3) -/
#guard_msgs in
#eval counts "def a := ('α', '\"') -- pair\ndef «β -- γ» := 1\n-- note\ndef δ' := 'ε'\n"

-- Windows line endings: the carriage return is whitespace.
/-- info: (1, 1, 1) -/
#guard_msgs in
#eval counts "def x := 1\r\n\r\n-- c\r\n"

/-- info: 7 -/
#guard_msgs in
#eval (countLeanLines "a\n\n-- c\n/- d\n\n-/\nb").total

end Verso.VersoBlueprintTests.BlueprintStatsSource
