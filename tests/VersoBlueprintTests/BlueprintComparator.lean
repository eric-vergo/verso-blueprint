/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

import VersoBlueprintTests.Blueprint.Support
import VersoBlueprint.Stats.Comparator
import VersoBlueprint.PreviewManifest
import VersoBlueprintTests.ComparatorFixtures.Match.Solution
import VersoBlueprintTests.ComparatorFixtures.Sorry.Solution
import VersoBlueprintTests.ComparatorFixtures.Statement.Solution
import VersoBlueprintTests.ComparatorFixtures.Definition.Solution
import VersoBlueprintTests.ComparatorFixtures.Hole.Solution

/-!
The headline of the project statistics: Comparator challenges under
`ComparatorFixtures/` (compiled by the library `VersoBlueprintComparatorChallenges`) compared
with their solutions, which this module imports; the configuration in `comparator.json`; what is
reported when no comparison can be made; and how statements and docstrings are read from the
challenge source.
-/

namespace Verso.VersoBlueprintTests.BlueprintComparator

open Lean
open Verso
open Verso.Genre.Manual
open Informal
open Informal.Stats

set_option doc.verso true

#docs (Genre.Manual) comparatorDoc "Comparator Doc" :=
:::::::
:::definition "def:cmp.double" (lean := "CmpMatch.double")
Twice a number.
:::

:::theorem "thm:cmp.double" (lean := "CmpMatch.double_eq") (uses := "def:cmp.double")
Doubling adds a number to itself.
:::
:::::::

/-- The challenge module and the solution module of a fixture. -/
private def fixture (scenario : String) : ChallengeConfig := {
  challengeModule := `VersoBlueprintTests.ComparatorFixtures ++ scenario.toName ++ `Challenge
  solutionModule := `VersoBlueprintTests.ComparatorFixtures ++ scenario.toName ++ `Solution
}

/-- The package root, three directories above this test file. -/
private def packageRoot : CoreM System.FilePath := do
  let file : System.FilePath := ← getFileName
  let file ← if file.isAbsolute then pure file else return (← IO.currentDir) / file
  return (file.parent.bind (·.parent) |>.bind (·.parent)).getD "."

/-- The headline of a fixture, with the fixtures' sources and compiled modules. -/
private def headline (config : ChallengeConfig) : CoreM Headline := do
  let layout : WorkspaceLayout :=
    { sourceDirs := #["tests"], libraryDirs := #[".lake/build/lib/lean"] }
  Headline.compute config (← packageRoot) layout (← searchPathRef.get)

private def short (n : Name) : String :=
  match n with
  | .str _ s => s
  | _ => n.toString

private def describe (h : Headline) : List String :=
  [s!"unavailable: {repr h.unavailable} {h.unavailableDetail.getD ""}"] ++
  h.theorems.toList.map (fun t =>
    s!"theorem {short t.name}: {repr t.solution}, sorry-free {t.sorryFree}, axioms " ++
    s!"{t.axioms.toList}, permitted {t.axiomsPermitted}, proved {t.proved}, node {t.node}" ++
    (match t.differingDeclaration, t.difference with
      | some d, some why => s!", differs at {short d}: {why}"
      | _, _ => "")) ++
  h.definitions.toList.map fun d => s!"definition {short d.name}: {repr d.solution}"

-- Same statements, complete proofs: proved, with each proof's axioms; the node that carries the
-- theorem; the definition both declare the same.
/--
info: ["unavailable: none ",
  "theorem double_eq: Informal.Stats.Correspondence.same, sorry-free (some true), axioms [], permitted none, proved true, node (some «thm:cmp.double»)",
  "theorem double_cases: Informal.Stats.Correspondence.same, sorry-free (some true), axioms [Classical.choice, Quot.sound, propext], permitted none, proved true, node none",
  "definition double: Informal.Stats.Correspondence.same"]
-/
#guard_msgs in
#eval show CoreM _ from do return describe (← headline (fixture "Match"))

-- The name, docstring and statement as the challenge writes them.
/--
info: [("CmpMatch.double_eq", some "Doubling a number\nadds it to itself.",
    "theorem double_eq (n : Nat) :\n    double n = n + n"),
  ("CmpMatch.double_cases", none, "theorem double_cases (n : Nat) : double n = 0 ∨ double n ≠ 0")]
-/
#guard_msgs in
#eval show CoreM _ from do
  return (← headline (fixture "Match")).theorems.toList.map fun t =>
    (t.name.toString, t.docstring, t.statement)

-- A solution with a `sorry`: the same statement, not proved.
/--
info: ["unavailable: none ",
  "theorem triple_eq: Informal.Stats.Correspondence.same, sorry-free (some false), axioms [sorryAx], permitted none, proved false, node none",
  "definition triple: Informal.Stats.Correspondence.same"]
-/
#guard_msgs in
#eval show CoreM _ from do return describe (← headline (fixture "Sorry"))

-- A statement that differs: not proved, though the proof is complete.
/--
info: ["unavailable: none ",
  "theorem half_le: Informal.Stats.Correspondence.differs, sorry-free (some true), axioms [propext], permitted none, proved false, node none, differs at half_le: the statement differs",
  "definition half: Informal.Stats.Correspondence.same"]
-/
#guard_msgs in
#eval show CoreM _ from do return describe (← headline (fixture "Statement"))

-- A definition the statement uses differs: the same statement text, a different theorem.
/--
info: ["unavailable: none ",
  "theorem square_two: Informal.Stats.Correspondence.differs, sorry-free (some true), axioms [], permitted none, proved false, node none, differs at square: the definition differs",
  "definition square: Informal.Stats.Correspondence.differs"]
-/
#guard_msgs in
#eval show CoreM _ from do return describe (← headline (fixture "Definition"))

-- A definition hole: without `definition_names` the solution's value differs; with it, the
-- solution supplies the value and the theorem is proved.
/--
info: ["unavailable: none ",
  "theorem answer_pos: Informal.Stats.Correspondence.differs, sorry-free (some true), axioms [], permitted none, proved false, node none, differs at answer: the definition differs",
  "definition answer: Informal.Stats.Correspondence.differs"]
-/
#guard_msgs in
#eval show CoreM _ from do return describe (← headline (fixture "Hole"))

/--
info: ["unavailable: none ",
  "theorem answer_pos: Informal.Stats.Correspondence.same, sorry-free (some true), axioms [], permitted (some true), proved true, node none",
  "definition answer: Informal.Stats.Correspondence.hole"]
-/
#guard_msgs in
#eval show CoreM _ from do
  return describe (← headline { fixture "Hole" with
    definitionNames := #[`CmpHole.answer], permittedAxioms := some #[``propext] })

-- `theorem_names` selects the theorems judged; `permitted_axioms` judges their axioms.
/--
info: ["unavailable: none ",
  "theorem double_cases: Informal.Stats.Correspondence.same, sorry-free (some true), axioms [Classical.choice, Quot.sound, propext], permitted (some false), proved true, node none",
  "definition double: Informal.Stats.Correspondence.same"]
-/
#guard_msgs in
#eval show CoreM _ from do
  return describe (← headline { fixture "Match" with
    theoremNames := some #[`CmpMatch.double_cases], permittedAxioms := some #[``propext] })

-- No comparison: no compiled challenge, or a solution the environment does not have (the
-- challenge's theorems are still listed).
/--
info: ["unavailable: some (Informal.Stats.Unavailable.challengeNotBuilt) VersoBlueprintTests.ComparatorFixtures.Absent.Challenge"]
-/
#guard_msgs in
#eval show CoreM _ from do return describe (← headline (fixture "Absent"))

/--
info: ["unavailable: some (Informal.Stats.Unavailable.solutionNotImported) VersoBlueprintTests.ComparatorFixtures.Absent.Solution",
  "theorem triple_eq: Informal.Stats.Correspondence.notCompared, sorry-free none, axioms [], permitted none, proved false, node none"]
-/
#guard_msgs in
#eval show CoreM _ from do
  return describe (← headline
    { fixture "Sorry" with solutionModule := (fixture "Absent").solutionModule })

/-- A scratch directory, removed afterwards; its real path is passed on. -/
private def withScratch [Monad m] [MonadLiftT IO m] [MonadFinally m]
    (k : System.FilePath → m α) : m α := do
  let dir ← (IO.FS.createTempDir : IO _)
  try k (← (IO.FS.realPath dir : IO _)) finally (IO.FS.removeDirAll dir : IO _)

private def write (path : System.FilePath) (text : String) : IO Unit := do
  if let some parent := path.parent then IO.FS.createDirAll parent
  IO.FS.writeFile path text

-- A compiled challenge is read when its theorems are where its source has them, however old
-- the source file looks; when they are not, it is out of date.
/--
info: [["unavailable: some (Informal.Stats.Unavailable.solutionNotImported) Comparator.Solution",
    "theorem triple_eq: Informal.Stats.Correspondence.notCompared, sorry-free none, axioms [], permitted none, proved false, node none"],
  ["unavailable: some (Informal.Stats.Unavailable.challengeOutOfDate) Comparator/Challenge.lean"]]
-/
#guard_msgs in
#eval show CoreM _ from do
  let fixtures := (← packageRoot) / "tests/VersoBlueprintTests/ComparatorFixtures/Sorry"
  let compiled := (← packageRoot) /
    ".lake/build/lib/lean/VersoBlueprintTests/ComparatorFixtures/Sorry"
  withScratch fun root => do
    IO.FS.createDirAll (root / "lib/Comparator")
    IO.FS.writeBinFile (root / "lib/Comparator/Challenge.olean")
      (← IO.FS.readBinFile (compiled / "Challenge.olean"))
    let layout : WorkspaceLayout := { sourceDirs := #["."], libraryDirs := #["lib"] }
    let mut out := #[]
    for text in [← IO.FS.readFile (fixtures / "Challenge.lean"),
        "theorem triple_eq : True := trivial\n"] do
      write (root / "Comparator/Challenge.lean") text
      let h ← Headline.compute {} root layout []
      out := out.push <| describe { h with unavailableDetail := h.unavailableDetail.map fun d =>
        (relativeTo? root (d : String)).getD d }
    return out.toList

-- Where the challenge comes from: `comparator.json`, else `Comparator/Challenge.lean` in a
-- source directory, else there is none.
/--
info: [none,
 some (Except.ok (`Comparator.Challenge, `Comparator.Solution, none, none, none)),
 some (Except.ok (`Puzzle.Statement, `Puzzle.Answer, some #[`main], some #[`propext], some "comparator.json")),
 some (Except.error "`permitted_axioms` is missing")]
-/
#guard_msgs in
#eval withScratch fun root => do
  let summary (found : Option (Except String ChallengeConfig)) :=
    found.map fun (r : Except String ChallengeConfig) => r.map fun (c : ChallengeConfig) =>
      (c.challengeModule, c.solutionModule, c.theoremNames, c.permittedAxioms, c.configFile)
  let none₁ ← ChallengeConfig.find? root #["."]
  write (root / "src/Comparator/Challenge.lean") "theorem t : True := sorry\n"
  let byDefault ← ChallengeConfig.find? root #[".", "src"]
  write (root / "comparator.json") <| "{\"challenge_module\": \"Puzzle.Statement\", " ++
    "\"solution_module\": \"Puzzle.Answer\", \"theorem_names\": [\"main\"], " ++
    "\"permitted_axioms\": [\"propext\"]}"
  let configured ← ChallengeConfig.find? root #["."]
  write (root / "comparator.json") <| "{\"challenge_module\": \"Puzzle.Statement\", " ++
    "\"solution_module\": \"Puzzle.Answer\", \"theorem_names\": []}"
  let broken ← ChallengeConfig.find? root #["."]
  return [summary none₁, summary byDefault, summary configured, summary broken]

-- A project without a challenge has no headline, and says so.
/-- info: (none, false) -/
#guard_msgs in
#eval show CoreM _ from do
  let cwd ← IO.currentDir
  withScratch fun root => do
    IO.Process.setCurrentDir root
    try
      let stats ← ({} : ProjectStats).withHeadline
      return (stats.headline.map (·.challengeModule), stats.hasComparatorChallenge)
    finally
      IO.Process.setCurrentDir cwd

-- Statements end at the first `:=`, `where` or line-initial `|` outside brackets, comments and
-- strings; a `:=` of a `let` or `have` inside the statement does not end it.
private def statementOf (text : String) (name : String) : String :=
  let chars := text.toList.toArray
  let start := (text.splitOn name).head!.length
  statementAt chars start (start + name.length)

/--
info: ["theorem a : x = y", "theorem b (h : { s : Nat // s ≠ 0 := 1 }) : True", "theorem c : let n := 1; n = 1",
  "theorem d (s : String := \":=\") /- := -/ : True", "theorem e : ∀ n : Nat, n = n", "instance f : Inhabited Nat"]
-/
#guard_msgs in
#eval [statementOf "theorem a : x = y := by\n  rfl" "a",
  statementOf "theorem b (h : { s : Nat // s ≠ 0 := 1 }) : True := trivial" "b",
  statementOf "theorem c : let n := 1; n = 1 := rfl" "c",
  statementOf "theorem d (s : String := \":=\") /- := -/ : True := trivial" "d",
  statementOf "theorem e : ∀ n : Nat, n = n\n  | 0 => rfl\n  | _ => rfl" "e",
  statementOf "instance f : Inhabited Nat where\n  default := 0" "f"]

/-- info: [some "One line.", some "First line\n  indented\nlast", none] -/
#guard_msgs in
#eval [docstringAt? "/-- One line. -/\ntheorem a".toList.toArray 0,
  docstringAt? "  /-- First line\n    indented\n  last -/".toList.toArray 0,
  docstringAt? "@[simp] theorem a".toList.toArray 0]

end Verso.VersoBlueprintTests.BlueprintComparator
