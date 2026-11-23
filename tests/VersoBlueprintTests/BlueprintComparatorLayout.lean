/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

import VersoBlueprint.Stats.ComparatorLayout
import VersoBlueprint.VbpComparator

/-!
The layout of a project's Comparator challenges (`Informal.Stats.ComparatorLayout`): every rule
on a project made for it in a temporary folder, with the exact message each violation gives, the
challenges of a project that follows the layout, and the move of the single-challenge layout
(`VersoBlueprint.Vbp.migrationPlan`, `applyChanges`).
-/

namespace Verso.VersoBlueprintTests.BlueprintComparatorLayout

open Lean
open Informal.Stats
open Informal.Stats.ComparatorLayout

/-- A project made of `files` (path and text) in a new temporary folder. -/
private def project (files : List (String × String)) : IO System.FilePath := do
  let root ← IO.FS.createTempDir
  for (path, text) in files do
    let file := root / path
    if let some dir := file.parent then IO.FS.createDirAll dir
    IO.FS.writeFile file text
  return root

/-- The rendered violations of a project, the folder's own name removed. -/
private def violations (files : List (String × String)) : IO (List String) := do
  let root ← project files
  let report ← check root
  IO.FS.removeDirAll root
  return report.violations.toList.map (·.render)

private def challenge (ns : String := "A") (thm : String := "t") : String :=
  s!"namespace {ns}\n\n/-- A statement. -/\ntheorem {thm} : 1 + 1 = 2 := by\n  sorry\n\nend {ns}\n"

private def solution (ns : String := "A") (thm : String := "t") : String :=
  s!"namespace {ns}\n\n/-- A statement. -/\ntheorem {thm} : 1 + 1 = 2 := rfl\n\nend {ns}\n"

private def config (name : String) (theorems : String := "[\"A.t\"]")
    (extra : String := "") : String :=
  s!"\{\"challenge_module\": \"Comparator.{name}.Challenge\", \
    \"solution_module\": \"Comparator.{name}.Solution\", \
    \"theorem_names\": {theorems}, \"permitted_axioms\": [\"propext\"]{extra}}"

/-- The three files of a conforming challenge `name`. -/
private def conforming (name : String) (ns : String := "A") : List (String × String) :=
  [(s!"Comparator/{name}/Challenge.lean", challenge ns),
   (s!"Comparator/{name}/Solution.lean", solution ns),
   (s!"Comparator/{name}/comparator.json", config name s!"[\"{ns}.t\"]")]

-- A project without Comparator files has no challenge and no violation.
/-- info: (0, 0, false) -/
#guard_msgs (whitespace := lax) in
#eval show IO _ from do
  let root ← project [("Main.lean", "def x := 1\n")]
  let r ← check root
  IO.FS.removeDirAll root
  return (r.challenges.size, r.violations.size, r.hasComparator)

-- A project that follows the layout: its challenges in the order of their names, configured.
/--
info: (0,
  #[("Alpha", `Comparator.Alpha.Challenge, `Comparator.Alpha.Solution, some #[`A.t], some #[`propext],
      some "Comparator/Alpha/comparator.json"),
    ("Beta", `Comparator.Beta.Challenge, `Comparator.Beta.Solution, some #[`B.t], some #[`propext],
      some "Comparator/Beta/comparator.json")])
-/
#guard_msgs (whitespace := lax) in
#eval show IO _ from do
  let root ← project (conforming "Beta" "B" ++ conforming "Alpha" "A" ++ [("Comparator/.DS_Store", "")])
  let r ← check root
  IO.FS.removeDirAll root
  return (r.violations.size, r.challenges.map fun c =>
    (c.name, c.challengeModule, c.solutionModule, c.theoremNames, c.permittedAxioms, c.configFile))

-- The single-challenge layout, with and without a configuration at the root.
/--
info: ["Comparator/Challenge.lean: rule L1 (one folder per challenge): the single-challenge layout (Comparator/Challenge.lean, Comparator/Solution.lean, comparator.json at the root) is not accepted; every challenge has a folder Comparator/<Name>/. Run `lake exe vbp comparator-migrate --name Main` (add `--dry-run` to see the changes first), or by hand: mkdir -p Comparator/Main; git mv Comparator/Challenge.lean Comparator/Main/Challenge.lean; git mv Comparator/Solution.lean Comparator/Main/Solution.lean; then write Comparator/Main/comparator.json with \"challenge_module\": \"Comparator.Main.Challenge\", \"solution_module\": \"Comparator.Main.Solution\", \"theorem_names\" and \"permitted_axioms\", and rename the modules Comparator.Challenge and Comparator.Solution to Comparator.Main.Challenge and Comparator.Main.Solution where the project names them (its lakefile, imports)"]
-/
#guard_msgs (whitespace := lax) in
#eval violations [("Comparator/Challenge.lean", challenge), ("Comparator/Solution.lean", solution)]
/--
info: ["comparator.json: rule L1 (one folder per challenge): the single-challenge layout (Comparator/Challenge.lean, Comparator/Solution.lean, comparator.json at the root) is not accepted; every challenge has a folder Comparator/<Name>/. Run `lake exe vbp comparator-migrate --name Main` (add `--dry-run` to see the changes first), or by hand: mkdir -p Comparator/Main; git mv Comparator/Challenge.lean Comparator/Main/Challenge.lean; git mv Comparator/Solution.lean Comparator/Main/Solution.lean; git mv comparator.json Comparator/Main/comparator.json; then set Comparator/Main/comparator.json with \"challenge_module\": \"Comparator.Main.Challenge\", \"solution_module\": \"Comparator.Main.Solution\", \"theorem_names\" and \"permitted_axioms\", and rename the modules Comparator.Challenge and Comparator.Solution to Comparator.Main.Challenge and Comparator.Main.Solution where the project names them (its lakefile, imports)"]
-/
#guard_msgs (whitespace := lax) in
#eval violations [("comparator.json", config "X")]

-- Folder names, stray files and stray configurations.
/--
info: ["docs/comparator.json: rule L5 (configuration files): a comparator.json belongs in a challenge's folder Comparator/<Name>/; move it there or remove it",
  "Comparator/lower: rule L3 (challenge folder names): a challenge's folder name starts with a capital letter and has only ASCII letters and digits, at most 64 characters (it becomes the module Comparator.<Name>.Challenge); rename lower",
  "Comparator/notes.txt: rule L3 (challenge folder names): Comparator/ holds only challenge folders; move or remove notes.txt",
  "Comparator/Good/README.md: rule F1 (the files of a challenge): a challenge's folder holds only Challenge.lean, Solution.lean, comparator.json; move or remove README.md"]
-/
#guard_msgs (whitespace := lax) in
#eval violations (conforming "Good" ++ [("Comparator/lower/Challenge.lean", challenge),
  ("Comparator/notes.txt", "x"), ("docs/comparator.json", "{}"),
  ("Comparator/Good/README.md", "x")])

-- Missing files.
/--
info: ["Comparator/Half/Solution.lean: rule F1 (the files of a challenge): it is missing; add Comparator/Half/Solution.lean"]
-/
#guard_msgs (whitespace := lax) in
#eval violations [("Comparator/Half/Challenge.lean", challenge),
  ("Comparator/Half/comparator.json", config "Half")]

-- The configuration's syntax, keys, modules and names.
/--
info: ["Comparator/J/comparator.json: rule J1 (comparator.json syntax): it is not valid JSON (offset 1: expected \")"]
-/
#guard_msgs (whitespace := lax) in
#eval violations [("Comparator/J/Challenge.lean", challenge), ("Comparator/J/Solution.lean", solution),
  ("Comparator/J/comparator.json", "{not json")]
/--
info: ["Comparator/J/comparator.json: rule J1 (comparator.json syntax): arrays and objects are nested more than 8 deep"]
-/
#guard_msgs (whitespace := lax) in
#eval violations [("Comparator/J/Challenge.lean", challenge), ("Comparator/J/Solution.lean", solution),
  ("Comparator/J/comparator.json", "[[[[[[[[[[1]]]]]]]]]]")]
/--
info: ["Comparator/J/comparator.json: rule J2 (comparator.json keys): the key \"enable_nanoda\" is not allowed; remove it (allowed: challenge_module, solution_module, theorem_names, permitted_axioms, definition_names, external_kernels)",
  "Comparator/J/comparator.json: rule J3 (module names): \"challenge_module\" is \"Comparator.Challenge\"; set it to \"Comparator.J.Challenge\"",
  "Comparator/J/comparator.json: rule J3 (module names): \"solution_module\" must be the string \"Comparator.J.Solution\"",
  "Comparator/J/comparator.json: rule J4 (theorem_names): \"theorem_names\" is empty; name the theorems the challenge judges",
  "Comparator/J/comparator.json: rule J5 (permitted_axioms): \"permitted_axioms\" names propext twice; keep one",
  "Comparator/J/comparator.json: rule J6 (definition_names): \"definition_names\" holds \"not a name\", which is not a Lean name; write the declaration's full name, such as \"Foo.bar\"",
  "Comparator/J/comparator.json: rule J7 (external_kernels): the kernel \"k\" must be a non-empty list of strings (the command and its arguments)"]
-/
#guard_msgs (whitespace := lax) in
#eval violations [("Comparator/J/Challenge.lean", challenge), ("Comparator/J/Solution.lean", solution),
  ("Comparator/J/comparator.json",
    "{\"challenge_module\": \"Comparator.Challenge\", \"solution_module\": 3, " ++
    "\"theorem_names\": [], \"permitted_axioms\": [\"propext\", \"propext\"], " ++
    "\"definition_names\": [\"A.t\", \"not a name\"], \"enable_nanoda\": true, " ++
    "\"external_kernels\": {\"k\": []}}")]
/--
info: ["Comparator/J/comparator.json: rule J6 (definition_names): A.t is in both \"theorem_names\" and \"definition_names\"; a definition hole is not a judged theorem: keep it in one"]
-/
#guard_msgs (whitespace := lax) in
#eval violations [("Comparator/J/Challenge.lean", challenge), ("Comparator/J/Solution.lean", solution),
  ("Comparator/J/comparator.json", config "J" "[\"A.t\"]" ", \"definition_names\": [\"A.t\"]")]

-- The Lean files: imports, `sorry`, the judged theorems declared.
/--
info: ["Comparator/L/Challenge.lean: rule C1 (the challenge's imports): it imports Comparator.L.Solution; a challenge and its solution import no module under Comparator (they declare the same names, and each challenge stands alone): remove the import",
  "Comparator/L/Challenge.lean: rule C2 (the challenge's sorry): the challenge states its theorems with `sorry` as their proofs, and this file has none: replace each proof by `sorry`",
  "Comparator/L/Solution.lean: rule S1 (the solution's imports): it imports Comparator.Other.Solution; a challenge and its solution import no module under Comparator (they declare the same names, and each challenge stands alone): remove the import",
  "Comparator/L/Solution.lean: rule C3 (judged theorems declared): the judged theorem A.t (theorem_names) is not declared here with `theorem`; declare it, or correct its name in comparator.json"]
-/
#guard_msgs (whitespace := lax) in
#eval violations [
  ("Comparator/L/Challenge.lean", "import Comparator.L.Solution\nnamespace A\ntheorem t : True := trivial\nend A\n"),
  ("Comparator/L/Solution.lean", "import Comparator.Other.Solution\n-- theorem A.t is in a comment\n"),
  ("Comparator/L/comparator.json", config "L")]

-- A theorem written with its full name, and one inside nested namespaces, are found.
/-- info: [] -/
#guard_msgs (whitespace := lax) in
#eval violations [
  ("Comparator/N/Challenge.lean", "namespace X\nnamespace Y\ntheorem u : True := sorry\nend Y\nend X\ntheorem Z.w : True := sorry\n"),
  ("Comparator/N/Solution.lean", "theorem X.Y.u : True := trivial\nnamespace Z\ntheorem w : True := trivial\nend Z\n"),
  ("Comparator/N/comparator.json", config "N" "[\"X.Y.u\", \"Z.w\"]")]

-- A Lean file over the limit, and one that is not UTF-8.
/--
info: ["Comparator/S/Challenge.lean: rule F2 (Lean files): it has 1048577 bytes, more than the 1048576 allowed",
  "Comparator/S/Solution.lean: rule F2 (Lean files): it is not valid UTF-8"]
-/
#guard_msgs (whitespace := lax) in
#eval show IO _ from do
  let root ← project [("Comparator/S/Solution.lean", solution), ("Comparator/S/comparator.json", config "S")]
  IO.FS.writeFile (root / "Comparator/S/Challenge.lean") (String.ofList (List.replicate (leanFileLimit + 1) 'a'))
  IO.FS.writeBinFile (root / "Comparator/S/Solution.lean") (ByteArray.mk #[0xff, 0xfe])
  let r ← check root
  IO.FS.removeDirAll root
  return r.violations.toList.map (·.render)

-- The single-challenge layout moved by `vbp comparator-migrate`: the changes, then a project
-- that follows the layout, its configuration judging the theorems the challenge declares.
/--
info: ["mkdir -p Comparator/Main", "git mv Comparator/Challenge.lean Comparator/Main/Challenge.lean",
  "git mv Comparator/Solution.lean Comparator/Main/Solution.lean", "write Comparator/Main/comparator.json",
  "in Blueprint.lean: Comparator.Solution -> Comparator.Main.Solution (1×)",
  "in Blueprint.lean: Comparator/Challenge.lean -> Comparator/Main/Challenge.lean (1×)",
  "in lakefile.toml: Comparator.Solution -> Comparator.Main.Solution (1×)",
  "{\n  \"challenge_module\": \"Comparator.Main.Challenge\",\n  \"solution_module\": \"Comparator.Main.Solution\",\n  \"theorem_names\": [\"A.t\"],\n  \"permitted_axioms\": [\"propext\", \"Quot.sound\", \"Classical.choice\"]\n}\n",
  "import Comparator.Main.Solution\n-- see Comparator/Main/Challenge.lean\n",
  "[[lean_lib]]\nname = \"Comparator\"\nroots = [\"Comparator.Main.Solution\"]\n"]
-/
#guard_msgs (whitespace := lax) in
#eval show IO _ from do
  let root ← project [("Comparator/Challenge.lean", challenge),
    ("Comparator/Solution.lean", "import Lib\n" ++ solution),
    ("Blueprint.lean", "import Comparator.Solution\n-- see Comparator/Challenge.lean\n"),
    ("lakefile.toml", "[[lean_lib]]\nname = \"Comparator\"\nroots = [\"Comparator.Solution\"]\n")]
  let .ok changes ← VersoBlueprint.Vbp.migrationPlan root "Main" | return ["no plan"]
  VersoBlueprint.Vbp.applyChanges root changes
  let r ← check root
  let config ← IO.FS.readFile (root / "Comparator/Main/comparator.json")
  let blueprint ← IO.FS.readFile (root / "Blueprint.lean")
  let lakefile ← IO.FS.readFile (root / "lakefile.toml")
  IO.FS.removeDirAll root
  return (changes.toList.map (·.describe)) ++ r.violations.toList.map (·.render) ++
    [config, blueprint, lakefile]

-- The migration refuses a project without that layout, and a name that is not a challenge name.
/--
info: ("Comparator/Challenge.lean is not a file here: this project does not have the single-challenge layout",
  "main is not a challenge name: an ASCII capital letter, then ASCII letters and digits, at most 64 characters")
-/
#guard_msgs (whitespace := lax) in
#eval show IO _ from do
  let root ← project (conforming "Main")
  let a ← VersoBlueprint.Vbp.migrationPlan root "Main"
  let b ← VersoBlueprint.Vbp.migrationPlan root "main"
  IO.FS.removeDirAll root
  return ((match a with | .error e => e | .ok _ => "ok"), (match b with | .error e => e | .ok _ => "ok"))

-- What lies in comments and strings is not code.
/-- info: ("a     \n                  f        i", #[`A.B, `C]) -/
#guard_msgs (whitespace := lax) in
#eval (codeOnly "a -- b\n/- c /- d -/ e -/ f \"g\\\"h\" i", importsOf (codeOnly "import A.B\npublic import all C\n-- import D"))

end Verso.VersoBlueprintTests.BlueprintComparatorLayout
