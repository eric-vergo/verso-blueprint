/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

import VersoBlueprint.Stats.Repo

/-!
The project statistics' reading of a project root: README summary, license guess and Lake
manifest, on fixture texts and on a scratch project directory.
-/

namespace Verso.VersoBlueprintTests.BlueprintStatsRepo

open Lean
open Informal.Stats

-- Title from the first heading; the first paragraph as plain text, links and emphasis removed.
/--
info: (some "Rokicki's constant", some "A Lean 4 / Mathlib formalization of Rokicki's constant")
-/
#guard_msgs in
#eval Readme.summarize
  "# Rokicki's constant\n\nA Lean 4 / [Mathlib](https://github.com/x/y) formalization of\n\
  **Rokicki's constant**\n\n    ρ = …\n\n## Main result\n"

-- Badge lines, HTML and fenced code before the prose are skipped; autolinks are unwrapped.
/--
info: (some "Verso Noperthedron", some "Port of the x blueprint, see https://example.org.")
-/
#guard_msgs in
#eval Readme.summarize
  "<!-- note -->\n# Verso Noperthedron #\n\n[![CI status](https://b/badge.svg)](https://b) ![x](y)\n\n\
  <p align=\"center\"><img src=\"a.png\"></p>\n\n```bash\nlake build\n```\n\n\
  Port of the `x` blueprint, see <https://example.org>.\n"

-- A setext heading, and a README without prose.
/-- info: ((some "Title", some "Body text."), some "Only", none) -/
#guard_msgs in
#eval (Readme.summarize "Title\n=====\n\nBody *text*.\n", Readme.summarize "# Only\n\n![logo](l.png)\n")

-- Images go with their targets; nested brackets in link text survive.
/-- info: "See the docs [v2] here." -/
#guard_msgs in
#eval Readme.plainText "See ![icon](i.png) the [docs [v2]](https://d) here."

-- A long first paragraph is cut at a word.
/-- info: (600, true) -/
#guard_msgs in
#eval
  let text := (Readme.summarize (String.join (List.replicate 200 "word "))).2.getD ""
  (text.length, text.endsWith "word…")

-- License texts, by the phrases each license contains; an SPDX line wins.
/--
info: #[some "Apache-2.0", some "MIT", some "BSD-3-Clause", some "BSD-2-Clause", some "GPL-3.0", some "LGPL-2.1",
  some "AGPL-3.0", some "MPL-2.0", some "Unlicense", some "CC-BY-4.0", some "ISC", none]
-/
#guard_msgs in
#eval #[
  "                                 Apache License\n                           Version 2.0, January 2004",
  "MIT License\n\nPermission is hereby granted, free of charge, to any person",
  "Redistribution and use in source and binary forms ...\n3. Neither the name of the copyright holder",
  "Redistribution and use in source and binary forms, with or without modification",
  "GNU GENERAL PUBLIC LICENSE\n  Version 3, 29 June 2007",
  "GNU LESSER GENERAL PUBLIC LICENSE\n Version 2.1, February 1999",
  "GNU AFFERO GENERAL PUBLIC LICENSE\n Version 3",
  "Mozilla Public License Version 2.0",
  "This is free and unencumbered software released into the public domain.",
  "Attribution 4.0 International",
  "Permission to use, copy, modify, and/or distribute this software for any purpose with",
  "All rights reserved."].map guessSpdx

/-- info: some "MIT OR Apache-2.0" -/
#guard_msgs in
#eval guessSpdx "SPDX-License-Identifier: MIT OR Apache-2.0\nApache License Version 2.0"

-- Addresses lose any user name or password.
/-- info: ["https://github.com/a/b", "https://host.example/x.git", "git@github.com:a/b.git"] -/
#guard_msgs in
#eval ["https://github.com/a/b", "https://user:secret@host.example/x.git",
  "git@github.com:a/b.git"].map stripUserInfo

-- The manifest's root name and locked packages, in manifest order.
/--
info: (some "Demo",
 #[{ name := "mathlib",
     source := "git",
     rev := some "56a0",
     inputRev := some "v4.35.0",
     url := some "https://github.com/leanprover-community/mathlib4",
     dir := none,
     inherited := false },
   { name := "Local",
     source := "path",
     rev := none,
     inputRev := none,
     url := none,
     dir := some "./Local",
     inherited := false },
   { name := "plausible",
     source := "git",
     rev := some "dfa4",
     inputRev := none,
     url := some "https://github.com/leanprover-community/plausible",
     dir := none,
     inherited := true }])
-/
#guard_msgs in
#eval parseManifest r#"{"version": "1.1.0", "packagesDir": ".lake/packages", "name": "Demo",
  "packages": [
    {"url": "https://tok@github.com/leanprover-community/mathlib4", "type": "git", "rev": "56a0",
     "name": "mathlib", "inputRev": "v4.35.0", "inherited": false},
    {"type": "path", "name": "Local", "dir": "./Local", "inherited": false},
    {"url": "https://github.com/leanprover-community/plausible", "type": "git", "rev": "dfa4",
     "name": "plausible", "inputRev": "", "inherited": true}]}"#

/-- info: (none, #[]) -/
#guard_msgs in
#eval parseManifest "not json"

/-- A scratch project root with the given files, removed afterwards. -/
private def withProject (files : Array (String × String)) (k : System.FilePath → IO α) : IO α := do
  let dir ← IO.FS.createTempDir
  try
    for (name, text) in files do
      IO.FS.writeFile (dir / name) text
    k dir
  finally
    IO.FS.removeDirAll dir

-- A project with a README, a license under another case and a toolchain.
/--
info: { name := some "Demo",
  readme := some "readme.md",
  title := some "Demo",
  description := some "A demo project.",
  license := some { file := "License.txt", spdx := some "MIT" },
  toolchain := some "leanprover/lean4:v4.35.0",
  packages := #[] }
-/
#guard_msgs in
#eval withProject #[("readme.md", "# Demo\n\nA demo project.\n"),
    ("License.txt", "Permission is hereby granted, free of charge"),
    ("lean-toolchain", "leanprover/lean4:v4.35.0\n"),
    ("lake-manifest.json", "{\"name\": \"Demo\", \"packages\": []}")]
  ProjectIdentity.read

-- No license file: the field stays empty, which pages show as "no license file".
/-- info: (none, some { file := "COPYING", spdx := none }) -/
#guard_msgs in
#eval do
  let without ← withProject #[("README.md", "# X\n")] ProjectIdentity.read
  let unknown ← withProject #[("COPYING", "All rights reserved.")] ProjectIdentity.read
  return (without.license, unknown.license)

end Verso.VersoBlueprintTests.BlueprintStatsRepo
