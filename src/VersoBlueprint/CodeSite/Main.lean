/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

import VersoBlueprint
import VersoBlueprint.CodeSite.Build
import VersoBlueprint.PreviewManifest

/-!
`vbp code-site`: generate a Blueprint site from compiled-code data (`Informal.CodeSite.Project`).

```
vbp code-site --data <file> [--root <dir>] [--output <dir>] [--title <text>]
              [--graphviz <program> | --no-graph-layout]
              [--no-comparator | --challenge-not-built <reason>]
              [--no-stats-page] [--reproducible] [--verbose]
```

`--root` is the project the data describes (default: the working directory): the source
excerpts and the Project Stats page read its files. The dependency graph's views are laid out
while the site is built with Graphviz's `dot` (`--graphviz` names another program; without one
on the `PATH`, or with `--no-graph-layout`, the page lays them out). When the project has a
Comparator challenge, the Project Stats page's headline compares it with its solution as a
Blueprint site does; the solution's modules are imported from the project's build for that
(`--no-comparator` leaves the comparison out; `--challenge-not-built <reason>` leaves it out and
the headline says the challenge module was not built, with the reason, for a caller that tried to
build it first). The site is written as a generator writes
it (`<output>/html-multi`, default `_out/site`), with the left navigation bar and side-by-side
node cards.
-/

namespace Informal.CodeSite

open Lean System

/-- Options of `vbp code-site`. -/
structure Options where
  data : Option FilePath := none
  root : Option FilePath := none
  title : Option String := none
  /-- The Graphviz program the graph is laid out with while the site is built (`none`: the page
  lays it out). -/
  graphviz : Option String := some "dot"
  /-- Compare the project's Comparator challenge for the headline (it imports the solution). -/
  compare : Bool := true
  /-- The caller could not build the challenge (why): the headline says so, nothing is compared. -/
  challengeNotBuilt : Option String := none
  /-- Everything else, passed on to the generator (`--output`, `--no-stats-page`, …). -/
  rest : Array String := #[]
deriving Inhabited

/-- The usage line. -/
def usage : String :=
  "vbp code-site --data <file> [--root <dir>] [--output <dir>] [--title <text>] " ++
  "[--graphviz <program> | --no-graph-layout] " ++
  "[--no-comparator | --challenge-not-built <reason>] [--no-stats-page] " ++
  "[--reproducible] [--verbose]"

/-- Parse the command line. -/
partial def parseOptions : List String → Options → Except String Options
  | [], opts => .ok opts
  | "--data" :: file :: args, opts => parseOptions args { opts with data := some file }
  | "--root" :: dir :: args, opts => parseOptions args { opts with root := some dir }
  | "--title" :: text :: args, opts => parseOptions args { opts with title := some text }
  | "--graphviz" :: program :: args, opts =>
    parseOptions args { opts with graphviz := some program }
  | "--no-graph-layout" :: args, opts => parseOptions args { opts with graphviz := none }
  | "--no-comparator" :: args, opts => parseOptions args { opts with compare := false }
  | "--challenge-not-built" :: why :: args, opts =>
    parseOptions args { opts with challengeNotBuilt := some why }
  | "--output" :: dir :: args, opts =>
    parseOptions args { opts with rest := opts.rest ++ #["--output", dir] }
  | flag :: args, opts =>
    if flag ∈ ["--data", "--root", "--title", "--output", "--graphviz", "--challenge-not-built"] then
      .error s!"missing value after {flag}"
    else if flag ∈ [Informal.Commands.noStatsPageFlag, Informal.PreviewManifest.reproducibleFlag,
        "--verbose"] then
      parseOptions args { opts with rest := opts.rest.push flag }
    else .error s!"unknown code-site option '{flag}'"

/-- Read the data and each module's source file under `root`. -/
def load (data root : FilePath) : IO (Project × Std.HashMap Lean.Name String) := do
  let project ← match Project.parse (← IO.FS.readFile data) with
    | .ok p => pure p
    | .error e => throw <| IO.userError s!"{data}: {e}"
  let mut sources : Std.HashMap Lean.Name String := {}
  for m in project.modules do
    unless m.source.isEmpty do
      if let some text ← (try some <$> IO.FS.readFile (root / m.source) catch _ => pure none) then
        sources := sources.insert m.module text
  return (project, sources)

/-- Generate the site of the data at `data` for the project at `root`; `args` are the
generator's own flags. Without `compare` the headline's comparison is left out; with
`challengeNotBuilt?` too, and the headline says why (`headlineOf?`). -/
def generate (data root : FilePath) (title? : Option String) (args : List String)
    (graphviz : Option String := some "dot") (compare : Bool := true)
    (challengeNotBuilt? : Option String := none) : IO UInt32 := do
  let root ← try IO.FS.realPath root catch _ => pure root
  let (project, sources) ← load data root
  let project := { project with title := title? <|> project.title }
  let hovers : Lean.NameMap Hover := project.hovers.foldl (init := {}) fun acc h => acc.insert h.name h
  let ctx : RenderContext := { hovers, sourceBase? := ← sourceBaseOf? root }
  let state := stateOf project sources.get? ctx
  let known : Lean.NameSet := project.modules.foldl (init := {}) fun acc m =>
    m.declarations.foldl (fun acc d => acc.insert d.name) acc
  let headline? ← match challengeNotBuilt? with
    | some why => headlineOf? root project known (notBuilt? := some why)
    | none => if compare then headlineOf? root project known else pure none
  let model ← modelOf root project state headline?
  let title := titleOf root project model.stats.identity
  Informal.PreviewManifest.blueprintMainWithPreviewData (documentOf title project graphviz sources.get?) args
    (extensionImpls := by exact extension_impls%) (model := model)
    -- side-by-side cards without highlighted declaration sources: the excerpts come from the data
    (config := Informal.PreviewManifest.withSideBySideDefaultStyle {})
    (sidebar? := some { homeLabel := "Home" })

/-- `vbp code-site` (see the module docstring). -/
def main (args : List String) : IO UInt32 := do
  match args with
  | ["--help"] | ["-h"] => IO.println usage; return 0
  | _ =>
  match parseOptions args {} with
  | .error e => IO.eprintln e; IO.eprintln usage; return 2
  | .ok { data := none, .. } => IO.eprintln "missing --data <file>"; IO.eprintln usage; return 2
  | .ok { data := some data, root, title, graphviz, compare, challengeNotBuilt, rest } =>
    let root := root.getD (← IO.currentDir)
    try generate data root title rest.toList graphviz compare challengeNotBuilt
    catch e => IO.eprintln s!"vbp code-site: {e}"; return 1

end Informal.CodeSite
