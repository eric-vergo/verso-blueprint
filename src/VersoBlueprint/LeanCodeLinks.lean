/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

import Lean.Server.References
import VersoManual
import VersoBlueprint.Git
import VersoBlueprint.LeanSourceAnchor
import VersoBlueprint.Process
import VersoBlueprint.Resolve
import VersoBlueprint.RuntimeCache
import VersoBlueprint.Stats.Collect
import VersoBlueprint.TraversalIndex

/-!
Links from the names in highlighted Lean code to the places where the site, or the project's
repository, shows their declarations.

Verso links a constant of highlighted Lean code to its documentation, when the document includes
its docstring, and to its definition in a Lean block of the document (`LinkTargets`). A Blueprint
site has two more places for the project's own declarations, which the Lean code that Verso
renders on the site's pages (the Lean blocks and inline Lean code of the running text) offers after
Verso's; the Blueprint's own components (the Lean column, code panels, previews) render their code
with links of their own:

* **the site**: a declaration that a Blueprint node names (`(lean := "…")`) links to the place the
  site gives it (`TraversalIndex.ExternalDeclAnchors.declHref?`): the Lean row of that node that
  shows it, else the node itself (a declaration attached to a proof, in a layout that shows no row
  of it) (`siteTargets`);
* **the repository**: a declaration of a project module of the document's environment (the modules
  the project statistics list, `Stats.ProjectStats.modules`) links to its lines in that module's
  source file on GitHub at the commit the site is built from (`SourceIndex.load`). The lines are
  read from the `.ilean` file Lake writes beside the compiled module. Only the environment's modules
  are read, so a declaration of the same name in a module the document does not import (the
  challenge of a Comparator challenge, say) is never the target; a name that two of them declare
  anyway gets no link. A file that Git does not track, or that differs from that commit, has no
  address there, so its declarations get no such link; neither do those of an `.ilean` file of a
  format this build does not know.

A name with both gets both: the site's row is followed on a click, the source is offered in the
hover's list of links. A name with neither (a declaration of Lean, of a dependency, or a local
variable) stays unlinked.
-/

namespace Informal.LeanCodeLinks

open Lean
open Verso.Genre.Manual

/-! ## The site -/

/-- The places of the site, by declaration name: each declaration a node names, linked to its
place as a declaration of the first node that names it (nodes in the order of their labels,
statements' declarations before proofs'; `TraversalIndex.ExternalDeclAnchors.declHref?`). -/
def siteTargets (state : TraverseState) : Std.HashMap Name String := Id.run do
  let some dom := TraversalIndex.Nodes.domain? state | return {}
  let mut nodes : Array (Name × Json) := #[]
  for (key, obj) in dom.objects do
    let label := (obj.data.getObjValAs? Name "label").toOption.getD key.toName
    nodes := nodes.push (label, obj.data)
  nodes := nodes.qsort (·.1.toString < ·.1.toString)
  let declsOf (data : Json) (field : String) : Array Name :=
    match data.getObjValAs? (Array Json) field with
    | .ok refs => refs.filterMap fun r => (r.getObjValAs? Name "canonical").toOption
    | .error _ => #[]
  let mut out : Std.HashMap Name String := {}
  for field in ["externalRefs", "proofExternalRefs"] do
    for (label, data) in nodes do
      for decl in declsOf data field do
        if out.contains decl then continue
        if let some href := TraversalIndex.ExternalDeclAnchors.declHref? state label decl then
          out := out.insert decl href
  return out

/-! ## The repository -/

/-- The project's declarations by name (as Lean prints it), each with the address of its lines in
the repository at the commit the site is built from. -/
structure SourceIndex where
  hrefs : Std.HashMap String String := {}
deriving Inhabited

/-- The files of the repository at `gitRoot` that Git tracks and that are as they are at its
current commit, relative to its root. -/
private def committedFiles (gitRoot : System.FilePath) : IO (Std.HashSet String) := do
  let lines (args : Array String) : IO (Option (Array String)) := do
    let out ← IO.Process.output { cmd := "git", args := #["-C", gitRoot.toString] ++ args }
    if out.exitCode != 0 then return none
    return some ((out.stdout.splitOn "\x00").filter (!·.isEmpty) |>.toArray)
  let some tracked ← lines #["ls-files", "-z"] | return {}
  let some changed ← lines #["diff", "--name-only", "-z", "HEAD", "--"] | return {}
  let changed := Std.HashSet.ofArray changed
  return Std.HashSet.ofArray (tracked.filter (!changed.contains ·))

/-- The path of `path` relative to `root`, when it is inside it. -/
private def relativeTo? (root path : System.FilePath) : Option String :=
  let r := root.toString
  let r := if r.endsWith "/" then r else r ++ "/"
  if path.toString.startsWith r then some (path.toString.drop r.length).toString else none

/-- A GitHub line fragment for 0-based start and end lines: `#L3` or `#L3-L7`. -/
def lineFragment (start stop : Nat) : String :=
  if stop > start then s!"#L{start + 1}-L{stop + 1}" else s!"#L{start + 1}"

/-- The version of the `.ilean` format that the Lean this build runs on writes; a file of another
version may place its ranges differently, so it is not read. -/
def ileanVersion : Nat :=
  ({ module := .anonymous, directImports := #[], references := {}, decls := {} } :
    Lean.Server.Ilean).version

/-- The declarations of one `.ilean` file: each declaration's name with the 0-based first and last
line of its range; an error when its version is not `ileanVersion` or it does not read. -/
def ileanDecls (json : Json) : Except String (Array (String × Nat × Nat)) := do
  let version ← json.getObjValAs? Nat "version"
  unless version == ileanVersion do
    throw s!"its format is version {version}, and this build reads version {ileanVersion}"
  let .obj fields ← json.getObjVal? "decls" | throw "it has no declarations"
  return fields.toList.foldl (init := #[]) fun acc (name, v) =>
    match (v.getArrVal? 0 >>= (·.getNat?)), (v.getArrVal? 2 >>= (·.getNat?)) with
    | .ok start, .ok stop => acc.push (name, start, stop)
    | _, _ => acc

/-- The index of the declarations of some modules: each module's address (its file at the
commit, or `none` when it has none) with its `.ilean` content. A name that two of them declare is
left out, since which one a mention means cannot be told; a module whose `.ilean` does not read
contributes nothing, and the result says why. -/
def SourceIndex.ofModules (modules : Array (Name × Option String × Json)) :
    SourceIndex × Array String := Id.run do
  let mut hrefs : Std.HashMap String String := {}
  let mut seen : Std.HashSet String := {}
  let mut clashes : Std.HashSet String := {}
  let mut problems := #[]
  for (module, base?, json) in modules do
    match ileanDecls json with
    | .error why => problems := problems.push s!"{module}: {why}"
    | .ok decls =>
      for (name, start, stop) in decls do
        if seen.contains name then
          clashes := clashes.insert name
        else
          seen := seen.insert name
          if let some base := base? then
            hrefs := hrefs.insert name (base ++ lineFragment start stop)
  return ({ hrefs := clashes.fold (init := hrefs) fun m n => m.erase n }, problems)

/-- The source index of the document traversed into `state`: the project modules of its
environment (`Stats.ProjectStats.modules`, with their source files) whose `.ilean` file is in one
of the project's library folders. Empty when the state has no project statistics or the project is
not a Git checkout with a GitHub `origin`; the second component lists the `.ilean` files that were
not read, and why. -/
def SourceIndex.load (state : TraverseState) : IO (SourceIndex × Array String) := do
  let modules : Array Stats.ModuleStats :=
    ((TraversalIndex.RenderOverviews.field? state `stats "modules").bind
      (fromJson? · |>.toOption)).getD #[]
  if modules.isEmpty then return ({}, #[])
  let layout : Stats.WorkspaceLayout :=
    ((TraversalIndex.RenderOverviews.field? state `stats "layout").bind
      (fromJson? · |>.toOption)).getD {}
  let root ← Stats.projectRoot layout.projectRoot
  let root ← try IO.FS.realPath root catch _ => pure root
  let some gitRoot ← RuntimeCache.cachedGitRoot? root (Git.toplevelAt? root) | return ({}, #[])
  let some info ← RuntimeCache.cachedGitRepoInfo? gitRoot (Git.repositoryInfoAtRoot? gitRoot)
    | return ({}, #[])
  let gitRoot ← try IO.FS.realPath gitRoot catch _ => pure gitRoot
  let committed ← committedFiles gitRoot
  let libraryDirs := (layout.libraryDirs.push ".lake/build/lib/lean").toList.eraseDups
  let mut read := #[]
  for m in modules do
    let files := libraryDirs.map fun (dir : String) => modToFilePath (root / dir) m.name "ilean"
    let some file ← files.findM? (·.pathExists) | continue
    let text ← try IO.FS.readFile file catch _ => continue
    let .ok json := Json.parse text | continue
    let base? := (relativeTo? gitRoot (root / m.path)).bind fun path =>
      if committed.contains path then
        some s!"{info.githubUrl}/blob/{info.commit}/{LeanSourceAnchor.percentEncode path}"
      else none
    read := read.push (m.name, base?, json)
  return SourceIndex.ofModules read

/-! ## Link targets -/

/-- Verso's link targets with the site's rows and the repository's sources added for constants. -/
def withBlueprintTargets (base : Verso.Code.LinkTargets TraverseContext)
    (site : Std.HashMap Name String) (sources : SourceIndex) :
    Verso.Code.LinkTargets TraverseContext :=
  base ++ {
    const := fun x _ =>
      let here := (site.get? x).toArray.map fun href =>
        { shortDescription := "Blueprint", description := s!"{x} in the Blueprint", href }
      let there := (sources.hrefs.get? x.toString).toArray.map fun href =>
        { shortDescription := "source",
          description := s!"Source of {x} at the commit this site is built from", href }
      here ++ there
  }

/-- The render configuration with these targets added to Verso's for every page it writes. -/
def withLinks (config : RenderConfig) (sources : SourceIndex) : RenderConfig :=
  let base := config.linkTargets
  { config with
    linkTargets := fun state remotes =>
      withBlueprintTargets (base state remotes) (siteTargets state) sources }

/-! ## Hovers of a page read from a file -/

/-- The script that assigns the site's hover table (`-verso-docs.json`) to `versoDocsData`, for a
page opened from a file, which cannot fetch it. -/
def docsScriptName : String := "-verso-docs.js"

/-- Write `-verso-docs.js` beside the hover table of the site in `dir`, if it has one. -/
def writeDocsScript (dir : System.FilePath) : IO Unit := do
  let json := dir / "-verso-docs.json"
  unless ← json.pathExists do return
  let text ← IO.FS.readFile json
  -- the table is JSON written by the generator: as a script it is the same value
  match Json.parse text with
  | .ok j => IO.FS.writeFile (dir / docsScriptName) s!"window.versoDocsData = {j.compress};\n"
  | .error _ => pure ()

/-- What Verso's hover script reads its table with (`Verso.Code.fetchDocsJson`), unchanged over
HTTP; a page opened from a file loads `-verso-docs.js` instead, as a script, since a page there may
not fetch. -/
def loadDocsJs : String :=
  "(window.location.protocol === \"file:\"
      ? new Promise((resolve, reject) => {
          const script = document.createElement(\"script\");
          script.src = new URL(\"" ++ docsScriptName ++ "\", document.baseURI).href;
          script.onload = () => window.versoDocsData && typeof window.versoDocsData === \"object\"
            ? resolve(window.versoDocsData)
            : reject(new Error(\"" ++ docsScriptName ++ " assigned no hover table\"));
          script.onerror = () => reject(new Error(\"could not load " ++ docsScriptName ++ "\"));
          document.head.appendChild(script);
        })
      : " ++ Verso.Code.fetchDocsJson ++ ")"

end Informal.LeanCodeLinks
