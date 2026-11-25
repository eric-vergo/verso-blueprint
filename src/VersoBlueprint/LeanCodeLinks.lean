/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

import VersoManual
import VersoBlueprint.BuildRecord
import VersoBlueprint.Git
import VersoBlueprint.LeanSourceAnchor
import VersoBlueprint.Process
import VersoBlueprint.Resolve
import VersoBlueprint.RuntimeCache
import VersoBlueprint.TraversalIndex

/-!
Links from the names in highlighted Lean code to the places where the site, or the project's
repository, shows their declarations.

Verso links a constant of highlighted Lean code to its documentation, when the document includes
its docstring, and to its definition in a Lean block of the document (`LinkTargets`). A Blueprint
site has two more places for the project's own declarations, which the links of every Lean block
of the site's pages (the running text's and the Blueprint's own) offer after Verso's:

* **the site**: a declaration that a Blueprint node names (`(lean := "…")`) is shown in a Lean row
  of that node, and its name links there (`siteTargets`);
* **the repository**: a declaration of the project, found in the `.ilean` files Lake writes for the
  project's own modules (under `.lake/build/lib/lean`), links to its lines in the source file on
  GitHub at the commit the site is built from (`SourceIndex.load`). A file that Git does not track,
  or that differs from that commit, has no address there, so its declarations get no such link.

A name with both gets both: the site's row is followed on a click, the source is offered in the
hover's list of links. A name with neither (a declaration of Lean, of a dependency, or a local
variable) stays unlinked.
-/

namespace Informal.LeanCodeLinks

open Lean
open Verso.Genre.Manual

/-! ## The site -/

/-- The Lean rows of the site, by declaration name: each declaration a node names, linked to the
first row that shows it (nodes in the order of their labels, statement rows before proof rows). -/
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
        if let some href := Resolve.resolveRenderedExternalDeclHref? state label decl then
          out := out.insert decl href
  return out

/-! ## The repository -/

/-- The project's declarations by name (as Lean prints it), each with the address of its lines in
the repository at the commit the site is built from. -/
structure SourceIndex where
  hrefs : Std.HashMap String String := {}
deriving Inhabited

/-- The `.ilean` files below `dir`. -/
private def ileanFiles (dir : System.FilePath) : IO (Array System.FilePath) := do
  unless ← dir.isDir do return #[]
  let files ← dir.walkDir
  return files.filter (·.extension == some "ilean")

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

/-- The declarations of one `.ilean` file: its module and each declaration's name with the 0-based
first and last line of its range. -/
def ileanDecls (json : Json) : Option (Name × Array (String × Nat × Nat)) := do
  let module ← (json.getObjValAs? Name "module").toOption
  let .obj fields ← (json.getObjVal? "decls").toOption | none
  let out := fields.toList.foldl (init := #[]) fun acc (name, v) =>
    match (v.getArrVal? 0 >>= (·.getNat?)), (v.getArrVal? 2 >>= (·.getNat?)) with
    | .ok start, .ok stop => acc.push (name, start, stop)
    | _, _ => acc
  return (module, out)

/-- The source index of the project at `root` (the working directory of a generator): empty
outside a Git checkout with a GitHub `origin`. -/
def SourceIndex.load (root : System.FilePath) : IO SourceIndex := do
  let root ← try IO.FS.realPath root catch _ => pure root
  let some gitRoot ← RuntimeCache.cachedGitRoot? root (Git.toplevelAt? root) | return {}
  let some info ← RuntimeCache.cachedGitRepoInfo? gitRoot (Git.repositoryInfoAtRoot? gitRoot)
    | return {}
  let gitRoot ← try IO.FS.realPath gitRoot catch _ => pure gitRoot
  let committed ← committedFiles gitRoot
  let mut hrefs : Std.HashMap String String := {}
  for file in ← ileanFiles (root / ".lake" / "build" / "lib" / "lean") do
    let some json ← (try some <$> IO.ofExcept (Json.parse (← IO.FS.readFile file))
        catch _ => pure none) | continue
    let some (module, decls) := ileanDecls json | continue
    if decls.isEmpty then continue
    let some source ← Stats.tracedSource? root [] module | continue
    let some path := relativeTo? gitRoot (root / source) | continue
    unless committed.contains path do continue
    let base := s!"{info.githubUrl}/blob/{info.commit}/{LeanSourceAnchor.percentEncode path}"
    for (name, start, stop) in decls do
      unless hrefs.contains name do
        hrefs := hrefs.insert name (base ++ lineFragment start stop)
  return { hrefs }

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
