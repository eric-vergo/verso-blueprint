/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

import VersoManual
import VersoBlueprint.Git
import VersoBlueprint.LeanSourceAnchor
import VersoBlueprint.Lib.ExtensionDecode
import VersoBlueprint.RuntimeCache

/-!
Links from the text to files of the project's repository, at the commit the site is built from.

`{repoFile "notes/engine.md"}[the engine guide]` links its text to `notes/engine.md` in the
repository, as the source links of Lean declarations do: on GitHub, at the commit of the checkout
the site is generated from (`blob/<commit>/<path>`). A path may end with a fragment
(`"Main.lean#L10-L20"`). The path is relative to the root of the repository and must name a file or
folder there that the repository tracks when the chapter is elaborated (a file Git does not track
has no address at the commit); in the link it is percent-encoded. A site generated outside a Git
checkout with a GitHub `origin` shows the text without a link.
-/

namespace Informal.RepoFile

open Lean Elab Verso Doc Elab ArgParse

/-- The arguments of `repoFile`: a path relative to the repository's root, with an optional
fragment. -/
structure RepoFileArgs where
  path : String

instance {m} [Monad m] [MonadError m] : FromArgs RepoFileArgs m where
  fromArgs := RepoFileArgs.mk <$> .positional `path (ValDesc.string.as "repository path")

/-- A path and its fragment: `"Main.lean#L10"` gives `("Main.lean", "#L10")`. -/
def splitFragment (path : String) : String × String :=
  match path.splitOn "#" with
  | file :: rest@(_ :: _) => (file, "#" ++ "#".intercalate rest)
  | _ => (path, "")

/-- Why a path cannot name a file of the repository, if it cannot: it must be relative and stay
inside the repository. -/
def pathProblem? (file : String) : Option String :=
  if file.isEmpty then some "the path is empty"
  else if file.startsWith "/" then some "the path is absolute; give it relative to the repository's root"
  else if (file.splitOn "/").contains ".." then some "the path leaves the repository (`..`)"
  else none

/-- The address of `path` in the repository of the checkout that contains `dir`, at its current
commit: `none` outside a Git checkout with a GitHub `origin`. -/
def href? (dir : System.FilePath) (path : String) : IO (Option String) := do
  let some root ← RuntimeCache.cachedGitRoot? dir (Git.toplevelAt? dir) | return none
  let some info ← RuntimeCache.cachedGitRepoInfo? root (Git.repositoryInfoAtRoot? root)
    | return none
  let (file, fragment) := splitFragment path
  let path := LeanSourceAnchor.percentEncode file
  return some s!"{info.githubUrl}/blob/{info.commit}/{path}{fragment}"

/-- Whether the Git repository at `root` tracks `path` (a file, or a folder with a tracked file). -/
def tracked (root : System.FilePath) (path : String) : IO Bool := do
  let out ← IO.Process.output
    { cmd := "git", args := #["-C", root.toString, "ls-files", "--error-unmatch", "--", path] }
  return out.exitCode == 0

inline_extension Inline.repoFile (path : String) where
  data := toJson path
  traverse _id _data _contents := pure none
  toTeX := some fun go _id _data contents => contents.mapM go
  toHtml :=
    open Verso.Output.Html in
    some fun go _id data contents => do
      let some path ← Informal.ExtensionDecode.decode? (α := String) data
          (fun err => s!"Malformed data in Inline.repoFile ({err})")
        | contents.mapM go
      let inner ← contents.mapM go
      match ← href? (← IO.currentDir) path with
      | some href => pure {{<a class="bp_repo_file" href={{href}}>{{inner}}</a>}}
      | none => pure (.seq inner)

end Informal.RepoFile

open Lean Elab Verso Doc Elab in
/-- `{repoFile "path"}[text]` links `text` to a file of the project's repository at the commit the
site is built from (`Informal.RepoFile`). -/
@[role]
def repoFile : RoleExpanderOf Informal.RepoFile.RepoFileArgs
  | { path }, contents => do
    let (file, _) := Informal.RepoFile.splitFragment path
    if let some problem := Informal.RepoFile.pathProblem? file then
      throwError "repoFile: {problem}: {path}"
    let source ← IO.FS.realPath (← getFileName)
    let dir := source.parent.getD "."
    let top? ← Informal.Git.toplevelAt? dir
    let root := top?.getD (← IO.currentDir)
    unless ← (root / file).pathExists do
      throwError "repoFile: {file} is not in the repository at {root}"
    -- a file the repository does not track has no address at the commit
    if top?.isSome then
      unless ← Informal.RepoFile.tracked root file do
        throwError "repoFile: {file} is not tracked by the repository at {root}: add it to Git, \
          or link to a file that is"
    let content ← contents.mapM elabInline
    ``(Verso.Doc.Inline.other (Informal.RepoFile.Inline.repoFile $(quote path)) #[$content,*])
