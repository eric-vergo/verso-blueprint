/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

import VersoBlueprint.Graph

/-!
Graph layout at build time.

The dependency graph's page lays out each view in the browser (Graphviz compiled to WebAssembly)
when it is first shown, which on a graph of a few thousand nodes keeps the page busy for seconds.
A generator that has Graphviz's `dot` program can instead lay every view out once, while the site
is built: `layoutVariants` runs `dot -Tdot` on each variant's DOT source, giving the same graph
with every position filled in. The graph block puts each layout beside the graph data as raw text
(`<script type="text/vnd.graphviz" class="bp-graph-layout" data-variant="<key>">`), and the page
draws a laid-out view with Graphviz's `nop2` engine, which only renders the given positions.

A layout is attached only for the variant's own options; a reader who changes the direction or
the packing gets the browser's layout as before. A variant that is too large or whose layout does
not finish in time is left to the browser, with a message saying so.
-/

namespace Informal.GraphLayout

open Informal.Graph

/-- How to lay graphs out at build time. -/
structure Config where
  /-- The Graphviz `dot` program (a path, or a name looked up on `PATH`). -/
  program : String := "dot"
  /-- Variants with more nodes than this are left to the browser. -/
  maxNodes : Nat := 6000
  /-- How long one layout may take, in milliseconds. -/
  timeoutMs : Nat := 120000
  /-- How many layouts run at once. -/
  jobs : Nat := 4
deriving Inhabited, Repr

/-- The number of node statements in a DOT source written by `Graph.toDot`. -/
def nodeCount (dot : String) : Nat :=
  (dot.splitOn " [id=\"").length - 1

/-- Whether `program` runs and reports a Graphviz version. -/
def available (program : String) : IO Bool := do
  try
    let out ← IO.Process.output { cmd := program, args := #["-V"], stdin := .null }
    return out.exitCode == 0 && (out.stderr ++ out.stdout).startsWith "dot - graphviz"
  catch _ => return false

/-- Lay one DOT source out with `program -Tdot`: the laid-out source, or why not. -/
def layoutDot (cfg : Config) (dot : String) : IO (Except String String) := do
  IO.FS.withTempFile fun h input => do
    h.putStr dot
    h.flush
    let child ← IO.Process.spawn {
      cmd := cfg.program, args := #["-Tdot", input.toString],
      stdin := .null, stdout := .piped, stderr := .piped }
    let out ← IO.asTask (prio := .dedicated) child.stdout.readToEnd
    let err ← IO.asTask (prio := .dedicated) child.stderr.readToEnd
    let start ← IO.monoMsNow
    let mut code? ← child.tryWait
    while code?.isNone do
      if (← IO.monoMsNow) - start > cfg.timeoutMs then
        child.kill
        let _ ← child.wait
        return .error s!"not finished within {cfg.timeoutMs / 1000} s"
      IO.sleep 5
      code? ← child.tryWait
    let code := code?.getD 1
    let text ← IO.ofExcept (← IO.wait out)
    -- the layout is written into the page as a script element's raw text
    if (text.toLower.splitOn "</script").length > 1 then
      return .error "the layout contains `</script`"
    if code == 0 && !text.isEmpty then return .ok text
    let msg := (← IO.ofExcept (← IO.wait err)).trimAscii.toString
    return .error s!"exit code {code}{if msg.isEmpty then "" else ": " ++ msg}"

/-- Draw a laid-out DOT source (`layoutDot`'s output) as SVG with `program -Knop2 -Tsvg`, which
renders the given positions: the `<svg>` element, or why not. A page shows it before its scripts
have drawn the interactive graph. -/
def prerender (cfg : Config) (layout : String) : IO (Except String String) := do
  IO.FS.withTempFile fun h input => do
    h.putStr layout
    h.flush
    let out ← IO.Process.output {
      cmd := cfg.program, args := #["-Knop2", "-Tsvg", input.toString], stdin := .null }
    if out.exitCode != 0 then return .error s!"exit code {out.exitCode}: {out.stderr.trimAscii}"
    match out.stdout.splitOn "<svg" with
    | _ :: rest@(_ :: _) => return .ok ("<svg" ++ "<svg".intercalate rest)
    | _ => return .error "no <svg> element in the output"

/-- Lay out every variant of `variants` that is small enough: the layouts by variant key, and a
message for each variant left to the browser. -/
def layoutVariants (cfg : Config) (variants : Array GraphRenderVariant) :
    IO (Array (String × String) × Array String) := do
  let mut layouts := #[]
  let mut skipped := #[]
  let todo := variants.filter fun v => nodeCount v.dot ≤ cfg.maxNodes
  for v in variants do
    if nodeCount v.dot > cfg.maxNodes then
      skipped := skipped.push s!"{v.label}: {nodeCount v.dot} nodes, more than {cfg.maxNodes}"
  let jobs := max cfg.jobs 1
  let mut i := 0
  while i < todo.size do
    let batch := todo.extract i (i + jobs)
    let tasks ← batch.mapM fun v => IO.asTask (prio := .dedicated) (layoutDot cfg v.dot)
    for v in batch, t in tasks do
      match ← IO.wait t with
      | .ok (.ok text) => layouts := layouts.push (v.key, text)
      | .ok (.error why) => skipped := skipped.push s!"{v.label}: {why}"
      | .error e => skipped := skipped.push s!"{v.label}: {e}"
    i := i + jobs
  return (layouts, skipped)

end Informal.GraphLayout
