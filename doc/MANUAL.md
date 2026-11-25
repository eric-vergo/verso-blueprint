# Blueprint Manual

This document is the current reference for Blueprint authoring and rendering.
For documented Lean, generated-data, and browser integration APIs, see
[`API.md`](./API.md).

If you are starting a first project, read
[project_template/README.md](../project_template/README.md) and
[GETTING_STARTED.md](./GETTING_STARTED.md) before this manual.

## Contents

- [Mental Model](#mental-model)
- [Labels and Node Identity](#labels-and-node-identity)
- [Minimal Project Shape](#minimal-project-shape)
- [The Blueprint Top-Level File](#the-blueprint-top-level-file)
- [Parts, Chapters, and Numbers](#parts-chapters-and-numbers)
- [A First Chapter](#a-first-chapter)
- [Core Block Forms](#core-block-forms)
- [Connecting Blocks to Lean](#connecting-blocks-to-lean)
- [Attached Rust Code](#attached-rust-code)
- [Math, TeX, and external markup](#math-tex-and-external-markup)
- [Groups, Authors, and Metadata](#groups-authors-and-metadata)
- [Rendering Surface](#rendering-surface)
- [Metadata Export and Preview Data](#metadata-export-and-preview-data)
- [Reusing Blueprint Nodes and Previews](#reusing-blueprint-nodes-and-previews)
- [Blueprint APIs](#blueprint-apis)
- [The Generator Entry Point](#the-generator-entry-point)
- [Sites from Compiled Code](#sites-from-compiled-code)
- [Blueprint Options](#blueprint-options)
- [Experimental Widget](#experimental-widget)
- [Current Limits](#current-limits)

## Mental Model

A Blueprint project usually owns three things:

- chapter modules containing the mathematical content
- a Blueprint top-level file that assembles the document
- a generator entry point that renders the site

The Blueprint top-level file is often called `Contents.lean` in existing
projects, but the filename is not special. What matters is that one module
assembles the chapters and chooses the rendered overview pages.

## Labels and Node Identity

Blueprint nodes are identified by labels chosen by the author.

Examples:

- statement labels such as `addition_spec` and `addition_right_identity`
- group labels such as `addition_core`
- author ids such as `jason`

These identifiers are used by:

- `{uses "addition_spec"}[]` dependency references
- `{bpref "addition_spec"}[]` link-only references
- labeled inline Lean code blocks
- labeled inline Rust code blocks
- `tex` and `md` code blocks carrying external markup source
- `@[blueprint]` or `@[blueprint "label"]` on compiled Lean declarations
- summary and graph nodes
- preview lookup and exported metadata

Choose labels early and treat them as stable project identifiers.

A statement and its proof may live in different modules. The proof module must
import the statement module and use the same label in `:::proof`. A later module
can also import the statement and attach Lean code, Rust code, or external markup
to its label. When those modules are imported together, Blueprint combines their
contributions into one node, preserving statement and proof dependencies
separately. Include the relevant chapter modules in the top-level document to
render their content.

Two modules that independently author a statement, proof, or explicit
placeholder for the same label are still duplicates. Bodyless attribute
associations are independent facts: several modules may associate declarations
with one label and those facts compose. Likewise, two sibling modules that each
supply a proof body for the same imported statement conflict, even if their
proof text is identical. Re-exporting a shared module does not create a duplicate.

The merge rules are:

| Contributions | Result |
| --- | --- |
| Statement, proof, and attachments with a shared label origin | Combine into one node |
| Independent authored introductions of the same label | Error |
| Two statement bodies or two proof bodies | Error, even when their text is identical |
| Dependencies without a body | Add edges without replacing the body or its authored kind |
| Duplicate dependency metadata | Deduplicate; manual metadata takes precedence over automatic metadata |
| Different intents at the same authority | Error, including automatic disagreements hidden by a manual override; neither import order nor spelling order selects the meaning |
| Repeated scalar metadata (`parent`, `owner`, `priority`, `effort`, `pr_url`, `issue_url`) | Accept equal values; reject unequal values |
| Tags | Unique union |
| External Lean associations | Union by canonical declaration, preferring resolved information |
| Literate Lean code | Keep every distinct block, its declarations, and its code preview |
| Attribute docstrings | A first attribute may supply an initial statement from its declaration docstring; later attributes attach code and dependencies only |
| Rust code | At most one attachment |
| External markup | At most one attachment per language and slot |

A rejected directive leaves Blueprint registrations, inferred dependencies, code
attachments, numbering, and provenance unchanged, including registrations made
while elaborating its body. Errors also close the directive scope, so a valid
following directive can still elaborate. Nested statement/proof directives are
not supported. Lean declarations elaborated inside a failed directive and the
reported diagnostics remain available to Lean's normal error recovery.

A bodyless placeholder can later acquire an explicit statement or proof body.
When both the placeholder and filled chapter are included, previews and links
select the filled body regardless of chapter order. The selected occurrence
also supplies that facet's source location and original-source provenance.
Inline references prefer a nonempty statement, then a nonempty proof, then a
code-backed facet, then external markup when available. Code-only declarations
use their standard statement preview key even when an external witness is blank
or external-markup rendering is disabled. A placeholder can
still be a link target without offering a hover preview. Imported nodes that
have no document occurrence display their authored label rather than a number.
This numbering rule also applies to dependency panels, code headings, and previews.
The mathematical kind is independent of which chapters are rendered: including
only a theorem's proof still gives it a caption such as `Proof for Theorem 1`.
Custom reference text is preserved in both HTML and TeX.

A statement's Lean status and declaration tooltip cover both external associations
and literate code. An incomplete external declaration therefore remains visible
in the status even when an associated literate block is complete. Each code
panel also reports the declarations it contains. When both sources name the same
canonical declaration, the heading summary uses its literate declaration facts once.
Omitting a formalization chapter keeps its declarations and status in statement
headings and summaries, including any `sorry`. It removes that chapter's code
panels, local links, and code previews from the generated document.

An explicit statement kind belongs to the author: attaching a Lean theorem to an informal
lemma keeps the informal node a lemma. For a Lean-only node without an authored
kind, a theorem association takes precedence over a definition association, whether
the declarations come from attributes or literate Lean blocks. Dependencies alone
do not count as an informal statement or proof in coverage summaries.

For conflicting dependency intents, make the manual declarations agree or remove
the redundant declaration. Attribute `uses` and `proofUses` entries are manual
with `regular` intent. An inferred edge from `autoDeps` can coexist with an
explicit prose edge, whose metadata takes precedence.

Precedence chooses the metadata to display; it does not suppress conflicts within
an authority. For example, automatic `regular` and automatic `technical` declarations
for one dependency conflict even if a manual `auxiliary` declaration is also present.
Reordering these declarations never repairs the conflict.
This also applies within a single Verso docstring and between its `{uses}`
roles and the attribute's `uses` entries. Repeating a dependency with a
different intent is an error, not a first-declaration-wins override.

For example, split the source into these three modules:

```lean
-- Project/Statements.lean
import VersoBlueprint
open Verso.Genre Informal

#doc (Manual) "Statements" =>

:::theorem "main_result"
The statement of the main result.
:::
```

```lean
-- Project/Proofs.lean
import Project.Statements
open Verso.Genre Informal

#doc (Manual) "Proofs" =>

:::proof "main_result"
The proof of the main result.
:::
```

```lean
-- Project/Blueprint.lean
import Project.Statements
import Project.Proofs
open Verso.Genre

#doc (Manual) "Blueprint" =>

{include 0 Project.Statements}
{include 0 Project.Proofs}

{blueprint_summary}
```

Imports supply semantic visibility; `include` renders chapter content. Import
later Lean attachment modules before defining the generator. The standard
Blueprint generator captures the final semantic data and resolves chapter labels
against it during rendering, so later dependencies and metadata appear in headers,
previews, and overview pages, including documents without a graph.

Use `uses` when the current node depends on the target and should add an edge to
the graph and dependency summaries. Use `bpref` when prose should link to a
Blueprint node without registering that relationship as a dependency.
References are checked during traversal against the captured project, so forward
references work. A known node omitted from the document falls back to its authored
label; an unknown label is an error. Reference-only documents also require the
project's rendering model. In preview-enabled pages, a rendered node whose preview
body is unavailable still has its ordinary link and title, but no hover trigger.
This also applies to references and relation panels inside cached preview bodies.
Dependency metadata can still describe unresolved graph edges, which appear in
graph diagnostics; it does not create a prose link.

Chapter and section tags are document targets, not Blueprint node labels. Declare
`tag := "chapter-tag"` in the destination's `%%%` metadata and link with
`{ref "chapter-tag"}[Chapter title]`. Ordinary Verso `ref` requires visible link
text; an empty `[]` does not generate a title. Other document targets use their
own reference domain, rather than adding nodes to the Blueprint graph.

For dependencies that do not have a natural sentence-level reference, use the
block option `(uses := "label1, label2")`. Inline uses can carry
`(intent := "auxiliary")` or `(intent := "technical")`; metadata-only uses use
the parallel `(uses_intent := "...")` option.

Dependency use metadata options are string-valued:

- `intent` / `uses_intent`: one of `"regular"`, `"auxiliary"`, or
  `"technical"`; omitted values default to `"regular"`
- `origin` / `uses_origin`: one of `"manual"` or `"automatic"`; omitted values
  default to `"manual"`

These metadata options are accepted only by dependency-bearing uses: inline
`uses` roles and block-level `(uses := ...)` entries. `bpref` is link-only and
does not accept `origin` or `intent`.

Rendered statement and proof headers include separate `uses` chips that preview
their own declared dependencies. Statement-level `(uses := ...)` options and
inline statement uses stay on the statement chip; proof-level options and inline
proof uses stay on the proof chip for the same label. Non-default dependency
metadata such as `automatic`, `auxiliary`, and `technical` is shown in those
previews.

Proof directives accept the same dependency options, so proof-only
prerequisites can stay attached to the proof header:

```lean
:::proof "addition_right_identity" (uses := "induction_setup, zero_simplifier") (uses_intent := "auxiliary")
Induct on `n`, then discharge the zero case with the simplifier.
:::
```

If a role such as `{uses "addition_spec"}[]`, `{bpref "addition_spec"}[]`, or a
citation has an empty payload, Blueprint can generate the visible text
automatically, for example `Theorem N`.

## Minimal Project Shape

The starter template in [project_template/](../project_template/) uses this
layout:

```text
ProjectTemplate/
  Blueprint.lean
  Chapters/
    Addition.lean
    Multiplication.lean
    Collatz.lean
  Formalization/
    Addition.lean
ProjectTemplate.lean
ProjectTemplateMain.lean
lakefile.lean
```

The role of each file is:

- `ProjectTemplate/Chapters/Addition.lean`: a chapter with Blueprint blocks
- `ProjectTemplate/Formalization/Addition.lean`: ordinary Lean declarations
  tagged with `@[blueprint]` and included as a generated module chapter
- `ProjectTemplate/Chapters/Multiplication.lean`: another chapter with the same
  pattern
- `ProjectTemplate/Chapters/Collatz.lean`: a separate chapter for an
  intentionally unfinished open problem
- `ProjectTemplate/Blueprint.lean`: the Blueprint top-level file
- `ProjectTemplateMain.lean`: the renderer entry point
- `lakefile.lean`: the package definition

## The Blueprint Top-Level File

The Blueprint top-level file assembles the rendered document.

Example:

```lean
import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import ProjectTemplate.Chapters.Addition
import ProjectTemplate.Chapters.Collatz
import ProjectTemplate.Chapters.Multiplication
import ProjectTemplate.Formalization.Addition

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Starter Blueprint" =>

This small Blueprint tracks a few basic arithmetic facts on natural numbers,
then ends with a separate Collatz chapter that is intentionally unfinished.

{include 0 ProjectTemplate.Chapters.Addition}
{includeBlueprintModule 0 ProjectTemplate.Formalization.Addition (title := "Compiled Addition Results")}
{include 0 ProjectTemplate.Chapters.Multiplication}
{include 0 ProjectTemplate.Chapters.Collatz}

{blueprint_graph}
{blueprint_summary}
```

This file decides:

- which chapter modules are included
- whether the dependency graph is rendered
- whether the summary page is rendered
- whether other global pages such as the bibliography are rendered

## Parts, Chapters, and Numbers

The parts directly under the top-level file are the chapters. Chapters are
numbered `1`, `2`, … and their sections `§1.1`, `§1.2`, …; statements are
numbered by their place in the chapter or section as the
[numbering options](#blueprint-options) say (by default `Theorem 1.2` before a
chapter's first section and `Theorem 1.3.2` in section `§1.3`). Statements and
sections are counted separately: `Theorem 9.1` and `§9.1` are different things,
and the section sign keeps them apart wherever a section number is shown (its
heading, the tables of contents, the buttons to the previous and next page and
the site's cross-reference data; the full-text search index keeps Verso's form).
Chapter numbers are written as Verso writes them (`9.`).

### Parts

A long Blueprint can group its chapters into parts, as a LaTeX book does. A part
is an ordinary part of the document directly under the top-level file whose
text contains `{blueprint_part}`; its own subparts are its chapters:

```lean
-- Project/Parts/Foundations.lean
import VersoManual
import VersoBlueprint
import Project.Chapters.Groups
import Project.Chapters.Orbits

open Verso.Genre Manual

#doc (Manual) "Foundations" =>

%%%
tag := "part-foundations"
%%%

{blueprint_part}

The chapters of this part set up the groups and their orbits.

{include 0 Project.Chapters.Groups}
{include 0 Project.Chapters.Orbits}
```

```lean
-- the top-level file
{include 0 Project.Chapters.Introduction}
{include 0 Project.Parts.Foundations}
{include 0 Project.Parts.MainResult}
```

Here the introduction is Chapter 1, the part's page is titled
`Part I — Foundations`, and its chapters are Chapters 2 and 3; the chapters of
the next part go on with Chapter 4. Chapter numbers run through all parts, so a
statement keeps the number it would have without parts (`Theorem 3.2` stays
`Theorem 3.2` when its chapter moves into a part). The part's page is
unnumbered: in the table of contents it stands before its chapters, at their
level, with its introduction as its text. It is written to the folder `Part-I`
unless the part names its own file (`file := ...`); its chapters keep their
folders. A cross-reference to the part's tag shows its title, numeral included.
TeX output has the same structure: the part's page is an unnumbered chapter.

Every subpart of a part is one of its chapters, and `{blueprint_part}` counts
only in a part directly under the top-level file; elsewhere the HTML build
reports an error that says so. A statement belongs in a chapter: one written in a
part's own text is numbered without a chapter number.

A document without `{blueprint_part}` is numbered as before.

## A First Chapter

The following chapter example uses descriptive labels and a real mathematical
story about addition.

````lean
import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Addition" =>

:::group "addition_core"
Core statements about addition on natural numbers.
:::

:::author "project_author" (name := "Project Author")
:::

:::definition "addition_spec" (parent := "addition_core")
We write $`a + b` for the result of adding $`b` to $`a`.
This Blueprint starts with the most basic sanity checks around that operation.
:::

:::theorem "addition_right_identity" (parent := "addition_core") (owner := "project_author") (tags := "starter, arithmetic") (effort := "small") (priority := "high")
For every natural number $`n`, adding zero on the right leaves it unchanged:
$`n + 0 = n`.
This is the first sanity check for {uses "addition_spec"}[].
:::

:::proof "addition_right_identity"
Induct on $`n`. The base case is immediate and the inductive step unfolds one
successor on each side.
:::

```lean "addition_right_identity"
theorem nat_add_zero_right (n : Nat) : n + 0 = n := by
  simp
```

:::theorem "addition_assoc" (parent := "addition_core") (lean := "Nat.add_assoc")
For all natural numbers $`a`, $`b`, and $`c`, addition is associative:
$`(a + b) + c = a + (b + c)`.
This is another consequence of {uses "addition_spec"}[].
:::

:::proof "addition_assoc"
Lean already provides this theorem as `Nat.add_assoc`, so this Blueprint entry
links to an existing declaration instead of restating the code locally.
:::
````

This example shows the core pattern:

- define an informal mathematical object
- attach later statements to it with `uses`
- point to related entries without adding dependencies with `bpref`
- keep informal proofs close to the statement
- connect to Lean either locally or through an existing declaration

## Core Block Forms

Blueprint chapters commonly use:

- `:::definition "label_1"`
- `:::proposition "label_2"`
- `:::lemma_ "label_3"`
- `:::theorem "label_4"`
- `:::corollary "label_5"`
- `:::proof "label_4"`

`:::proof "label_4"` attaches to the earlier statement with the same label.

## Connecting Blocks to Lean

Statement-like blocks can connect to Lean in three main ways.

### Inline Lean code

Attach a labeled Lean code block to the same Blueprint label:

````md
:::theorem "addition_right_identity"
For every natural number $`n`, $`n + 0 = n`.
:::

```lean "addition_right_identity"
theorem nat_add_zero_right (n : Nat) : n + 0 = n := by
  simp
```
````

This is the clearest way to connect a Blueprint entry to local formalization
work in the same project.

### Compiled code tagged with `@[blueprint]`

Use the `@[blueprint]` attribute when a compiled definition-like
declaration or theorem should appear as a compiled-declaration-backed Blueprint
node. With no string argument, its Blueprint label is the declaration's
qualified Lean name:

```lean
/-- Associativity of addition under its qualified declaration name. -/
@[blueprint]
theorem MyProject.addition_assoc (a b c : Nat) :
    (a + b) + c = a + (b + c) := by
  simpa [Nat.add_assoc]
```

Use `@[blueprint "label"]` when the document should own a shorter or otherwise
independent label:

```lean
/--
Associativity of addition, exposed as a compiled-declaration-backed Blueprint
node.
-/
@[blueprint "addition_assoc_compiled"]
theorem addition_assoc_compiled (a b c : Nat) : (a + b) + c = a + (b + c) := by
  simpa [Nat.add_assoc]
```

This mode is useful when the formal declaration already exists as ordinary Lean
code and you want to register it as a Blueprint node.

When no node has been accepted for a label, an attribute may reuse its
declaration's docstring as the initial informal statement. A bodyless attribute
association alone is an independent fact, not an authored introduction.
Attributes targeting an existing label attach code and dependencies only: their
docstrings neither replace a statement nor fill a bodyless placeholder. Use an
explicit statement directive to fill a shared placeholder. This rule also
applies when attachments come from sibling modules.

For example, after importing a chapter that declares `addition_right_identity`,
this attribute attaches compiled code while preserving the chapter's prose:

```lean
@[blueprint "addition_right_identity"]
theorem attached_add_zero (n : Nat) : n + 0 = n := Nat.add_zero n
```

If that chapter instead declares an empty `:::theorem "addition_right_identity"`,
fill it explicitly in a later chapter that imports it:

```lean
#doc (Manual) "Addition details" =>

:::theorem "addition_right_identity"
For every natural number $`n`, adding zero on the right leaves it unchanged.
:::
```

Include the later chapter to render the completed statement. Attaching the Lean
code and supplying this body can happen in separate sibling modules importing
the same placeholder.

Plain docstrings are parsed
through the Manual Markdown path when possible. With the `doc.verso` option
enabled, standard structural content such as paragraphs, emphasis, lists,
links, code, math, quotations, and section content is converted into Manual
blocks. The same structural content is rendered inside the attached “Lean code
for…” declaration panel. If no docstring is available, the node is still
registered, but there is no imported informal statement body.

Every docstring a page shows, in a declaration panel or in a Lean hover, is
rendered from Markdown when the site is built, by Verso's Markdown renderer;
pages load no Markdown renderer and fetch nothing from another site. Docstring
text is treated as untrusted: raw HTML in it is shown as text, and links keep
only relative targets and the `http`, `https` and `mailto` schemes (images also
`data`); any other link is shown as its text.

Importing `VersoBlueprint` registers Lean docstring handlers for the same
`Informal.uses` and `Informal.bpref` names used in Manual prose. Enable
`doc.verso` in the module containing the declaration and open `Informal` (or use
the qualified role names):

```lean
import VersoBlueprint
open Informal
set_option doc.verso true

/--
An interpolation space based on {uses "normed-space" (intent := "technical")}[].
See also {bpref "interpolation-example"}[the motivating example].
-/
@[blueprint "k-interpolation-space" (proofUses := ["completeness-lemma"])]
def interpolationSpace : Nat := 0
```

Lean elaborates the docstring once into its own docstring tree. The Blueprint
handlers preserve typed references in that tree. When `@[blueprint]` adopts
the docstring as its statement, it converts those references into ordinary
Manual links and records `{uses}` as statement dependencies. The `origin` and
`intent` options have the same defaults and validation as the Manual role;
`{bpref}` accepts neither option and never adds an edge. Labels can refer to
nodes declared later or in the consuming Blueprint. Duplicate edges use the
normal metadata merge rules, and the attribute's negative `uses` entries and
self-edge suppression apply to docstring dependencies too. Proof dependencies
remain on `(proofUses := [...])`.

Links, automatic reference text, numbering, and hover previews are resolved
when the nodes are placed and traversed. Editor hovers and attached “Lean code
for…” panels use readable fallback text: authored content, or the label for an
empty reference. They do not add dependencies or require a generated site.
Untagged declarations can use these roles as documentation without creating
Blueprint nodes. Importing the handlers only in a later consumer does not
change docstrings already compiled in another module.

Other successfully elaborated Lean docstring extensions retain their fallback
children; their custom semantics are not converted to Manual. Arbitrary Manual
roles and directives do not become Lean docstring extensions. The adapter does
not reparse the docstring or run a synthetic `DocElabM` context.

#### Including an attribute module as a chapter

When a regular Lean module is the primary Blueprint source, import it in the
document module's Lean header and include all of its directly tagged
declarations as one Verso part:

```lean
import MyProject.Formalization.Interpolation

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Project Blueprint" =>

{includeBlueprintModule 0 MyProject.Formalization.Interpolation (title := "Interpolation Spaces")}
```

The generated Manual part contains one materialized Blueprint node for each
distinct label with an `@[blueprint]` application in the named module, in first
attribute-application order. This selects contributions, not exclusive ownership:
if sibling modules contribute declarations to one shared label, including either
contributor renders the complete merged node available through the document's
imports. If several declarations in the named module use the same label, the
part contains that node only once, with all of its Lean panels.
Dependencies and declarations accumulate in source order. Only the declaration
that introduces a label supplies its implicit docstring body; later attributes
do not replace it or fill a bodyless placeholder. Re-exported or
otherwise transitive modules are not folded into the part: include each desired
module explicitly. Every node follows the same docstring/code-only, numbering,
relation, preview, manifest, and cache path as an individual placement. Its
local display number is allocated in the consuming source's traversal order;
the generated placement does not retain a display number from the provider
module.

Local numbering preserves ordinary elaboration-assigned counts in independently
authored sources. A generated placement adds an offset only to later authored
counts in the same consuming source; it does not renumber sibling chapters.
If reordered authored content makes a shifted count collide with an already
assigned number, that occurrence receives the next number above all assignments
in its source. Reordering authored content without generated placements keeps
its original local numbers.
Use `set_option verso.blueprint.numbering "global"`
when numbers should instead follow the order of the whole assembled document.

Repeated placements share node identity and numbering, but honor their own
explicit code/proof folding options. Without an explicit override, reuse takes
the selected statement or proof occurrence's presentation defaults. A compact
placement does not advertise a declaration-code destination; declaration links
prefer the selected statement's visible code, or another placement that actually
renders it. Adding Markdown or TeX witnesses does not change a placed node's
statement preview key. Disabling external-markup rendering still allows its Lean
code to be reused.

This is Blueprint's current Verso-native counterpart to
[LeanArchitect's `\inputleanmodule`](https://github.com/hanwenzhu/LeanArchitect#extracting-entire-lean-file-to-latex):
it turns tagged declarations from a regular imported Lean module into document
content. The current command includes declaration-backed nodes only. It does
not yet have LeanArchitect's ordered `blueprint_comment` equivalent for prose
interleaved among declarations; put compact prose in declaration docstrings, or
use individual `{blueprint_node "label"}` placements inside an ordinary Verso
chapter when the prose needs its own position.

Module inclusion currently materializes the statement facet only. A separate
informal `:::proof` body persisted in the defining module is not automatically
registered in the consuming document. Proof prose written and traversed in the
consuming document remains available through the ordinary proof facet. This is
separate from the compiled Lean proof: Blueprint's external-declaration panel
does not reproduce the original `:= by ...` source text.

The first positional number has the same structural role as in Verso's regular
`{include 0 Some.Document}` command. It is optional; without it, the generated
part is a child of the current part. The optional `(title := "...")` overrides
the generated title, whose default is the final component of the module name:

```lean
{includeBlueprintModule MyProject.Formalization.Interpolation}
```

The command is available only in Manual documents. It reads Blueprint metadata
from the imported `.olean`; it does not perform a Lean import from inside the
document body. If the exact named module is not available through the Lean
module's import graph, or if it directly owns no `@[blueprint]` declarations,
the command reports an error. A module include is best when declaration
docstrings are the chapter prose. To interleave longer prose between selected
declarations, use individual `{blueprint_node "label"}` placements instead.

#### Placing an attribute-owned node in a chapter

Import the module containing the tagged declaration, then write
`{blueprint_node "label"}` at the exact place where the node should appear:

```lean
import MyProject.Formalization.Interpolation

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Interpolation spaces" =>

The next result packages the formal definition used throughout this chapter.

{blueprint_node "k-interpolation-space"}

The surrounding chapter can continue with examples, motivation, or links to
later Blueprint nodes.
```

For an imported `@[blueprint]` node, this command does two jobs. It projects the
persistent Lean-side node into the current document traversal, which gives it a
number, page destination, relation metadata, and generated preview entries; it
then renders that entry through the ordinary Blueprint graft path. A docstring
becomes the statement body. A declaration without a docstring renders as a
code-only node instead of failing with “Blueprint node not found”.

This placement behavior is specific to attribute-owned nodes in Manual
documents. For ordinary `:::theorem` and related blocks, `{blueprint_node}`
continues to mean “render another view of a node already traversed in this
document”. In Slides, grafts continue to read the Blueprint site manifest/cache
passed to the Slides generator.

The usual graft options apply at the placement site, including `+compact`,
`-header`, `(displayLabel := "...")`, and `(facet := "proof")`. Compact mode
intentionally hides the attached Lean panel. For an imported attribute-owned
node, the initial placement currently materializes only its statement facet; a
proof facet is available after a matching `:::proof` has been traversed in the
consuming document. A persisted provider-module proof is not automatically
materialized, and a compiled theorem proof does not automatically become
informal proof prose.

Additional prose can simply surround the placement command. If the tagged
declaration has no docstring and the prose should live inside the numbered
statement shell, write a matching statement block instead; it fills the
attribute-created node and keeps the Lean association and dependency metadata:

```lean
:::theorem "k-interpolation-space"
An interpolation space satisfying the conditions used in this chapter.
:::

:::proof "k-interpolation-space"
The informal proof outline can be maintained separately from the Lean proof.
:::
```

Do not also use `{blueprint_node "k-interpolation-space"}` merely to create the
first occurrence in that case: the statement block is already the canonical
placement. Later `{blueprint_node}` commands may reuse it elsewhere.

#### Automatic dependency inference

`autoDeps` infers dependencies on Lean declarations with Blueprint associations.
By default it follows unassociated helpers until it reaches associated
declarations. Those first associated declarations form the dependency frontier:
the walk stops there rather than flattening their own Blueprint dependencies
into the current node. An empty
inferred dependency list does not establish mathematical independence.

Inference is opt-in and disabled by default. Enable it locally with
`(autoDeps := true)`, or set the file/section default with:

```lean
set_option verso.blueprint.autoDeps true
```

The local argument wins over the option, so `(autoDeps := false)` disables
inference for one node even when the file default is enabled.

Traversal through untagged Lean declarations is controlled independently by a
Boolean Lean option. Here, "untagged" means a declaration without any Blueprint
association, including associations made by external or inline Lean attachments:

```lean
set_option verso.blueprint.autoDeps.expandUntagged true   -- default: follow helpers
set_option verso.blueprint.autoDeps.expandUntagged false  -- direct references only
```

The option has normal Lean scoping: it affects subsequent commands in the
current file/section/namespace, and `set_option verso.blueprint.autoDeps.expandUntagged false in`
limits it to the following command, including a `#docs` command. Nested settings
override the outer value and restore it when the scope ends. Settings are not
exported to importing modules. This option does not enable `autoDeps`; both
controls apply equally to attributes, external-Lean statements, and inline Lean.

For `result → helper₁ → helper₂ → tagged`, the default finds the tagged
dependency through both helpers. With expansion disabled, neither helper is
expanded, but a direct reference to `tagged` still produces an edge. Use
`autoDeps := false` to disable inference altogether, or explicit additions and
exclusions to curate the resulting edges. There is no selective helper list.

For example, the following records an automatic proof dependency from
`"prop9.6.direct"` to `"prop9.5"`. The small propositions illustrate dependency
inference, rather than the contents of any particular paper:

```lean
import VersoBlueprint

@[blueprint "prop9.5"]
theorem prop95 : True := True.intro

@[blueprint "prop9.6.direct" (autoDeps := true)]
theorem prop96Direct : True := prop95
```

The same local option is accepted on labeled inline Lean blocks and on informal
statement blocks that use `(lean := "...")`:

````md
:::theorem "prop9.6.external" (lean := "prop96Direct") (autoDeps := true)
This result follows from Proposition 9.5.
:::

```lean "prop9.6.inline" (autoDeps := true)
theorem prop96Inline : True := prop95
```
````

When inference is enabled, Blueprint starts separate walks from the constants in
the declaration's type and compiled body. The type walk produces statement
dependencies; the body walk produces proof dependencies. At an unassociated
definition, theorem, or opaque declaration, when helper expansion is enabled,
each walk follows both its type and body, keeping the axis of the walk that
reached it. For example, a helper's type can introduce a proof dependency when
that helper is used only in the root proof. A Lean declaration is associated with
a Blueprint label by `@[blueprint]` or `@[blueprint "..."]`, by a labeled inline Lean code
block, or by an informal statement block with `(lean := "...")`.

The scan uses elaborated Lean expressions, not names appearing in source text or
tactic scripts. Implicit arguments and instance arguments can therefore
contribute references too. Structures and inductives are followed through their
constructors and constructor types. Constructor and recursor types are inspected
when expansion is enabled and no association stops the walk. The constructor
types of a root inductive are its own body and are inspected even with expansion
disabled. Unassociated axioms, quotient primitives, and missing declarations are
terminal: they do not create synthetic Blueprint nodes.
Visited names prevent cycles and repeated helper expansion within each walk.
There is no fixed hop limit; Lean's normal heartbeat/cancellation checks still
apply. This is expression inspection, not reduction or execution of helper code.

Inference runs when the attribute is applied or the corresponding document
block is elaborated, using the associations available at that point. Register
the dependencies' Lean-to-Blueprint associations first. The resulting edges
persist through imports; enabling `autoDeps` in a consuming chapter, placing an
imported node with `{blueprint_node}`, or including its module with
`{includeBlueprintModule}` does not rerun inference for that attribute node.
Adding an association later does not retroactively fill earlier inferred edges.

Lean associations are many-to-many. One Blueprint label may be associated with
several Lean code items, and one Lean declaration may be associated with several
Blueprint labels. Automatic dependency inference emits all associated labels and
then deduplicates edges by label.

Inferred edges are stored with origin `"automatic"` so relationship panels can
distinguish them from author-written edges. Self-edges are suppressed. If the
same label is both inferred and explicitly listed on the same axis, the edge is
emitted once with manual origin. If the same label is inferred on both axes, the
statement edge wins and the automatic proof edge is suppressed; an explicit `proofUses`
entry can still put the label on the proof axis when that is what the Blueprint
should say.

##### Dependencies through helpers

Continuing the example above:

```lean
theorem helper : True := prop95

@[blueprint "prop9.6.helper" (autoDeps := true)]
theorem prop96Helper : True := helper
```

Here the proof refers to `helper`, which has no Blueprint association. The walk
inspects its type and proof by default, reaches `prop95`, and records an
automatic proof dependency on `"prop9.5"`. Chains of helpers work the same way,
including across imported modules, when helper expansion is enabled. An
unassociated type alias in the root's type likewise exposes its associated
dependencies on the statement axis.

If `helper` is itself associated with a Blueprint label before inference runs,
the dependency is on that helper's label instead. The walk does not continue to
`prop95` through that boundary. An attribute exclusion removes the resulting
edge; it does not reopen the excluded declaration and walk through it.

You can still explicitly curate the same edge:

```lean
@[blueprint "prop9.6.curated" (autoDeps := true)
  (proofUses := ["prop9.5"])]
theorem prop96Curated : True := helper
```

This records a manual proof dependency regardless of the expansion policy.
Use `proofUses` for a result needed to prove a proposition; attribute
`uses` and `{uses ...}[]` in the declaration docstring add statement dependencies.
No prose mention is required for an explicit attribute dependency.

When several Lean declarations genuinely formalize the same informal result,
they can share a Blueprint label. However, helpers need not become separate
Blueprint nodes merely to expose their dependencies. Review inferred edges
against the mathematical argument: elaborated terms can expose implicit
dependencies and still omit mathematical motivation absent from the Lean terms.

This traversal boundary follows LeanArchitect's helper expansion. Unlike
LeanArchitect's output-time inference, Blueprint records edges during authoring
elaboration and keeps status checking separate. An association added later does
not retroactively change persisted edges. Definitions retain body dependencies
on the proof axis even when they have no informal proof body.

Migration from direct-only inference: existing `autoDeps := true` sites may gain
helper-mediated edges. Review those edges and use attribute exclusions to curate
them. Set `verso.blueprint.autoDeps.expandUntagged` to `false` to retain direct-only
inference, or use `autoDeps := false` for fully manual dependencies.

##### Manual additions and exclusions

Manual attribute dependencies can be merged with or excluded from the inferred
set:

```lean
@[blueprint "addition_assoc_compiled"
  (autoDeps := true)
  (uses := ["addition_right_identity", -"addition_zero"])
  (proofUses := [nat_add_zero_right])]
theorem addition_assoc_compiled (a b c : Nat) : (a + b) + c = a + (b + c) := by
  simpa [Nat.add_assoc]
```

`uses` affects statement dependencies and `proofUses` affects proof
dependencies. Each list accepts Lean declaration names or Blueprint label
strings. Use string labels for ordinary Blueprint-only nodes. Prefix an entry
with `-` to remove that inferred or explicit edge from the same axis after
inference and manual entries have been resolved.

A tagged declaration can still receive a prose statement or proof block with the
same Blueprint label. If the attribute has only created dependency metadata for
that statement or proof, the later block fills in the rendered body and keeps
the inferred dependency edges.

#### Attribute-first use-case matrix

| Use case | Current behavior |
| --- | --- |
| Definitions, theorems, structures, and inductives | Supported. They become definition- or theorem-shaped Blueprint nodes. Constructors, recursors, axioms, and declarations introduced with `opaque` are not accepted as direct attribute targets. |
| Omit an explicit Blueprint label | Supported with bare `@[blueprint]`; the label defaults to the declaration's qualified Lean name. Attribute options such as `uses`, `proofUses`, and `autoDeps` remain available. |
| Direct and transitive imports | Supported. Attribute nodes, Lean associations, docstring bodies, and dependency metadata persist through imported `.olean` files. Independent bodyless attribute facts for one label compose; conflicting authored introductions, groups, and authors are diagnosed. |
| Include a regular Lean module as a Blueprint chapter | Supported in Manual documents with `{includeBlueprintModule 0 Some.Module}` after importing the module. Distinct directly owned labels are emitted in first attribute-application order; transitive modules must be named and included explicitly. |
| Place a tagged declaration on a specific Manual page | Supported with `{blueprint_node "label"}` after importing its module. The placement participates in numbering, links, relations, previews, the manifest, and the rendered-fragment cache. |
| Add chapter prose around the declaration | Supported with ordinary prose before and after the placement command. For an attribute node without a docstring, a matching statement directive can instead supply prose inside the node shell. |
| Reuse the same node in several places | Supported. The node keeps one semantic identity; later `{blueprint_node}` occurrences are presentation views and may use compact/header/display-label options. |
| Use the declaration docstring as the statement | Supported for plain Markdown, standard structural `doc.verso` content, and Blueprint `{uses}` / `{bpref}` references. Structural markup and math also survive in the attached external-declaration panel, where references use readable fallback text. Other custom extensions use their fallback children. An absent docstring produces a code-only placement. |
| Infer formal dependencies | Supported with `(autoDeps := true)` or `set_option verso.blueprint.autoDeps true`. Follows unassociated helpers by default; `set_option verso.blueprint.autoDeps.expandUntagged false` selects direct-only inference. Type/body walks produce statement/proof dependencies respectively. |
| Curate dependencies manually | Supported with attribute options `uses` and `proofUses`, using either Blueprint label strings or tagged Lean declaration names. Prefixing an entry with `-` excludes it on that axis. With `doc.verso` enabled, `{uses ...}[]` inside the adopted docstring adds statement dependencies; `{bpref ...}[]` adds links only. |
| Attach several labels to one Lean declaration, or several Lean declarations to one label | Supported. Associations are many-to-many and are deduplicated by canonical Lean name or Blueprint label as appropriate. |
| Add a separate informal proof | Supported with `:::proof "label"` once the node has a statement payload. For an undocumented, dependency-free attribute node, first add a matching statement directive. A proof body persisted in an imported provider module is not yet materialized by `{includeBlueprintModule}` or an initial `{blueprint_node}` placement. |
| Show the formal declaration | Supported as a highlighted external-declaration panel with its signature, kind-specific structure information, docstring, proof/completeness status, and source link when available. |
| Show the original definition body or `:= by ...` proof text | Not currently supported by the compiled-declaration renderer. The panel renders the declaration interface, not the original source body. Use the source link, or a labeled inline Lean block when the exact authored proof text must be embedded in the page. |
| Put `parent`, `owner`, `tags`, `effort`, `priority`, `pr_url`, or `issue_url` directly on `@[blueprint]` | Not currently supported. These remain Blueprint statement-block metadata. A separate attribute-side metadata surface needs an ownership and validation design before it is added. |
| Use an unplaced attribute node in global views | The persistent node can contribute semantic graph/summary facts, but it has no page destination or rendered preview until it is placed in a Manual document. |

### Existing Lean declarations

Use `(lean := "Nat.add_assoc")` when Lean already owns the declaration and you
want an informal Blueprint node to point at it:

```md
:::theorem "addition_assoc" (lean := "Nat.add_assoc")
For all natural numbers $`a`, $`b`, and $`c`, addition is associative.
:::
```

This links the Blueprint entry to an existing Lean declaration without copying
the declaration body into the chapter.

Proof blocks can attach Lean declarations to the same Blueprint node:

```md
:::proof "addition_assoc" (lean := "Nat.add_comm, Nat.add_left_comm")
The proof is associated with the referenced Lean declarations.
:::
```

These declarations appear in a **Lean declarations attached to this proof** panel,
with their own signatures, status, source links, and hover previews. The proof
facet retains them in generated data; `lake exe vbp query node addition_assoc`
returns that facet under `proof`.

Statement and proof attachments both contribute to the node's associated
declarations, declaration lookup, summaries, and progress. A declaration mentioned
on both facets is counted once; its observed status evidence is merged
conservatively. An incomplete or missing proof attachment cannot be ignored
when computing the node's formalization status.

With `autoDeps := true`, dependencies inferred from declarations attached to a
proof contribute to the proof-side dependency track. Authored dependencies can
also be supplied with proof-side `uses`. `lake exe vbp query code <decl>` finds
nodes associated through either facet.

Each facet retains its own declaration panels and source provenance. A proof
with no attachments does not borrow its statement's declarations or code panels.
An association is the author's asserted correspondence with the informal node;
the status check does not prove that its Lean type captures the intended
mathematics.

If the same Blueprint label also has a labeled inline Lean block, Blueprint
keeps both Lean associations. External declaration references render with the
informal statement block, while inline Lean blocks render at their source
location.

Notes:

- `(lean := "Nat.add_assoc")` points at Lean-owned declaration names
- `(lean := "Nat.add, Nat.succ")` supports comma-separated declaration lists
- `@[blueprint "addition_assoc_compiled"]` registers a
  compiled-declaration-backed Blueprint node
- bare `@[blueprint]` uses the qualified declaration name as its Blueprint
  label
- `(autoDeps := true)` is accepted by `@[blueprint]`, labeled inline Lean blocks,
  and statement blocks with `(lean := "...")`
- Blueprint labels are Blueprint-owned metadata
- Blueprint label conventions do not rewrite external Lean names

## Attached Rust Code

Blueprint also supports labeled inline Rust code blocks as attached source:

````md
:::definition "ffi_helper"
Helper routine mirrored in Rust.
:::

```rust "ffi_helper"
pub fn ffi_helper(x: i32) -> i32 {
    x + 1
}
```
````

Current behavior:

- the `rust` block label is parsed the same way as a labeled `lean` block
- the block attaches to the Blueprint node with the same label
- the rendered page shows an associated Rust code panel for that node
- Rust rendering currently uses a small built-in syntax highlighter
- Rust attachments do not currently participate in Blueprint progress or proof
  status computation
- Rust diagnostics, hover information, and external Rust refs are not currently
  part of the supported surface

## Math, TeX, and external markup

Blueprint supports ordinary Verso math syntax inside the informal text.

Examples:

```md
Inline math: $`n + 0 = n`

Display math:
$$`\sum_{i=0}^{n} i = \frac{n(n+1)}{2}`
```

Projects can also define reusable TeX macros:

```lean
tex_prelude r#"\newcommand{\NatAdd}{\mathbin{+}}"#
```

After that, Blueprint math can use the macro in rendered pages:

```md
We write $`a \NatAdd b` for addition on natural numbers.
```

Blueprint nodes can also store raw external markup through `tex` and `md`
code blocks:

````md
:::theorem "addition_right_identity"
For every natural number $`n`, $`n + 0 = n`.
:::

```tex "addition_right_identity"
\begin{theorem}\label{thm:addition-right-identity}
For every natural number $n$, adding zero on the right leaves it unchanged.
\end{theorem}
```

```md "addition_right_identity" (slot := proof)
Imported Markdown proof sketch.
```
````

External markup attachments are intended for faithful import and comparison
workflows. They are stored on the associated Blueprint node, exported in the
Blueprint manifest, and do not replace an authored Verso body. Rendered node
headers show a small `MD` and/or `TeX` badge when external markup is attached;
the badge is only an attachment signal and does not display the raw source.

To keep an external markup witness without attaching it to a Blueprint node,
omit the label:

````md
```tex
\begin{theorem}
Unlabeled TeX witness kept in the source file while porting.
\end{theorem}
```
````

To start a port before writing the Verso statement, use a labeled standalone
witness block:

````md
```tex "raw_addition_right_identity"
\begin{theorem}\label{thm:addition-right-identity}
For every natural number $n$, adding zero on the right leaves it unchanged.
\end{theorem}
```
````

A bodyless Markdown-backed node can still keep Lean links by pairing a bodyless
Blueprint directive with a labeled Markdown witness. The directive contributes
the semantic Blueprint node and `(lean := ...)` declarations; the Markdown block
contributes the source-backed preview body:

````md
:::theorem "raw_addition_right_identity" (lean := "Nat.add_zero")
:::

```md "raw_addition_right_identity" (slot := statement)
# Addition right identity

For every natural number `n`, adding zero on the right leaves it unchanged.
```
````

The generated manifest entry is `targetKind: "externalMarkup"` with key
`externalMarkup:raw_addition_right_identity`. Its external-markup data records
the Markdown source, and its Lean preview keys and `codeData` still refer to
`Nat.add_zero`. Because the directive has no authored Verso body, rendered pages
and the HTML cache use a source-backed Markdown fragment for the visible body;
HTML-cache generation can disable that fragment with
`--external-markup-render none`.

If a label needs more than one external span, give each block a separate slot.
Common slots are `statement` and `proof`; importer-specific slots are also
allowed when they are stable and documented by the project.

````md
```tex "raw_addition_right_identity" (slot := statement)
\begin{theorem}\label{thm:addition-right-identity}
For every natural number $n$, adding zero on the right leaves it unchanged.
\end{theorem}
```

```tex "raw_addition_right_identity" (slot := "proof")
\begin{proof}
Raw proof witness kept near the imported source.
\end{proof}
```
````

External markup can also carry a project-relative file location. Locations use
LSP-compatible ranges: zero-based `line` and `character`, inclusive `start`,
exclusive `end`, and a non-empty range. The manifest stores the range using
Lean's standard `Lean.Lsp.Range` JSON shape.

````md
```md "raw_addition_right_identity" (slot := statement) (path := "imported/addition.md") (start_line := 12) (start_character := 0) (end_line := 17) (end_character := 0)
Imported Markdown statement.
```
````

Current behavior:

- unlabeled `tex` and `md` blocks are accepted as hidden source witnesses and do not
  create Blueprint nodes
- labeled external-markup block labels are parsed like labeled `lean` blocks
- a labeled block stores raw source on the associated Blueprint node
  under slot `"default"` unless `(slot := ...)` is provided
- a labeled standalone external-markup block is exported to the semantic
  manifest as `targetKind: "externalMarkup"` with key `externalMarkup:<label>`;
  by default the generated HTML cache also gets a source-backed rendered
  fragment for that key
- a bodyless statement directive with external markup uses the same
  source-backed rendering path for the ordinary generated page body
- manifest entries include `authoredLabel` alongside the canonical `label` so
  clients can display and round-trip punctuation-heavy authored labels without
  parsing Lean pretty-name quoting
- source-backed rendered fragments choose Markdown `statement`, Markdown
  `default`, TeX `statement`, then TeX `default` when multiple source slots are
  available; Markdown is rendered by MD4Lean with raw HTML disabled and falls
  back to escaped source if MD4Lean cannot render the fragment, while TeX
  sources are escaped
- if a bodyless directive for the same label carried `(lean := ...)`, the
  external-markup manifest entry keeps the corresponding Lean preview keys and
  `codeData`
- generation emits a non-fatal warning if traversal recorded Lean preview
  metadata for a bodyless/source-backed node but the exported manifest entry no
  longer carries it
- pass `--external-markup-render source` during manifest/cache generation to
  render the selected source as escaped source text, or
  `--external-markup-render none` to keep source-backed entries manifest-only with
  no HTML cache body
- if the same label also has a rendered statement or proof, the external markup
  is attached to that block's manifest entry instead of creating a separate
  external-markup entry
- uniqueness is by label, language, and slot, so `tex`/`statement` and
  `md`/`statement` can coexist
- repeating the same label/language/slot key is an error
- locations are all-or-nothing: provide `path`, `start_line`,
  `start_character`, `end_line`, and `end_character`, or omit the location
- the block is not displayed in the rendered output unless `(display := summary)`
  or `(display := source)` is provided, or the file sets
  `set_option verso.blueprint.externalMarkup.display "summary"` or `"source"`
- display and source-backed cache rendering are intentionally a preview path:
  Markdown cache fragments use MD4Lean with escaped-source fallback, while
  richer converters can still replace this path when projects need TeX or
  native Blueprint structure

### Original Source Provenance

Blueprint can record a three-level source provenance chain for audit tooling:
original source document, Verso Blueprint node, and associated Lean material.
This phase stores the source-document catalog and source spans for each
statement/proof facet.
Generated Blueprint node shells show a compact source chip when a node has
source provenance. The chip opens a lightweight source preview with the
document id and recorded span details. Fuller source review interfaces such as
PDF page viewers, crop overlays, and side-by-side text review remain interface
work for clients or later Blueprint UI.

Declare source documents with `:::source_document`. The directive body must
contain exactly one Verso metadata block:

````md
:::source_document "paper"
%%%
title := "Representation Theory"
kind := .pdf
pdf := "source/paper.pdf"
pageRoot := "source/pages"
imageRoot := "source/pages/images"
%%%
:::
````

Attach source provenance to a Blueprint node with a leading metadata block
inside the node directive. The metadata block must be the first block in the
directive body; a later metadata block is rejected so that provenance is easy to
find and strip before rendering the visible statement.

A statement and its proof can cite different pages or different source
documents. Each facet's generated preview retains its own provenance. When
several facets share a Lean-code preview, that preview lists their combined
source references.

````md
:::lemma_ "addition_right_identity"
%%%
source := {
  document := "paper"
  spans := #[
    {
      page := "12"
      anchor := "lem:addition-right-identity"
      citation := "Lemma 2.1(1)"
      text := some {
        path := "source/pages/page-12.md"
        startLine := 41
        endLine := 45
      }
      pdf := some {
        path := "source/pages/page-12.pdf"
        image := "source/pages/images/page-12.png"
      }
    }
  ]
}
%%%

For every natural number $`n`, $`n + 0 = n`.
:::
````

The generated manifest exports declared documents in `sourceDocuments` and each
manifest entry's original-source refs in `entry.sources`. Normal generated node
shells also show a compact source chip when source provenance is present; open
it to inspect the source document id, source-native anchor and citation, page
summary, and recorded text/PDF span details.

When an entry has exactly one source ref and every span has the same nonempty
citation, the chip displays that citation as `source: ...`. Repeating a citation
across several pages is supported. A single ref with uncited spans or differing
citations uses `source 1`; entries that aggregate several refs use `sources N`
so the compact label does not hide additional provenance. The expanded panel preserves
every span in its recorded order, regardless of the compact label.

`anchor` is a stable identifier in the original source, such as a TeX
`\label`; `citation` is the corresponding human-readable source identity, such
as `Lemma 2.1(1)` or `Equation (2.4)`. These fields do not replace the
Blueprint node's label or generated heading number. A node may therefore remain
`Lemma 2.2` in the Blueprint while its source chip explicitly reads
`source: Lemma 2.1(1)`. Keeping the identities separate avoids silently
changing graph keys, Blueprint references, or site-local numbering to imitate
the source document.

Source-native identity is qualified by the source-document id: the same anchor
in two documents denotes two different origins. Citations are display text,
not join keys. Several regions may legitimately share one anchor or citation.

Provenance is not a promise of a renderable original excerpt. An anchor-only
reference remains useful without a published asset or an anchor-to-location
mapping. Keep that metadata visible; an informal Markdown/TeX attachment is not
an original-source excerpt merely because it can be rendered. `sourceLocation`
locates authored Blueprint or Lean code, whereas `sources` records its
original-source provenance.

Each source span must supply at least one location: a page, source anchor, text
range, or PDF location. Any one of these is sufficient; a `citation` alone is
not a location. Supplied `page`, `anchor`, and `citation` strings must be
nonblank (not empty or whitespace-only). Omit optional fields instead of using
blank strings; supplied text ranges and PDF locations must also be valid.

For a text source such as the TeX input itself, omit `page` and use a source
anchor, a text line range, or both:

````md
:::source_document "paper-tex"
%%%
title := "Representation Theory (TeX source)"
kind := .text
%%%
:::

:::lemma_ "addition_right_identity"
%%%
source := {
  document := "paper-tex"
  spans := #[{
    anchor := "itm:addition-right-identity"
    citation := "Lemma 2.1(1)"
    text := some {
      path := "paper.tex"
      startLine := 439
      endLine := 440
    }
  }]
}
%%%

For every natural number $`n`, $`n + 0 = n`.
:::
````

Manifest clients should read `entry.sources`; there is no singular
`entry.source` field. Lean code preview entries may contain multiple refs when
several sourced Blueprint nodes share the same rendered Lean preview. External
declaration previews are keyed by canonical declaration, while inline code
previews are keyed by the source code-block identity and use
`targetKind: "inlineLeanCode"`. Declaration-specific inline identity is the
source code-block identity plus the declaration's position in the owning block
entry's ordered inline code metadata (`definedDefs` followed by
`definedTheorems`).
Browser clients can resolve those document ids with `loadSourceDocument` or
read the complete catalog with `loadSourceDocuments`.

Browser clients can call `resolveSourceMetadata` from `api/data.mjs` or
`api/preview.mjs` to resolve source refs for a preview key, manifest entry, or
render result. The API returns structured source-document metadata, source
identities, and text/PDF spans.
Manifest entries also include `sourceLocation`, a lookup result for the authored
Blueprint label/facet location or Lean declaration source. Browser clients that
start from semantic names can call `resolveLabel`, or `resolveDeclaration` for
declaration-keyed previews, from `api/data.mjs` or `api/preview.mjs` to get the
generated link and source location together. Inline code previews are keyed by
the source code-block identity and should be loaded through the explicit key in
`leanCodePreviewKeys`.
For a `codeOnlyPreview` entry, the preview API composes those Lean fragments
into the hover body. Its own block-body cache fragment is inert so full-node
renderers can render associated code panels separately without duplicating them.
Use the data API for metadata-only audit or dashboard clients; use the preview
API when the same client also renders Blueprint nodes or cached previews.
The built-in source preview is intentionally lightweight; richer PDF page
viewers and crop overlays remain Blueprint/Verso interface work.

Blueprint also supports best-effort KaTeX linting during elaboration. KaTeX is
the renderer used by the generated HTML, so this helps catch math problems
before the final site render.

## Groups, Authors, and Metadata

Use `:::group` to define reusable group metadata:

```md
:::group "group_1"
Core statements for the first chapter.
:::
```

Use `:::author` to define author metadata:

```md
:::author "author_1" (name := "Jason Example")
:::
```

Statement-like directives can carry:

- `(parent := "group_1")`
- `(owner := "author_1")`
- `(tags := "starter, arithmetic")`
- `(effort := "small" | "medium" | "large")`
- `(priority := "high" | "medium" | "low")`
- `(pr_url := "https://github.com/org/repo/pull/123")`
- `(issue_url := "https://github.com/org/repo/issues/109")`

These fields are primarily used by rendered overview pages and project triage
views.

`pr_url` and `issue_url` accept any `http://` or `https://` URL after trimming
surrounding whitespace; on a statement block a blank value is treated as
absent, while a proof block rejects either option whatever its value. The
trimmed URL is published as written into the
rendered pages and the generated manifest, so do not put credentials or other
private data in it. The metadata panel captions the issue link with the
trailing numeric path segment of the URL (`#109` for `…/issues/109`, also
`…/-/issues/109#note`), or with `link` when the path does not end in a number.
The manifest entry carries `issueUrl` as written and a derived `issueNumber`,
which is `null` when no number can be read. Issue links do not count toward
the summary's linked-PR statistics.

## Rendering Surface

### Rendered statement blocks

Rendered statement headers show related metadata chips in this order: group,
uses, used by, external-markup badge, then Lean status. The statement `uses`
chip shows statement-side dependencies; proof headers show their own `uses`
chip for proof-side dependencies on the same label. This keeps prerequisites
for the statement and prerequisites used only by the proof visually distinct.
When local or external Lean material is available, the rendered page links or
previews the associated content. Rows in the uses and used-by panels show
statement/proof badges plus any non-default dependency origin or intent badges.
A proof's dependency badges describe only the proof contribution, even when the
same target has different statement metadata. Manifest-backed blocks, including
grafts, use the same rule. Statement headers retain empty dependency chips and a
missing Lean association indicator; proof headers show their own dependencies
without repeating statement-only group, used-by, markup, or Lean status controls.

Relation previews show the human title and a right-aligned concrete Blueprint
label in the preview header; the label links to the target statement. Single
uses or used-by entries with a rendered preview use the same inline preview
chrome, with relation metadata badges shown in the preview footer. If that body
is unavailable, the chip opens a relation panel instead: its row, link, and badges
remain visible, with an unavailable-preview message and no cache request.

Inline preview triggers require manifest-backed rendered fragments. A missing
or stale preview key renders the shared preview diagnostic instead of inventing
label-only fallback HTML.

When labeled inline Rust code is attached to a node, the rendered page also
shows an associated Rust code panel below the statement body.

The Lean status link of a statement header (`L∃∀N`) opens a summary of the
statement's Lean declarations, headed by the statement's numbered title
(`Lemma 6.2`). The summary and the line under an informal statement that stands
beside Lean code ("Informal statement from the blueprint · not checked against
the Lean statement") end with a "What this means" link to the explanation of the
marks on the Project Stats page, when the site has that page. Lean declarations
attached to a proof are set in the code size of the side-by-side Lean column, and
their signatures take Verso's narrow layout, one binder a line, whenever the
panel is narrower than the wide layout needs.

Popovers (relation panels, Lean summaries, inline previews) open on hover and
on keyboard focus. Opening one closes any other, except one that holds the new
trigger, such as a preview opened from a link inside a relation panel. A popover
opened by focus closes as soon as the focus moves to an element outside it and
its trigger; one opened by the pointer closes shortly after the pointer leaves.
Popovers are kept inside the viewport and beside, not under, the table of
contents, and are never wider than the screen.

### Links to repository files

`{repoFile "path"}[text]` links its text to a file or folder of the project's
repository at the commit the site is built from, as the source links of Lean
declarations are:

```lean
See the {repoFile "notes/engine.md"}[engine guide] and the
{repoFile "Project/Main.lean#L10-L20"}[main loop].
```

The path is relative to the root of the repository; a fragment (`#L10-L20`) is
kept. Elaboration fails when the path is absolute, leaves the repository (`..`),
or names nothing in the checkout that contains the chapter. The link is made
when the site is generated, from the `HEAD` commit and the GitHub `origin`
remote of the checkout it is generated in
(`https://github.com/<owner>/<repo>/blob/<commit>/<path>`); outside a Git
checkout with a GitHub `origin` the text is shown without a link. TeX output
shows the text.

### Side-by-side layout

A generator can render every statement that has `(lean := ...)` references as a
two-column node: the statement, its status glyph and its proof on the left, and
the highlighted Lean source of the referenced declarations on the right:

### Sidebar

A generator can turn Verso's table of contents into a navigation sidebar:

```lean
def main (args : List String) : IO UInt32 :=
  Informal.PreviewManifest.blueprintMainWithPreviewData
    (%doc Contents) args
    (extensionImpls := by exact extension_impls%)
    (sideBySide := true)
```

The generator flag `--side-by-side` does the same for one build. With the
layout on:

- The Lean column shows the source of each declaration's defining command,
  with the same hover information as other highlighted Lean code. Definitions,
  structures and instances are shown whole; theorem-like declarations show their
  statement up to `:=` (and a following `by`), with the proof folded under
  "Lean proof [show]". A command that defines several of the node's
  declarations (a `mutual` block, a structure and its fields) is shown once.
  Declarations whose source is not available (declarations from dependencies
  under `.lake/packages`, or modules that could not be highlighted) keep the
  signature-and-docstring row of the Lean code panel.
- Proofs are folded ("Proof [show]") and placed in the left column of their
  statement's node when they directly follow it on the page; the generator
  places them, so this holds without scripts too.
- Nodes have no card. Consecutive Blueprint blocks form a *run*
  (`div.bp_sbs_run`); prose, a code block or a heading between two blocks ends
  it, while a block that renders nothing (group metadata, hidden external
  markup) does not. Each node has its own hairline divider in the middle of the
  column gap, as tall as the node (its proof included, while it opens or
  closes), with a gap between the dividers of consecutive nodes; a statement without
  Lean declarations takes the full width and has no divider. The node a link lands on (its statement, its proof or
  one of its declarations) is tinted on screen, not in print. Other styles and
  print stack the columns and keep the nodes of a run apart.
- With the page script, "Proof [show]" on the prose side opens and closes the
  prose proof and the node's Lean proofs together, and the Lean proofs' own
  toggles are hidden; a node with Lean proofs but no prose proof keeps
  "Lean proof [show]". Opening and closing animate the height, a second press
  reverses a running animation, and `prefers-reduced-motion` makes the change
  immediate. A link into a proof opens it. Without scripts each proof keeps its
  own native toggle.
- The look is set by CSS custom properties a project stylesheet can override
  on `:root`: `--bp-sbs-column-gap` (2.25rem), `--bp-sbs-divider-width` (1px),
  `--bp-sbs-divider-color` (the soft border colour), `--bp-sbs-node-gap`
  (space between the nodes of a run, and so between their dividers, 3.25rem), `--bp-sbs-run-margin` (around a
  run, 1.5rem), `--bp-sbs-target-surface` and `--bp-sbs-target-bleed` (the
  tint of a linked node), `--bp-sbs-proof-duration` (200ms, the length of every
  opening and closing, long proofs included) and `--bp-sbs-proof-easing`.
- The node title carries a status glyph, which is about the node's Lean code
  and nothing else: ✓ the Lean declarations, and everything they use, contain
  no `sorry`, and the kernel replay made while the site was generated accepted
  them together with every constant they depend on (the tooltip says "Lean
  proof complete" for a theorem and "Lean definition complete" for a
  definition, and names the checker); ◇ no `sorry` as the compiled files
  report, with no verdict of a replay behind it (the tooltip says "not
  replayed by a kernel" when nothing was replayed for the node, with the
  reason: no replay was run, no checker was found, the export went over its
  limit, or the node is not part of the replay; and "no verdict of a kernel
  replay" when a replay was started and stopped without one); ⊘ a kernel
  checker rejected the build, or the two checkers disagree; ◐ a
  `sorry` in the proof or in what it uses; ⚠ a `sorry` in the statement, an axiom beyond Lean's standard three
  (also when there is no `sorry`: the tooltip names the axiom, or the compiled
  code the proof rests on, and says what the replay did, for example
  "not checked by the kernel replay: it rests on an axiom outside Lean's
  standard three (Demo.ax), and a replay checks only what rests on Lean's
  standard three axioms alone, so it is not shown as proved"), or code that
  could not be inspected; ✗ a
  declaration is missing; ○ no Lean declaration is attached. The glyph's
  tooltip gives its meaning and the details. A folded "Status legend" lists
  the glyphs and ends with what no mark is about: "No tool checks that an
  informal statement says the same as the Lean statement." It sits in the
  sidebar foot when the site has a sidebar, otherwise at the end of the page.
- Under a statement that has Lean declarations a small line names where the
  text comes from and says the same in short: "Informal statement from the
  blueprint · not checked against the Lean statement".
- The relation and Lean chips of the title row (`uses N`, `used by N`,
  `✓ L∃∀N`) are shown small and muted at the right of the title; counts of
  zero are hidden.
- In the Lean column the code comes first, its first line on the baseline of
  the node title; the module path (a link to the source when the repository is
  on GitHub) and, where it is shown, the "Lean proof [show]" toggle form a
  caption row below it.
  Long lines wrap with a hanging indent of four columns beyond their own
  indentation, without horizontal scrolling.
- `sbs` ("side by side") becomes the site's default style in the style
  switcher; choosing another style stacks the two columns. Nodes also stack
  when their container is narrower than about 760 pixels, and when printing;
  stacked nodes have no column divider.
- Typography of the `sbs` style: one serif text face for reading text (chapter
  prose, node headings, statements and proofs), by default the KaTeX text face
  so that text and formulas match, with upright statements (italics are left to
  emphasis and the "Proof" caption); Verso's structure face for navigation and
  controls; a monospace face for code. The faces are CSS variables a project
  stylesheet can set: `--bp-sbs-text-font-family`, `--bp-sbs-code-font-family`
  (and `--bp-sbs-text-size`). Every page of the site uses the wide content
  area, with running text kept to a readable measure (`--bp-sbs-measure`,
  48rem); links in reading text use the theme's link colour.
- Display formulas wider than the left column are set smaller to fit (down to
  70%); wider ones scroll inside the column.

Declaration sources come from SubVerso's per-module highlighted JSON. Before
rendering, the generator runs `lake build +<Module>:highlighted` once for every
workspace module that declares a referenced declaration; Lake caches the result
per module, so only changed modules are highlighted again. The first build of a
large project can take a while: highlighting re-elaborates each such module.

### Dark theme

Every blueprint page ships a dark palette. It applies in two cases: when the
page's `<html>` element carries `data-theme="dark"` (the attribute a Verso theme
toggle sets), and when the operating system prefers a dark colour scheme, unless
the page opts out with `data-theme="light"`. Both triggers use identical values.

All colours are CSS variables (`--bp-color-*`, `--bp-shadow-*`). Verso's own page
variables (`--verso-text-color`, `--verso-tooltip-bg-color`, ...) are overridden
as well, so the whole page turns dark. A project can override any of these
variables in its own stylesheet; to change only the dark values, scope the
override under `html[data-theme="dark"]`.

The status colours form one family, `--bp-color-status-*`, with a light and a
dark value each (`Informal.StatusColors`): the proof-status fills
(`not-ready`, `definition`, `ready`, `incomplete`, `formalized`,
`formalized-with-ancestors`, `unresolved`), the label colours on them
(`fill-text`, `formalized-with-ancestors-text`, `unresolved-text`) and the
statement-status borders (`blocked-border`, `ready-border`,
`formalized-border`, `mathlib-border`, `unresolved-border`). The dependency
graph paints its nodes from them: the drawings carry the light values, each node
carries its status classes (`bp_graph_status_<status>`,
`bp_graph_statement_<status>`) in the SVG, and the graph stylesheet repaints the
node from the tokens in the active theme. The graph legend and the summary's
status cards use the same tokens, so overriding one changes it everywhere.
Group-overview nodes mix their members' light colours and are not repainted.

    (sidebar? := some {
      links := #[
        { label := "Paper [web]", href := "https://arxiv.org/abs/..." },
        { label := "Paper [pdf]", href := "https://arxiv.org/pdf/..." },
        { label := "GitHub", href := "https://github.com/..." }
      ]
    })
```

The generator flag `--sidebar` enables the sidebar with the default
configuration (no external links) for one build.

The sidebar lists "Blueprint Home" (the label is `homeLabel`), the numbered
chapters with the current one in bold, a separator, the unnumbered pages
(dependency graph, summary, bibliography, ...), the configured external links
after another separator (none when `links` is empty), and a light/dark switch at
its foot. The current chapter's sections are listed under that chapter,
indented and smaller (and a section's subsections under the section); Verso's
separate per-level lists are not shown. The current entry is in bold.

The site title and the search box sit at the top of the sidebar instead of in a
full-width header, so pages start at the top of the window. Page controls that
would otherwise float over the content move into the sidebar foot: the
Blueprint style switcher, and the status-glyph legend of the side-by-side
layout. A site without the sidebar keeps the style switcher in the foot of
Verso's table of contents, in the page's layout, so it never covers text; it
floats in the window's corner only on a page that has no table of contents.
On narrow screens (700 pixels and less) the sidebar collapses behind
Verso's menu button and the title and search stay in Verso's slim header bar.
When printing, the sidebar, header and page navigation are left out.

The theme switch sets `data-theme="light"` or `data-theme="dark"` on the root
element and stores the choice under the `localStorage` key `verso-theme`; an
inline script in `<head>` applies a stored choice before the page is drawn.
Without a stored choice the operating system's preference applies. If the page
already has a theme control in the table of contents, the sidebar adds none.
The sidebar colours are CSS variables (`--bp-sidebar-bg`, `--bp-sidebar-fg`,
`--bp-sidebar-rule`, ...) that a project stylesheet can override.

### Dependency graph

`blueprint_graph` renders a dependency-oriented view of the current Blueprint
document.

Use it as either:

```lean
{blueprint_graph}
```

or with explicit graph layout options:

```lean
{blueprint_graph (direction := LR)}
{blueprint_graph (direction := LR) (pack := true)}
{blueprint_graph (routing := spline)}
{blueprint_graph (preview := hover)}
{blueprint_graph (preview := hover) (previewPlacement := anchored)}
```

Supported directions are `LR`, `RL`, `TB`, and `BT`. When `(direction := ...)`
is omitted, the command falls back to the
`verso.blueprint.graph.defaultDirection` option.
The `(pack := true | false)` option controls component packing: with `true`
each connected component is laid out on its own and the drawings are packed
into rows; with `false` the whole graph is laid out in one set of layers. It
defaults to `verso.blueprint.graph.defaultPack`, which is `true`. A view with
one connected component has a single drawing for both settings.
The `(routing := bundled | spline)` option chooses how edges are drawn:
`bundled` (the default) draws them as horizontal and vertical lanes, and
`spline` as one smooth curve per edge (see "How the graph is laid out"). It
defaults to `verso.blueprint.graph.defaultRouting`, which is `bundled`; a site
generated from compiled code takes `--graph-routing spline` (`vbp code-site`).
The `(preview := pinned | hover)` option chooses the initial graph-node preview
behavior. The default is `pinned`: clicking a node opens a persistent preview
panel that stays open until closed. `hover` opens a transient preview that
disappears after the pointer leaves the node and preview panel.
The `(previewPlacement := docked | anchored)` option chooses where the preview
panel appears. The default is `docked`, so both pinned and hover previews
open in the graph corner unless `anchored` is selected to place the panel near
the active node.

The rendered graph page is interactive:

- a `View` selector switches between the full graph and any derived grouped
  views
- a `Legend` button opens the current graph legend in a popover
- a `Graph options` button exposes runtime graph options such as direction and
  component packing, plus the graph-node preview behavior and placement
- the drawing pans and zooms: the wheel zooms about the pointer, a drag pans (a
  press that moves less than a few pixels stays a click on the node under it),
  two fingers pinch, a double click zooms in, and with the drawing focused the
  keys `+` and `-` zoom in and out, `0` goes back to the first view (and, pressed
  there, shows the whole drawing), and the arrow
  keys pan; nothing is animated
- the first view shows the whole drawing when its node labels are at least 9
  CSS pixels high there; a graph too large for that opens at the scale where
  they are 9 pixels high, on its roots (the first layer in the current
  direction), and a `Show whole graph` button beside `Graph options` (offered
  while part of the drawing is out of view) and the key `0` show all of it;
  this holds for every view, and a page read without scripts shows the
  drawing as it was written, fitted
- when grouped metadata produces multiple children for the same parent, the
  selector includes a synthetic group overview plus one subgraph view per group

The command-side options and the runtime graph controls are compatible:

- `(direction := ...)` chooses the initial graph direction when the page first
  loads
- the rendered `Graph options` control lets readers switch among the supported
  directions, toggle component packing, and choose between pinned and
  hover previews and docked or anchored placement without regenerating the site

Group metadata may be used to organize the presentation, but grouping does not
change dependency edges.

#### Neighbourhood (ego) view

On a large graph a reader can look at one node's surroundings instead of the
whole graph: the *ego view* of a node shows the node, the nodes it uses and the
nodes that use it, up to a number of hops (1 to 3) chosen beside the view
selector. It is a drawing of its own made while the site is built, so it keeps
every node's and edge's styling; the centre node is outlined. The page
URL names it (`#ego=<label>&k=<hops>`, the label percent-encoded), so a link or
a reload opens it again; a node view's *Neighbourhood* link opens its node's ego
view, and so do the declaration cards of a site generated from compiled code.

#### Drawings made at build time

Every view of the graph is laid out and drawn while the site is built, in Lean
(`Informal.GraphLayout`, using the PILean library), as inert SVG: no script,
link or event handler, and no layout program or graph library in the page. The
drawing of a view is deterministic: the same graph gives the same bytes. A view
is drawn for each of the four directions and, when it has more than one
connected component, with its components packed and unpacked.

The graph block writes the view shown first into the page, in
`div.bp_graph_first_drawing` inside `.bp_graph_canvas`, so a reader sees it as
soon as the page is parsed; the page's script replaces it with the same drawing
under pan and zoom. The attributes `data-variant`, `data-direction` and
`data-pack` (`true`, `false` or `any`) say which drawing it is.

The other drawings depend on how the site is generated:

- A generator that writes the site's data folder (`-verso-data/`, as `vbp build`
  and `vbp code-site` do) writes `-verso-data/blueprint-graph/<key>/`, where
  `<key>` is the graph's key with every character that is not a letter or digit
  replaced by `-`. The folder holds `v<i>-<TB|BT|LR|RL>-<true|false|any>.svg`
  for each view `i`, direction and packing, `e<set>-<TB|LR>.svg` for each
  distinct set of nodes that a neighbourhood view shows, and `index.json`. The
  page reads `index.json` and fetches a drawing when it is first shown.
- A page rendered without that folder carries every other drawing as
  `script[type="image/svg+xml"].bp-graph-drawing` beside the graph data, with
  the same three attributes; the page parses only the one it shows.

`index.json` has `variants` (for each view key, its file stem and packings),
`nodes` (for each node, the neighbourhood sets of one, two and three hops),
`sizes` (the number of nodes of each set), `over` (for each set, whether it
stands for neighbourhoods of more than `nodeLimit` nodes: the search for a
node's neighbourhood stops as soon as it passes the limit, and every such
neighbourhood is that one set, never drawn, whose size is not counted),
`drawn` (for each set, the
directions drawn, as a bit mask: `TB` is 1, `LR` is 4), `omitted` (how many
neighbourhood drawings were left out), `limit` (the byte limit on the
neighbourhood drawings) and `nodeLimit` (the most nodes of a neighbourhood that
is drawn, 150).

Neighbourhoods are drawn with the layers from the top down and from left to
right only; the page mirrors them for the opposite directions and keeps every
label upright. The neighbourhood drawings of one graph stop at 192 MiB in all,
smallest sets first, and a neighbourhood of more than 150 nodes is not drawn
(the page says it has "more than 150 nodes"). These limits are on the
neighbourhood drawings of the current build: the work of finding the
neighbourhoods is bounded by the node limit (about `3 × 151²` steps per node at
most, whatever the graph), while the drawings of the whole graph's views are
not part of the byte limit. A build into a folder an earlier build wrote
removes the drawings, and every other file of the earlier build, that it does
not write again (see "Output folders"). When a neighbourhood's drawing was left
out, the page shows a notice under the controls and, where the other axis was
drawn, shows that drawing instead.

#### How the graph is laid out

The layout is a layered drawing in the tradition of Sugiyama, Tagawa and Toda.
Cycles are removed by reversing a small set of edges (Eades, Lin and Smyth).
Nodes are assigned to layers by network simplex (Gansner, Koutsofios, North and
Vo, 1993). A graph whose groups are drawn as boxes is layered from the inside
out: every group has a block of layers of its own, two groups that an edge joins
lie one above the other, and the edge leaves the upper group through its lower
side and enters the lower one through its upper side (Gansner et al. rank
clusters recursively; Sander's layout of compound graphs, 1996). A layer much
wider than the others is split into rows. Crossings are reduced by
weighted-median sweeps with transposition and sifting (Matuszewski, Schönfeld
and Molitor, 1999), run from several deterministic starts. Coordinates within
layers follow Brandes and Köpf (2001), improved by network simplex with the
width of every layer counted, so that the drawing of a written blueprint fits a
page with its labels readable. With packing on, each connected component is laid
out alone and the drawings are placed on shelves, tallest first, each filling a
row before the next begins (next-fit decreasing height; Coffman, Garey, Johnson
and Tarjan, 1980).

Edges are drawn in **bundled lanes** by default. Every node has one exit port
(the middle of its side towards the next layers) and one entry port (the middle
of the opposite side). The edges that leave a node share a straight *stem* from
its exit port and then split onto their own tracks; the edges that enter a node
join one stem that ends in a single arrowhead, so a node has one arrowhead
however many edges reach it. Between two layers the horizontal runs of the
edges are given tracks of a routing channel (the channel routing of circuit
layout), long edges run as parallel vertical lanes beside the nodes they pass,
in the free places nearest the stretch between their two ends (a lane goes
round the drawing only where nothing nearer is free), keeping 16 pixels from
any group box they do not enter, and a bundle of lanes that turns does so with
concentric corners. The look is
fixed: neighbouring lanes 8 pixels apart, the innermost corner of a turning
bundle of radius 10, stems of 14 pixels, and at least 16 pixels between two runs
on one track. Stems are solid and one pixel wide in the edges' colour; the edges
keep their line styles: an edge from a definition is dashed, an edge that only a
proof uses is dotted, and an edge that both the statement and the proof use is
thicker. An edge never turns back across the layers.

With `(routing := spline)` an edge is routed as in section 5 of Gansner et al.:
its room is the free space beside the nodes of every layer it passes, the route
is the shortest polyline through that room (an edge with nothing in its way is a
straight line), and the edge is drawn as one smooth curve that rounds the bends
of that route and stays clear of every node and group it does not end in. The
ends of the edges are spread along a node's side in the order of their other
ends, and every edge has its own arrowhead along the end of its curve.

**Limits of bundled lanes.** A bundled drawing is taller than a drawing with
curves, since the runs between two layers take tracks of their own, and a node
with very many edges makes a bundle as wide as its lanes. A view with more than
2,000 edges, or with a node of more than 60 edges, is therefore drawn with
curves even when bundled lanes are asked for, and the page says so under the
graph controls ("A node of this view has 70 edges, so the view is drawn with
curved edges: …"). The limits come from measurements of the layouts of real
graphs (the time of the layout and of the drawing, the size of the SVG and its
area; Apple M2 Ultra, a load average of 3 to 9):

| Graph | Nodes | Edges | Largest degree | Bundled: ms, KiB, Mpx² | Curves: ms, KiB, Mpx² |
|---|---|---|---|---|---|
| a blueprint | 67 | 171 | 16 | 120, 66, 5.5 | 78, 57, 3.2 |
| the same, by chapter | 67 | 171 | 16 | 392, 75, 8.6 | 297, 72, 5.4 |
| a code site's modules | 85 | 159 | 16 | 195, 73, 7.9 | 140, 65, 3.6 |
| a neighbourhood | 150 | 468 | 51 | 1,808, 198, 28.6 | 931, 173, 17.8 |
| a neighbourhood | 290 | 793 | 45 | 4,246, 372, 83.8 | 2,439, 322, 33.6 |
| a code site's largest module | 561 | 422 | 400 | 1,640, 370, 55.7 | 1,591, 430, 27.3 |
| a node with 400 neighbours | 401 | 400 | 400 | 1,062, 294, 60.7 | 611, 356, 30.5 |
| a random module graph | 800 | 1,077 | 9 | 2,376, 637, 43.9 | 1,498, 553, 21.9 |
| a random module graph | 3,000 | 4,019 | 11 | 8,726, 2,416, 847 | 2,394, 2,142, 317 |
| a code site, by module | 2,866 | 5,516 | 400 | 18,545, 3,097, 11,335 | 12,703, 3,287, 4,049 |

Bundled drawings take up to about twice as long as curves (placing the lanes
of long edges near their ends is most of the difference) and are up to a sixth
larger as SVG for ordinary graphs; their area is 1.6 to 2.5 times that of
curves up to about a thousand edges, and grows faster beyond (2.7 times at
4,000 edges, with three and a half times the time), hence the limit of 2,000
edges (the layout also gives up the constraints between the runs of a channel
of more than 4,000 runs, and its promises about them then lapse). The blueprint
above with one more node joined to 20 to 200 of the others keeps its area at
1.7 to 2.2 times that of curves, but from about 60 edges at one node that
node's lanes fill a band as wide as the drawing, hence the limit of 60.

**Following a route.** Pointing at an edge, or pointing at or focusing a node
(the nodes that open a view are reached with the Tab key), draws the whole
route of each edge concerned in the trace colour, from the port it leaves to
the arrowhead it reaches, its parts of the shared stems included; nothing else
on the page changes, so moving the pointer across many edges does not flicker.
Escape or moving away clears it. Everything this needs is written into
the drawing when the site is built: every `path.edge` carries `data-edge` (its
number), `data-from` and `data-to` (the ids of its nodes) and, when it shares a
stem, `data-stems` (the path data of its own parts of the shared stems); every
`path.stem` carries `data-node` and `data-port` (`out` or `in`); an arrowhead
carries `data-node` and `data-port="in"` (bundled lanes) or `data-edge` (curves).
The page draws those parts as given and computes nothing about the layout; a
drawing is the same picture without scripts. The `svg` element says how its
edges are drawn (`data-bp-routing`: `bundled` or `spline`) and, for a view drawn
with curves because of the limits, why (`data-bp-routing-note`, also shown under
the first drawing of a page read without scripts).

Labels are drawn at 12 pixels. A node of a statement the document numbers is
labelled with its numbered title (`Theorem 6.5`); its label (`critical_radius`)
stays its name and its tooltip, and both make its accessible name: every node is
an image (`role="img"`) named by `aria-label` (`Theorem 6.5 (critical_radius)`),
and on the page a node that opens a view or preview is a button the keyboard
reaches (`role="button"`). Other nodes are labelled with their label. A label
that is a long dotted name (a module, a declaration in its namespaces) is broken
after dots into lines of at most 28 characters, so that a node is not much wider
than the others; the node's name and its tooltip keep the whole name.

Measured against Graphviz `dot` (16.1.0) on dependency graphs of real projects, both given
the same node sizes and gaps, with the layout's own default options. The first numbers are this
layout's value over `dot`'s (below 1 is better): pairs of edges that cross, total edge length,
the area of the drawing. Then, for this layout and for `dot`: by how many degrees an edge turns
on average, how often it changes the side it bends to, and how near an edge comes to a node it
does not end at, in pixels.

| Graph | Nodes, edges | Crossings | Edge length | Area | Turning of an edge (degrees) | Changes of bend per edge | Nearest node to an edge (px) |
|---|---|---|---|---|---|---|---|
| a blueprint of 58 nodes | 58, 146 | 1.01 | 0.83 | 0.89 | 48.4, 43.6 | 0.25, 0.29 | 4.9, 0.3 |
| a blueprint of 69 nodes | 69, 111 | 1.06 | 1.14 | 1.05 | 15, 18 | 0.07, 0.03 | 5.7, 1.2 |
| a code site's group view | 85, 159 | 1.13 | 1.01 | 0.97 | 44.8, 40.1 | 0.36, 0.31 | 5.7, 0.9 |
| a neighbourhood of 34 nodes | 34, 93 | 0.92 | 0.93 | 0.79 | 52.5, 43.4 | 0.29, 0.26 | 4.6, 1.3 |
| a neighbourhood of 46 nodes | 46, 119 | 1.09 | 0.88 | 1.02 | 50.1, 49.7 | 0.26, 0.42 | 5.3, 0.8 |
| another of 46 nodes | 46, 72 | 0.95 | 1.10 | 1.03 | 14.6, 14 | 0.08, 0.1 | 6, 1.8 |
| a neighbourhood of 50 nodes | 50, 152 | 0.95 | 0.85 | 0.88 | 61.7, 57 | 0.36, 0.49 | 5.4, 1.1 |
| a neighbourhood of 150 nodes | 150, 468 | 0.77 | 0.70 | 0.99 | 87.4, 83.5 | 0.75, 0.98 | 4.5, 0 |
| a neighbourhood of 290 nodes | 290, 793 | 0.86 | 0.78 | 1.22 | 69, 61.7 | 0.63, 0.66 | 4.6, 0 |
| a code site's full view, 85 groups | 2866, 5516 | 0.48 | 1.04 | 5.53 | 111.5, 108.7 | 1.06, 1.37 | 3.5, 0 |

On graphs of up to a few hundred nodes the drawings have about as many crossings as `dot`'s
(0.77 to 1.13 times), shorter edges on most, and edges that turn about as much and keep clear of
the nodes they pass, where `dot`'s touch or cross such nodes. With the groups as boxes the full
view of a large project has half of `dot`'s crossings and edges about as long (1.04 times); a
handful of its edges still pass through a group they do not end in (in `dot`'s drawing a sixth
of the edges do), and its drawing is taller than `dot`'s wide strip, five times its area. A
layout takes one to four times as long as `dot`'s on a graph of 50 to 100 nodes (0.02 to 0.1 s
against 0.02 to 0.03 s) and up to seven times as long on a dense neighbourhood of a few hundred
nodes; the full view with 85 group boxes takes about 25 s where `dot` takes 2 s, because the
layers are found again, up to twelve times, while an edge would pass through a group.

#### Node views

In pinned mode, clicking a node opens its *node view* in the graph's panel,
which widens to hold it:

- the node's informal statement on the left, when the node has one;
- its Lean declarations on the right: the highlighted source of each defining
  command with its hovers on sites built with side-by-side source (see
  "Side-by-side layout"), otherwise the signature and docstring rows of the
  Lean code panel, plus any inline Lean code of the node;
- a node with only one of the two (a code-only node from `@[blueprint]`
  without a docstring, or a statement without `(lean := ...)`) shows it at full
  width, never an empty column;
- above, the node's status glyph and status text (where a `sorry` is, an
  axiom-like declaration); below, links to the nodes it uses and the nodes
  that use it, which switch the panel to that node;
- under the informal statement, when the node also has Lean declarations, its
  source and the sentence "No tool has checked that this text says the same as
  the Lean statement.", with a link to the explanation on the Project Stats
  page; and the author's claim about the declaration, when the project has one
  ("Author's claims" below);
- an *Axioms* row listing the axioms the node's Lean declarations depend on,
  as `#print axioms` reports them, each with its class: a `sorry`
  (`sorryAx`), an extra axiom (one the project or a dependency declares) and
  an axiom that trusts compiled code (the `<declaration>._native.<tactic>.ax_*`
  axioms `native_decide` and `bv_decide` add) come first, with a short tag,
  and the standard axioms `propext`, `Classical.choice` and `Quot.sound` last.
  The row says "none" when the declarations use no axiom, and is left out for
  a node without Lean declarations.

The axioms are computed when a node is captured, once per declaration name
and environment (`Informal.Data.declarationAxioms`), and stored with each
declaration reference (`ExternalRef.axioms`) and with the declarations a
blueprint defines itself, so they are also in the site manifest's
`codeData`.

The open view is named in the page URL as `#node=<label>` (the label
URI-encoded), so a link to `Dependency-Graph/#node=<label>` or a reload opens
it again; closing the panel leaves `#node=` with no label. The fragment
changes with `location.replace`, so it adds no browser history entry, and an
embedding viewer sees each change as a same-document navigation. Hover mode
keeps the compact statement preview.

The views are rendered with the site into
`-verso-data/blueprint-node-views.json` (`{"entries": [{"label", "html"}]}`;
hover ids refer to the HTML cache's hover table) by `Informal.NodeView`, which
takes plain data, so other generators can render the same view.

Graph data is also available through documented Lean, manifest, and browser APIs.
Lean callers build a semantic `GraphModel` before traversal and cross one
finalization boundary to obtain an immutable `GraphData` record after traversal,
while browser clients can read generated manifest graph records or data embedded
in a rendered graph block. See
[`API.md#graph-data-apis`](./API.md#graph-data-apis) for the full graph API
contract and examples.

The graph uses two orthogonal status tracks:

- statement border:
  `Blocked`, `Ready to formalize`, `Formalized`, `In Mathlib`
- proof fill:
  `Not ready`, `Ready to formalize`, `Lean code incomplete`,
  `Locally formalized`, `Locally formalized + dependencies complete`

This split is intentional. For theorem-like nodes, the statement can already be
formalized while the proof still remains unstarted, in progress, or complete.

Read the proof fill states as:

- `Not ready`: the proof still depends on unfinished prerequisites
- `Ready to formalize`: prerequisites are done, but there is no associated Lean
  proof code yet
- `Lean code incomplete`: associated Lean code exists, but still has gaps such
  as `sorry`
- `Locally formalized`: the node's own Lean code is complete, but some
  dependency upstream is still not complete
- `Locally formalized + dependencies complete`: both the node and its full
  dependency closure are complete

Lean completion independently inspects the full transitive dependency closure of
associated checked declarations: their types, available values (including opaque
values), inductive constructor types, and recursor reduction rules and links.
A theorem using an unassociated admitted helper is incomplete even when its own
source has no `sorry` and the Blueprint graph has no edge for that helper.

The guarantee is conservative: **complete implies no reachable `sorryAx` in the
checked declaration closure**. Completion requires a closed inspection with
neither observed holes nor missing, hidden, or unchecked information. Lean's
cached positive axiom footprints remain useful observations. Cached absence
never certifies completion: recursive constructor traversal can leave an empty
cached footprint even when a transitive hole exists.

Blocked analysis stops after an observed witness on each axis rather than
exhaustively enumerating every reachable blocker. Breadth-first search finds
nearby admitted helpers without first unfolding large unrelated proof closures.
An axis with no observed blocker must still close its inspected graph; whole
completion always requires the full declaration certificate. Reported evidence
and verification gaps are observations, not an exhaustive hole inventory.

This assumes ordinary kernel-checked Lean artifacts and faithful checked
constant views, rather than deliberate kernel/environment manipulation.
Completion means absence of admitted `sorryAx` holes, not freedom from other
axioms, nor correctness of the intended mathematical statement. Genuine axioms
are allowed as dependencies; directly associated axiom declarations retain the
separate `axiomLike` blocking policy. Ordinary hypotheses are hypotheses.

Body access uses Lean's original declaration kind to distinguish a genuine
axiom from a hidden theorem or definition. An own-name entry in an axiom
footprint is not kind evidence: without initialized imported extension state,
the collector can synthesize that entry from a hidden axiom view. Programmatic
exported imports with `loadExts := false` therefore retain unavailable-body
coverage gaps for hidden declarations; they do not turn exposed consumers into
complete declarations. Loading the bodies with `importAll` permits ordinary
checked inspection. Original-kind lookup shares Lean's assumption that
declarations were added through its normal `Lean.addDecl` pipeline.

Known holes and verification gaps are separate facts and may coexist. Hidden
proofs remain unverified even if their cached footprint is empty. A positive
footprint proves that some hole exists, but does not reveal its origin. It can
be localized to the proof only after independently verifying the visible
statement closure; otherwise its location remains unknown. Unknown locations
block both completion tracks. Verification gaps identify the declaration, axis,
and reason (`bodyUnavailable`, `declarationUnavailable`, or
`uncheckedExpression`); they never assert that a hole was observed.

For visible bodies, identical outer lambda binder types repeating the
statement telescope belong to statement evidence. Other annotations in the body
remain proof evidence. Constructor fields belong to statement evidence. Direct
terms and inherited dependency observations retain distinct origins and both
can occur on an axis; inherited holes carry no local source-reference count.
An inherited hole or a verification failure blocks completion without proving a
local proof-writing task. Frontier advice remains tracked in
[#476](https://github.com/leanprover/verso-blueprint/issues/476).

| Inspected declaration | Known evidence | Verification | Completion |
| --- | --- | --- | --- |
| Visible clean type/body and closed clean dependencies | None | Verified | Complete |
| Visible direct `sorry` | Direct, on its observed axis | Verified or partial | Incomplete |
| Clean local body using admitted helper | Dependency, on consuming axis | Verified or partial | Incomplete |
| Constructor or nested field depending on admitted type | Statement dependency | Verified or partial | Incomplete |
| Hidden body with empty cached footprint | None unless visible evidence exists | Body unverified | Blocked |
| Hidden body with positive footprint, verified clean statement | Proof, unknown origin | Body unverified | Incomplete |
| Hidden body whose statement already explains positive footprint | Statement plus unknown-location evidence | Body unverified | Incomplete |
| Exposed body using a hidden helper with empty cache | None unless other evidence exists | Helper unverified | Blocked |
| Missing checked declaration or open dependency boundary | None unless other evidence exists | Unverified | Blocked |
| Directly associated genuine axiom | Axiom-like policy | Body intentionally absent | Blocked |
| No associated declarations | None | No declaration certificate | Blocked |

The statement track for theorem-like nodes requires verified statement coverage
and no statement or unlocalized hole. A proof-only verification gap can leave
that statement track complete; the proof track remains blocked. Definitions
require both axes for statement completion. Whole-declaration `isProved` and
agent `complete` always require the entire closure.

`ProvedStatus.incomplete` carries `IncompletenessInfo` with `knownSorry` and
`unverified` arrays. Empty incomplete payloads and default declaration statuses
are unverified, never complete and never invented sorry evidence. `SorryWhere`
and `SorryOrigin` both include `unknown`. `hasTypeGap`/`hasProofGap` describe
observed axis blockers; `hasUnverifiedType`/`hasUnverifiedProof` describe coverage.
Use completion predicates for decisions instead of testing zero source counts.

Duplicate snapshots retain each axis/origin pair and the maximum known source
count, plus every verification gap. `proved` remains a neutral merge element;
missing and axiom-like declarations retain their blocking dominance. Summary
headings use stored evidence. Summary API fields are `incompleteDecls`,
`incompleteDetails`, and `withIncompleteCode`, since blockers include uncertainty.

Lean callers use `Informal.Data.analyzeDeclaration name` in the environment
monad; the classifier fetches the canonical checked declaration itself.
Direct callers of `ConstantInfo.blueprintBodyAccess` now pass `env` and its
checked `info`, replacing the former declaration-name and axiom-footprint
arguments. The environment supplies the original-kind evidence.
`ProvedStatus.ofInspection_not_reachable` connects the production completion
constructor to the closure certificate theorem. The expression extraction and
checked-environment API form the trusted boundary of that theorem.
For agents, use `lake exe vbp query status <label>` after building the current
sources; see [API](API.md#lean-completeness-evidence).

Warning markers are reserved for structural or resolution issues such as:

- unresolved Blueprint references
- missing external Lean declarations
- Lean-owned entries that have code but no informal statement body

### Progress summary

`blueprint_summary` renders a summary page for the current Blueprint document.

The default view is an overview: it highlights overall progress, current
blockers, and the next ready work items first, while keeping deeper audit and
structural sections collapsed until needed.

That page uses dependency data, metadata, and Lean status to present:

- automatic progress counts
- blockers and incomplete declarations
- next ready work and project triage information
- grouped rollups by parent, owner, and tags

For routine project work, read the summary from top to bottom:

1. Start with **Current blockers**. Missing external declarations and incomplete
   Lean declarations usually explain why apparently small tasks are not ready.
2. Use **Actionable priorities** for work that can start now and already
   unlocks downstream entries.
3. Check **Quick wins** when you want small high-priority tasks.
4. Use **Dependency insights** and **Structure and coverage** when planning a
   larger batch of work or reviewing the shape of a Blueprint.
5. Use **Metadata audit** to keep ownership, effort, tags, and linked PRs useful
   for collaborators.

Some summary sections use deliberately practical project-management terms:

- **Actionable** entries are not locally formalized yet, and their statement or
  proof status says there is work that can start now.
- **Actionable priorities** are the actionable entries that also unlock
  downstream work. The broader **Ready now** count, quick wins, and owner/tag
  rollups still include actionable leaf entries with no dependents.
- **Quick wins** are actionable entries marked with high priority and small
  effort metadata.
- **Missing informal statement or proof** counts the nodes with Lean code that
  lack an informal statement or, for a theorem-like node, an informal proof,
  and its description gives the two parts ("Nodes with Lean code: 4 nodes
  without an informal statement, 5 nodes of the theorem-like ones without an
  informal proof; a node without either is counted once."). The Project Stats
  page counts informal statements over every node ("Informal statements: 1 of
  5 nodes has one."), so the two agree in the same terms.
- **Direct uses** count immediate statement or proof dependency edges into an
  entry. **Downstream unlocks** count entries that depend on it transitively,
  with cycles ignored.
- **Group health** rolls progress, blockers, Lean gaps, and unlock counts up by
  parent or group, and points at the next ready child when one exists.
- **Proof debt** groups incomplete or missing Lean declaration snapshots by
  parent or group.
- **Metadata audit** lists entries that have PR links and entries missing owner,
  effort, or tag metadata.

Maintainer-oriented diagnostics such as external declaration render failures are
available through an explicit summary debug option so they do not appear in the
default end-user view.

### Work queue page

`{blueprint_work_queue}` adds an unnumbered "Ready to Prove" page that lists
what can be worked on next:

```
{blueprint_work_queue}
```

It reads the same finalized dependency-graph statuses as the dependency graph
and `lake exe vbp query work-queue`: a node is listed when its statement is ready
to formalize, or, for theorem-like nodes, when its proof is ready to formalize
or its Lean code is incomplete. Ready nodes are listed first, then nodes with
incomplete Lean code, each in document order. Each entry links to its node,
says which stage is next, shows the beginning of the node's statement (about
three lines), and lists under "needs:" the direct dependencies of that stage
that are not formalized yet.

### Project statistics

Every render model carries project statistics (`Informal.Stats.ProjectStats`),
the numbers a first-time reader of a project looks for. They are captured with
the rest of the model and saved as the traversal's `stats` overview; their JSON
form is described in `doc/schemas/project-stats.schema.json`.

- **Identity**: the root package name from `lake-manifest.json`, the first
  heading and first prose paragraph of the README, the license file with a
  guess of its SPDX identifier (no license file: the field is empty), the
  `lean-toolchain` and the locked package revisions.
- **Size**: the project's modules (environment modules whose source lies under
  the project root and outside `.lake`), their declarations by kind (theorems,
  definitions, instances, structures, classes, inductives, axioms, opaques;
  generated declarations are not counted), and every `.lean` file under the
  root with its blank, comment and code lines. Comments include nested block
  comments and docstrings.
- **Build**: each file is either imported by the generator, compiled by
  another build target, or in no build.
- **Progress**: nodes by the dependency graph's fill status, for the whole
  project and per chapter (the first directory of the nodes' page addresses);
  and by kind group (`leanProgress`): for theorem-like nodes and for
  definitions, how many there are, how many are *Lean complete* (the node's
  Lean declarations, with everything they use, contain no `sorry`), how many of
  those have only Lean-complete dependencies, and how many have an informal
  statement (a statement with a body).
- **Trust**: declarations with a `sorry` of their own or through a dependency,
  with axioms outside Lean's standard three, or with proofs that rest on the
  result of compiled code (`native_decide`), plus Lean names that are missing
  and labels nobody defines.
- **Headlines** (`challenges`): for each of the project's Comparator
  challenges, the theorems it states, compared with its solution (see below and
  "Comparator challenges"). A project without a challenge has none, and
  `hasComparatorChallenge` is false.
- **Claims**: what the project's author says its Lean declarations state, from
  `informal-claims.json` (see "Author's claims" below).

The project is the folder the generator runs in. A Blueprint that is a Lake
package of its own inside the project it describes (a `blueprint/` folder with
its own `lakefile`) names the project's root where its generator is defined,
relative to that folder:

```lean
set_option verso.blueprint.projectRoot ".."
```

The statistics are then the project's (its README, license, sources and
Comparator challenge), and the Blueprint package's own files are not counted
among them.

The statistics hold no version-control data, and every path in them is
relative to the project root, so they do not change between `--reproducible`
builds of the same files. The generator reads the project's files again when it
runs, so README, license and source edits that no Lean module imports still
reach the statistics without a rebuild of the generator.

#### The headline: a Comparator challenge

A Comparator challenge states a project's main results in a module of their
own, the way `lake comparator` judges them: a challenge module states each
theorem with `sorry`, together with every definition its statement needs, and a
solution module declares the same theorems with the same statements and proves
them. A project may have several challenges, each in a folder of its own,
`Comparator/<Name>/`, with `Challenge.lean`, `Solution.lean` and the
`comparator.json` that `lake comparator` reads (the layout and its rules are in
"Comparator challenges" below):

```json
{
  "challenge_module": "Comparator.Main.Challenge",
  "solution_module": "Comparator.Main.Solution",
  "theorem_names": ["main_theorem"],
  "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"]
}
```

Each challenge gets a headline of its own. The solutions must be imported by
the Blueprint (a chapter that presents the main theorem can import its
solution), so that the environment the site is generated from has their
declarations; two solutions that declare the same name cannot both be imported,
and the second's headline then says that its solution is not imported. A
challenge is read from its compiled module without importing it; `lake exe vbp
build` builds every challenge first.

For each theorem the headline records its name, its docstring and its
statement as the challenge writes them (from the keyword to the end of the
signature), and:

- whether the solution has the **same statement**: the solution declares the
  name as the same kind of declaration with the same universe parameters and
  the same type, and every declaration of the challenge module that this type
  uses, directly or through other such declarations, is declared identically by
  the solution, type and value. A judged theorem and a definition hole (listed
  in `definition_names`) only need the same type. Constants from imports count
  as the same: imports are matched by module name, which assumes that the
  challenge was compiled against the same compiled modules the site loads (one
  build). Otherwise the first declaration that differs is named;
- whether the solution's proof is free of `sorry`, directly or through what it
  uses, and the axioms it depends on, sorted by class as in node views;
- whether those axioms are all in `permitted_axioms`, when the file lists them,
  and the axioms the verdict does not allow (`axiomsNotAllowed`): those outside
  that list, or outside Lean's standard three when there is no list;
- **proved**: the same statement, no `sorry` and no axiom that is not allowed
  (`conditionsMet`); a page says "proved" only when a kernel replay also
  accepted the theorem (below). A name in `theorem_names` that the challenge
  declares as something other than a theorem (a definition, say) is never
  judged as proved: its verdict is "Not a theorem in the challenge". The
  per-theorem verdict is about that theorem; it is not the statement that the
  whole challenge, every definition hole included, passes `lake comparator`;
- the Blueprint node whose Lean declarations include the theorem.

The other declarations the challenge introduces (its definitions) are listed
with the same comparison. When no comparison can be made, `unavailable` says
why and the theorems are listed without a verdict: the challenge has no
compiled module or one that does not match its source (also when a project
module it imports changed since the build), the module cannot be read, a module
the proof uses changed since the build (`solutionOutOfDate`: the solution
module, or a project module it imports, directly or not) or is not known to
match it (`solutionProvenanceUnknown`), with the module and its file in
`unavailableDetail`, or the site's environment lacks the solution module or a
module the challenge imports. A configuration that does not follow
the layout stops the build, so `configInvalid` is not reported.

The statements the headline shows are cut from the challenge's source, while
the verdict is about its compiled module, so the two must be the same text; the
Comparator pages show the solution's source in full too, so the solution's
compiled module is held to its source by the same build record. The
challenge is out of date when a theorem is not where the module was compiled
from, and when the source differs from the one Lake's build record of the
compiled module (`<module>.trace` beside the `.olean`) names: Lake's hash of the
source text must be the one recorded, and the record must describe the compiled
files that are read (by Lake's hash of their bytes). So an edit inside a
statement that moves no name, not built again, is out of date too. A compiled
challenge without such a record, or with one that describes other files, is not
compared (`challengeProvenanceUnknown`): it is not known which source it was
compiled from. The headline is computed with the rest of the render model. A
resident session (`vbp build --resident`) builds the challenge whenever it goes
through Lake (when it starts, and on `build --full`); a challenge edited after
that shows as out of date once the model is captured again.

What this comparison is not. It reads the compiled modules of the build the
site is generated from, and the axioms as Lean reports them for that build. It
does not build the project from its sources in a sandbox and does not replay
any proof in a kernel; `lake comparator` does both, and is the tool to run
before relying on a result. Neither says what a statement means: that a Lean
statement is the theorem of a manuscript is for a reader to judge, which is why
the page shows the challenge's docstring under its own caption and never under
the verdict.

#### Author's claims

A project can say which result of which manuscript a Lean declaration is meant
to state, so that a reader knows what to compare. `informal-claims.json` at the
project root:

```json
{
  "source": { "title": "…", "authors": "…", "version": "v2", "url": "https://…" },
  "claims": [
    { "declaration": "Project.main_theorem",
      "reference": "Theorem 2.2",
      "statement": "The informal statement, as plain text.",
      "attestations": [
        { "by": "A. Reader", "date": "2026-01-31", "note": "compared with v2" } ] }
  ]
}
```

Every field but `declaration` is optional; there is one claim per declaration.
`reference` is the result's own number in the source: a site never numbers a
node as if it were the manuscript. An attestation records that a person says
they compared the claim with the Lean statement.

The file is separate from `comparator.json` on purpose: that file configures a
judgement a tool makes, and nothing in a claim is judged. A claim is shown as
text under the caption "Author's claim", with the sentence "No tool has checked
that this text says the same as the Lean statement." and its attestations as
"Attested by NAME, DATE: NOTE", closed by "An attestation is a person's
statement, not a check." It appears on the headline card of a judged theorem,
in the node view of the declaration's node, and, for other declarations, in an
"Author's claims" band of the Project Stats page. No status, count or colour
depends on it.

### Comparator challenges

A project's Comparator challenges follow one layout, which a site build
enforces: a build of a project whose Comparator files do not follow it fails,
naming each file, the rule and the change needed. A project with no
`Comparator` folder and no `comparator.json` has no challenge and is not
affected.

#### The layout

Each challenge has a folder `Comparator/<Name>/` at the project root; a project
with one challenge has one such folder:

```
Comparator/
  Main/
    Challenge.lean      -- module Comparator.Main.Challenge
    Solution.lean       -- module Comparator.Main.Solution
    comparator.json
  SecondResult/
    ...
```

The rules, as the messages number them:

- **L1** One folder per challenge. `Comparator/Challenge.lean`,
  `Comparator/Solution.lean` and a `comparator.json` at the project root (the
  layout of a single challenge) are not accepted; the message gives the moves
  (see "Moving a single challenge" below).
- **L2** `Comparator` is a folder, not a file or a symbolic link.
- **L3** Every entry of `Comparator/` is a challenge's folder whose name starts
  with an ASCII capital letter and has only ASCII letters and digits, at most 64
  characters, so that `Comparator.<Name>` is a module name without escapes.
  Entries whose names start with `.` are ignored.
- **L4** At most 64 challenges.
- **L5** No `comparator.json` outside the challenges' folders. Folders whose
  names start with `.`, `_out`, `build`, and folders that hold a lakefile of
  their own (other Lake projects, such as test fixtures) are not searched; the
  search looks at no more than 50,000 entries.
- **F1** A challenge's folder holds exactly `Challenge.lean`, `Solution.lean` and
  `comparator.json`, as regular files (not symbolic links), and nothing else
  (entries starting with `.` aside).
- **F2** `Challenge.lean` and `Solution.lean` are UTF-8 text of at most 1 MiB
  each.
- **J1** `comparator.json` is a JSON object of at most 64 KiB, with arrays and
  objects nested at most 8 deep.
- **J2** It has the keys `challenge_module`, `solution_module`, `theorem_names`
  and `permitted_axioms`; it may have `definition_names` and
  `external_kernels`; no other key (in particular not `enable_nanoda`, which
  `lake comparator` still accepts; name the checker in `external_kernels`).
- **J3** `challenge_module` is `Comparator.<Name>.Challenge` and
  `solution_module` is `Comparator.<Name>.Solution`, for the folder's name.
- **J4** `theorem_names` is a non-empty list of distinct Lean names, at most
  256, each written as Lean prints it (`Foo.bar`); these are the theorems
  judged.
- **J5** `permitted_axioms` is a list (possibly empty) of distinct Lean names,
  at most 64.
- **J6** `definition_names`, when present, is a list of distinct Lean names, at
  most 256, none of them in `theorem_names`.
- **J7** `external_kernels`, when present, maps a checker's name to a non-empty
  list of strings (its command). The site does not run these checkers; the
  site's verdict rests on its own kernel replay.
- **C1** `Challenge.lean` imports no module under `Comparator` (not its
  solution, not another challenge's module).
- **C2** `Challenge.lean` states its theorems with `sorry`: the word `sorry`
  occurs in its code (comments, strings, raw strings and character literals
  aside, and nothing after a `#exit` command, which Lean does not read).
- **C3** Every name of `theorem_names` is declared with `theorem` in
  `Challenge.lean`, and **S2** in `Solution.lean`. Names are read from the
  source text, with `namespace` and `end` followed, and a name written in full
  (`theorem Foo.bar`, `theorem _root_.bar`) taken as written.

The rules C1 to C3, S1 and S2 are read from the text of the files, not by
Lean's parser, so that the layout can be checked without building anything; a
file can be written to mislead such a reading. What a page says about a
challenge, its theorems and its solution comes from the compiled modules (the
comparison of their declarations and the kernel replay), never from these
rules.
- **S1** `Solution.lean` imports no module under `Comparator`. It may import
  the project's library.
- **K1** The project's Lake workspace can build both modules: a library holds
  them. `lake exe vbp build` checks this with the workspace it loads anyway;
  `vbp check` and `vbp comparator-check` check the files only, since loading
  a workspace whose packages are missing makes Lake fetch them. For example, in
  `lakefile.toml`:

  ```toml
  [[lean_lib]]
  name = "Comparator"
  globs = ["Comparator.+"]
  ```

The files are the project's data: they are read with the limits above, never
followed through a symbolic link, and never run; `comparator.json` is parsed
only after its size and nesting were checked.

**A project that depends on another.** The layout fixes the module names
(`Comparator.<Name>.Challenge`, `Comparator.<Name>.Solution`), so two projects
that follow it with a challenge folder of the same name have modules of the
same names. When a project depends on such a project (a Lake package, from Git
or from a path), the module has a compiled file in the build of each, and
which of them a build means depends on the order of the search path. That
challenge is then not compared, and its card says why, naming the module and
its files: "Not compared: a module of the comparison has a compiled file in
more than one directory of the search path, so which of them a build means
depends on the order of the path (Comparator.Main.Challenge: …); give the
challenges of each project folder names of their own." A kernel replay that
loads such a module gives no verdict, for the same reason ("A module name with
two files", under "Kernel replay"). A challenge whose name only one of the two
projects has is compared as usual.

**Why this layout works with `lake comparator`.** The layout is a strict subset
of what `lake comparator` accepts: a configuration file per challenge with the
four keys it requires (it accepts `definition_names`, `external_kernels` and
`enable_nanoda` besides; the layout leaves out the last), modules it builds by
name from the project's workspace, and a `theorem_names` it judges. `lake
comparator` needs the project's `lake-manifest.json` (Lake writes it when it
resolves the project's dependencies, with `lake update`). So a project that follows the layout can
run, from its root, for each challenge:

```bash
lake comparator --config Comparator/<Name>/comparator.json
```

`lake comparator` rebuilds and judges the challenge in a sandbox (Linux only);
the site's verdict is its own comparison of the compiled modules and its own
kernel replay (see "The headline" above and "Kernel replay" below).

#### Checking the layout

- `lake exe vbp build` checks the layout, rule K1 included, before it builds
  anything; a project that does not follow it stops with exit code 1 and the
  messages, one per line.
- The generators check it too: a generator run (`lake exe vbp build`,
  `vbp code-site`, or a document's own `main`) of a project that does not follow
  it fails with the messages, and the render model captured while the Blueprint
  is elaborated fails its elaboration with them.
- `lake exe vbp check` adds every violation to the errors it reports for a site.
- `lake exe vbp comparator-check` reports the violations of the files' rules
  (every rule but K1) alone, with exit code 1 when there is one and 0 otherwise,
  for continuous integration. Neither it nor `vbp check` loads the Lake
  workspace.

A message reads:

```
Comparator/Main/comparator.json: rule J3 (module names): "challenge_module" is "Comparator.Challenge"; set it to "Comparator.Main.Challenge"
```

#### Moving a single challenge

`lake exe vbp comparator-migrate [--name <Name>] [--dry-run]` moves the layout
of a single challenge into `Comparator/<Name>/` (the name `Main` by default)
and prints every change; with `--dry-run` it prints the same list and changes
nothing:

- `git mv Comparator/Challenge.lean Comparator/<Name>/Challenge.lean` and the
  same for `Solution.lean`, for a file Git tracks; a file Git does not track,
  or any file outside a Git work tree, is moved by a plain rename (`mv …`);
- a `comparator.json` at the root is moved into the folder and given the new
  module names; without one, the folder gets one that judges every theorem the
  challenge declares and permits Lean's standard three axioms, which is what
  the single-challenge layout judged without the file (in a Git work tree it
  is added with `git add`);
- the module names `Comparator.Challenge` and `Comparator.Solution` and the paths
  `Comparator/Challenge.lean` and `Comparator/Solution.lean` are replaced in the
  project's Lean files (a `lakefile.lean` among them), `lakefile.toml` and
  Markdown files (whole words only; one that cannot be read stops the command
  before any change, and a symbolic link is not followed, so the file it leads
  to is left as it is).

Everything is checked before the first change, in both modes: the project has
the single-challenge layout, the folder does not exist yet, every file to be
rewritten is a regular file, and, in a Git work tree, no file the command moves
with Git or rewrites has changes that are not committed (it refuses and names
them: commit or stash them first). The changes are made all or nothing: when
one fails, every change made before it is undone, in reverse order, and the
command says so and exits with status 1.

It then checks the layout again and says what is left to change (rule K1, a
library for the challenges, for instance).

#### The Comparator pages

A site of a project with challenges has an unnumbered page "Comparator" at the
end of its table of contents, and below it one page per challenge, titled with
the challenge's name. The Project Stats page links each headline to its
challenge's page.

The page "Comparator" lists every challenge: a link to its page, its two
modules, and the verdict of each judged theorem, or "Not compared: …" with the
reason.

A challenge's page shows:

- what the challenge is, in one paragraph;
- the challenge's headline exactly as the Project Stats page shows it: each
  judged theorem with its verdict and the line under it, its Lean statement as
  the challenge writes it, the axioms the solution's proof rests on, the
  challenge's docstring and the author's claim (`informal-claims.json`) under
  their own captions, the challenge's definitions and what the comparison is
  and is not;
- what a verdict of the kernel replay leaves trusted (the sentence of the
  replay band);
- the challenge file in full and the solution file in full, highlighted as the
  side-by-side Lean column is, with hovers: on a Blueprint site from the
  modules' highlighted build (Lake's `highlighted` facet), on a site generated
  from compiled-code data from the data's constants. When no highlighted build
  matches the file, the file is shown with its syntax colours only, and a line
  says so; the text shown is always the file's;
- `comparator.json` in full;
- links: each file's source in the project's repository at the commit the site
  is built from (a GitHub checkout), the dependency graph's neighbourhood of the
  node of each judged theorem, the Project Stats page, and the
  continuous-integration run that built the site, when it was built in GitHub
  Actions (`GITHUB_SERVER_URL`, `GITHUB_REPOSITORY` and `GITHUB_RUN_ID`, each
  checked for its form; none outside it).

Every verdict on these pages is drawn by the same code from the same statistics
as the Project Stats page's headline: a page never computes a verdict of its
own. With several challenges, the Project Stats page shows one headline band per
challenge, each titled with its challenge's name, so each verdict stays exactly
what its own comparison and the replay establish.

#### What each verdict means

| Verdict | Meaning |
|---|---|
| Lean statement proved | The solution declares the theorem with the same Lean statement as the challenge (and every declaration of the challenge its statement uses is the same), its proof uses no `sorry` and no axiom the verdict does not allow, and the kernel replay's two checkers each checked the theorem with every constant it depends on and accepted it. |
| Same Lean statement as the challenge; no sorry; permitted axioms: as the compiled files report, not replayed by a kernel | The comparison's conditions hold as the compiled files report; no kernel replay stands behind it. |
| … with no verdict of a kernel replay | The same; a replay was started and stopped without a verdict. |
| Same Lean statement as the challenge; not checked by the kernel replay: it rests on an axiom outside Lean's standard three (X) … | The conditions hold, but the proof rests on an axiom outside the standard three (even one the challenge permits): a replay checks only what rests on the standard three, so it is not shown as proved. |
| Not accepted: a kernel checker rejected this build | A checker rejected the build; nothing on the site is called proved. |
| Not accepted: the two kernel checkers disagree on this build | One checker accepted and the other rejected the build. |
| Same Lean statement as the challenge; the proof uses sorry | The statement is the same; the proof is not complete. |
| Same Lean statement as the challenge; the proof rests on … | The proof uses an axiom the verdict does not allow. |
| Lean statement differs from the challenge: … | The solution's statement, or a declaration it uses, differs; the first difference is named. |
| Not in the solution | The solution does not declare the theorem. |
| Not a theorem in the challenge: … | A name of `theorem_names` that the challenge declares as something else; never judged as proved. |
| Not compared: … | No comparison was made, with the reason, in one sentence with what lies behind it in parentheses ("Not compared: the challenge module has not been built (Comparator.Demo.Challenge)."): the challenge module not built, out of date or not known to come from its source; the solution's source not the one its compiled module came from; the solution not imported or not built; a module the challenge imports missing; the compiled modules not loaded for the replay; the challenge or the solution module with a compiled file in more than one directory of the search path. |

### Project Stats page

Every site that `blueprintMain` or `blueprintMainWithPreviewData` generates has
an unnumbered "Project Stats" page at the end of its table of contents, so it
is reached from the site's navigation like the summary and the dependency
graph. It shows the project statistics on one page, in this order:

1. **Identity**: the README's heading (or the document's title; a heading that
   names no project, such as "Readme", is passed over for the package's name)
   and first paragraph; then, as labelled rows of chips, the licence (or "No
   license file"), the Lean version, the packages the project requires
   directly with the revision it asked for and the locked commit, and the
   generator's sidebar links; and the sentence that the page reports on this
   one build ("No other toolchain or revision was checked."). A chip is a link
   when its fact has a known address, and a plain chip otherwise: the licence
   to its file in the project's repository at the commit the site is built
   from (a GitHub checkout that tracks the file); the Lean version to its
   release page on GitHub (a release or release candidate of
   `leanprover/lean4`; a nightly or a custom toolchain has none); a package to
   its repository's tree at the locked commit (a `git` package from GitHub
   locked to a full commit; a `path` package or another host has none).
2. **Headline result**: a band per Comparator challenge (titled with the
   challenge's name when there are several), with a link to its page, and in it
   a card per judged theorem: its name, linked to the challenge file on the
   challenge's page; the
   verdict, worded about the Lean statement ("Lean statement proved", "Same
   Lean statement as the challenge; the proof uses sorry", "…; the proof rests
   on an axiom …", "Lean statement differs from the challenge", "Not in the
   solution"), as a pill that links to the entry of the explanation of the
   marks that explains it (and to nothing else); the node of the theorem on
   this site; the Lean statement as the challenge writes it, highlighted (with
   hovers when the challenge module's highlighted build has the same text);
   the axioms of the solution's proof, each of Lean's standard three linked to
   its account in the Lean Language Reference; then, under their own captions,
   the challenge's docstring and the author's claim. Under the cards: the
   challenge's two files, each linked to its text on the challenge's page, and
   what the comparison is and is not.
   A project without a challenge gets one line saying that a challenge would
   add a headline. "Lean statement proved" is said only when the kernel replay
   accepted the solution's theorem with every constant it depends on; when the replay
   rejected the build the verdict is "Not accepted: the kernel checker
   rejected this build" (the checker stops at its first problem, which need
   not be in this theorem's proof); when the replay accepted the theorem and
   found under it an axiom the verdict does not allow, the verdict says so
   ("…; replayed and accepted by a kernel; it rests on an axiom …, so it is
   not shown as proved"); and without a verdict of a replay it is what the
   compiled files report: "Same Lean statement as the challenge; no sorry;
   permitted axioms: as the compiled files report, not replayed by a kernel"
   (or "…, with no verdict of a kernel replay" when a replay stopped without
   one). A line under the verdict names the checker and, for a rejection,
   gives its message. The table under "Kernel replay" below gives every
   state's words.
3. **Kernel replay**: what the replay of this build established (see "Kernel
   replay" below): accepted, rejected with the checker's message, or not
   replayed with the reason; the checker and its Lean version; how many
   constants were checked and where they come from (the project, each
   dependency, Lean's own library); the declarations checked, those left out
   with the reason, and those that rest on an axiom outside Lean's standard
   three; and what a replay leaves trusted.
4. **Author's claims**, when the project supplies claims about declarations
   the headline does not judge.
5. **How far along**: how many nodes are theorems and how many definitions;
   how many of each are Lean complete; how many nodes have an informal
   statement, with the sentence that no tool has checked any of them against
   the Lean statements; then the nodes by progress status as one bar with
   counts, a legend, a link to the work-queue page when the site has one, and
   a table with one row per chapter. The page never says "proved" of a
   definition or of a count of nodes.
6. **How big**: Lean files, lines (code, comment and blank), declarations by
   kind, Blueprint nodes by kind, chapters and dependencies.
7. **Does it build**: how many Lean files the site's build compiled, how many
   declarations have a `sorry` of their own, and the Lean files on disk that
   are in no build.
8. **What the Lean code rests on**: the nodes whose declarations have a `sorry`
   (their own or through a dependency), use axioms beyond Lean's standard three
   or rest on the result of compiled code (`native_decide`), plus Lean names
   not found and references to no node.
9. **What this page reports, and what it does not**: a short explanation of
   the marks (Lean complete, the kernel replay, axioms, the headline's verdict,
   this build) ending
   with what no tool checks: that a Lean statement says what an informal
   statement, a docstring or a manuscript says. Notes elsewhere on the site
   link to it ("What this means"). A viewer that documents the marks itself
   can show one more link there: it is hidden unless the page's root element
   has `data-lean-links`, and its address is `lean:help/marks`.

It ends with a link to the summary page for the detailed breakdown. The page
is plain HTML and CSS: the bars use the shared status colour tokens, each
status with its own pattern, and their counts are written out, so colour is
never the only signal. It needs no script. The only version-control data it
uses is the address of the licence file at the commit the site is built from;
every link that leaves the site is marked with "↗".

To place the page elsewhere in the document, write the command where it
should go; the generator then does not add a second one:

```
{blueprint_stats}
```

#### Kernel replay

A site is generated from compiled modules, and what they say is what Lean's
elaborator recorded: a file can keep the kernel from seeing a declaration
(`set_option debug.skipKernelTC true`), and such a declaration has no `sorry`
and adds no axiom. It can be in the project or in anything the project
depends on. So a site says "proved", and draws the check mark, only after a
kernel replay of what the declaration concerned depends on:
`lake exe vbp build` and `vbp code-site` run one while the site is generated.

- **What is checked**: the Lean declarations of the site's nodes and the
  theorems its headline judges, each together with every constant it depends
  on: its statement, its proof or body, and so on through everything those
  mention, in the project's own modules, in its dependencies (Mathlib
  included) and in Lean's own library. Nothing is left out because of where it
  is. Constants that no such declaration depends on are not checked.
- **How**: the compiled modules are loaded into an environment. The
  declarations are taken from it and written to a file with everything they
  depend on, by the exporter of the Lean toolchain. Two checkers that ship with
  the toolchain (Lean 4.35 and later) then each check the whole file, one after
  the other, each starting from nothing but its own built-in prelude (its
  `--help` lists it: `Eq`, `Nat`, `Empty`, `False`, `Quot`, `Bool`, `And`):
  `con-leche` and `con-ron`,
  each run as `--verified --jobs=N FILE`, with `N` half the machine's hardware
  threads, at most 8 and at least 2. The checkers read the export, not the
  compiled modules. **The replay accepts only when both accept.**
- **Reading a checker's answer**: by its exit status first and its words
  second. Status 0 is an acceptance only with the checker's line `accepted N
  declarations` and `N` at least the count the generator makes of the file,
  which is the count the checkers of Lean 4.36 state, as measured on them: one
  per `def`, `thm`, `opaque`, `axiom` and `inductive` record, one for the
  quotient package when the file has its `quot` records (four of them, also
  for `Quot.mk` without `Quot.sound`), and none for the records of the axioms
  `Quot.sound` and `sorryAx`, which the checkers have built in. The count is a
  lower bound, and `N` may only be larger; it does not tell a cut-off or padded
  file from the one the worker wrote, so the file must also be exactly the one
  the worker wrote (its size) and end with a complete line, and hold at least
  one declaration: both checkers accept an empty, metadata-only or cut-off file
  with status 0. Status
  1 is a rejection only with the checker's words of rejection (`invalid: …`
  from `con-leche`, `rejected: …` from `con-ron`); status 1 with an uncaught
  exception is an error. Status 2 is a decline. Status 3 (in `con-ron`'s
  `--help`, which says it keeps `con-leche`'s exit codes: a usage error,
  malformed input or an internal error; also seen for a reduction that ran out
  of fuel), any other status, a signal, or a
  process stopped at a limit is no answer. The words of a decline differ
  between Lean 4.35 and 4.36 (4.36 says `declined (N declarations checked, M
  skipped for tolerated axioms) …`); both are read. The run times a checker
  adds to its lines are dropped from what the page quotes.
- **The verdict of the two**: accepted when both accept; rejected when one
  rejects and neither accepts, naming the checker and quoting it; **the
  checkers disagree** when one accepts and the other rejects, a state of its
  own that the page says plainly, and that counts as a rejection; otherwise no
  verdict, with the reason (a limit, a decline, an error, no answer), naming the
  checker.
- **One environment**: when the project has a Comparator challenge, the
  headline is computed again in the loaded environment, and that result is the
  one shown: the comparison with the challenge, the axioms and the export all
  come from the same loaded modules. The axioms are found by walking the
  terms, not read from the tables that compiled modules record. When the
  modules cannot be loaded, the headline says so instead of showing a
  comparison made in another environment.
- **Axioms**: both checkers decline a whole export that uses `sorryAx` or any
  axiom outside Lean's standard three (the axioms that `native_decide` adds
  among them): `con-leche`'s `--help` says so, and both do so when run. So a declaration under which the replay finds such an axiom is
  **not exported and not checked**: its node gets the warning mark with "not
  checked by the kernel replay: it rests on … (X)", and the rest of the project
  is still exported and checked. A judged theorem in that state is not called
  proved, also when its challenge permits the axiom.
- **A module name with two files**: a module is found by its name on the
  search path. When a loaded module, or the Comparator challenge, has a
  compiled file in more than one directory of the search path, which file a
  build means depends on the order of the path: the replay then gives no
  verdict and names the module and the directories. The path searched is the
  project's own build, every package in `.lake/packages` and every package the
  project's `lake-manifest.json` lists, a package from a path outside the
  project among them, and, for a Blueprint, the path Lean is given
  (`LEAN_PATH`, which Lake sets for a program it runs). Two paths to one file
  (through a symbolic link) count once. A name is looked up as the file system
  looks it up, so on a file system that ignores case two files whose names
  differ only by case are two files for one module.
- **What stays trusted**: the export, which the generator's worker writes from
  the modules it loaded with the toolchain's exporter (nothing reads it back
  against the loaded environment); `con-leche`, a checker written in Lean, with
  the Lean compiler and runtime it is built with; `con-ron`, a checker written
  in Rust, with the Rust compiler and the memory allocator it is built with (its
  `--help` names the allocator); and Lean's elaborator, for the step from the
  source text to the compiled module. The generator, the worker and the files
  they exchange are trusted as the build is. A replay says nothing about what a
  statement means.
- **A process of its own**: the generator's own process usually has the
  project's modules loaded already, and a second copy of a compiled module is
  read into memory instead of being mapped from the disk. So the modules are
  loaded and the export is written by a worker process: `vbp`, which
  `vbp build` names to the generator (`--kernel-replay-with <program>`), or a
  compiled generator itself. A generator that another program starts as a
  library is named by `VERSO_BLUEPRINT_KERNEL_REPLAY_WORKER`: the program, then
  each argument that comes before the generator's own, one per line. The
  worker runs with `LEAN_SYSROOT` set to the toolchain the modules are loaded
  on. A generator run by `lean --run` without a worker has no replay: it gives
  no verdict and says why.
- **Limits**: the worker and the two checkers run at a lower priority, one
  after the other, with a time limit for the whole replay (900 seconds;
  `VERSO_BLUEPRINT_KERNEL_REPLAY_SECONDS` sets another), a memory limit for
  each process (a quarter of the machine's physical memory;
  `VERSO_BLUEPRINT_KERNEL_REPLAY_MEMORY_MB`, in MiB, sets another, `0` none)
  and a size limit for the export (4 GiB;
  `VERSO_BLUEPRINT_KERNEL_REPLAY_EXPORT_MB`, in MiB, sets another, `0` none).
  A replay that is stopped at a limit is reported with the limit, never as
  accepted. The limits are enforced by polling, not by the system: a process's
  memory is read from its process id twice a second (its physical footprint on
  macOS, its anonymous and swapped memory on Linux, its resident size
  elsewhere, so the pages of compiled modules mapped from the disk are not
  counted), a peak between two readings is not seen, a reading that cannot be
  made is skipped, and a process over a limit is stopped (the immediate child;
  the checkers start no process of their own). What a process writes is kept up
  to 1 MiB per stream; the rest is read and dropped.
- **Cost**: it grows with what the declarations depend on, and with loading
  the compiled modules and reading their headers, not with the size of the
  project. A small project on Lean's own library is checked in seconds; a
  project that uses a broad part of Mathlib has tens of thousands of constants
  to export and check and an export of several hundred megabytes.
- **Not twice**: the key of an export both checkers accepted is recorded: the
  SHA-256 of the export's contents and its count of declarations (as above), with
  both checkers, each by its name, the SHA-256 of its program file and its Lean
  version. A later build writes the export again, and when its key is recorded
  the checkers are not run; the page then says that an identical export was
  accepted in an earlier run. Any change to a constant that a declaration
  depends on changes the export, and any change to either checker's file
  changes the key. The record is the file `VERSO_BLUEPRINT_KERNEL_REPLAY_RECORD`
  names (empty for no record), or else `verso-blueprint/kernel-replay-checkers.json` in
  the user's cache directory (`~/Library/Caches` on macOS, `$XDG_CACHE_HOME` or
  `~/.cache` elsewhere, `%LOCALAPPDATA%` on Windows; a file of its own, so that
the record of a generator with one checker is left as it is). By default it is never in
  the project's own folders: a record states that the checkers accepted
  something, and a project cannot bring that statement with it; a path the
  variable names is used as given, since the environment is the user's. Two
  generators writing the record at once can lose an entry, which only means a
  second check: the record is read again and merged just before it is
  replaced. (Code that a build runs with the user's rights can write the
  record, as it can write the site itself: building a project is trusting its
  build.)
- **The checkers**: `con-leche` and `con-ron` in `LEAN_SYSROOT`'s `bin` (Lake
  sets it), or beside the running `lean`; `VERSO_BLUEPRINT_CON_LECHE` and
  `VERSO_BLUEPRINT_CON_RON` name other programs. `VERSO_BLUEPRINT_KERNEL_CHECKER`
  is `off` to switch the replay off; any other value of it gives no verdict and
  says that the checkers are named by the two variables; a variable that names
  a file that does not exist gives no verdict and says so. A toolchain that ships
  neither (Lean before 4.35) gives no verdict: "this project's Lean (vX) ships no
  con-leche or con-ron".
- **Switching it off**: `lake exe vbp build --no-kernel-replay`,
  `vbp code-site --no-kernel-replay`. A generator run directly replays only
  with the flag `--kernel-replay` or `(kernelReplay := true)` passed to
  `blueprintMain` or `blueprintMainWithPreviewData`. Without a replay every
  verdict and mark says what the compiled files report.

##### Colour follows the replay

Green is a statement too, so a success colour is drawn only where a kernel
replay accepted the Lean code concerned (a status legend's sample check mark is
neutral, since it is about no node). Syntax highlighting and the badges of
proof relations use colours of their own, which are not success colours, and a
custom stylesheet can of course define any colour. The rule is the check
mark's:

- **A node** (its fill and border in the dependency graph, its mark, the
  status chips of its Lean code) is green only when the accepted replay
  covers every Lean declaration of the node, each with everything it depends
  on (both checkers accepted the export that holds them). A
  declaration whose module is not known, or that is not in the compiled
  modules that were loaded (a code block in a file that is run as a script and
  never compiled, say), is covered by nothing: the node keeps the neutral
  mark ◇, with the reason "not part of the replay". A node that rests on an
  axiom of the project or on the result of compiled code is not checked: it has
  the warning mark and a grey fill. The graph's darker fill,
  "dependencies too", needs the same of every node the node depends on;
  otherwise the node is drawn as complete on its own.
- **Counts, bars and legends** (the progress bars and their legend on the
  Project Stats page, the cards of the Blueprint Summary, the legend of the
  dependency graph) are about every node at once. They are green only when the
  replay accepted the build, leaves no node with Lean code uncovered, found no
  node without `sorry` resting on an axiom outside Lean's standard three, and
  no node's Lean source is not known to be the text that was compiled ("Source
  text and the build"). Otherwise they are grey, and each says what it rests on, in words
  that are true of the site in its state (the table below): nothing
  replayed, no verdict, a rejection, or an accepted replay with the nodes it
  does not cover and the nodes that rest on such an axiom, with the reason
  once per page. The Project Stats page lists the nodes a replay did not
  cover and the nodes that rest on such an axiom.
- **After a rejected replay** nothing on the site is green: the headline and
  the sentence beside the counts are in the error colour, and fills, bars and
  cards are grey. This holds for every node, also those no checker complained
  about: a checker names the first declaration it rejects, and what else it
  would have rejected is not known. The same holds when the two checkers
  disagree.

In the stylesheets a success colour is a custom property with two values
(`Informal.StatusColors.successColors`): `--bp-color-status-formalized`, for
example, carries the neutral value, `--bp-color-status-formalized-accepted`
the green one. An element behind which an accepted replay stands has the class
`bp_replay_accepted` (or the attribute `data-bp-replay-scope="accepted"`), and
inside it the properties take their green values; `bp_replay_none` and
`bp_replay_rejected` switch them back. A page or a custom stylesheet that
carries none of these classes shows no green. In the graph data a node's
field `replay` (`none`, `accepted`, `acceptedWithDependencies`) says the same,
and its `visual` colours follow it.

##### Source text and the build

A page shows a declaration's source as the file reads when the site is
generated, beside what the build established about the compiled module: its
mark, its colour, "no sorry", the kernel replay's verdict. So every module
whose source a site shows is held to the build that compiled it, and a module
whose source is not known to be that text gets **no positive mark** for its
declarations: no check mark, no success colour, no "no sorry", no count as
complete.

- **What it is compared with**: Lake's build record of the compiled module (the
  `<Module>.trace` file beside its `.olean`), which names the hash of the source
  text the module was compiled from and the hashes of the compiled files. The
  record must describe the compiled files that are there (beside it, or in
  Lake's artifact cache, `LAKE_CACHE_DIR`), and the file's text must have the
  hash the record names, both as Lake computes them. This is the check the
  Comparator pages make of a challenge and its solution.
- **When**: `vbp code-site` compares each module the data lists, whose source
  it shows, when the site is generated. A Blueprint records, while the module
  that captures the site's data is elaborated, the hash of the text each
  project module its nodes' Lean declarations are in was compiled from (from
  the module's build record; for the module being elaborated, its own text);
  the generator compares it with the file when it runs. (A module whose
  compiled files Lake took from its artifact cache has a record that names no
  source; Lake checked it against its source in the build that elaborates the
  Blueprint, so its text then is taken as the one compiled, unless the file
  was modified after the record was written. A site from
  compiled code, generated later, has no such build behind it: there such a
  module is not known to match.) A generator that is
  run again without a build after a file was edited therefore shows that
  file's declarations with no verdict. Modules checked out as dependencies
  (`.lake/packages`) are not compared: no page shows their source.
- **What is shown**: such a declaration's mark is ◌, with the words "Lean
  proof: the source of M (F) changed since the build, so nothing is shown as
  checked: what the compiled files report and what a kernel replay found are
  about the compiled modules as they were built, not the sources as they read
  now" (or "… is not known to match
  the build: WHY, …" when no build record says which text it was, with the
  reason: the record is missing, describes other compiled files, does not name
  the file, or the compiled module was not found). The same words are the
  node's tooltip and accessible name in the dependency graph, whose fill is
  neutral (`proofStatus` `sourceChanged`, its own legend entry); the Lean-code
  entry and the badges of its declarations say "source changed since the
  build"; a node that depends on such a node is not complete with its
  dependencies. A source excerpt of a site from compiled code is headed
  "Source, not the compiled one" with the sentence why; a Blueprint shows no
  highlighted source of such a module at all (the side-by-side layout falls
  back to the signature), and the status badge its declarations were rendered
  with is replaced.
- **Counts**: such a node is in a bucket of its own on the Project Stats page
  ("Lean source changed since the build, in its module or a project module it
  imports, or not known to match it, not shown as checked") and in the statistics' `progress.sourceChanged`, never among the
  complete ones; an accepted replay then does not make the counts green, and
  the sentences about the site add "the Lean source of C nodes changed since
  the build or is not known to match it". The replay band on the Project Stats
  page names the modules, each with why, and lists the nodes. The statistics
  carry the modules (`sourceChanged`) and, for a Blueprint, what was recorded
  when its data was captured (`builtSources`).
- **Modules a module imports**: a compiled module is built against the
  compiled modules it imports, so a module whose own source is the text that
  was compiled is still not known to match the build when a project module it
  imports, directly or not, changed since the build or is not known to match
  it (a lemma of the library turned into `sorry`, say); Lake would rebuild it.
  Its declarations get the same ◌ mark, with the module that changed named:
  "Lean proof: M (F) imports M2 in F2, which changed since the build, so
  nothing is shown as checked: …" (and, with several, how many others). The
  imports are read from the module's source as Lake reads them, and only from
  a source known to be the text that was compiled, so they are the compiled
  module's; a module that changed is not followed further. Only the project's
  own modules are followed: a module of a package the project depends on, or of
  Lean, is not checked (no page shows its source, and its build is the
  package's, at the revision the project's manifest pins). A Blueprint records
  the text of each project module its nodes' modules import, directly or not,
  as it does for the nodes' modules.
- **The headline**: a Comparator challenge's verdict is about the compiled
  challenge and solution and everything they rest on. So the challenge module
  and the project modules it imports, and the solution module and the project
  modules it imports, directly or not, must each be the text that was
  compiled; otherwise the challenge is not compared, on every page that shows
  it, with the module named: "Not compared: a module the proof uses changed
  since the build (M in F); build it again after an edit.", "Not compared: a
  module the proof uses is not known to match the build (M in F: WHY).", or,
  for a module the challenge imports, "Not compared: the compiled challenge
  module does not match its source (it imports M in F, which changed since the
  build); …". The check is made when the headline is computed (in the replay's
  worker, against the modules it loads) and once more just before the pages are
  written, so an edit while the site is generated takes the verdict back too.
- **Cost**: one read of each such module's build record, and Lake's hash of
  its source and of its compiled files (`.olean`, `.olean.server`,
  `.olean.private`). Lake hashes them the same way when it builds.

##### What each state says

Every sentence a site prints about the replay is true of the state it is
printed in; `tests/VersoBlueprintTests/BlueprintReplayWording.lean` renders
each combination and pins its words. The replay ends in one of these kinds of
state: **accepted** (both checkers accepted); **rejected** (a checker
rejected, and neither accepted); **the checkers disagree** (one accepted, the
other rejected; counted as a rejection); **no verdict**, when a replay was
started and stopped (at its time or memory limit, a checker declined, ended
with an error or gave no answer, or the generator could not run it); and
**nothing replayed**, when no replay was run, it was switched off, the
project's toolchain ships no checker, or the export went over its limit before
the checkers ran. A replay that accepted the build covers a node when it
checked every Lean declaration of the node; it does not when a declaration was
not among those it checked or its module is not known; a declaration that
rests on an axiom outside the standard three is **not checked**. In the
sentences below, `C` is the two checkers with their version (`con-leche and
con-ron (Lean 4.35.0)`), `C1` one of them (`con-ron (Lean 4.35.0)`), `WHY` the
reason the replay gives, `X` the axioms by name, and "Lean proof" reads "Lean
definition" for a definition.

A node's mark and its tooltip:

| Replay | The node's Lean code | Mark | Tooltip |
|---|---|---|---|
| accepted, covers it | no `sorry`, no axiom or Lean's standard three only | ✓ | Lean proof complete: no sorry in it or in what it uses; checked again by C, with everything it depends on, and both accepted it |
| accepted | no `sorry`, an axiom outside the standard three (the replay found it) | ⚠ | Lean proof without sorry, as the compiled files report; not checked by the kernel replay: it rests on an axiom outside Lean's standard three (X), and a replay checks only what rests on Lean's standard three axioms alone, so it is not shown as proved |
| accepted | the same, an axiom only the replay found in the terms | ⚠ | the same, ending "(the replay found it in the terms; the compiled files report none)" |
| accepted | `native_decide` | ⚠ | the same, with "it rests on the result of compiled code (X)" |
| accepted, does not cover it | no `sorry` | ◇ | Lean proof without sorry, as the compiled files report; not replayed by a kernel (not part of the replay: WHY) |
| rejected | no `sorry`, no axiom outside the standard three | ⊘ | Lean proof not accepted: C1 rejected this build (both, when both did) |
| the checkers disagree | no `sorry`, no axiom outside the standard three | ⊘ | Lean proof not accepted: the two checkers disagree on this build: C1 accepted it and C2 rejected it |
| rejected or disagree | no `sorry`, an axiom the compiled files report, or `native_decide` | ⚠ | Lean proof without sorry, as the compiled files report, resting on X; not accepted: … (as above) |
| no verdict | no `sorry` | ◇ | Lean proof without sorry, as the compiled files report; no verdict of a kernel replay (WHY) |
| no verdict | no `sorry`, an axiom the compiled files report, or `native_decide` | ⚠ | Lean proof without sorry, as the compiled files report, resting on X; no verdict of a kernel replay (WHY) |
| nothing replayed | no `sorry` | ◇ | Lean proof without sorry, as the compiled files report; not replayed by a kernel (WHY) |
| nothing replayed | no `sorry`, an axiom the compiled files report, or `native_decide` | ⚠ | Lean proof without sorry, as the compiled files report, resting on X; not replayed by a kernel (WHY) |
| any | a `sorry` in the proof or in what it uses | ◐ | Lean code incomplete: a sorry in the proof or in what it uses (the status) |
| any | its module's source changed since the build | ◌ | Lean proof: the source of M (F) changed since the build, so nothing is shown as checked: what the compiled files report and what a kernel replay found are about the compiled modules as they were built, not the sources as they read now |
| any | its module's source is not known to match the build | ◌ | Lean proof: the source of M (F) is not known to match the build: WHY, so nothing is shown as checked: … (as above) |
| any | a project module its module imports changed since the build | ◌ | Lean proof: M (F) imports M2 in F2, which changed since the build, so nothing is shown as checked: … (as above) |

The reasons `WHY` of the new states read: a decline, "C1 declined to check the
export: the checker's words"; no answer, "the replay could not run to a
verdict: C1 gave no answer (status 3: the checker's words)", or "… C1 ended with
an error (…)", or "… C1 gave no answer (status 0, and it said it accepted N
declarations, but the export holds M)"; a toolchain without checkers, "this
project's Lean (vX) ships no con-leche or con-ron" (or names the one missing).

The headline, for a theorem of the Comparator challenge that meets the
comparison's conditions (the same Lean statement, no `sorry`, no axiom the
verdict does not allow as the compiled files report). A theorem that does not
meet them keeps its verdict ("…; the proof uses sorry", "…; the proof rests on
an axiom …", "Lean statement differs …", "Not a theorem in the challenge …") in
every state, without a line under it. A site without a challenge shows the one
line that a challenge would add a headline.

| Replay | Verdict | Line under it |
|---|---|---|
| accepted, covers the theorem | Lean statement proved | Kernel replay: C each checked this theorem and every constant it depends on, in this project, in its dependencies and in Lean's own library, starting from its own built-in prelude, and both accepted it. (Recorded: "… (in an earlier run, for an export identical to this build's)."; a reproducible build: "… (in this run, or in an earlier one for an export identical to this build's).") |
| accepted, the theorem rests on an axiom outside the standard three | Same Lean statement as the challenge; not checked by the kernel replay: it rests on an axiom outside Lean's standard three (X), and a replay checks only what rests on the standard three alone, so it is not shown as proved | Kernel replay: not checked: it rests on an axiom outside Lean's standard three (X), and a replay checks only what rests on the standard three alone. |
| accepted, does not cover it | Same Lean statement as the challenge; no sorry; permitted axioms: as the compiled files report, not replayed by a kernel | No kernel replay: not part of the replay: WHY. |
| rejected | Not accepted: a kernel checker rejected this build | Kernel replay: C1 rejected this build: the checker's words. The replay covers the whole build, and a checker stops at the first declaration it rejects, so a rejection stands against every theorem judged on this site, also one whose proof does not use the rejected declaration. |
| the checkers disagree | Not accepted: the two kernel checkers disagree on this build | Kernel replay: the two checkers disagree on this build: C1 accepted it and C2 rejected it: the rejecting checker's words. The replay covers the whole build, … (as above) |
| no verdict | Same Lean statement as the challenge; no sorry; permitted axioms: as the compiled files report, with no verdict of a kernel replay | No verdict of a kernel replay: WHY. |
| nothing replayed | Same Lean statement as the challenge; no sorry; permitted axioms: as the compiled files report, not replayed by a kernel | No kernel replay: WHY. |

The axioms of the solution's proof are listed under the verdict. Beside "Lean
statement proved" the line reads "Axioms of the solution's proof", with "no
axioms" or "the standard axioms of Lean's logic only"; beside any other verdict
it reads "Axioms of the solution's proof, as the build reports them, not
confirmed by the kernel checkers", with "none reported" or "only the standard
axioms of Lean's logic reported", so that it does not read as a finding beside
a verdict that is not one.

The site as a whole: the words after a legend entry or a bucket of
`sorry`-free code (graph legend, Project Stats bar and legend), the sentence
after a summary card's description, and the sentence above the counts
(Project Stats, Blueprint Summary). Under an accepted replay of every node
there are none, and the counts are green. `U` is the number of nodes with Lean
code the replay does not cover, `R` the number of nodes without `sorry` that
rest on an axiom outside the standard three, `C` the number of nodes whose Lean
source is not known to be the text that was compiled ("Source text and the
build"), and `E` the clauses about them: "U nodes with Lean code are not part
of the replay", "the Lean source of C nodes changed since the build or is not
known to match it" and "R nodes without sorry rest on the axiom X" (in the
singular for one node). A node whose Lean code is the axiom itself (declared
without a proof) is not one of the `R`: it has the warning mark of its own
("Declared without a proof or a body … assumed, not proved") and is never
counted as complete.

| Site | Beside an entry | After a card | Above the counts |
|---|---|---|---|
| accepted, every node covered, none resting | (none) | (none) | (none) |
| accepted, U, C or R positive | (the kernel replay accepted the build; on this site E) | Counted as the compiled files report: the kernel replay accepted the build, and on this site E, so it was not checked and is not shown as proved. | The kernel replay accepted the build, and the counts are as the compiled files report: E, so it was not checked and is not shown as proved. |
| rejected, or the checkers disagree | (a kernel checker rejected this build) | A kernel checker rejected this build. | A kernel checker rejected this build: the counts say what the compiled files report, and nothing here counts as checked by a kernel. |
| no verdict | (as the compiled files report, with no verdict of a kernel replay) | Counted as the compiled files report, with no verdict of a kernel replay. | The counts are as the compiled files report, with no verdict of a kernel replay: WHY. |
| nothing replayed | (as the compiled files report, not replayed by a kernel) | Counted as the compiled files report, not replayed by a kernel. | The counts are as the compiled files report, not replayed by a kernel: WHY. |

(The clause "so it was not checked and is not shown as proved" follows the
clause about resting nodes only; a site whose replay leaves only uncovered
nodes ends the sentence after E.)

The replay band on the Project Stats page starts with "Accepted: C each checked
… starting from its own built-in prelude, and both accepted them." or "Accepted: C
both accepted an export identical to this build's in an earlier run: …" (a
reproducible build: "Accepted: C both accepted this build's export, in this run
or, for an identical export, in an earlier one: …") after an acceptance (also
when it does not cover every node: the band then lists those nodes, and the
nodes not checked because they rest on an axiom); "Rejected: C1 rejected this
build (the export of this site's declarations and what they depend on). Nothing
on this site counts as checked by a kernel." after a rejection; "Rejected: the two
checkers disagree on this build: C1 accepted it and C2 rejected it. Nothing on
this site counts as checked by a kernel." after a disagreement; "No verdict of
a kernel replay: WHY. The marks on this site say what the compiled files
report." and "Not replayed by a kernel: WHY. The marks on this site say what the
compiled files report." otherwise. Below it the band lists each checker's
answer ("con-leche (Lean 4.35.0) accepted the export (N declaration records)
(12 s, at most 410 MiB of memory); its file's SHA-256 begins …", "con-ron (Lean 4.35.0) rejected the export:
…"), without the time and memory in a reproducible build.

These tests pin the functions that print the words and selected rendered
components (the Project Stats page in each site state, a node's code status);
they do not render every full page in every state.

To leave the page out, pass `(statsPage := false)` to `blueprintMain` or
`blueprintMainWithPreviewData`, or run the generator with the flag
`--no-stats-page` (`lake exe vbp build --no-stats-page` hands it on). Such a
build also removes the page an earlier build wrote into the same output folder.
TeX and PDF output never get the page.

### Bibliography page

`blueprint_bibliography` renders the bibliography entries
registered in the document.

Projects that do not use citations can omit this page entirely.

### Math-enabled previews

Blueprint pages support shared previews in generated HTML, including math
rendering through KaTeX.

## Metadata Export and Preview Data

Blueprint builds emit two preview-data files:

- `html-multi/-verso-data/blueprint-manifest.json`
- `html-multi/-verso-data/blueprint-html-cache.json`

Most authors do not need these files for routine writing. They are mainly
useful for:

- runtime preview support in generated sites
- tooling and integration work
- metadata export for other tools
- inspection and debugging

For informal blocks, these files are the same semantic manifest and opaque
rendered-fragment cache used by generated previews, grafts, Slides, and custom
clients. See [`API.md#generated-data-files`](./API.md#generated-data-files)
for the current consumer contract. The manifest may also include VBP-internal
generated-data markers for stale-artifact diagnostics; those markers are not
part of the public interface.

After building the relevant Lean targets, useful inspection flags on a
Blueprint generator are:

```bash
lake lean <GeneratorMain>.lean -- --run <GeneratorMain>.lean --dump-schema
lake lean <GeneratorMain>.lean -- --run <GeneratorMain>.lean --dump-manifest
lake lean <GeneratorMain>.lean -- --run <GeneratorMain>.lean --dump-html-cache
lake lean <GeneratorMain>.lean -- --run <GeneratorMain>.lean --help
```

- `--dump-schema` prints the JSON Schema for the manifest
- `--dump-manifest` prints the generated manifest JSON instead of writing the
  site and then reading the file
- `--dump-html-cache` prints the rendered-fragment cache JSON
- `--help` includes these manifest-related flags alongside the usual rendering
  options

## Reusing Blueprint Nodes and Previews

Blueprint has one reusable preview data model. Manual pages can graft from the
current traversal state, Slides and generated audit pages can graft from the
manifest/cache files emitted by a Blueprint site, and browser-side UI can
resolve and insert previews after the page loads. See
[`API.md#generated-data-files`](./API.md#generated-data-files) for the data
contract shared by those workflows.

### Grafting a Node

Use `{blueprint_node "label"}` when an overview, introduction, roadmap, or slide
needs to feature an existing Blueprint entry without rewriting it.

In Manual documents, an ordinary informal node resolves from the current
traversal state:

```lean
import VersoBlueprint

open Verso
open Verso.Genre.Manual
open Informal

#docs (Genre.Manual) doc "Overview" :=
:::::::
:::theorem "thm:key"
The statement to feature.
:::

{blueprint_node "thm:key" -header +compact}
:::::::
```

An imported node owned by bare `@[blueprint]` or `@[blueprint "label"]` is the
other Manual case. If the label is not yet in the traversal, the command first
materializes the persistent attribute node at that source position, then
renders the same graft shell. See [Placing an attribute-owned node in a
chapter](#placing-an-attribute-owned-node-in-a-chapter) for the attribute-first
workflow and its current code/proof limitations.

In Slides decks, the same source command is available after importing
`VersoBlueprint.Slides`, but the rendered node comes from the manifest/cache
files passed to the deck generator:

```lean
import VersoBlueprint.Slides

open VersoSlides

#docs (Slides) deck "Talk" :=
:::::::
# Key statement

{blueprint_node "addition_assoc" (siteBase := "blueprint")}
:::::::
```

The first positional argument is the Blueprint label to graft. Available options
are:

- `(facet := "statement")` or `(facet := "proof")`; statement is the default
- `(displayLabel := "...")`, which overrides the displayed label/number in the
  grafted shell without changing the semantic manifest entry
- `+compact`, which omits attached Lean-code panels
- `+header` or `-header`; headers are shown by default
- `(siteBase := "...")`, for Slides decks whose manifest links should open
  against a Blueprint site hosted next to, or below, the deck

Presentation options such as `-header` and `+compact` do not create new nodes,
dependencies, groups, or manifest entries.

### Side-by-side Grafts

Use `blueprint_side_by_side` to place grafts next to each other. Add `+boxed`
when each side should be visually framed:

```lean
:::blueprint_side_by_side +boxed
{blueprint_node "thm:key" -header +compact}

{blueprint_node "thm:key" (facet := "proof") -header +compact}
:::
```

The side-by-side directive is presentation-only. Each child remains an ordinary
`{blueprint_node ...}` command with its own label and options; the directive does
not create dependencies, groups, or new manifest entries.

### Slides Generator Setup

A Slides deck that contains `{blueprint_node}` must use the Blueprint slide
wrapper. The wrapper adds the Blueprint slide CSS/JS assets, reads the manifest
and rendered-fragment cache, renders node grafts into static slide HTML, and
copies preview data into the deck output when requested.

```lean
import VersoBlueprint.Slides
import MyTalk.Deck

def main : IO UInt32 :=
  Informal.Slides.slidesMainWithBlueprintPreviews
    { outputDir := "_out/slides" }
    (previewManifest? := some "_out/site/html-multi/-verso-data/blueprint-manifest.json")
    (%doc MyTalk.Deck.deck)
```

When `previewHtmlCache?` is omitted, the wrapper looks for
`blueprint-html-cache.json` next to the provided manifest. Pass
`previewHtmlCache?` explicitly if the cache lives elsewhere.

The slide generator also seeds the deck's Verso hover table from the cache, so
cached Lean fragments keep the usual `data-verso-hover` markup instead of
embedding duplicate hover payloads into each code token.

### Generator-side Consumers

Custom generators should follow the same manifest/cache path as Slides. This is
the right layer for audit reports, dashboards, comparison pages, and other
interfaces that create their own wrappers around Blueprint nodes.

See [`API.md#lean-graft-and-render-apis`](./API.md#lean-graft-and-render-apis)
for the reusable `Informal.Graft` data shapes, manifest/cache lookup helpers,
and lower-level block-shell rendering APIs.

### Browser-side Consumers

Browser-side custom interfaces should start through
the generated ESM modules under `-verso-data/`; use `createPreview()` from
`api/preview.mjs` when the client needs the render API object. Use
`renderPreviewInto` for body fragments,
`renderCanonicalPreviewInto` for the full generated Blueprint node wrapper, and
`loadGraphs` for standalone graph-data clients.

Use [`API.md#choosing-an-api`](./API.md#choosing-an-api) when deciding between
the generated ESM modules and Lean-side graft helpers.
See [`API.md#browser-esm-apis`](./API.md#browser-esm-apis) for ordinary
`import { ... } from ...` usage, module path rules, and copyable inline
examples. See [`API.md#browser-runtime-api`](./API.md#browser-runtime-api) for
the public render API table.

### Troubleshooting Grafts

- `Blueprint node not found` means the label/facet pair did not match a
  rendered Blueprint preview. Check the label spelling and use
  `(facet := "proof")` when grafting a proof block instead of the statement.
  The diagnostic includes the requested label, facet, and normalized manifest
  key.
- `Preview manifest unavailable` in Slides means the deck generator did not pass
  `previewManifest?` to `slidesMainWithBlueprintPreviews`.
- `Blueprint HTML cache entry not found` means the manifest entry was found, but
  the matching rendered-fragment body was not in `blueprint-html-cache.json`.
  Keep the manifest and cache from the same Blueprint render. For source-backed
  external-markup entries generated with `--external-markup-render none`, a
  semantic manifest entry without a cache body is expected; custom renderers
  should treat those entries as metadata-only.
- `siteBase` only affects Slides link rewriting. Manual grafts resolve from the
  current document traversal state and do not need it.
- `-header`, `+compact`, and `+boxed` are presentation options only. They do not
  create new nodes, dependencies, groups, or manifest entries.

## Blueprint APIs

The detailed public API reference lives in [`API.md`](./API.md). It covers:

- the generated `blueprint-manifest.json` and `blueprint-html-cache.json` files
- [which API to use for each integration shape](./API.md#choosing-an-api)
- [finalized graph data](./API.md#graph-data-apis) from Lean, the manifest,
  and browser clients
- [`Informal.Graft` and manifest/cache rendering helpers](./API.md#lean-graft-and-render-apis)
  for custom generators
- [generated ESM modules](./API.md#browser-esm-apis) such as `api/preview.mjs`
  and `api/graph.mjs`
- [the public browser runtime API](./API.md#browser-runtime-api) and the
  boundary around bundled helper APIs

### Lean source anchors for embedding viewers

Generated HTML carries plain attributes that let an embedding viewer (an editor
that shows the Blueprint next to the Lean code, for example) map rendered nodes
to Lean declarations and back without scraping presentation markup:

- The root element of every node facet (statement or proof) with associated
  Lean declarations carries `data-lean-decls="<Name1> <Name2>"`: the declared
  names of its `(lean := ...)` references, space separated, including names
  that were missing when the Blueprint was built.
- The element that renders one declaration carries `data-lean-decl="<Name>"`
  and, when the declaring module and source range are known,
  `data-lean-source="<path>:<startLine>:<startCol>-<endLine>:<endCol>"`.
- The Lean code panel heading contains one jump link per present declaration,
  `lean:decl/<Name>`. Generated pages contain only this form: a declaration
  name stays valid when the Lean file is edited after the Blueprint was built,
  a source position does not. A viewer that wants to jump to a position reads
  it from `data-lean-source`; `LeanSourceAnchor.sourceHref` builds the
  matching `lean:source/<path>:<line>:<col>` link for custom generators and
  viewers that accept that form.

`<path>` is the declaring module's source path relative to its package source
directory (`Mathlib/Order/Basic.lean` for `Mathlib.Order.Basic`). Lines are
1-based; columns are 0-based UTF-16 code units, as in the Language Server
Protocol. The range is Lean's declaration range, which starts at the doc comment
or first modifier. Names are printed as Lean prints them; in links they are
percent-encoded (UTF-8) outside `A-Z a-z 0-9 . _ ~ - ' ! / :`.

Browsers have no handler for the `lean:` scheme, so the jump links are hidden
unless the page's root element has a `data-lean-links` attribute. A viewer sets
it (for example with a script injected at document start), intercepts
navigations to `lean:` URLs, cancels them, and opens the target in its editor.

## The Generator Entry Point

Blueprint projects normally expose a small generator `main` function.

In the commands below, `<GeneratorMain>.lean` stands for the Lean file that
defines the generator `main`, such as `ProjectTemplateMain.lean`.

Minimal example:

```lean
import VersoManual
import VersoBlueprint.PreviewManifest
import ProjectTemplate.Blueprint

open Verso Doc
open Verso.Genre Manual

def main (args : List String) : IO UInt32 :=
  Informal.PreviewManifest.blueprintMainWithPreviewData
    (%doc ProjectTemplate.Blueprint)
    args
    (extensionImpls := by exact extension_impls%)
```

This Blueprint-provided main wrapper owns the Blueprint-specific generation
layer around Verso's renderer. It injects the frontend assets required by
Blueprint-specific rendered surfaces, applies Blueprint's preview-data and
public-xref emission policy, and keeps downstream projects from needing to
remember those dependencies manually.

Blueprint does not keep compatibility layers for renamed helpers, documented
public entry points, read-through aliases, command aliases, or old rendering
paths. When an interface changes, update the in-repository callers, tests,
examples, and documentation together; downstream projects can migrate when
they update their pinned Blueprint revision. New generators should call
`Informal.PreviewManifest.blueprintMainWithPreviewData` directly.

For normal local and CI usage, prefer the project helper:

```bash
lake exe vbp build
lake exe vbp build --serve
```

It discovers the generator, then uses Lake to build its imports and execute it;
VBP can optionally serve the result. When the project has Comparator
challenges (see "Comparator challenges"), VBP checks their layout first and
stops when it does not hold, then builds every challenge module; a challenge
that fails to build is reported and the site is still generated. When a maintainer harness or advanced CI
job cannot use `vbp`, the equivalent lower-level command is:

```bash
lake lean <GeneratorMain>.lean -- --run <GeneratorMain>.lean --output _out/site
```

The project helper can emit TeX and compile a PDF in the same run:

```bash
lake exe vbp build --pdf
```

The PDF is written to `_out/site/pdf/main.pdf`. The default engine is
`lualatex`, run with `-shell-escape` because Verso TeX output may include
assets that require it. Use `--pdf-engine <cmd>` for another
lualatex-compatible command and `--pdf-runs <n>` to change the number of LaTeX
passes. The generated prelude uses standard TeX Live packages plus the Source
font packages; on Ubuntu CI, install `python3-pygments`, `texlive-luatex`,
`texlive-latex-extra`, `texlive-fonts-recommended`, and
`texlive-fonts-extra`, and `texlive-plain-generic`. `--pdf` implies
`--with-tex`; `--with-tex` alone still only writes the TeX tree under
`_out/site/tex/`.

### Output folders

A build writes its site into its output folder (`html-multi`, `html-single`),
which may hold an earlier build. Each build records the files it wrote in
`.vbp-generated.json` in that folder, and removes every file of the earlier
build's record that it did not write again, with the folders that leaves empty:
a chapter that was removed, or the drawing of a neighbourhood that changed, is
not left at its old address with the marks it had then. A file counts as
written by a build when it was modified after the build began. A file the
generator never wrote is on no record and is never removed, so files a person
put into the folder stay; the first build into a folder that holds an older
site without a record removes nothing.

### Checks of the written site

After a site is written, the generator checks its navigation: every link of a
`nav` element (Verso's table of contents, the buttons to the previous and next
page, a sidebar) and every link with a `bp_` class (the links the Blueprint
generates, such as "What this means") that names a place on a page of the site
(`Chapter/#id`) must find a page with that `id`, resolved against the page's
`<base href>` as a browser resolves it. A dead link fails the build with an error
that names the page and the link. Links written in the document's text are the
author's and are not checked; a fragment with `=` (`#node=…`, `#ego=…`) is state
a page's script reads, not a place, and is not checked either.

Pages are written with a viewport that lets the reader zoom
(`width=device-width, initial-scale=1`).

The title page shows when the site was compiled, the project's commit, the Lean
toolchain, and the commits of VersoBlueprint and, when the project uses them,
of Mathlib and an upstream formalization, each once: a package pinned by a commit
shows that commit, and one pinned by a branch or tag shows the name and the
commit (`v4.35.0@56a0058`). Commit subjects are not shown.

### Reproducible output

By default the title page shows when and from which commits the site was built,
and the generated preview manifest records absolute source paths. For output
that depends only on the project's content, for example to check whether a
site is up to date by comparing it with a previous build, pass:

```bash
lake exe vbp build --reproducible
```

Two such builds of an unchanged project, with the same toolchain and packages,
each into a folder of its own or into the same folder, are byte-identical. That
holds whether or not the record of accepted exports held the export: with
`--omit-build-time` the Project Stats page does not say whether an acceptance
came from this run or from the record, and leaves out the checkers' times and
memory. `--reproducible` enables three generator options, which a generator
also accepts one by one:

- `--omit-build-time` drops the "Compiled" timestamp from the build metadata,
  and the run-dependent facts of the kernel replay named above;
- `--omit-git-metadata` drops facts read from Git working trees (the project's
  and the upstream formalization's commit, and versions of path
  dependencies); versions pinned in `lake-manifest.json` and repository links
  stay;
- `--relative-source-paths` writes `sourceLocation.location.path` in
  `blueprint-manifest.json` relative to the project root (the generator's
  working directory) when the file lies under it. A Blueprint records its
  source paths relative to the workspace root already when it is elaborated,
  and a site from compiled code takes them from its data, relative to
  `--root`, so a published site names no path of the machine it was built on
  (no file under the project root by its absolute path, and a file outside it,
  such as one of the toolchain's library, by its module only).

Generators can also fix these options in code by passing
`(reproducibility := Informal.PreviewManifest.ReproducibilityOptions.all)` (or
individual fields) to `blueprintMainWithPreviewData`; command-line flags add to
that setting. GitHub source links in Lean code panels still name the project's
current commit, so they change when the project is committed, not between builds.

### Resident builds

Editing one chapter's prose and running `lake exe vbp build` again costs
seconds to a minute on a Mathlib-based project, most of it spent outside the
edit: Lake re-elaborates the chapter and the document root, and the generator
then imports the whole project once more. For an edit loop (an editor
integration, a watcher), keep a build session running instead:

```bash
lake exe vbp build --resident [--output <dir>] [--verbose] [--reproducible]
```

The session builds once, as `vbp build` does, then reads requests from standard
input, one per line:

- `build`: rebuild what changed since the last build;
- `build --full`: let Lake build the generator's imports and load them again,
  whatever changed;
- `prepare <chapter>` (a module name or source path): elaborate that chapter
  now, so that its first rebuild does not pay for importing its imports;
- `quit`, or the end of the input: end the session.

Every request ends with one line on standard output, after the generator's
usual output, so a client can wait for it:

```
vbp resident: done exit=<code> mode=<full|chapters|unchanged|prepare> ms=<wall time> chapters=<modules>
```

A module of the generator's import closure is a *chapter* when the document
root (the module of the generator's `%doc`) includes it, imports it, and is the
only module of the closure that imports it, and it does not use the module
system. When only chapters changed, and not their imports, the session
elaborates each of them again in-process (Lean's own processing pipeline, with
the options and imports Lake gives the module, reusing the chapter's imported
environment from its previous elaboration), substitutes the new chapter in the
document the generator renders, rebuilds the Blueprint state with the chapter's
new entries, and runs the generator's `main` again (`Informal.Resident`;
generators that call `blueprintMain` or `blueprintMainWithPreviewData` need no
change). The output is byte-identical to a `vbp build` of the same sources.
Anything else (a Lean module, the root, the generator file, a changed import)
goes through Lake, as `vbp build` does, and the session loads the result. A
change of `lakefile.*`, `lake-manifest.json`, `lean-toolchain` or
`.lake/package-overrides.json` ends the session with
`vbp resident: restart (<file> changed)` and exit code 3: start a new one.

The session does not rewrite the `.olean` of a chapter it elaborated
in-process; the next Lake build (in the session or a plain `vbp build`)
rebuilds it as usual. A session holds the project's environment and up to two
chapter environments in memory: on a Mathlib-based project, several GB.
Native code comes from the `vbp` executable itself, which links
VersoBlueprint and its dependencies; other precompiled libraries named by
Lake's setup for the generator are loaded as `lake lean` loads them.

### HTML and PDF Feature Support

PDF generation is a static TeX/PDF output path. It is useful for reading,
archiving, and print-oriented review, but it is not a replacement for the
interactive HTML site. Unless a generator disables the HTML modes explicitly,
`--pdf` still writes the usual HTML and preview-data artifacts in addition to
the TeX tree and `main.pdf`.

The table below describes the current built-in rendering behavior. The PDF
column refers to what appears in `_out/site/pdf/main.pdf`, not to data files
that may still be emitted alongside the HTML site. PDF status values mean:
`Supported` renders directly in PDF, `Static only` renders without HTML
interaction, `Partial` renders only selected static pieces, `Notice only`
renders a pointer to the HTML output, and `Not in PDF` is absent from
`main.pdf`.

| Feature | HTML site | PDF status | PDF output |
| --- | --- | --- | --- |
| Ordinary Manual prose, headings, lists, and structure | Full generated HTML pages | Supported | Static TeX/PDF via Verso's TeX renderer |
| Blueprint statement and proof blocks | Numbered headers, metadata chips, folding, relation panels, Lean status, previews, and authored body content | Static only | Static title and authored body content; no folding, chips, panels, or hover UI |
| Math and project TeX macros | KaTeX-rendered math, with best-effort KaTeX linting during elaboration | Supported | LaTeX math in the generated TeX/PDF; Blueprint inserts project TeX preludes into the generated TeX |
| Citations and bibliography | Linked citation and bibliography UI | Supported | Static citations and bibliography entries |
| `{uses ...}` and `{bpref ...}` inline references | Links, preview triggers, and dependency metadata | Static only | Static inline text, or the resolved target title when no inline text is provided |
| Attached Lean code | Code panels, Lean declaration summaries, hovers, and preview data | Static only | Static code content when present; no hovers, status widgets, or runtime previews |
| Attached Rust code | Styled and foldable Rust code panels | Static only | Static verbatim Rust code block |
| External Markdown or TeX markup attachments | Stored in the manifest; headers show attachment badges; bodyless Markdown-backed nodes can render source-backed HTML cache fragments | Partial | Explicit external-markup blocks render only when shown with `(display := summary)` or `(display := source)`; source-backed HTML cache bodies are not converted into PDF bodies |
| Source provenance and source-PDF spans | Source chips, manifest entries, and data/preview API access for source document ids and text/PDF spans | Not in PDF | Not shown as source chips or page overlays in the PDF |
| Dependency graph and progress summary pages | Interactive graph and summary views with runtime controls and previews | Notice only | Static notice pointing readers to the HTML output |
| Grafted Blueprint nodes, including `{includeBlueprintModule}` and attribute-owned `{blueprint_node}` placements | Rendered from current traversal preview data and emitted to the preview manifest and HTML cache | Partial | Inserted graft nodes render as a static notice; side-by-side authored content still renders statically |
| Browser preview runtime, relation panels, and interactive controls | Supported in generated HTML | Not in PDF | Not available in PDF |
| Preview manifest, HTML cache, and JavaScript APIs | Emitted for generated-data and browser consumers | Not in PDF | Not embedded in `main.pdf`; still emitted alongside HTML unless those outputs are disabled |
| Slides and other generator-side consumers | Supported through their own HTML/data render paths | Not in PDF | Not part of the `--pdf` output path |

## Sites from Compiled Code

A project without a Blueprint can still get a Blueprint site: `vbp code-site`
generates one from data about its compiled code, without a Blueprint package,
without changing the project's sources and without loading its environment.
(The kernel replay loads the compiled modules in a process of its own; its
record of accepted exports is kept outside the project, see "Kernel replay".)

```
lake exe vbp code-site --data code.json --root <project> [--output <dir>]
    [--title <text>]
    [--no-comparator | --challenge-not-built <reason>]
    [--no-kernel-replay] [--no-stats-page] [--reproducible] [--verbose]
```

The data (`doc/schemas/code-site.schema.json`, format tag
`verso-blueprint-code-1`) lists the project's modules and, for each, its
declarations in source order: name, kind, printed signature, docstring, source
range, proof status (`proved`, `sorry-here`, `depends-on-sorry`, `axiom`,
`opaque` or `unverified`; a declaration without one is `unverified`, never
`proved`), the axioms it depends on, and the other declarations
of the project it uses in its statement or only in its proof. Any tool that can
read a build can write it, for example by importing the project's modules with
`importModules` and walking each constant's type and value. Unbuilt and skipped
modules may be listed; the front page names them. A module's `source` is read
only when it names a file inside `--root`: a relative path without `..`, whose
real path (every symbolic link resolved) lies under the real path of the root,
a regular file of at most 16 MiB. Any other source is not read, the site names
no file for that module, and the generator prints a warning. Optionally, each declaration
lists the constants its source mentions and where (`occurrences`, as a
module's `.ilean` file records them), and the data gives, once per constant,
the hover a reader sees on it (`hovers`: its printed signature and docstring).
A declaration may carry an informal statement (`statement`: its `text`, an
optional `proof` and `title`, and the `source` the producer found it in, such
as a LaTeX blueprint or a docstring), written as Markdown with TeX math
between `$…$` and `$$…$$`; `texPrelude` holds TeX definitions (`\newcommand`
lines) put before every formula of the statements, as a written Blueprint's
`tex_prelude` is.

The site is an ordinary Blueprint site:

- one chapter per module with declarations (the front page counts both),
  starting with the module's docstrings (`/-! … -/`,
  read from its source as Markdown with raw HTML shown as text, formulas between
  `$…$` and `$$…$$` and in Verso's docstring syntax, `` $`…` `` and
  `` $$`…` ``), with a node per declaration: theorems are
  theorems, everything else is a definition. Nothing is numbered: a node is
  titled by its kind and its declaration's name, a chapter by its module, and
  the front page says so, because a number on such a site would read as the
  number of a result in the project's manuscript. A node with a
  statement in the data shows it as on a written Blueprint: in its chapter card
  and in the graph's node view, beside the Lean side, its title in bold, its
  formulas typeset when the site is built (by KaTeX in the page when one is not
  accepted then), its proof below it (folded in the node view); the statement's
  Markdown is read with raw HTML shown as text and link
  targets other than web, mail and site-relative ones dropped. Under the
  statement a line names its `source` ("Informal statement from the docstring ·
  not checked against the Lean statement"). A node without
  one shows the Lean side alone. The Lean side is an API entry: the signature
  and the source excerpt read from `--root`,
  highlighted (`Informal.CodeSite.Highlight`: a lexer for the token classes,
  the data's occurrences for the constants, with their hovers), the docstring
  rendered as Markdown (raw HTML shown as text, link targets other than web,
  mail and site-relative ones dropped; a module whose source is not known to be
  the text that was compiled gets no positive mark, "Source text and the
  build"), where it is defined (a link to the file
  on GitHub when `--root` is a GitHub checkout), a link to its neighbourhood in
  the dependency graph, the status and the axioms;
- the search box finds declarations by name (as Lean constant documentation),
  modules by name and docstring text, and the text of the statements
  (`Block.declSearch`);
- the dependency graph, with one group per module, drawn at build time; above
  300 declarations it opens on the group view
  (`GraphBlockData.initialView`);
- the summary page, the Project Stats page (the files, identity and
  Comparator challenges of `--root`) and the Comparator pages. When the project
  has challenges, their solution modules and the challenges' imports are
  imported from the project's
  build (`--root`'s `.lake` directories, with the Lean installation that
  `LEAN_SYSROOT` names or `lean` on the `PATH` finds) and the headline is
  compared as on a Blueprint site; when that is not possible the card says why.
  `--no-comparator` leaves the comparison out; `--challenge-not-built <reason>`
  is for a caller that tried to build the challenges first and could not:
  nothing is compared and every card says its challenge module was not built,
  with the reason. Without a challenge there is no card. A project whose
  Comparator files do not follow the layout is not generated;
- the left navigation bar and the side-by-side card style.

What highlighting from data cannot give, compared with a Blueprint's
elaborated sources: local variables' types, hovers on notation and tactics,
tactic states and messages.

Nothing is inferred beyond the data: a use is an edge only when both
declarations are in it, and a `sorry` of a declaration's own is shown as a gap
in its proof.

## Blueprint Options

Set Blueprint options with ordinary Lean `set_option` commands in the module
that elaborates the Blueprint chapter or document:

```lean
set_option verso.blueprint.numbering global
set_option verso.blueprint.subNumberingPrefix full
set_option verso.blueprint.subNumberingCounter prefix
set_option verso.blueprint.foldProofBlocks true
set_option verso.blueprint.foldCodeBlocks false
```

Current options:

- `verso.blueprint.numbering`
  - default: `sub`
  - `sub`: prefixed numbering such as `Theorem 1.3.2`; the prefix and counter
    are controlled by the sub-numbering options below
  - `global`: document-order numbering such as `Theorem 27`
  - `local`: unprefixed local numbering without a chapter prefix
  - `none`: no numbers; a block is titled by its kind and its label (`Theorem
    Project.main_theorem`). For documents whose order is not a numbering a
    reader could cite: a site generated from code uses it, so that no number
    there can be taken for the number of a result in a manuscript
- `verso.blueprint.subNumberingPrefix`
  - default: `full`
  - `full`: use the full numbered section path, such as `1.3`
  - `first`: use only the first numbered ancestor, such as `1`
- `verso.blueprint.subNumberingCounter`
  - default: `prefix`
  - `prefix`: reset the block counter for each rendered prefix, such as
    `Theorem 1.3.2`
  - `document`: use the document-order block count after the prefix, such as
    `Theorem 1.93`

Set `verso.blueprint.subNumberingPrefix first` together with
`verso.blueprint.subNumberingCounter document` to recover chapter-only
prefixes with document-order block counts.

- `verso.blueprint.foldProofs`
  - default: `true`
  - folds proof bodies in rendered Lean code panels after `by`
- `verso.blueprint.foldProofBlocks`
  - default: `false`
  - renders proof blocks as collapsed disclosure blocks
- `verso.blueprint.foldCodeBlocks`
  - default: `false`
  - renders Lean, Rust, and external code panels as collapsed disclosure blocks,
    including panels produced by attribute-owned `{blueprint_node}` placements
    and `{includeBlueprintModule}`
- `verso.blueprint.trimTeXLabelPrefix`
  - default: `false`
  - trims TeX-style label prefixes when deriving Lean names
- `verso.blueprint.math.lint`
  - default: `true`
  - runs best-effort KaTeX validation during elaboration
  - uses a local `node` executable from `PATH`; the worker source and KaTeX
    runtime are embedded in imported Lean artifacts, and linting is silently
    skipped if Node cannot start or the worker protocol fails
  - set this option to `false` to disable elaboration-time math linting
- `verso.blueprint.externalCode.strictResolve`
  - default: `false`
  - upgrades unresolved or ambiguous external Lean names from warnings to errors
- `verso.blueprint.externalCode.sourceLinkTemplate`
  - default: `""` (automatic GitHub links when the source file belongs to a
    Git checkout with a GitHub `origin` remote)
  - builds source links for external declarations using `{path}`, `{relpath}`,
    `{module}`, `{line}`, `{column}`, `{endLine}`, and `{endColumn}`
- `verso.blueprint.summary.debugDiagnostics`
  - default: `false`
  - keeps maintainer diagnostics hidden from `blueprint_summary` by default
  - set to `true` when debugging Blueprint rendering or external Lean
    declaration integration; the summary then includes diagnostics such as
    external declarations that resolved and checked but could not be rendered as
    HTML
- `verso.blueprint.graph.defaultDirection`
  - default: `TB`
  - sets the fallback graph direction for `blueprint_graph` when
    `(direction := ...)` is omitted
- `verso.blueprint.graph.defaultPack`
  - default: `true`
  - sets the fallback component packing behavior for
    `blueprint_graph` when `(pack := ...)` is omitted
- `verso.blueprint.graph.defaultPreviewMode`
  - default: `pinned`
  - sets the fallback graph-node preview behavior for `blueprint_graph` when
    `(preview := ...)` is omitted; accepts `pinned` and `hover`
- `verso.blueprint.graph.defaultPreviewPlacement`
  - default: `docked`
  - sets the fallback graph-node preview placement for `blueprint_graph` when
    `(previewPlacement := ...)` is omitted; accepts `docked` and `anchored`
- `verso.blueprint.debug.commands`
  - default: `false`
  - emits debug info logs while elaborating Blueprint graph, summary, and
    bibliography commands
- `verso.blueprint.profile`
  - default: `false`
  - enables timing logs for Blueprint directive and code-block elaboration

## Experimental Widget

The widget surface is experimental.

To enable it, import `VersoBlueprint.Widget` explicitly in the project that
wants to use it.

## Current Limits

- parent/group metadata is structural only; it does not change proof status or
  dependency edges
- group labels are metadata, not first-class reference targets
- unresolved Blueprint references currently degrade locally at the call site;
  they are not accumulated into a global diagnostics report
- Rust support currently covers only labeled inline Rust blocks with basic
  built-in syntax coloring
- Rust attachments currently do not provide diagnostics, hover data, or
  external Rust symbol references
- some rendering details and summary ranking policies are still expected to
  evolve
