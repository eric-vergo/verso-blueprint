/-
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

import VersoBlueprint.Informal.Block.Common
import VersoBlueprint.Axioms
import VersoBlueprint.Replay

/-!
The status mark of a node's Lean code and the words that go with it: one function
(`statusGlyph`) for every place that shows the state of a node to a reader or to assistive
technology (the heading's mark, the Lean-code link, the dependency graph's tooltip and accessible
names, the node view).
-/

namespace Informal

/-- A status glyph of the side-by-side layout: its symbol, CSS modifier and meaning. Every
meaning is about the node's Lean code; none is about its informal statement. -/
structure StatusGlyphKind where
  glyph : String
  modifier : String
  meaning : String

namespace StatusGlyphKind
/-- The check mark: only for Lean code without `sorry` that a kernel replay accepted, with
everything it depends on, while the site was generated, and under which it found no axiom
outside Lean's standard three. -/
def proved : StatusGlyphKind :=
  ⟨"✓", "proved", "Lean code complete: no sorry in it or in what it uses, no axiom outside \
    Lean's standard three under it, and two kernel checkers each checked it again for this site, \
    with everything it depends on, and both accepted it"⟩
/-- What the compiled files report, with no verdict of a kernel replay behind it (none was run,
it stopped without one, or it does not cover the code): not a check mark. -/
def reported : StatusGlyphKind :=
  ⟨"◇", "reported", "Lean code without sorry, as the compiled files report; no verdict of a \
    kernel replay stands behind it"⟩
/-- The kernel replay rejected the build. -/
def rejected : StatusGlyphKind :=
  ⟨"⊘", "rejected", "Lean code not accepted: a kernel checker rejected this build"⟩
def incomplete : StatusGlyphKind :=
  ⟨"◐", "partial", "Lean code incomplete: a sorry in the proof or in what it uses"⟩
def problem : StatusGlyphKind :=
  ⟨"⚠", "problem", "Lean code needs a look: a sorry in the statement, an axiom (declared, or \
    used beyond Lean's standard three, which a kernel replay does not check), or code that \
    could not be inspected"⟩
def missing : StatusGlyphKind := ⟨"✗", "missing", "Lean declaration missing"⟩
/-- The source of the node's Lean code, or of a project module its module imports, is not known
to be the text that was compiled: it changed since the build, or no build record says which text
it was. Nothing is shown as checked. -/
def sourceChanged : StatusGlyphKind :=
  ⟨"◌", "changed", "Lean source changed since the build, in its module or a project module it \
    imports, or not known to match it: nothing about it is shown as checked"⟩
def noLean : StatusGlyphKind := ⟨"○", "none", "No Lean declaration"⟩

/-- Every status glyph, in legend order. -/
def all : Array StatusGlyphKind :=
  #[proved, reported, rejected, incomplete, problem, sourceChanged, missing, noLean]
end StatusGlyphKind

/-- What the Lean code of a node of this kind is: a proof, or a definition. -/
def leanCodeNoun (kind : Data.NodeKind) : String :=
  if kind.isTheoremLike then "Lean proof" else "Lean definition"

/-- What a declaration free of `sorry` still rests on, from its axioms outside Lean's standard
three: compiled code (`native_decide` and similar tactics) and other axioms, by name. -/
def extraAxiomsText (axioms : Array Lean.Name) : String :=
  let compiled := axioms.filter (Data.AxiomClass.ofName · == .compilerTrusted)
  let other := axioms.filter (Data.AxiomClass.ofName · != .compilerTrusted)
  let names (xs : Array Lean.Name) := ", ".intercalate (xs.toList.map (·.toString))
  let parts :=
    (if other.isEmpty then [] else
      [s!"{if other.size == 1 then "an axiom" else "axioms"} outside Lean's standard three \
        ({names other})"]) ++
    (if compiled.isEmpty then [] else [s!"the result of compiled code ({names compiled})"])
  " and ".intercalate parts

/-- The text for `sorry`-free Lean code that rests on `axioms`, outside Lean's standard three:
the axioms, that the replay did not check it, and why there is no check mark. -/
def notCheckedText (noun : String) (axioms : Array Lean.Name) (source : String) :
    String :=
  s!"{noun} without sorry, as the compiled files report; not checked by the kernel replay: it \
    rests on {extraAxiomsText axioms}, and a replay checks only what rests on Lean's standard \
    three axioms alone, so it is not shown as proved{source}"

/-- The text for Lean code whose module's source, or a project module it imports, is not known to
be the text that was compiled, for the reason `change` ("the source of Demo.A (Demo/A.lean)
changed since the build", `Informal.Stats.SourceChange.text`). -/
def sourceChangedText (noun change : String) : String :=
  s!"{noun}: {change}, so nothing is shown as checked: what the compiled files report and what \
    a kernel replay found are about the compiled modules as they were built, not the sources as \
    they read now"

/-- What the words of a mark about the Lean code attached to a proof start with: there is no
Lean statement. -/
def noLeanStatementText : String := "No Lean statement"

/-- The Lean code a mark without a Lean statement is about. -/
def proofCodeNoun : String := "Lean code attached to the proof"

/-- The status glyph of a node and its text (the glyph's meaning for this node, then the
detailed status where it adds something). A node whose Lean code has no `sorry` but depends on
an axiom outside Lean's standard three, as the compiled files report it or as the replay found
it in the terms, gets the warning mark: the text names the axiom and says that the replay did
not check it. Nor does a node that no kernel replay covers (`replay?`, the replay made while the
site was generated, of the node's declarations and everything they depend on) get the check
mark: its mark says what the compiled files report, or that a checker rejected the build. Every
text is true of the state it is shown in: "not replayed by a kernel" only when nothing was
replayed for the node, "no verdict" when a replay stopped without one, "accepted" only after both
checkers accepted. -/
def statusGlyph (mark? : Option BlockStatusMark) (replay? : Option Replay.Result := none) :
    StatusGlyphKind × String :=
  match mark? with
  | none => (.noLean, StatusGlyphKind.noLean.meaning)
  | some mark =>
    let (kind, text) := statusGlyphOfMark mark replay?
    if mark.hasStatement then (kind, text) else (kind, s!"{noLeanStatementText}; {text}")
where
  /-- The glyph and words of `mark`; a mark without a Lean statement is about the code attached
  to the proof (`leanCodeNoun` gives way to "Lean code attached to the proof"). -/
  statusGlyphOfMark (mark : BlockStatusMark) (replay? : Option Replay.Result) :
      StatusGlyphKind × String :=
    let status := mark.status
    let noun := if mark.hasStatement then leanCodeNoun mark.kind else proofCodeNoun
    if let some change := mark.sourceChange? then
      (.sourceChanged, sourceChangedText noun change)
    else if status.isProved then
      let checker := (replay?.map (·.checkerName)).getD "the kernel checkers"
      let rejection := (replay?.map (·.rejectionText)).getD "a kernel checker rejected this build"
      let reported := mark.extraAxioms
      let resting (s : String) : String :=
        if reported.isEmpty then s else s!"{s}, resting on {extraAxiomsText reported}"
      let base := s!"{noun} without sorry, as the compiled files report"
      match Replay.provedStanding replay? mark.declarations mark.unplaced mark.sourceChange? with
      | .accepted =>
        if reported.isEmpty then
          (.proved, s!"{noun} complete: no sorry in it or in what it uses; checked again by \
            {checker}, with everything it depends on, and both accepted it")
        else (.problem, s!"{noun} without sorry; checked again by {checker}, with everything \
          it depends on, and both accepted it; the compiled files report that it rests on \
          {extraAxiomsText reported}, which the replay did not find in the terms, so it is not \
          shown as proved")
      | .notChecked found =>
        let all := Data.sortAxioms (reported ++ found)
        let source := if reported.isEmpty then
            " (the replay found it in the terms; the compiled files report none)"
          else ""
        (.problem, notCheckedText noun all source)
      | .rejected =>
        if reported.isEmpty then (.rejected, s!"{noun} not accepted: {rejection}")
        else (.problem, s!"{resting base}; not accepted: {rejection}")
      | standing =>
        let clause := standing.unreplayed?.getD "not replayed by a kernel"
        (if reported.isEmpty then .reported else .problem, s!"{resting base}; {clause}")
    else if status.isAxiomLike then
      (.problem, if mark.hasStatement then
          "Declared without a proof or a body (an axiom or an opaque constant): assumed, not \
            proved"
        else "a declaration attached to the proof is declared without a proof or a body (an \
          axiom or an opaque constant): assumed, not proved")
    else
      let kind :=
        if status.isMissing then StatusGlyphKind.missing
        else if status.hasTypeGap || status.hasUnverifiedType then .problem
        else .incomplete
      (kind, s!"{kind.meaning} ({mark.title})")

end Informal
