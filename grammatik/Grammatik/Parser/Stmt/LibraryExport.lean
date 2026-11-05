module

public import Grammatik.Logik.Vertraege.Uebersetzung
public import Grammatik.Parser.Stmt.LibraryFixtures
public import Grammatik.Parser.Stmt.LibraryCertificates
public import Grammatik.Zielsatz.Kern.Akzeptiert
public import Grammatik.Nebenlaeufigkeit.Sperren.SperreSem
import Grammatik.Parser.Stmt.LibraryFixtureScanning
import all Grammatik.Parser.Stmt.LibraryQualifiedFixtures
import Grammatik.Parser.Stmt.LibraryFixtureProofs
import Grammatik.Parser.Elab.UebersetzeAllg3.TransitionCert
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil12
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Elaborate
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Erzeuge
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Torhuelle
import all Grammatik.Parser.Elab.Generic.StaticConformance
import all Grammatik.Parser.Elab.UebersetzeAllg3.Rest1
import all Grammatik.Parser.Elab.UebersetzeAllg3.Body
import all Grammatik.Parser.Elab.UebersetzeAllg3.Rest2a
import all Grammatik.Parser.Elab.UebersetzeAllg3.Stufe
import all Grammatik.Parser.Elab.UebersetzeAllg3.Seq
import all Grammatik.Parser.Elab.UebersetzeAllg3.Struct
import all Init.Data.Repr
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.Modify
import all Init.Data.String.OrderInstances
import all Init.Data.String.Pattern
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.Char
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Pattern.String
import all Init.Data.String.PosRaw
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Stream
import all Init.Data.String.Subslice
import all Init.Data.String.Substring
import all Init.Data.String.TakeDrop
import all Init.Data.String.Termination
import all Init.Data.String.ToSlice

@[expose] public section

namespace Gabbro.Grammatik.Uebersetzung

open Gabbro.Grammatik.Parser
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2
open LibraryFixtureProofs

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-! ## Connected export witness: a qualified library call through the pipeline.

    Source text with a qualified library call elaborates (through the certified expansion) to an
    ordinary unit, lowers, and the checker Bool holds -- on the non-degenerate two-module
    fixture with a real call, not a degenerate empty unit. Layout and image, C14/C08 and Stage-0
    closure stay with their owners. -/

/-- Whether every function body is ordinary (no library construct remains). -/
def alleOhneBibliothek : List SItemTief → Bool
  | [] => true
  | .fnT _ body :: rest => ohneBibliothekAnw body && alleOhneBibliothek rest
  | _ :: rest => alleOhneBibliothek rest

-- Use the already checked tokens and text bridge of this exact two-module source.
private def fullTokens : List Token := qualPhaseTokens

private theorem tokens_from_text (text : String) (characters : List Char) (tokens : List Token)
    (textEq : text = String.ofList characters) (scanned : lexL characters = .ok tokens) :
    (lexL text.toList).toOption.getD [] = tokens := by
  rw [textEq, String.toList_ofList, scanned]
  rfl

private theorem full_tokens : translationQualTokens = fullTokens := by
  exact tokens_from_text translationQualText translationQualCharacters qualPhaseTokens
    translation_qual_text qual_lexed

private theorem full_parse : parseTopTief fullTokens = .ok translationQualItems := by
  have complete : parseTopTief translationQualTokens = .ok translationQualItems :=
    translation_qual_phases.2.1
  rw [full_tokens] at complete
  exact complete

private theorem export_seq_succ (u : UProg) (caller : Fin u.fns.length) (fuel : Nat)
    {l : Bool} (Γ : Ctx) (fn : UFn) (Λ : List (Res (declOf u)))
    (entry : AtTop u caller Λ) (statements : List UStmt) :
    lowSeqL (l := l) u caller Γ fn (fuel + 1) Λ entry statements =
      lowSeqStep u caller (lowStufe u caller fuel) Γ fn Λ entry statements := rfl

attribute [local cbv_opaque] lowStufe lowSeqL lowStructL lowEndL uFloatLimit
attribute [local cbv_eval] export_seq_succ lowStructL_succ lowEndL_succ
  lowStufe_seq lowStufe_struct lowStufe_ende

private def checkedImage (u : UProg)
    (image : Programm (declOf u) × List (declOf u).Fn) : Prop :=
  Akzeptiert image.1 (SperrInv.leer _) image.2 (List.finRange u.locks.length)
    ((List.finRange u.tabs.length).map Sum.inl ++ (List.finRange u.globs.length).map Sum.inr) [] = true

-- The checker evidence is attached to the actual function producer results.
-- The remaining fields are arbitrary only inside this proof: the actual
-- assembler supplies its own original invariants and interface contracts.
private structure ExportFacts (u : UProg) : Prop where
  gate : u.exportGate = .ok ()
  invs : u.invs = []
  contracts : contractGate u = true
  measures : ∀ f : Fin u.fns.length, (fnAt u f).decreases = none
  functions : ∃ pieces : ∀ f : Fin u.fns.length, EnsTy u f × RumpTy u f × ReqTy u f,
    (∀ f, lowerFnAt u f = .ok (pieces f)) ∧
    ∀ (invariants : ∀ i : Fin u.invs.length, InvTy u i)
      (pointers : ∀ n, CallContract (declOf u) ((declOf u).sigNr n))
      (foreigns : ∀ a, CallContract (declOf u) ((declOf u).asignatur a)),
      checkedImage u (progOfFn u (fun f => (pieces f).1) (fun f => (pieces f).2.1)
        (fun f => (pieces f).2.2) invariants pointers foreigns, List.finRange u.fns.length)

private theorem functions_of_success (u : UProg)
    (produced : ∀ f, (lowerFnAt u f).toOption.isSome = true)
    (safe : ∀ invariants pointers foreigns,
      checkedImage u (progOfFn u
        (fun f => ((lowerFnAt u f).toOption.get (produced f)).1)
        (fun f => ((lowerFnAt u f).toOption.get (produced f)).2.1)
        (fun f => ((lowerFnAt u f).toOption.get (produced f)).2.2)
        invariants pointers foreigns, List.finRange u.fns.length)) :
    ∃ pieces : ∀ f : Fin u.fns.length, EnsTy u f × RumpTy u f × ReqTy u f,
      (∀ f, lowerFnAt u f = .ok (pieces f)) ∧
      ∀ invariants pointers foreigns,
        checkedImage u (progOfFn u (fun f => (pieces f).1) (fun f => (pieces f).2.1)
          (fun f => (pieces f).2.2) invariants pointers foreigns, List.finRange u.fns.length) :=
  ⟨(fun f => (lowerFnAt u f).toOption.get (produced f)),
    (fun f => except_ok_get (produced f)), safe⟩

private theorem export_lowered {u : UProg} (facts : ExportFacts u) :
    (lowerAllg u).toOption.isSome = true := by
  obtain ⟨pieces, origin, _⟩ := facts.functions
  apply lowering_ok u facts.invs facts.contracts
  intro f
  exact ⟨by rw [origin f] <;> rfl, facts.measures f⟩

private theorem export_checked {u : UProg} (facts : ExportFacts u)
    {image : Programm (declOf u) × List (declOf u).Fn}
    (emitted : lowerAllg u = .ok image) : checkedImage u image := by
  rcases image with ⟨program, functions⟩
  obtain ⟨pieces, origin, safe⟩ := facts.functions
  have selected (f : Fin u.fns.length) (proof : ∃ value, lowerFnAt u f = .ok value) :
      lowerAtPair u f proof = pieces f := lowerAtPair_of_ok u f proof (origin f)
  unfold lowerAllg at emitted
  split at emitted
  · cases emitted
  · split at emitted
    · cases emitted
    · split at emitted
      · obtain ⟨programEq, functionsEq⟩ := Measures.checkedProgram_eq emitted
        rw [programEq, functionsEq]
        simp only [selected]
        exact safe _ _ _
      · cases emitted

-- Three is checked against the actual elaborated function carrier at each use.
-- The equality names are explicitly substituted before evaluating a child.
local macro "export_functions" : tactic => `(tactic| (
  rintro ⟨index, bound⟩
  have size : index < 3 := bound
  have choices : index = 0 ∨ index = 1 ∨ index = 2 := by omega
  rcases choices with first | second | third
  · subst index
    cbv <;> exact Eq.refl _
  · subst index
    cbv <;> exact Eq.refl _
  · subst index
    cbv <;> exact Eq.refl _))

-- Each complete value below is inferred exclusively from a canonical success
-- equation, before any dependent function or declaration projection is used.
private theorem full_phases :
    ∃ items, parseTopTief fullTokens = .ok items ∧
      (∃ expanded, exportLibraryUnit (uMembers (pre108 items)) = .ok expanded ∧
        alleOhneBibliothek expanded = true) ∧
      ∃ unit, elabU (pre108 items) = .ok unit ∧ ExportFacts unit := by
  refine ⟨?items, ?parsed, ?expanded, ?elaboration⟩
  case parsed => cbv <;> exact Eq.refl _
  case expanded =>
    refine ⟨?expandedItems, ?expansion, ?ordinary⟩
    case expansion => cbv <;> exact Eq.refl _
    case ordinary => cbv
  case elaboration =>
    refine ⟨?unit, ?made, ?facts⟩
    case made => cbv <;> exact Eq.refl _
    case facts =>
      refine {
        gate := by cbv
        invs := by cbv
        contracts := by cbv
        measures := by export_functions
        functions := ?_ }
      refine functions_of_success _ ?produced ?safe
      case produced => export_functions
      case safe =>
        intro invariants pointers foreigns
        cbv

private theorem selected_phases :
    (∃ expanded, exportLibraryUnit (uMembers (pre108 translationQualItems)) = .ok expanded ∧
      alleOhneBibliothek expanded = true) ∧
    ∃ unit, elabU (pre108 translationQualItems) = .ok unit ∧ ExportFacts unit := by
  obtain ⟨items, parsed, expansion, elaboration⟩ := full_phases
  have itemsEq : translationQualItems = items := Except.ok.inj (full_parse.symm.trans parsed)
  rw [itemsEq]
  exact ⟨expansion, elaboration⟩

/-- The qualified caller unit through the export: the two-module source with a qualified library
    call elaborates to an ordinary unit. -/
def exportQualEinheit : UProg :=
  (elabU (pre108 translationQualItems)).toOption.getD { tabs := [], locks := [], fns := [] }

theorem export_qual_elab_zeuge :
    (elabU (pre108 translationQualItems)).toOption.isSome = true := by
  obtain ⟨unit, made, _⟩ := selected_phases.2
  rw [made]
  rfl

private theorem export_facts : ExportFacts exportQualEinheit := by
  obtain ⟨unit, made, facts⟩ := selected_phases.2
  unfold exportQualEinheit
  rw [made]
  exact facts

/-- The export leaves no ignored source duty behind on the fixture. -/
theorem export_qual_tor_zeuge : exportQualEinheit.exportGate = .ok () := export_facts.gate

/-- The expanded source: the pre-pass output on the fixture members. -/
def exportQualErweitert : List SItemTief :=
  (exportLibraryUnit (uMembers (pre108 translationQualItems))).toOption.getD []

/-- The pre-pass ran: every expanded body is ordinary. -/
theorem export_qual_ohne_zeuge : alleOhneBibliothek exportQualErweitert = true := by
  obtain ⟨expanded, produced, ordinary⟩ := selected_phases.1
  unfold exportQualErweitert
  rw [produced]
  exact ordinary

theorem export_qual_lower_ok :
    (lowerAllg exportQualEinheit).toOption.isSome = true := export_lowered export_facts

def exportQualGesenkert :
    Programm (declOf exportQualEinheit) × List (declOf exportQualEinheit).Fn :=
  (lowerAllg exportQualEinheit).toOption.get export_qual_lower_ok

-- Exact alias domains are normalized before applying the canonical selection
-- law. Consumers use this opaque theorem without comparing source formulas.
private theorem export_emitted : lowerAllg exportQualEinheit = .ok exportQualGesenkert := by
  unfold exportQualGesenkert
  exact except_ok_get (x := lowerAllg exportQualEinheit) export_qual_lower_ok

/-- The connected verdict on the full caller unit, with the original complete
    function, lock and carrier enumerations and unchanged checker defaults. -/
theorem export_qual_akzeptiert_zeuge :
    Gabbro.Grammatik.Akzeptiert exportQualGesenkert.1 (Gabbro.Grammatik.SperrInv.leer _)
      exportQualGesenkert.2 (List.finRange exportQualEinheit.locks.length)
      ((List.finRange exportQualEinheit.tabs.length).map Sum.inl ++
        (List.finRange exportQualEinheit.globs.length).map Sum.inr) [] = true := by
  exact export_checked export_facts export_emitted

end Gabbro.Grammatik.Uebersetzung
