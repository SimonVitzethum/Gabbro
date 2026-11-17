module

public import Grammatik.Logik.Vertraege.Uebersetzung
public import Grammatik.Parser.Stmt.LibraryFixtures
public import Grammatik.Parser.Stmt.LibraryCertificates
public import Grammatik.Zielsatz.Kern.Akzeptiert
public import Grammatik.Nebenlaeufigkeit.Sperren.SperreSem
import Grammatik.Logik.Vertraege.Pruefer.Witness.Selection
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
attribute [local cbv_opaque] Invarianten.Pruefer.invariantVCB
  Vertraege.Pruefer.checkFunction
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

-- Select complete phase values before unfolding the dependent checker goal.
attribute [local irreducible] checkedImage

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
    cbv <;> (set_option smartUnfolding false in with_unfolding_all rfl)
  · subst index
    cbv <;> (set_option smartUnfolding false in with_unfolding_all rfl)
  · subst index
    cbv <;> (set_option smartUnfolding false in with_unfolding_all rfl)))

-- The unit is tied to the actual elaborator result below. Each function value
-- is retained together with its canonical success equation before checking.
private def fullUnit : UProg where
  tabs :=
    [{ name := "a::Rows", count := 2, cols := [("v", 0, 10)], breiten := [("v", 8)] },
     { name := "b::Rows", count := 2, cols := [("v", 0, 10)], breiten := [("v", 8)] }]
  locks := []
  fns :=
    [{ name := "a::consume",
       params := [("p", .ptr { space := 0, rights := { read := true }, target := .table 0 })],
       kinds := [.ptr { space := 0, rights := { read := true }, target := .table 0 }],
       res := none, held := [], puts := [], gives := [], body := [], ret := .empty },
     { name := "b::consume",
       params := [("p", .ptr { space := 0, rights := { read := true }, target := .table 1 })],
       kinds := [.ptr { space := 0, rights := { read := true }, target := .table 1 }],
       res := none, held := [], puts := [], gives := [], body := [], ret := .empty },
     { name := "caller", params := [], kinds := [], res := none, held := [], puts := [], gives := [],
       body := [.call "a::consume" [.freshPtr "a::Rows"
         { space := 0, rights := { read := true }, target := .table 0 }]], ret := .empty }]

private def produced0 : { value : EnsTy fullUnit ⟨0, by decide⟩ ×
    RumpTy fullUnit ⟨0, by decide⟩ × ReqTy fullUnit ⟨0, by decide⟩ //
    lowerFnAt fullUnit ⟨0, by decide⟩ = .ok value } := by
  refine ⟨?value, ?computed⟩
  case computed => cbv <;> exact Eq.refl _

private def produced1 : { value : EnsTy fullUnit ⟨1, by decide⟩ ×
    RumpTy fullUnit ⟨1, by decide⟩ × ReqTy fullUnit ⟨1, by decide⟩ //
    lowerFnAt fullUnit ⟨1, by decide⟩ = .ok value } := by
  refine ⟨?value, ?computed⟩
  case computed => cbv <;> exact Eq.refl _

private def produced2 : { value : EnsTy fullUnit ⟨2, by decide⟩ ×
    RumpTy fullUnit ⟨2, by decide⟩ × ReqTy fullUnit ⟨2, by decide⟩ //
    lowerFnAt fullUnit ⟨2, by decide⟩ = .ok value } := by
  refine ⟨?value, ?computed⟩
  case computed => cbv <;> exact Eq.refl _

private def fullPieces : (f : Fin fullUnit.fns.length) →
    EnsTy fullUnit f × RumpTy fullUnit f × ReqTy fullUnit f :=
  Fin.cases produced0.val
    (Fin.cases produced1.val (Fin.cases produced2.val (fun f : Fin 0 => Fin.elim0 f)))

private abbrev fullDeclaration := declOf fullUnit
private abbrev callerIndex : Fin fullUnit.fns.length := ⟨2, by decide⟩
private abbrev callerSymbols : Invarianten.Frag.Symbolic.SymEnv fullDeclaration Nat
    (fullDeclaration.params callerIndex) := .nil
private theorem callerBounded : callerSymbols.Bounded 0 := trivial

private def fullProgram
    (invariants : ∀ i : Fin fullUnit.invs.length, InvTy fullUnit i)
    (pointers : ∀ n, CallContract fullDeclaration (fullDeclaration.sigNr n))
    (foreigns : ∀ a, CallContract fullDeclaration (fullDeclaration.asignatur a)) : Programm fullDeclaration :=
  progOfFn fullUnit (fun f => (fullPieces f).1) (fun f => (fullPieces f).2.1)
    (fun f => (fullPieces f).2.2) invariants pointers foreigns

private noncomputable def callerInvariants (program : Programm fullDeclaration) :
    Invarianten.VC.InvariantFormula program (fullDeclaration.invs.filter (schuldet callerIndex)) :=
  (Invarianten.VC.invariantFormula program []).toOption.get (by rfl)

open Invarianten Invarianten.Frag.Symbolic Invarianten.VC Vertraege.Pruefer

private noncomputable def callerCompiled
    (invariants : ∀ i : Fin fullUnit.invs.length, InvTy fullUnit i)
    (pointers : ∀ n, CallContract fullDeclaration (fullDeclaration.sigNr n))
    (foreigns : ∀ a, CallContract fullDeclaration (fullDeclaration.asignatur a)) : Except Invarianten.Frag.Refusal
    (Vertraege.Pruefer.Symbolic.EndCondition (S := SperrInv.leer fullDeclaration)
      (requiresPolicy (fullProgram invariants pointers foreigns) (Vertraege.Pruefer.Symbolic.entryContext callerSymbols callerBounded)).semantic
      (((fullProgram invariants pointers foreigns)).rumpf callerIndex) callerSymbols
      (contractGoals (fullProgram invariants pointers foreigns) callerIndex callerSymbols callerBounded (callerInvariants (fullProgram invariants pointers foreigns)))) :=
  Vertraege.Pruefer.ending (requiresPolicy (fullProgram invariants pointers foreigns) (Vertraege.Pruefer.Symbolic.entryContext callerSymbols callerBounded))
  (S := SperrInv.leer fullDeclaration) (Invarianten.Pruefer.lockFormula _ (fun _ => none)) {} none 128
  (((fullProgram invariants pointers foreigns)).rumpf callerIndex) callerSymbols callerBounded (contractGoals (fullProgram invariants pointers foreigns) callerIndex callerSymbols callerBounded
    (callerInvariants (fullProgram invariants pointers foreigns)))

set_option maxHeartbeats 400000 in
private theorem callerCompiled_present
    (invariants : ∀ i : Fin fullUnit.invs.length, InvTy fullUnit i)
    (pointers : ∀ n, CallContract fullDeclaration (fullDeclaration.sigNr n))
    (foreigns : ∀ a, CallContract fullDeclaration (fullDeclaration.asignatur a)) : (callerCompiled invariants pointers foreigns).toOption.isSome = true := by
  with_unfolding_all rfl

private noncomputable def callerCertificate
    (invariants : ∀ i : Fin fullUnit.invs.length, InvTy fullUnit i)
    (pointers : ∀ n, CallContract fullDeclaration (fullDeclaration.sigNr n))
    (foreigns : ∀ a, CallContract fullDeclaration (fullDeclaration.asignatur a)) := (callerCompiled invariants pointers foreigns).toOption.get
  (callerCompiled_present invariants pointers foreigns)

private theorem callerCompiled_result
    (invariants : ∀ i : Fin fullUnit.invs.length, InvTy fullUnit i)
    (pointers : ∀ n, CallContract fullDeclaration (fullDeclaration.sigNr n))
    (foreigns : ∀ a, CallContract fullDeclaration (fullDeclaration.asignatur a)) : callerCompiled invariants pointers foreigns =
    .ok (callerCertificate invariants pointers foreigns) := by
  have present := callerCompiled_present invariants pointers foreigns
  cases result : callerCompiled invariants pointers foreigns with
  | error cause => rw [result] at present; cases present
  | ok value => simp only [callerCertificate, result, Except.toOption, Option.get_some]

private def callerFormula : Invarianten.Frag.LProp (Key fullDeclaration Nat) :=
  .and .tru (.and (.imp .tru (.and .tru .tru)) .tru)

set_option maxHeartbeats 400000 in
private theorem callerCompiled_shape
    (invariants : ∀ i : Fin fullUnit.invs.length, InvTy fullUnit i)
    (pointers : ∀ n, CallContract fullDeclaration (fullDeclaration.sigNr n))
    (foreigns : ∀ a, CallContract fullDeclaration (fullDeclaration.asignatur a)) :
    (callerCompiled invariants pointers foreigns).map Certificate.formula = .ok callerFormula := by
  unfold callerCompiled
  dsimp only [fullProgram, progOfFn, fullPieces, produced2, callerIndex, Fin.cases]
  rw (config := { transparency := .all }) [ending.eq_6]
  rw (config := { transparency := .all })
    [Vertraege.Pruefer.statement.eq_11]
  with_unfolding_all rfl

private theorem callerCompiled_valid
    (invariants : ∀ i : Fin fullUnit.invs.length, InvTy fullUnit i)
    (pointers : ∀ n, CallContract fullDeclaration (fullDeclaration.sigNr n))
    (foreigns : ∀ a, CallContract fullDeclaration (fullDeclaration.asignatur a)) (values : Invarianten.Frag.Assignment (Key fullDeclaration Nat)) :
    (callerCertificate invariants pointers foreigns).formula.denote values := by
  have shape := callerCompiled_shape invariants pointers foreigns
  rw [callerCompiled_result invariants pointers foreigns] at shape
  have same := Except.ok.inj shape
  change (callerCertificate invariants pointers foreigns).formula = callerFormula at same
  rw [same]
  exact ⟨trivial, ⟨fun _ => ⟨trivial, trivial⟩, trivial⟩⟩

attribute [local irreducible] entryVC callerCertificate

set_option maxHeartbeats 400000 in
private theorem caller_checked
    (invariants : ∀ i : Fin fullUnit.invs.length, InvTy fullUnit i)
    (pointers : ∀ n, CallContract fullDeclaration (fullDeclaration.sigNr n))
    (foreigns : ∀ a, CallContract fullDeclaration (fullDeclaration.asignatur a)) :
    (checkFunction (fullProgram invariants pointers foreigns) (SperrInv.leer fullDeclaration) (fun _ => none) {} none callerIndex).toOption.isSome = true := by
  apply Vertraege.Pruefer.SelectionWitness.function_success
  · with_unfolding_all rfl
  · with_unfolding_all rfl
  · apply Vertraege.Pruefer.SelectionWitness.execution_success (fullProgram invariants pointers foreigns) (SperrInv.leer fullDeclaration) (fun _ => none) {}
      none callerIndex (by with_unfolding_all rfl) (callerInvariants (fullProgram invariants pointers foreigns)) (by rfl)
      ((parameters (D := fullDeclaration) 128 0 []).toOption.get (by rfl)) (by rfl)
    · with_unfolding_all
        change 2 ≤ 16384
        decide
    · rintro ⟨symbols, member⟩
      cases symbols
      let requirement := (Invarianten.Frag.Symbolic.translate ((fullProgram invariants pointers foreigns).requires callerIndex) callerSymbols).toOption.get (by with_unfolding_all rfl)
      have decided : Invarianten.Elim.decideB (close (lower (entryVC callerSymbols requirement.payload
          (callerCertificate invariants pointers foreigns).formula))) (close_closed _) = true := by
        apply (close_decide_true_iff (lower (entryVC callerSymbols requirement.payload
          (callerCertificate invariants pointers foreigns).formula))).mpr
        intro values
        apply (lower_denote (entryVC callerSymbols requirement.payload
          (callerCertificate invariants pointers foreigns).formula) values).mpr
        unfold entryVC
        intro _ _ _
        exact callerCompiled_valid invariants pointers foreigns values
      exact Vertraege.Pruefer.SelectionWitness.environment_success (D := fullDeclaration) (f := callerIndex) (next := 0)
        (fullProgram invariants pointers foreigns) (SperrInv.leer fullDeclaration) callerSymbols callerBounded (requiresPolicy (fullProgram invariants pointers foreigns) _) (fun _ => none) {} none
        (callerInvariants (fullProgram invariants pointers foreigns)) (by with_unfolding_all rfl) requirement (by rfl)
        (callerCertificate invariants pointers foreigns) (callerCompiled_result invariants pointers foreigns) decided

private theorem full_phases :
    ∃ items, parseTopTief fullTokens = .ok items ∧
      (∃ expanded, exportLibraryUnit (uMembers (pre108 items)) = .ok expanded ∧
        alleOhneBibliothek expanded = true) ∧
      ∃ unit, elabU (pre108 items) = .ok unit ∧ ExportFacts unit := by
  let items : List SItemTief := ?items
  have parsed : parseTopTief fullTokens = .ok items := by cbv <;> exact Eq.refl _
  refine ⟨items, parsed, ?expanded, ?elaboration⟩
  case expanded =>
    refine ⟨?expandedItems, ?expansion, ?ordinary⟩
    case expansion => cbv <;> exact Eq.refl _
    case ordinary => cbv
  case elaboration =>
    have made : elabU (pre108 items) = .ok fullUnit := by cbv
    refine ⟨fullUnit, made, ?facts⟩
    case facts =>
      refine {
        gate := by cbv
        invs := by cbv
        contracts := by cbv
        measures := by export_functions
        functions := ?_ }
      refine ⟨?pieces, ?equations, ?safe⟩
      case pieces =>
        change (f : Fin 3) → EnsTy fullUnit f × RumpTy fullUnit f × ReqTy fullUnit f
        exact fullPieces
      case equations =>
        rintro ⟨index, bound⟩
        have small : index < 3 := bound
        have choices : index = 0 ∨ index = 1 ∨ index = 2 := by omega
        rcases choices with h | h | h
        · subst index; exact produced0.property
        · subst index; exact produced1.property
        · subst index; exact produced2.property
      case safe =>
        intro invariants pointers foreigns
        unfold checkedImage
        delta Akzeptiert
        apply Bool.and_eq_true_iff.mpr
        constructor
        · cbv
        · simp only [Invarianten.Pruefer.invariantVCB, Bool.and_eq_true]
          constructor
          · cbv
          · apply Vertraege.Pruefer.SelectionWitness.contracts_success
            rintro ⟨index, bound⟩
            have small : index < 3 := bound
            have choices : index = 0 ∨ index = 1 ∨ index = 2 := by omega
            rcases choices with first | second | third
            · subst index; cbv <;> (set_option smartUnfolding false in with_unfolding_all rfl)
            · subst index; cbv <;> (set_option smartUnfolding false in with_unfolding_all rfl)
            · subst index; exact caller_checked invariants pointers foreigns

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
  simpa only [checkedImage] using export_checked export_facts export_emitted

end Gabbro.Grammatik.Uebersetzung
