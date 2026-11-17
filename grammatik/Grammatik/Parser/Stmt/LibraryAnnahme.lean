module

public import Grammatik.Logik.Vertraege.Uebersetzung
public import Grammatik.Parser.Stmt.LibraryFixtures
public import Grammatik.Parser.Stmt.LibraryCertificates
public import Grammatik.Parser.Stmt.LibraryExport
public import Grammatik.Zielsatz.Kern.Akzeptiert
public import Grammatik.Nebenlaeufigkeit.Sperren.SperreSem
import Grammatik.Logik.Vertraege.Pruefer.Witness.Selection
import all Grammatik.Parser.Stmt.LibraryExport
import all Grammatik.Parser.Stmt.LibraryTranslationFixtures
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

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-! ## C02 item 8: connected source/image correctness and refusal witnesses.

    The generic lowering covers the expanded call: source text with an
    (unqualified) library call elaborates through the actual export path
    to an ordinary unit, lowers with `lowerAllg`, and the checker Bool
    holds -- on the non-degenerate identity fixture with a real call, not
    a degenerate empty unit. Layout and image, C14/C08 and Stage-0
    closure stay with their owners. The certified expansion can never hit
    the lowering's C02 refusal (`uAnwReiheCore` refuses `lcall`/`bindLib`
    by name): an expanded statement is definitionally no library call. -/

-- Reuse the checked ordinary-source tokens, parser equation and exact text
-- bridge. Instantiate getter laws only after they have been proved symbolically.
private theorem ident_tokens : translationTokens false = translationPhaseTokens false := by
  unfold translationTokens
  exact tokens_from_text (translationText false) (translationCharacters false)
    (translationPhaseTokens false) (translation_text false) (translation_lexed false)

private theorem items_from_tokens (original tokens : List Token) (items : List SItemTief)
    (tokenEq : original = tokens) (parsed : parseTopTief tokens = .ok items) :
    (parseTopTief original).toOption.getD [] = items := by
  rw [tokenEq, parsed]
  rfl

private theorem ident_items : translationItems false =
    LibraryFixtureProofs.parsedFixture 2 (translationResult false) [.num 3, .num 5] := by
  unfold translationItems
  exact items_from_tokens (translationTokens false) (translationPhaseTokens false)
    (LibraryFixtureProofs.parsedFixture 2 (translationResult false) [.num 3, .num 5])
    ident_tokens (translation_parsed false)

attribute [local cbv_opaque] lowStufe lowSeqL lowStructL lowEndL uFloatLimit
  Invarianten.Pruefer.invariantVCB Vertraege.Pruefer.checkFunction
attribute [local cbv_eval] export_seq_succ lowStructL_succ lowEndL_succ
  lowStufe_seq lowStufe_struct lowStufe_ende

-- The actual whole ordinary caller unit has two implemented functions after
-- its translator declaration is consumed. Check this against its own carrier.
local macro "ident_functions" : tactic => `(tactic| (
  rintro ⟨index, bound⟩
  have size : index < 2 := bound
  have choices : index = 0 ∨ index = 1 := by omega
  rcases choices with first | second
  · subst index
    cbv <;> (set_option smartUnfolding false in with_unfolding_all rfl)
  · subst index
    cbv <;> (set_option smartUnfolding false in with_unfolding_all rfl)))

private def identUnit : UProg where
  tabs := [{ name := "Rows", count := 2, cols := [("v", 0, 10)], breiten := [("v", 8)] }]
  locks := []
  fns :=
    [{ name := "consume",
       params := [("p", .ptr { space := 0, rights := { read := true }, target := .table 0 })],
       kinds := [.ptr { space := 0, rights := { read := true }, target := .table 0 }],
       res := none, held := [], puts := [], gives := [], body := [], ret := .empty },
     { name := "caller", params := [], kinds := [], res := none, held := [], puts := [], gives := [],
       body := [.call "consume" [.freshPtr "Rows"
         { space := 0, rights := { read := true }, target := .table 0 }]], ret := .empty }]

private def identProduced0 : { value : EnsTy identUnit ⟨0, by decide⟩ ×
    RumpTy identUnit ⟨0, by decide⟩ × ReqTy identUnit ⟨0, by decide⟩ //
    lowerFnAt identUnit ⟨0, by decide⟩ = .ok value } := by
  refine ⟨?value, ?computed⟩
  case computed => cbv <;> exact Eq.refl _

private def identProduced1 : { value : EnsTy identUnit ⟨1, by decide⟩ ×
    RumpTy identUnit ⟨1, by decide⟩ × ReqTy identUnit ⟨1, by decide⟩ //
    lowerFnAt identUnit ⟨1, by decide⟩ = .ok value } := by
  refine ⟨?value, ?computed⟩
  case computed => cbv <;> exact Eq.refl _

private def identPieces : (f : Fin identUnit.fns.length) →
    EnsTy identUnit f × RumpTy identUnit f × ReqTy identUnit f :=
  Fin.cases identProduced0.val (Fin.cases identProduced1.val (fun f : Fin 0 => Fin.elim0 f))

private abbrev identDeclaration := declOf identUnit
private abbrev identCallerIndex : Fin identUnit.fns.length := ⟨1, by decide⟩
private abbrev identCallerSymbols : Invarianten.Frag.Symbolic.SymEnv identDeclaration Nat
    (identDeclaration.params identCallerIndex) := .nil
private theorem identCallerBounded : identCallerSymbols.Bounded 0 := trivial

private def identProgram
    (invariants : ∀ i : Fin identUnit.invs.length, InvTy identUnit i)
    (pointers : ∀ n, CallContract identDeclaration (identDeclaration.sigNr n))
    (foreigns : ∀ a, CallContract identDeclaration (identDeclaration.asignatur a)) : Programm identDeclaration :=
  progOfFn identUnit (fun f => (identPieces f).1) (fun f => (identPieces f).2.1)
    (fun f => (identPieces f).2.2) invariants pointers foreigns

private noncomputable def identCallerInvariants (program : Programm identDeclaration) :
    Invarianten.VC.InvariantFormula program (identDeclaration.invs.filter (schuldet identCallerIndex)) :=
  (Invarianten.VC.invariantFormula program []).toOption.get (by rfl)

open Invarianten Invarianten.Frag.Symbolic Invarianten.VC Vertraege.Pruefer

private noncomputable def identCallerCompiled
    (invariants : ∀ i : Fin identUnit.invs.length, InvTy identUnit i)
    (pointers : ∀ n, CallContract identDeclaration (identDeclaration.sigNr n))
    (foreigns : ∀ a, CallContract identDeclaration (identDeclaration.asignatur a)) : Except Invarianten.Frag.Refusal
    (Vertraege.Pruefer.Symbolic.EndCondition (S := SperrInv.leer identDeclaration)
      (requiresPolicy (identProgram invariants pointers foreigns) (Vertraege.Pruefer.Symbolic.entryContext identCallerSymbols identCallerBounded)).semantic
      (((identProgram invariants pointers foreigns)).rumpf identCallerIndex) identCallerSymbols
      (contractGoals (identProgram invariants pointers foreigns) identCallerIndex identCallerSymbols identCallerBounded (identCallerInvariants (identProgram invariants pointers foreigns)))) :=
  Vertraege.Pruefer.ending (requiresPolicy (identProgram invariants pointers foreigns) (Vertraege.Pruefer.Symbolic.entryContext identCallerSymbols identCallerBounded))
  (S := SperrInv.leer identDeclaration) (Invarianten.Pruefer.lockFormula _ (fun _ => none)) {} none 128
  (((identProgram invariants pointers foreigns)).rumpf identCallerIndex) identCallerSymbols identCallerBounded (contractGoals (identProgram invariants pointers foreigns) identCallerIndex identCallerSymbols identCallerBounded
    (identCallerInvariants (identProgram invariants pointers foreigns)))

set_option maxHeartbeats 400000 in
private theorem identCallerCompiled_present
    (invariants : ∀ i : Fin identUnit.invs.length, InvTy identUnit i)
    (pointers : ∀ n, CallContract identDeclaration (identDeclaration.sigNr n))
    (foreigns : ∀ a, CallContract identDeclaration (identDeclaration.asignatur a)) : (identCallerCompiled invariants pointers foreigns).toOption.isSome = true := by
  with_unfolding_all rfl

private noncomputable def identCallerCertificate
    (invariants : ∀ i : Fin identUnit.invs.length, InvTy identUnit i)
    (pointers : ∀ n, CallContract identDeclaration (identDeclaration.sigNr n))
    (foreigns : ∀ a, CallContract identDeclaration (identDeclaration.asignatur a)) := (identCallerCompiled invariants pointers foreigns).toOption.get
  (identCallerCompiled_present invariants pointers foreigns)

private theorem identCallerCompiled_result
    (invariants : ∀ i : Fin identUnit.invs.length, InvTy identUnit i)
    (pointers : ∀ n, CallContract identDeclaration (identDeclaration.sigNr n))
    (foreigns : ∀ a, CallContract identDeclaration (identDeclaration.asignatur a)) : identCallerCompiled invariants pointers foreigns =
    .ok (identCallerCertificate invariants pointers foreigns) := by
  have present := identCallerCompiled_present invariants pointers foreigns
  cases result : identCallerCompiled invariants pointers foreigns with
  | error cause => rw [result] at present; cases present
  | ok value => simp only [identCallerCertificate, result, Except.toOption, Option.get_some]

private def identCallerFormula : Invarianten.Frag.LProp (Key identDeclaration Nat) :=
  .and .tru (.and (.imp .tru (.and .tru .tru)) .tru)

set_option maxHeartbeats 400000 in
private theorem identCallerCompiled_shape
    (invariants : ∀ i : Fin identUnit.invs.length, InvTy identUnit i)
    (pointers : ∀ n, CallContract identDeclaration (identDeclaration.sigNr n))
    (foreigns : ∀ a, CallContract identDeclaration (identDeclaration.asignatur a)) :
    (identCallerCompiled invariants pointers foreigns).map Certificate.formula = .ok identCallerFormula := by
  unfold identCallerCompiled
  dsimp only [identProgram, progOfFn, identPieces, identProduced1, identCallerIndex, Fin.cases]
  rw (config := { transparency := .all }) [ending.eq_6]
  rw (config := { transparency := .all })
    [Vertraege.Pruefer.statement.eq_def]
  with_unfolding_all rfl

private theorem identCallerCompiled_valid
    (invariants : ∀ i : Fin identUnit.invs.length, InvTy identUnit i)
    (pointers : ∀ n, CallContract identDeclaration (identDeclaration.sigNr n))
    (foreigns : ∀ a, CallContract identDeclaration (identDeclaration.asignatur a)) (values : Invarianten.Frag.Assignment (Key identDeclaration Nat)) :
    (identCallerCertificate invariants pointers foreigns).formula.denote values := by
  have shape := identCallerCompiled_shape invariants pointers foreigns
  rw [identCallerCompiled_result invariants pointers foreigns] at shape
  have same := Except.ok.inj shape
  change (identCallerCertificate invariants pointers foreigns).formula = identCallerFormula at same
  rw [same]
  exact ⟨trivial, ⟨fun _ => ⟨trivial, trivial⟩, trivial⟩⟩

attribute [local irreducible] entryVC identCallerCertificate

set_option maxHeartbeats 400000 in
private theorem identCaller_checked
    (invariants : ∀ i : Fin identUnit.invs.length, InvTy identUnit i)
    (pointers : ∀ n, CallContract identDeclaration (identDeclaration.sigNr n))
    (foreigns : ∀ a, CallContract identDeclaration (identDeclaration.asignatur a)) :
    (checkFunction (identProgram invariants pointers foreigns) (SperrInv.leer identDeclaration) (fun _ => none) {} none identCallerIndex).toOption.isSome = true := by
  with_unfolding_all
    apply Vertraege.Pruefer.SelectionWitness.function_success
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · apply Vertraege.Pruefer.SelectionWitness.execution_success (identProgram invariants pointers foreigns) (SperrInv.leer identDeclaration) (fun _ => none) {}
        none identCallerIndex (by with_unfolding_all rfl) (identCallerInvariants (identProgram invariants pointers foreigns)) (by rfl)
        ((parameters (D := identDeclaration) 128 0 []).toOption.get (by with_unfolding_all rfl)) (by with_unfolding_all rfl)
      · with_unfolding_all
          change 2 ≤ 16384
          decide
      · rintro ⟨symbols, member⟩
        cases symbols
        let requirement := (Invarianten.Frag.Symbolic.translate ((identProgram invariants pointers foreigns).requires identCallerIndex) identCallerSymbols).toOption.get (by with_unfolding_all rfl)
        exact Vertraege.Pruefer.SelectionWitness.environment_success_of_valid (D := identDeclaration) (f := identCallerIndex) (next := 0)
          (identProgram invariants pointers foreigns) (SperrInv.leer identDeclaration) identCallerSymbols identCallerBounded (requiresPolicy (identProgram invariants pointers foreigns) _) (fun _ => none) {} none
          (identCallerInvariants (identProgram invariants pointers foreigns)) (by with_unfolding_all rfl) requirement (by rfl)
          (identCallerCertificate invariants pointers foreigns) (identCallerCompiled_result invariants pointers foreigns) (by
            intro values
            unfold entryVC
            intro _ _ _
            exact identCallerCompiled_valid invariants pointers foreigns values)

-- Retain the canonical producer equations before assembling the actual image,
-- as for the qualified source in LibraryExport.
private theorem ident_phases :
    (∃ expanded, exportLibraryUnit (uMembers (pre108 (translationItems false))) = .ok expanded ∧
      alleOhneBibliothek expanded = true) ∧
    ∃ unit, elabU (pre108 (translationItems false)) = .ok unit ∧ ExportFacts unit := by
  rw [ident_items]
  constructor
  · refine ⟨?expanded, ?produced, ?ordinary⟩
    case produced => cbv <;> exact Eq.refl _
    case ordinary => cbv
  · refine ⟨identUnit, ?made, ?facts⟩
    case made => cbv
    case facts =>
      refine {
        gate := by cbv
        invs := by cbv
        contracts := by cbv
        measures := by ident_functions
        functions := ?_ }
      refine ⟨?pieces, ?equations, ?safe⟩
      case pieces =>
        change (f : Fin 2) → EnsTy identUnit f × RumpTy identUnit f × ReqTy identUnit f
        exact identPieces
      case equations =>
        rintro ⟨index, bound⟩
        have small : index < 2 := bound
        have choices : index = 0 ∨ index = 1 := by omega
        rcases choices with h | h
        · subst index; exact identProduced0.property
        · subst index; exact identProduced1.property
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
            have small : index < 2 := bound
            rcases (by omega : index = 0 ∨ index = 1) with first | second
            · subst index
              cbv <;> (set_option smartUnfolding false in with_unfolding_all rfl)
            · subst index
              exact identCaller_checked invariants pointers foreigns

/-- The identity caller unit through the export: the source text with an
    unqualified library call elaborates to an ordinary unit. -/
def exportIdentEinheit : UProg :=
  (elabU (pre108 (translationItems false))).toOption.getD { tabs := [], locks := [], fns := [] }

theorem export_ident_elab_zeuge :
    (elabU (pre108 (translationItems false))).toOption.isSome = true := by
  obtain ⟨unit, made, _⟩ := ident_phases.2
  rw [made]
  rfl

private theorem ident_export_facts : ExportFacts exportIdentEinheit := by
  obtain ⟨unit, made, facts⟩ := ident_phases.2
  unfold exportIdentEinheit
  rw [made]
  exact facts

/-- The export leaves no ignored source duty behind on the fixture. -/
theorem export_ident_tor_zeuge : exportIdentEinheit.exportGate = .ok () := ident_export_facts.gate

/-- The expanded source: the pre-pass output on the fixture members. -/
def exportIdentErweitert : List SItemTief :=
  (exportLibraryUnit (uMembers (pre108 (translationItems false)))).toOption.getD []

/-- The pre-pass ran: every expanded body is ordinary. -/
theorem export_ident_ohne_zeuge :
    Gabbro.Grammatik.Uebersetzung.alleOhneBibliothek exportIdentErweitert = true := by
  obtain ⟨expanded, produced, ordinary⟩ := ident_phases.1
  unfold exportIdentErweitert
  rw [produced]
  exact ordinary

theorem export_ident_lower_ok :
    (lowerAllg exportIdentEinheit).toOption.isSome = true := export_lowered ident_export_facts

def exportIdentGesenkert :
    Programm (declOf exportIdentEinheit) × List (declOf exportIdentEinheit).Fn :=
  (lowerAllg exportIdentEinheit).toOption.get export_ident_lower_ok

-- Normalize the actual selected-image alias before applying the success law.
private theorem ident_emitted : lowerAllg exportIdentEinheit = .ok exportIdentGesenkert := by
  unfold exportIdentGesenkert
  exact except_ok_get (x := lowerAllg exportIdentEinheit) export_ident_lower_ok

/-- The connected verdict: source text with an unqualified library call
    elaborates, lowers, and the checker Bool holds. The enumerations are
    complete by construction (`finRange` over the elaborated tables,
    statics and locks; the lowered functions; no starts, since the fixture
    declares no `concurrent` item). -/
theorem export_ident_akzeptiert_zeuge :
    Gabbro.Grammatik.Akzeptiert exportIdentGesenkert.1 (Gabbro.Grammatik.SperrInv.leer _)
      exportIdentGesenkert.2 (List.finRange exportIdentEinheit.locks.length)
      ((List.finRange exportIdentEinheit.tabs.length).map Sum.inl ++
        (List.finRange exportIdentEinheit.globs.length).map Sum.inr) [] = true := by
  simpa only [checkedImage] using export_checked ident_export_facts ident_emitted

/-- The end-to-end chain in one witness: source text to accepted unit. -/
theorem export_ident_kette_zeuge :
    (elabU (pre108 (translationItems false))).toOption.isSome = true ∧
    (lowerAllg exportIdentEinheit).toOption.isSome = true ∧
    Gabbro.Grammatik.Akzeptiert exportIdentGesenkert.1 (Gabbro.Grammatik.SperrInv.leer _)
      exportIdentGesenkert.2 (List.finRange exportIdentEinheit.locks.length)
      ((List.finRange exportIdentEinheit.tabs.length).map Sum.inl ++
        (List.finRange exportIdentEinheit.globs.length).map Sum.inr) [] = true :=
  ⟨export_ident_elab_zeuge, export_ident_lower_ok, export_ident_akzeptiert_zeuge⟩

/-- An expanded statement is definitionally no `lcall`: the lowering's
    C02 refusal is unreachable on certified expansions. -/
theorem ohneBibliothekAnw_kein_lcall (c : SLibraryCall) :
    ohneBibliothekAnw (.lcall c) = false := rfl

/-- An expanded statement is definitionally no `bindLib` either. -/
theorem ohneBibliothekAnw_kein_bindLib (m : Bool) (x : String) (ty : Option STyp)
    (c : SLibraryCall) :
    ohneBibliothekAnw (.bindLib m x ty c) = false := rfl

/-- Every certified expansion takes the ordinary lowering path: it is
    neither an `lcall` nor a `bindLib`, in either call form, so the
    generic lowering (`uAnwReiheCore`, which refuses both by name) treats
    it exactly like an ordinary call. -/
theorem libraryExpansion_trifft_kein_bibliothekruf {source : LibrarySource} {u : UProg}
    {decl : TranslationDecl source u} {certificate : TranslationCertificate decl}
    {payload : LibraryPayload certificate} (expansion : LibraryExpansion payload)
    (c : SLibraryCall) :
    expansion.aufruf ≠ .lcall c ∧
      (∀ m x ty, expansion.aufruf ≠ .bindLib m x ty c) := by
  have h := libraryExpansion_ohneBibliothek expansion
  constructor
  · intro heq
    have same : ohneBibliothekAnw (.lcall c) = true := heq ▸ h
    rw [ohneBibliothekAnw_kein_lcall] at same
    exact absurd same (by decide)
  · intro m x ty heq
    have same : ohneBibliothekAnw (.bindLib m x ty c) = true := heq ▸ h
    rw [ohneBibliothekAnw_kein_bindLib] at same
    exact absurd same (by decide)

end Gabbro.Grammatik.Uebersetzung
