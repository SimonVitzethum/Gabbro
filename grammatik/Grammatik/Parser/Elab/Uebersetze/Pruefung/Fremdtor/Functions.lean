/- Actual function results are retained with their producer equations before
   dependent checker access. Source.lean connects them to the real assembly. -/
module
public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Fremdtor.Units
public import Grammatik.Parser.Elab.UebersetzeAllg3
public import Grammatik.Parser.Cover.Differenz
public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Ableitung
public import Grammatik.Parser.Elab.UebersetzePipeline
public import Grammatik.Logik.Vertraege.Pruefer.Witness.Selection
public import Grammatik.Zielsatz.Kern.Akzeptiert.CheckProof
import Grammatik.Kern.Taktik.KernelRfl
import all Init.Data.Int.Repr
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
namespace Gabbro.Grammatik.Parser.Uebersetze.ForeignGateFunctions
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

-- Select the existing one-layer lowering equations instead of expanding the
-- entire mutual fuel recursion while retaining a typed function result.
private theorem foreign_seq_succ (u : UProg) (caller : Fin u.fns.length) (fuel : Nat)
    {l : Bool} (Γ : Ctx) (fn : UFn) (Λ : List (Res (declOf u)))
    (entry : AtTop u caller Λ) (statements : List UStmt) :
    lowSeqL (l := l) u caller Γ fn (fuel + 1) Λ entry statements =
      lowSeqStep u caller (lowStufe u caller fuel) Γ fn Λ entry statements := rfl

-- A real probe with a binding instantiates the one-layer equation.
private theorem foreign_seq_succ_zeuge :
    lowSeqL (l := false) uFremd ⟨1, by decide⟩ [] (fnAt uFremd ⟨1, by decide⟩)
      2 [] [] [.bindB "#checkVerdict" .tru] =
    lowSeqStep uFremd ⟨1, by decide⟩ (lowStufe uFremd ⟨1, by decide⟩ 1)
      [] (fnAt uFremd ⟨1, by decide⟩) [] [] [.bindB "#checkVerdict" .tru] :=
  foreign_seq_succ _ _ 1 _ _ _ _ _

attribute [local cbv_opaque] lowStufe lowSeqL lowStructL lowEndL uFloatLimit
attribute [local cbv_eval] foreign_seq_succ lowStructL_succ lowEndL_succ
  lowStufe_seq lowStufe_struct lowStufe_ende

private def inf0 : { value : EnsTy uFremd ⟨0, by decide⟩ ×
    RumpTy uFremd ⟨0, by decide⟩ × ReqTy uFremd ⟨0, by decide⟩ //
    lowerFnAt uFremd ⟨0, by decide⟩ = .ok value } := by
  refine ⟨?value, ?computed⟩
  case computed => cbv <;> (set_option smartUnfolding false in with_unfolding_all rfl)

-- The probe's actual two bindings: a true verdict and the reporter result.
private def infProbe : RumpTy uFremd ⟨1, by decide⟩ :=
  .bind .tru
    (.bindCall ⟨2, by decide⟩
      (.cons (.le (.lit 1) (.lit 2)) (.cons (.var .here) .nil)) rfl
      { hw := fun t => nomatch t
        hg := fun g => nomatch g
        hk := ⟨[], List.Perm.refl [], List.nil_sublist _⟩
        hh := fun L => nomatch L }
      rfl (.ret (.val (.var .here)) (List.Perm.refl _)))

private def inf1 : { value : EnsTy uFremd ⟨1, by decide⟩ ×
    RumpTy uFremd ⟨1, by decide⟩ × ReqTy uFremd ⟨1, by decide⟩ //
    lowerFnAt uFremd ⟨1, by decide⟩ = .ok value } :=
  ⟨(.tru, infProbe, .tru), by kernel_rfl⟩

private def inf2 : { value : EnsTy uFremd ⟨2, by decide⟩ ×
    RumpTy uFremd ⟨2, by decide⟩ × ReqTy uFremd ⟨2, by decide⟩ //
    lowerFnAt uFremd ⟨2, by decide⟩ = .ok value } := by
  refine ⟨?value, ?computed⟩
  case computed => cbv <;> (set_option smartUnfolding false in with_unfolding_all rfl)

private def inf3 : { value : EnsTy uFremd ⟨3, by decide⟩ ×
    RumpTy uFremd ⟨3, by decide⟩ × ReqTy uFremd ⟨3, by decide⟩ //
    lowerFnAt uFremd ⟨3, by decide⟩ = .ok value } := by
  refine ⟨?value, ?computed⟩
  case computed => cbv <;> (set_option smartUnfolding false in with_unfolding_all rfl)

private def infPieces : (f : Fin 4) → EnsTy uFremd f × RumpTy uFremd f × ReqTy uFremd f :=
  Fin.cases inf0.val (Fin.cases inf1.val
    (Fin.cases inf2.val (Fin.cases inf3.val (fun f : Fin 0 => Fin.elim0 f))))

private theorem infPieces_ok (f : Fin uFremd.fns.length) :
    lowerFnAt uFremd f = .ok (infPieces f) := by
  rcases f with ⟨index, bound⟩
  have small : index < 4 := bound
  have choices : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by omega
  rcases choices with h | h | h | h
  · subst index; exact inf0.property
  · subst index; exact inf1.property
  · subst index; exact inf2.property
  · subst index; exact inf3.property

private def fall0 : { value : EnsTy uFremdFallible ⟨0, by decide⟩ ×
    RumpTy uFremdFallible ⟨0, by decide⟩ × ReqTy uFremdFallible ⟨0, by decide⟩ //
    lowerFnAt uFremdFallible ⟨0, by decide⟩ = .ok value } := by
  refine ⟨?value, ?computed⟩
  case computed => cbv <;> (set_option smartUnfolding false in with_unfolding_all rfl)

-- The probe's actual two bindings: a true verdict and the reporter result.
private def fallProbe : RumpTy uFremdFallible ⟨1, by decide⟩ :=
  .bind .tru
    (.bindCall ⟨2, by decide⟩
      (.cons (.le (.lit 1) (.lit 2)) (.cons (.var .here) .nil)) rfl
      { hw := fun t => nomatch t
        hg := fun g => nomatch g
        hk := ⟨[], List.Perm.refl [], List.nil_sublist _⟩
        hh := fun L => nomatch L }
      rfl (.ret (.val (.var .here)) (List.Perm.refl _)))

private def fall1 : { value : EnsTy uFremdFallible ⟨1, by decide⟩ ×
    RumpTy uFremdFallible ⟨1, by decide⟩ × ReqTy uFremdFallible ⟨1, by decide⟩ //
    lowerFnAt uFremdFallible ⟨1, by decide⟩ = .ok value } :=
  ⟨(.tru, fallProbe, .tru), by kernel_rfl⟩

private def fall2 : { value : EnsTy uFremdFallible ⟨2, by decide⟩ ×
    RumpTy uFremdFallible ⟨2, by decide⟩ × ReqTy uFremdFallible ⟨2, by decide⟩ //
    lowerFnAt uFremdFallible ⟨2, by decide⟩ = .ok value } := by
  refine ⟨?value, ?computed⟩
  case computed => cbv <;> (set_option smartUnfolding false in with_unfolding_all rfl)

private def fall3 : { value : EnsTy uFremdFallible ⟨3, by decide⟩ ×
    RumpTy uFremdFallible ⟨3, by decide⟩ × ReqTy uFremdFallible ⟨3, by decide⟩ //
    lowerFnAt uFremdFallible ⟨3, by decide⟩ = .ok value } := by
  refine ⟨?value, ?computed⟩
  case computed => cbv <;> (set_option smartUnfolding false in with_unfolding_all rfl)

private def fallPieces : (f : Fin 4) → EnsTy uFremdFallible f × RumpTy uFremdFallible f × ReqTy uFremdFallible f :=
  Fin.cases fall0.val (Fin.cases fall1.val
    (Fin.cases fall2.val (Fin.cases fall3.val (fun f : Fin 0 => Fin.elim0 f))))

private theorem fallPieces_ok (f : Fin uFremdFallible.fns.length) :
    lowerFnAt uFremdFallible f = .ok (fallPieces f) := by
  rcases f with ⟨index, bound⟩
  have small : index < 4 := bound
  have choices : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by omega
  rcases choices with h | h | h | h
  · subst index; exact fall0.property
  · subst index; exact fall1.property
  · subst index; exact fall2.property
  · subst index; exact fall3.property

end Gabbro.Grammatik.Parser.Uebersetze.ForeignGateFunctions

namespace Gabbro.Grammatik.Parser.Uebersetze.ForeignGateAcceptance

open UebersetzeAllg UebersetzeAllg2 Zielsatz
open Invarianten Invarianten.Frag Invarianten.Elim Invarianten.Elim.Korrekt Invarianten.VC
open Invarianten.Frag.Symbolic Vertraege.Pruefer Vertraege.Pruefer.Symbolic
open Vertraege.Pruefer.SelectionWitness

theorem checked_image (u : UProg)
    (pieces : ∀ f : Fin u.fns.length, EnsTy u f × RumpTy u f × ReqTy u f)
    (origin : ∀ f, lowerFnAt u f = .ok (pieces f))
    (checks : List (CheckDecl (declOf u)))
    {image : Programm (declOf u) × List (declOf u).Fn}
    (emitted : lowerAllg u = .ok image)
    (verdict : Bool)
    (checked : ∀ (invariants : ∀ i : Fin u.invs.length, InvTy u i)
      (foreignGate : axContractsB u = true),
      AkzeptiertX (progOfFn u (fun f => (pieces f).1) (fun f => (pieces f).2.1)
        (fun f => (pieces f).2.2) invariants (ptrVertragOf u)
        (fun a => axVertragOf u a foreignGate)) (Cover.Differenz.sperrFamilie u)
        (List.finRange u.fns.length) [] [] [] [] checks = verdict) :
    AkzeptiertX image.1 (Cover.Differenz.sperrFamilie u)
      (List.finRange u.fns.length) [] [] [] [] checks = verdict := by
  rcases image with ⟨program, functions⟩
  have selected (f : Fin u.fns.length) (proof : ∃ value, lowerFnAt u f = .ok value) :
      lowerAtPair u f proof = pieces f := lowerAtPair_of_ok u f proof (origin f)
  unfold lowerAllg at emitted
  split at emitted
  · cases emitted
  · split at emitted
    · cases emitted
    · split at emitted
      · obtain ⟨programEq, _⟩ := Measures.checkedProgram_eq emitted
        rw [programEq]
        simp only [selected]
        exact checked _ _
      · cases emitted


private abbrev unit := uFremdFallible
private abbrev declaration := declOf unit
private abbrev index : Fin unit.fns.length := ⟨3, by decide⟩
private abbrev family := Cover.Differenz.sperrFamilie unit
private abbrev budget : VCBudget := {}

private theorem foreign_contracts : axContractsB unit = true := by decide +kernel

private def program : Programm declaration :=
  progOfFn unit (fun f => (ForeignGateFunctions.fallPieces f).1)
    (fun f => (ForeignGateFunctions.fallPieces f).2.1)
    (fun f => (ForeignGateFunctions.fallPieces f).2.2)
    (fun i => Fin.elim0 (show Fin 0 from i)) (ptrVertragOf unit)
    (fun a => axVertragOf unit a foreign_contracts)

private abbrev symbols : SymEnv declaration Nat (declaration.params index) := .nil

private theorem bounded : symbols.Bounded 0 := trivial

private noncomputable def invariants : InvariantFormula program (declaration.invs.filter (schuldet index)) :=
  (invariantFormula program []).toOption.get (by rfl)

private noncomputable def compiled := ending (requiresPolicy program (entryContext symbols bounded))
  (S := family) (Invarianten.Pruefer.lockFormula family (fun _ => none)) budget none budget.depth
  (program.rumpf index) symbols bounded (contractGoals program index symbols bounded invariants)

private theorem compiled_present : compiled.toOption.isSome = true := by with_unfolding_all rfl

private noncomputable def certificate := compiled.toOption.get compiled_present

private theorem compiled_result : compiled = .ok certificate := by
  have present := compiled_present
  cases result : compiled with
  | error reason => rw [result] at present; cases present
  | ok value => simp only [certificate, result, Except.toOption, Option.get_some]

/-- The original wide-answer VC is valid by equivalence-preserving reduction.
    The elimination procedure is composed below, never kernel-evaluated. -/
private theorem normalized : (Reduce.normalize 8 certificate.formula).val = .tru := by
  with_unfolding_all rfl

private theorem original_valid (values : Assignment (Key declaration Nat)) :
    (entryVC symbols .tru certificate.formula).denote values := by
  intro _ _ _
  apply ((Reduce.normalize 8 certificate.formula).property values).mp
  rw [normalized]
  trivial

attribute [local irreducible] entryVC certificate

/-- The actual fallible wrapper accepts every u64 answer and the real reason
    continuation, including the source's linear Duty cleanup. -/
private theorem wrapper_accepted_zeuge :
    (checkFunction program family (fun _ => none) budget none index).toOption.isSome = true := by
  apply function_success
  · with_unfolding_all rfl
  · with_unfolding_all rfl
  · apply execution_success program family (fun _ => none) budget none index
      (by with_unfolding_all rfl) invariants (by rfl)
      ((parameters (D := declaration) 128 0 []).toOption.get (by rfl)) (by rfl)
    · with_unfolding_all decide
    · intro entry
      rcases entry with ⟨selected, member⟩
      cases selected
      let requirement := (Invarianten.Frag.Symbolic.translate (program.requires index) symbols).toOption.get
        (by with_unfolding_all rfl)
      exact environment_success_of_valid program family symbols bounded (requiresPolicy program _)
        (fun _ => none) budget none invariants (by with_unfolding_all rfl) requirement (by rfl)
        certificate compiled_result original_valid

private theorem contracts_checked :
    KontrakteGeprueftB program family (List.finRange unit.fns.length) = true := by
  apply contracts_success
  rintro ⟨chosen, bound⟩
  have small : chosen < 4 := bound
  have choices : chosen = 0 ∨ chosen = 1 ∨ chosen = 2 ∨ chosen = 3 := by omega
  rcases choices with same | same | same | same
  · subst chosen
    change (checkFunction program family (fun _ => none) budget none ⟨0, by decide⟩).toOption.isSome = true
    with_unfolding_all decide +kernel
  · subst chosen
    change (checkFunction program family (fun _ => none) budget none ⟨1, by decide⟩).toOption.isSome = true
    with_unfolding_all decide +kernel
  · subst chosen
    change (checkFunction program family (fun _ => none) budget none ⟨2, by decide⟩).toOption.isSome = true
    with_unfolding_all decide +kernel
  · subst chosen; exact wrapper_accepted_zeuge

private theorem checks_present : (uCheckDecls unit).toOption.isSome = true := by decide +kernel
private def checks := (uCheckDecls unit).toOption.get checks_present

private theorem canonical_accepted :
    AkzeptiertX program family (List.finRange unit.fns.length) [] [] [] [] checks = true := by
  -- The wide quantified VC is already certified. Only structural gates remain.
  simp only [AkzeptiertX, Invarianten.Pruefer.invariantVCB, contracts_checked]
  decide +kernel

/-- The unchanged four-function source unit accepts its u64 fallible wrapper,
    preserving both normal and reason Duty paths through the real assembler. -/
theorem fallible_image_accepted (ready : (uCheckDecls uFremdFallible).toOption.isSome = true)
    {image : Programm (declOf uFremdFallible) × List (declOf uFremdFallible).Fn}
    (emitted : lowerAllg uFremdFallible = .ok image) :
    AkzeptiertX image.1 (Cover.Differenz.sperrFamilie uFremdFallible)
      (List.finRange uFremdFallible.fns.length) [] [] [] []
      ((uCheckDecls uFremdFallible).toOption.get ready) = true := by
  apply checked_image unit ForeignGateFunctions.fallPieces ForeignGateFunctions.fallPieces_ok
    ((uCheckDecls unit).toOption.get ready) emitted true
  intro invariants foreignGate
  have emptyFamily : invariants = (fun i => Fin.elim0 (show Fin 0 from i)) := by
    funext i
    exact Fin.elim0 (show Fin 0 from i)
  subst invariants
  have sameProof : foreignGate = foreign_contracts := Subsingleton.elim _ _
  subst sameProof
  exact canonical_accepted

end Gabbro.Grammatik.Parser.Uebersetze.ForeignGateAcceptance
