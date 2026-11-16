/- Exact source/lowering and Duty-check witnesses for C16 foreign gates.
   The strict checker refuses the unchanged void foreign statement and wide
   fallible-result domain. Normal report completion and error-path Duty
   preservation remain separate model facts. The legacy axiom spelling also
   retains the front end's source-export refusal. -/
module

public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Fremdtor.Units
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Fremdtor.Functions
public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Export
public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Ableitung
public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Falte
public import Grammatik.Parser.Elab.UebersetzeAllg3
public import Grammatik.Parser.Elab.UebersetzeAllg3.Rest2a
public import Grammatik.Parser.Cover.Differenz
public import Grammatik.Parser.Elab.UebersetzePipeline
public import Grammatik.Zielsatz.Atomar.AtomarAkzeptiert
public import Grammatik.Zielsatz.Kern.Akzeptiert.CheckDecide
public import Grammatik.Zielsatz.Kern.Akzeptiert.CheckProof
public import Grammatik.Kern.Syntax.Satz.PruefungMessung
public import Grammatik.Kern.Syntax.Satz.PruefungAbschluss
import Grammatik.Logik.Vertraege.Pruefer.Witness.Refusal
import all Grammatik.Logik.Vertraege.Pruefer.Program
import all Grammatik.Logik.Vertraege.Pruefer.Duties
import all Grammatik.Logik.Vertraege.Pruefer.Basic
import all Grammatik.Logik.Invarianten.Pruefer.Locks
import all Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtGeraetSem.Teil1
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

namespace Gabbro.Grammatik.Parser.Uebersetze


open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2
open Gabbro.Grammatik.Zielsatz

-- Check the closed source witnesses serially; overlapping kernel decisions
-- otherwise retain several complete front-end reductions in the same process.
set_option Elab.async false

/-! ## The foreign-gated units, from source text -/

/-- The infallible foreign gate: the `axiom` body stays foreign, the wrapper
    calls it with `axCall` while threading the Duty. -/
def checkTextFremd : String :=
  "axiom f() effects { pure } unfalsifiable \"hw\"; impl fn g() { return; } check p { claim \"c\" measures x gates f can_fail { return true; } floor 2 >= 1 }"

/-- The fallible foreign gate: the `extern fn` with a reason channel is called
    with `bindAxElse`; the error branch preserves the reason channel. -/
def checkTextFremdFallible : String :=
  "reason R { A = 0 \"t\" exhaustive } extern fn f() -> u64 or R effects { pure }; impl fn g() { return; } check p { claim \"c\" measures x gates f can_fail { return true; } floor 2 >= 1 }"

/-- Both explicit unit values are exactly the successful source elaborations. -/
theorem uFremd_from_source : elabText checkTextFremd = .ok uFremd := by kernel_rfl

theorem uFremdFallible_from_source : elabText checkTextFremdFallible = .ok uFremdFallible := by
  kernel_rfl

/-- Both foreign-gated units elaborate. -/
theorem checkTextFremd_ok : (elabText checkTextFremd).toOption.isSome = true := by
  rw [uFremd_from_source]
  rfl

theorem checkTextFremdFallible_ok :
    (elabText checkTextFremdFallible).toOption.isSome = true := by
  rw [uFremdFallible_from_source]
  rfl

/-- The foreign bodies stay foreign: they elaborate to `axs`, never to `fns`. -/
example : (elabText checkTextFremd).map (fun u => u.axs.map (·.name)) =
    .ok ["f"] := by kernel_rfl

example : (elabText checkTextFremdFallible).map (fun u => u.axs.map (·.name)) =
    .ok ["f"] := by kernel_rfl

/-- The wrappers travel as ordinary functions of the units. -/
example : (elabText checkTextFremd).map (fun u => u.fns.map (·.name)) =
    .ok ["g", "p#probe", "p#report#0", "p#tor#f"] := by kernel_rfl

example : (elabText checkTextFremdFallible).map (fun u => u.fns.map (·.name)) =
    .ok ["g", "p#probe", "p#report#0", "p#tor#f"] := by kernel_rfl

/-- The infallible wrapper calls the foreign body with `axCall`, threading the Duty. -/
example : (elabText checkTextFremd).map
    (fun u => (u.fns.find? fun f => strEq f.name "p#tor#f").map (·.body)) =
    .ok (some [.axCall "f" []]) := by kernel_rfl

/-- The fallible wrapper threads the Duty through both paths: the call, the
    error-branch return and the branch marker. -/
example : (elabText checkTextFremdFallible).map
    (fun u => (u.fns.find? fun f => strEq f.name "p#tor#f").map
      fun f => (f.nimmt, f.gibt, f.body.length)) =
    .ok (some (["p#duty"], ["p#duty"], 6)) := by kernel_rfl

/-- The units have no tables and no statics. -/
theorem uFremd_tabs_leer : uFremd.tabs = [] := by kernel_rfl

theorem uFremd_globs_leer : uFremd.globs = [] := by kernel_rfl

theorem uFremdFallible_tabs_leer : uFremdFallible.tabs = [] := by kernel_rfl

theorem uFremdFallible_globs_leer : uFremdFallible.globs = [] := by kernel_rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- Both units lower. -/
theorem uFremd_lowered : (lowerAllg uFremd).toOption.isSome = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem uFremdFallible_lowered :
    (lowerAllg uFremdFallible).toOption.isSome = true := by
  decide +kernel

/-- The lowered programs behind the foreign-gate witnesses. -/
def checkPFremd : Programm (declOf uFremd) :=
  ((lowerAllg uFremd).toOption.get uFremd_lowered).1

def checkPFremdFallible : Programm (declOf uFremdFallible) :=
  ((lowerAllg uFremdFallible).toOption.get uFremdFallible_lowered).1

/-- The checks derive. -/
theorem uFremd_checks_ok : (uCheckDecls uFremd).toOption.isSome = true := by
  decide +kernel

theorem uFremdFallible_checks_ok :
    (uCheckDecls uFremdFallible).toOption.isSome = true := by
  decide +kernel

def checkChecksFremd : List (CheckDecl (declOf uFremd)) :=
  (uCheckDecls uFremd).toOption.get uFremd_checks_ok

def checkChecksFremdFallible : List (CheckDecl (declOf uFremdFallible)) :=
  (uCheckDecls uFremdFallible).toOption.get uFremdFallible_checks_ok

/-! ## The Duty is declared and threaded, non-vacuously -/

/-- The derived checks travel under their elaborated names. -/
theorem fremd_namen :
    (uCheckDecls uFremd).map (List.map CheckDecl.name) = .ok ["p"] := by kernel_rfl

theorem fremdFallible_namen :
    (uCheckDecls uFremdFallible).map (List.map CheckDecl.name) = .ok ["p"] := by kernel_rfl

/-- The Duty is the declared mark `p#duty` at stage 0. -/
theorem fremd_duty_marke :
    (uCheckDecls uFremd).map
      (List.map fun d => (uFremd.marken.get d.duty.1, d.duty.2)) =
    .ok [("p#duty", 0)] := by kernel_rfl

theorem fremdFallible_duty_marke :
    (uCheckDecls uFremdFallible).map
      (List.map fun d => (uFremdFallible.marken.get d.duty.1, d.duty.2)) =
    .ok [("p#duty", 0)] := by kernel_rfl

/-- The foreign wrappers discharge the Duty: they consume it in their lowered
    signatures. -/
theorem fremd_tor_threadet :
    (uCheckDecls uFremd).map (fun cs => cs.all fun d =>
      d.gates.all fun g =>
        decide (d.duty ∈ ((declOf uFremd).signatur g).konsumiert)) =
    .ok true := by
  decide +kernel

theorem fremdFallible_tor_threadet :
    (uCheckDecls uFremdFallible).map (fun cs => cs.all fun d =>
      d.gates.all fun g =>
        decide (d.duty ∈ ((declOf uFremdFallible).signatur g).konsumiert)) =
    .ok true := by
  decide +kernel

/-! ## Duty admission and strict contract-fragment refusals -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- The lowered units pass the Duty check with their actual derived checks. -/
theorem fremd_checkB :
    checkB checkPFremd [] [] (List.finRange uFremd.fns.length) checkChecksFremd = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem fremdFallible_checkB :
    checkB checkPFremdFallible [] [] (List.finRange uFremdFallible.fns.length) checkChecksFremdFallible = true := by
  decide +kernel


/-- Transfer a canonical checker verdict to the actual successful
    assembler result. Interface contracts remain exactly the source contracts. -/
private theorem foreign_checked_image (u : UProg)
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

private theorem fremd_foreign_contracts : axContractsB uFremd = true := by decide +kernel
private theorem fremdFallible_foreign_contracts : axContractsB uFremdFallible = true := by
  decide +kernel

/-- A refused actual member blocks the unchanged default-hint collector. -/
private theorem foreign_contracts_refused {D : Deklaration}
    (P : Programm D) (S : SperrInv D) (fs : List D.Fn) (f : D.Fn) (member : f ∈ fs)
    (rejected : (Vertraege.Pruefer.checkFunction P S (fun _ => none) {} none f).toOption.isSome = false) :
    Vertraege.Pruefer.KontrakteGeprueftB P S fs = false := by
  change (Invarianten.Pruefer.collect fs (Vertraege.Pruefer.ContractDuties P S)
    (fun g => Vertraege.Pruefer.checkFunction P S (fun _ => none) {} none g)).toOption.isSome = false
  cases result : Invarianten.Pruefer.collect fs (Vertraege.Pruefer.ContractDuties P S)
      (fun g => Vertraege.Pruefer.checkFunction P S (fun _ => none) {} none g) with
  | error cause => rfl
  | ok checked =>
      have ready := Vertraege.Pruefer.RefusalWitness.collect_each fs
        (Vertraege.Pruefer.ContractDuties P S)
        (fun g => Vertraege.Pruefer.checkFunction P S (fun _ => none) {} none g)
        (by rw [result]; rfl) f member
      rw [rejected] at ready
      cases ready

private def fremdCanonical : Programm (declOf uFremd) :=
  progOfFn uFremd (fun f => (ForeignGateFunctions.infPieces f).1)
    (fun f => (ForeignGateFunctions.infPieces f).2.1)
    (fun f => (ForeignGateFunctions.infPieces f).2.2)
    (fun i => Fin.elim0 (show Fin 0 from i)) (ptrVertragOf uFremd)
    (fun a => axVertragOf uFremd a fremd_foreign_contracts)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- Outside the decidable fragment: contract statement is outside the checked scalar/control fragment. -/
private theorem fremd_fragment_refusal :
    (Vertraege.Pruefer.checkFunction fremdCanonical (Cover.Differenz.sperrFamilie uFremd)
      (fun _ => none) {} none ⟨3, by decide⟩).map (fun _ => ()) =
      .error (.unsupported "contract statement is outside the checked scalar/control fragment") := by
  decide +kernel

private theorem fremdCanonical_refused :
    AkzeptiertX fremdCanonical (Cover.Differenz.sperrFamilie uFremd)
      (List.finRange uFremd.fns.length) [] [] [] [] checkChecksFremd = false := by
  have rejected : (Vertraege.Pruefer.checkFunction fremdCanonical
      (Cover.Differenz.sperrFamilie uFremd) (fun _ => none) {} none ⟨3, by decide⟩).toOption.isSome = false := by
    have reason := fremd_fragment_refusal
    cases result : Vertraege.Pruefer.checkFunction fremdCanonical
        (Cover.Differenz.sperrFamilie uFremd) (fun _ => none) {} none ⟨3, by decide⟩ with
    | error cause => rfl
    | ok checked => simp only [result, Except.map, reduceCtorEq] at reason
  have contracts := foreign_contracts_refused fremdCanonical (Cover.Differenz.sperrFamilie uFremd)
    (List.finRange uFremd.fns.length) ⟨3, by decide⟩ (List.mem_finRange _) rejected
  simp only [AkzeptiertX, Invarianten.Pruefer.invariantVCB, contracts, Bool.and_false]

-- The collector rule has an actual refused member of a four-function unit.
private theorem foreign_contracts_refused_zeuge :
    (⟨3, by decide⟩ : Fin uFremd.fns.length) ∈ List.finRange uFremd.fns.length ∧
    (Vertraege.Pruefer.checkFunction fremdCanonical (Cover.Differenz.sperrFamilie uFremd)
      (fun _ => none) {} none ⟨3, by decide⟩).toOption.isSome = false ∧
    Vertraege.Pruefer.KontrakteGeprueftB fremdCanonical (Cover.Differenz.sperrFamilie uFremd)
      (List.finRange uFremd.fns.length) = false := by
  have rejected : (Vertraege.Pruefer.checkFunction fremdCanonical
      (Cover.Differenz.sperrFamilie uFremd) (fun _ => none) {} none ⟨3, by decide⟩).toOption.isSome = false := by
    have reason := fremd_fragment_refusal
    cases result : Vertraege.Pruefer.checkFunction fremdCanonical
        (Cover.Differenz.sperrFamilie uFremd) (fun _ => none) {} none ⟨3, by decide⟩ with
    | error cause => rfl
    | ok checked => simp only [result, Except.map, reduceCtorEq] at reason
  exact ⟨List.mem_finRange _, rejected,
    foreign_contracts_refused _ _ _ _ (List.mem_finRange _) rejected⟩

private def fremdFallibleCanonical : Programm (declOf uFremdFallible) :=
  progOfFn uFremdFallible (fun f => (ForeignGateFunctions.fallPieces f).1)
    (fun f => (ForeignGateFunctions.fallPieces f).2.1)
    (fun f => (ForeignGateFunctions.fallPieces f).2.2)
    (fun i => Fin.elim0 (show Fin 0 from i)) (ptrVertragOf uFremdFallible)
    (fun a => axVertragOf uFremdFallible a fremdFallible_foreign_contracts)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- Outside the decidable fragment: local observation type range exceeds the VC budget. -/
private theorem fremdFallible_fragment_refusal :
    (Vertraege.Pruefer.checkFunction fremdFallibleCanonical (Cover.Differenz.sperrFamilie uFremdFallible)
      (fun _ => none) {} none ⟨3, by decide⟩).map (fun _ => ()) =
      .error (.unsupported "local observation type range exceeds the VC budget") := by
  decide +kernel

private theorem fremdFallibleCanonical_refused :
    AkzeptiertX fremdFallibleCanonical (Cover.Differenz.sperrFamilie uFremdFallible)
      (List.finRange uFremdFallible.fns.length) [] [] [] [] checkChecksFremdFallible = false := by
  have rejected : (Vertraege.Pruefer.checkFunction fremdFallibleCanonical
      (Cover.Differenz.sperrFamilie uFremdFallible) (fun _ => none) {} none ⟨3, by decide⟩).toOption.isSome = false := by
    have reason := fremdFallible_fragment_refusal
    cases result : Vertraege.Pruefer.checkFunction fremdFallibleCanonical
        (Cover.Differenz.sperrFamilie uFremdFallible) (fun _ => none) {} none ⟨3, by decide⟩ with
    | error cause => rfl
    | ok checked => simp only [result, Except.map, reduceCtorEq] at reason
  have contracts := foreign_contracts_refused fremdFallibleCanonical (Cover.Differenz.sperrFamilie uFremdFallible)
    (List.finRange uFremdFallible.fns.length) ⟨3, by decide⟩ (List.mem_finRange _) rejected
  simp only [AkzeptiertX, Invarianten.Pruefer.invariantVCB, contracts, Bool.and_false]

attribute [local irreducible] checkPFremd checkPFremdFallible

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- The strict checker refuses the unchanged source unit for its certified fragment gap. -/
theorem fremd_abgelehnt :
    AkzeptiertX checkPFremd (Cover.Differenz.sperrFamilie uFremd)
      (List.finRange uFremd.fns.length) [] [] [] [] checkChecksFremd = false := by
  delta checkPFremd
  apply foreign_checked_image uFremd ForeignGateFunctions.infPieces
    ForeignGateFunctions.infPieces_ok checkChecksFremd
    (except_ok_get uFremd_lowered) false
  intro invariants foreignGate
  have emptyFamily : invariants = (fun i => Fin.elim0 (show Fin 0 from i)) := by
    funext i
    exact Fin.elim0 (show Fin 0 from i)
  subst invariants
  have sameProof : foreignGate = fremd_foreign_contracts := Subsingleton.elim _ _
  subst sameProof
  exact fremdCanonical_refused

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- The strict checker refuses the unchanged source unit for its certified fragment gap. -/
theorem fremdFallible_abgelehnt :
    AkzeptiertX checkPFremdFallible (Cover.Differenz.sperrFamilie uFremdFallible)
      (List.finRange uFremdFallible.fns.length) [] [] [] [] checkChecksFremdFallible = false := by
  delta checkPFremdFallible
  apply foreign_checked_image uFremdFallible ForeignGateFunctions.fallPieces
    ForeignGateFunctions.fallPieces_ok checkChecksFremdFallible
    (except_ok_get uFremdFallible_lowered) false
  intro invariants foreignGate
  have emptyFamily : invariants = (fun i => Fin.elim0 (show Fin 0 from i)) := by
    funext i
    exact Fin.elim0 (show Fin 0 from i)
  subst invariants
  have sameProof : foreignGate = fremdFallible_foreign_contracts := Subsingleton.elim _ _
  subst sameProof
  exact fremdFallibleCanonical_refused

/-- Joint non-degeneracy for the assembler/refusal proof rules: four real
    functions, one foreign item, one derived Duty check, and an actual refusal. -/
theorem foreign_checked_image_zeuge :
    uFremd.fns.length = 4 ∧ uFremd.axs.length = 1 ∧ checkChecksFremd.length = 1 ∧
    checkB checkPFremd [] [] (List.finRange uFremd.fns.length) checkChecksFremd = true ∧
    AkzeptiertX checkPFremd (Cover.Differenz.sperrFamilie uFremd)
      (List.finRange uFremd.fns.length) [] [] [] [] checkChecksFremd = false :=
  ⟨rfl, rfl, by kernel_rfl, fremd_checkB, fremd_abgelehnt⟩

end Gabbro.Grammatik.Parser.Uebersetze
