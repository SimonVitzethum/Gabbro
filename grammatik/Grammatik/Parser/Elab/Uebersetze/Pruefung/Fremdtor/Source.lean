/- C16 remaining forms (3): foreign gates end to end.

   A gate may name a C08 foreign body. The wrapper is still an ordinary nullary
   `UFn` threading the Duty; the gate call is the ordinary foreign call Stage 0
   already lowers. The infallible answer-less case rides `axCall`; the fallible
   `int`-answered case rides `bindAxElse` whose error branch rethrows the exact
   reason while retaining the Duty. Only a normal gate return completes the
   evidence fold. An unclosed error branch is refused by the lowering:
   dropping it would drop the Duty's discharge path. -/
module

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

-- As with `kernel_rfl`, leave the final conversion to Lean's kernel. The
-- elaborator otherwise normalizes the complete closed front-end result while
-- matching the conclusion of an already constructed component proof.
open Lean Elab Tactic in
elab "foreign_exact " value:term : tactic => withMainContext do
  let proof ← Term.elabTerm value none
  Term.synthesizeSyntheticMVarsNoPostponing
  let proof ← instantiateMVars proof
  (← getMainGoal).assign proof
  replaceMainGoal []

/-! ## The foreign-gated units, from source text -/

/-- The infallible foreign gate: the `axiom` body stays foreign, the wrapper
    calls it with `axCall` while threading the Duty. -/
def checkTextFremd : String :=
  "axiom f() effects { pure } unfalsifiable \"hw\"; impl fn g() { return; } check p { claim \"c\" measures x gates f can_fail { return true; } floor 2 >= 1 }"

/-- The fallible foreign gate: the `extern fn` with a reason channel is called
    with `bindAxElse`; the error branch preserves the reason channel. -/
def checkTextFremdFallible : String :=
  "reason R { A = 0 \"t\" exhaustive } extern fn f() -> u64 or R effects { pure }; impl fn g() { return; } check p { claim \"c\" measures x gates f can_fail { return true; } floor 2 >= 1 }"

/-- The generated report index uses the ordinary decimal zero. -/
private theorem fremd_repr_zero : Nat.repr 0 = "0" := by kernel_rfl

attribute [local cbv_eval] fremd_repr_zero

-- Retain the actual front-end values once, together with their complete
-- success equations. Dependent checker callbacks then read ordinary unit data.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
def fremdElaborated : { unit : UProg // elabText checkTextFremd = .ok unit } := by
  refine ⟨?unit, ?computed⟩
  case computed => cbv <;> (set_option smartUnfolding false in with_unfolding_all rfl)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
def fremdFallibleElaborated :
    { unit : UProg // elabText checkTextFremdFallible = .ok unit } := by
  refine ⟨?unit, ?computed⟩
  case computed => cbv <;> (set_option smartUnfolding false in with_unfolding_all rfl)

/-- Both foreign-gated units elaborate. -/
theorem checkTextFremd_ok : (elabText checkTextFremd).toOption.isSome = true := by
  rw [fremdElaborated.property]
  rfl

theorem checkTextFremdFallible_ok :
    (elabText checkTextFremdFallible).toOption.isSome = true := by
  rw [fremdFallibleElaborated.property]
  rfl

/-- The elaborated units behind the foreign-gate witnesses. -/
def uFremd : UProg := fremdElaborated.val

def uFremdFallible : UProg := fremdFallibleElaborated.val

/-- Both retained units are exactly the successful source elaborations. -/
theorem uFremd_from_source : elabText checkTextFremd = .ok uFremd :=
  fremdElaborated.property

theorem uFremdFallible_from_source : elabText checkTextFremdFallible = .ok uFremdFallible :=
  fremdFallibleElaborated.property

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

/-- Recover handler absence through the successful assembler, without evaluating
    bodies under an abstract function index. -/
private theorem lowered_no_handlers (u : UProg)
    (lowered : (lowerAllg u).toOption.isSome = true) (noHandlers : u.hands = []) :
    ∀ f, (((lowerAllg u).toOption.get lowered).1).unterbricht f = false := by
  have h := except_ok_get lowered
  generalize hp : (lowerAllg u).toOption.get lowered = result at h ⊢
  unfold lowerAllg at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · have fields := Measures.checkedProgram_eq h
        rw [fields.1]
        intro f
        simp only [progOfFn, noHandlers, List.any_nil]
      · cases h

/-! ## Acceptance with the real Duty -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- The lowered units with their derived checks are admitted. -/
theorem fremd_checkB :
    checkB checkPFremd [] [] (List.finRange uFremd.fns.length) checkChecksFremd = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem fremdFallible_checkB :
    checkB checkPFremdFallible [] [] (List.finRange uFremdFallible.fns.length) checkChecksFremdFallible = true := by
  decide +kernel

/-- Compose the unchanged atomic checker over abstract inputs. Keeping this
    Boolean factorization abstract avoids converting a complete closed front-end
    result while assembling its independently checked component certificates. -/
private theorem foreign_acceptance_of_components {D : Deklaration}
    [DecidableEq D.Fn] [DecidableEq D.Ax]
    (P : Programm D) (S : SperrInv D) (fs : List D.Fn) (checks : List (CheckDecl D))
    (fragment : programmImFragmentG P fs = true) (bounds : abgAlleB P fs = true)
    (footprints : fussWXB P S fs [] = true) (levels : stufenB P fs = true)
    (pool : einzelnPoolB P fs [] [] = true) (races : rennB P fs [] [] = true)
    (answers : antwortenB P fs = true) (masks : maskenB P fs = true)
    (interfaces : schnittstellenB P fs = true)
    (duties : checkB P [] [] fs checks = true) (scopes : scopesOkProgB P fs = true)
    (invariants : Invarianten.Pruefer.programInvariantsB P S fs (fun _ => none) = true)
    (contracts : Vertraege.Pruefer.KontrakteGeprueftB P S fs = true) :
    AkzeptiertX P S fs [] [] [] [] checks = true := by
  simp only [AkzeptiertX, Invarianten.Pruefer.invariantVCB, Bool.and_eq_true]
  and_intros
  · exact fragment
  · exact bounds
  · exact footprints
  · exact levels
  · rfl
  · rfl
  · exact pool
  · exact races
  · exact answers
  · exact masks
  · exact interfaces
  · exact libraryB_immer _ _
  · exact Kernzelle.accumulatorB_leer
  · exact duties
  · rfl
  · exact scopes
  · exact GuestBoundary.admissionB_nil
  · exact invariants
  · exact contracts

end Gabbro.Grammatik.Parser.Uebersetze
