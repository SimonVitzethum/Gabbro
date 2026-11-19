/- Exact source/lowering and Duty-check witnesses for C16 foreign gates.
   The strict checker accepts both the unchanged void foreign statement and
   the quantified fallible foreign continuation. Normal report completion and error-path Duty
   preservation remain separate model facts. The legacy axiom spelling also
   retains the front end's source-export refusal. -/
module

public import Grammatik.Logik.Vertraege.Pruefer.Program
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
import Grammatik.Logik.Vertraege.Pruefer.Witness.Selection

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

/-! ## Duty admission and checked contract-fragment boundaries -/

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


private theorem fremd_foreign_contracts : axContractsB uFremd = true := by decide +kernel
private def fremdCanonical : Programm (declOf uFremd) :=
  progOfFn uFremd (fun f => (ForeignGateFunctions.infPieces f).1)
    (fun f => (ForeignGateFunctions.infPieces f).2.1)
    (fun f => (ForeignGateFunctions.infPieces f).2.2)
    (fun i => Fin.elim0 (show Fin 0 from i)) (ptrVertragOf uFremd)
    (fun a => axVertragOf uFremd a fremd_foreign_contracts)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- The void foreign call now has a generic totality certificate. -/
private theorem fremd_contract_checked :
    (Vertraege.Pruefer.checkFunction fremdCanonical (Cover.Differenz.sperrFamilie uFremd)
      (fun _ => none) {} none ⟨3, by decide⟩).toOption.isSome = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem fremdCanonical_accepted :
    AkzeptiertX fremdCanonical (Cover.Differenz.sperrFamilie uFremd)
      (List.finRange uFremd.fns.length) [] [] [] [] checkChecksFremd = true := by
  decide +kernel

attribute [local irreducible] checkPFremd checkPFremdFallible

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- The elaborated void-call unit is accepted; source-export metadata is separate. -/
theorem fremd_accepted :
    AkzeptiertX checkPFremd (Cover.Differenz.sperrFamilie uFremd)
      (List.finRange uFremd.fns.length) [] [] [] [] checkChecksFremd = true := by
  delta checkPFremd
  apply ForeignGateAcceptance.checked_image uFremd ForeignGateFunctions.infPieces
    ForeignGateFunctions.infPieces_ok checkChecksFremd
    (except_ok_get uFremd_lowered) true
  intro invariants foreignGate
  have emptyFamily : invariants = (fun i => Fin.elim0 (show Fin 0 from i)) := by
    funext i
    exact Fin.elim0 (show Fin 0 from i)
  subst invariants
  have sameProof : foreignGate = fremd_foreign_contracts := Subsingleton.elim _ _
  subst sameProof
  exact fremdCanonical_accepted

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- The unchanged fallible source unit passes with its quantified oracle VC. -/
theorem fremdFallible_accepted :
    AkzeptiertX checkPFremdFallible (Cover.Differenz.sperrFamilie uFremdFallible)
      (List.finRange uFremdFallible.fns.length) [] [] [] [] checkChecksFremdFallible = true := by
  delta checkPFremdFallible
  exact ForeignGateAcceptance.fallible_image_accepted uFremdFallible_checks_ok
    (except_ok_get uFremdFallible_lowered)

/-- Joint non-degeneracy for the assembler: four real functions, one foreign
    item, one derived Duty check and an accepted void foreign call. -/
theorem foreign_checked_image_zeuge :
    uFremd.fns.length = 4 ∧ uFremd.axs.length = 1 ∧ checkChecksFremd.length = 1 ∧
    checkB checkPFremd [] [] (List.finRange uFremd.fns.length) checkChecksFremd = true ∧
    AkzeptiertX checkPFremd (Cover.Differenz.sperrFamilie uFremd)
      (List.finRange uFremd.fns.length) [] [] [] [] checkChecksFremd = true :=
  ⟨rfl, rfl, by kernel_rfl, fremd_checkB, fremd_accepted⟩

/-- The fallible assembler premises hold together on four real functions,
    a nonempty oracle/reason range, a real Duty check and the actual image. -/
theorem foreign_fallible_checked_image_zeuge :
    uFremdFallible.fns.length = 4 ∧ uFremdFallible.axs.length = 1 ∧
    checkChecksFremdFallible.length = 1 ∧ ∃ image,
      lowerAllg uFremdFallible = .ok image ∧
      AkzeptiertX image.1 (Cover.Differenz.sperrFamilie uFremdFallible)
        (List.finRange uFremdFallible.fns.length) [] [] [] [] checkChecksFremdFallible = true := by
  refine ⟨rfl, rfl, by kernel_rfl, (lowerAllg uFremdFallible).toOption.get uFremdFallible_lowered,
    except_ok_get uFremdFallible_lowered, ?_⟩
  exact ForeignGateAcceptance.fallible_image_accepted uFremdFallible_checks_ok
    (except_ok_get uFremdFallible_lowered)

end Gabbro.Grammatik.Parser.Uebersetze
