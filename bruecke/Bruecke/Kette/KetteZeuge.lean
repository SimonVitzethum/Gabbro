module
public import Bruecke.Kette.Quelle
public import Bruecke.Anweisung.Zweig.ZweigZeuge
import Grammatik.Kern.Taktik.KernelRfl
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

/-!
# Joint witness for the consolidated carried chain

A fresh `let` precedes the proved branching fixture (early return and slot writes). A second
carried function calls it inside a branch, making closure nontrivial. A Boolean function is
open and is a declared start. Pointer refinement and its G body duty remain explicit premises.
This witnesses a lowered unit, without claiming measured source-parser acceptance.
-/

namespace Gabbro.Bruecke.KetteZeuge

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- The existing proved function with an unused fresh local binding. -/
def routine : UFn :=
  { ZweigZeuge.routine with body := .bind "scratch" none (.lit 0) :: ZweigZeuge.routine.body }

def caller : UFn :=
  { name := "caller", params := [], kinds := [], res := none, held := [], puts := ["T"],
    gives := [], body := [.ifBeg (.cmp "==" (.lit 0) (.lit 0)),
      .call "pick" [.val (.lit 2)], .ifElse, .blkEnd], ret := .empty }

def openFn : UFn :=
  { name := "open", params := [], kinds := [], res := none, resBool := true,
    held := [], puts := [], gives := [], body := [], ret := .bool .tru }

def unit : UProg :=
  { ZweigZeuge.unit with fns := [routine, caller, openFn], roots := ["caller", "open"] }

def koerper : List Gabbro.Body.Stmt :=
  .bindName "scratch" (.lit (.int 0)) :: ZweigZeuge.koerper

def ruf : Gabbro.Body.Stmt :=
  .call "pick" ["k"] [.lit (.int 2)] (.hasShape "k" (.intIn 0 9))

def callerBody : List Gabbro.Body.Stmt :=
  [.ite (.bin .eq (.lit (.int 0)) (.lit (.int 0))) [ruf] []]

abbrev carried (c : Fin unit.fns.length) : Prop := c.val < 2

instance (c : Fin unit.fns.length) : Decidable (carried c) :=
  inferInstanceAs (Decidable (c.val < 2))

theorem carried_indices (c : Fin unit.fns.length) (hc : carried c) :
    c = ⟨0, by decide⟩ ∨ c = ⟨1, by decide⟩ := by
  have h : c.val = 0 ∨ c.val = 1 := by
    unfold carried at hc
    omega
  exact h.elim (fun h => .inl (Fin.ext h)) (fun h => .inr (Fin.ext h))

theorem carried_checks : ∀ c : Fin unit.fns.length, carried c →
    artB (fnAt unit c) = true ∧ namenB (fnAt unit c) = true ∧
    freiB (fnAt unit c) = true ∧ oldsB unit (fnAt unit c) = true ∧
    postB unit (fnAt unit c) = true ∧ schreibtB unit (fnAt unit c) = true ∧
    bindFrischB (fnAt unit c) = true := by
  intro c hc
  rcases carried_indices c hc with rfl | rfl
  · exact (by decide +kernel : artB routine = true ∧ namenB routine = true ∧
      freiB routine = true ∧ oldsB unit routine = true ∧ postB unit routine = true ∧
      schreibtB unit routine = true ∧ bindFrischB routine = true)
  · exact (by decide +kernel : artB caller = true ∧ namenB caller = true ∧
      freiB caller = true ∧ oldsB unit caller = true ∧ postB unit caller = true ∧
      schreibtB unit caller = true ∧ bindFrischB caller = true)

theorem getragen_zeuge : GetragenG unit carried := by
  refine { toGetragen := {
    geschlossen := ?_
    boolTab := (keinBoolB_ok (u := ZweigZeuge.unit) (by decide +kernel)).1
    boolErg := ?_
    tab := tabB_ok (by decide +kernel)
    art := fun c hc => artB_ok (carried_checks c hc).1
    namen := fun c hc => (of_decide_eq_true (carried_checks c hc).2.1 :
      ((fnAt unit c).params.map (·.1)).Nodup)
    frei := fun c hc => freiB_ok (carried_checks c hc).2.2.1
    olds := fun c hc => oldsB_ok (carried_checks c hc).2.2.2.1
    post := fun c hc => postB_ok (carried_checks c hc).2.2.2.2.1
    schreibt := fun c hc => schreibtB_ok (carried_checks c hc).2.2.2.2.2.1
    gschreibt := fun c hc => gschreibtB_ok (carried_checks c hc).2.2.2.2.2.1
    ohneReq := ?_
    ohneGrund := ?_
    ohneInv := rfl
    statics := staticsB_ok (by decide +kernel)
    ohneTransition := fun c _ => ohneTransitionB_ok (by decide +kernel) c }
           frisch := fun c hc => bindFrischB_ok (carried_checks c hc).2.2.2.2.2.2 }
  · intro c hc n hn d hd
    rcases carried_indices c hc with rfl | rfl
    · have empty : calleesOf routine = [] := by kernel_rfl
      change n ∈ calleesOf routine at hn
      rw [empty] at hn
      cases hn
    · have hn' : n = "pick" := List.mem_singleton.mp hn
      subst n
      match d with
      | ⟨0, _⟩ => show (0 : Nat) < 2; omega
      | ⟨1, _⟩ => show (1 : Nat) < 2; omega
      | ⟨2, _⟩ =>
        have hd' : fnSuch unit "pick" = some openFn := hd
        have hl : fnSuch unit "pick" = some routine := by kernel_rfl
        rw [hl] at hd'
        have names := congrArg UFn.name (Option.some.inj hd')
        exact False.elim ((by decide : routine.name ≠ openFn.name) names)
      | ⟨n + 3, h⟩ =>
        have h' : n + 3 < 3 := h
        omega
  · intro c hc
    rcases carried_indices c hc with rfl | rfl
    · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · intro c hc
    rcases carried_indices c hc with rfl | rfl
    · kernel_rfl
    · kernel_rfl
  · intro c hc
    rcases carried_indices c hc with rfl | rfl
    · kernel_rfl
    · kernel_rfl

/-- Reuse the closed branching duty after executing the additional fresh binding. -/
theorem routine_meets : meetsU unit (wfU unit) routine koerper := by
  intro ρ s hW hpre
  let t : Gabbro.Body.State := ⟨s.world, Gabbro.Body.bindLocal s.local' "scratch" (.int 0)⟩
  have hk : t.local' "k" = s.local' "k" := by
    simp [t, Gabbro.Body.bindLocal]
  have hp : Gabbro.Body.eval t (preExpr ZweigZeuge.routine) = some (.bool true) := by
    change Gabbro.Body.eval s (preExpr ZweigZeuge.routine) = some (.bool true) at hpre
    simpa only [ZweigZeuge.pre_eq, Gabbro.Body.eval, hk] using hpre
  have hm := ZweigZeuge.routine_meets ρ t hW hp
  have run : Gabbro.Body.exec ρ koerper s = Gabbro.Body.exec ρ ZweigZeuge.koerper t := by
    rfl
  change ∃ s', Gabbro.Body.finalState (Gabbro.Body.exec ρ koerper s) = some s' ∧
    (postU unit (wfU unit) routine s s'
      (Gabbro.Body.finalValue (Gabbro.Body.exec ρ koerper s))).getD False
  rw [run]
  exact hm

/-- A call inside the then-arm consumes the callee's contract, including its world typing. -/
theorem caller_meets : meetsU unit (wfU unit) caller callerBody := by
  intro ρ s hW _
  change Gabbro.Body.Contract ρ "pick" (preProp (wfU unit) routine)
      (fun s s' r => (postU unit (wfU unit) routine s s' r).getD False) →
    Gabbro.Body.Frame ρ "pick" ["T"] → _
  intro hContract _
  let t : Gabbro.Body.State :=
    ⟨s.world, Gabbro.Body.bindAll ["k"] [.int 2] (fun _ => .absent)⟩
  have hp : Gabbro.Body.eval t (preExpr routine) = some (.bool true) := by
    have pre : preExpr routine = .hasShape "k" (.intIn 0 9) := by kernel_rfl
    rw [pre]
    simp [Gabbro.Body.eval, t, Gabbro.Body.bindAll, Gabbro.Body.bindLocal,
      Gabbro.Body.Value.hasShape_int_intIn]
  have hpost := hContract t ⟨hW, hp⟩
  have hw : wfU unit (ρ "pick" t).1 := hpost.1
  let s' : Gabbro.Body.State := ⟨(ρ "pick" t).1.world, s.local'⟩
  have hcall : Gabbro.Body.step ρ ruf s = .running s' := by
    change (match Gabbro.Body.eval t (preExpr routine) with
      | some (.bool true) => Gabbro.Body.Outcome.running s'
      | _ => .stuck) = .running s'
    rw [hp]
  have hc : Gabbro.Body.eval s (.bin .eq (.lit (.int 0)) (.lit (.int 0))) =
      some (.bool true) := by rfl
  have run : Gabbro.Body.exec ρ callerBody s = .running s' := by
    simp only [callerBody, Gabbro.Body.exec, step_ite_wahr ρ hc, hcall]
  refine ⟨s', ?_, ?_⟩
  · rw [run]; rfl
  · exact hw

theorem body_duties_zeuge : ∀ c : Fin unit.fns.length, carried c →
    ∃ body, zuBodyZ unit (fnAt unit c) = some body ∧
      meetsU unit (wfU unit) (fnAt unit c) body := by
  intro c hc
  rcases carried_indices c hc with rfl | rfl
  · exact ⟨koerper, by kernel_rfl, routine_meets⟩
  · exact ⟨callerBody, by kernel_rfl, caller_meets⟩

/-- The call nested between branch markers is present in closure's flat callee list. -/
theorem branch_call_zeuge : calleesOf caller = ["pick"] ∧
    fnSuch unit "pick" = some (fnAt unit ⟨0, by decide⟩) ∧
    carried ⟨1, by decide⟩ ∧ carried ⟨0, by decide⟩ := by
  exact ⟨by kernel_rfl, by kernel_rfl, by decide, by decide⟩

theorem lowered_some : (lowerAllg unit).toOption.isSome = true := by decide +kernel

def program : Programm (declOf unit) := ((lowerAllg unit).toOption.get lowered_some).1

def functions : List (declOf unit).Fn := ((lowerAllg unit).toOption.get lowered_some).2

theorem lowered : lowerAllg unit = .ok (program, functions) := except_ok_get lowered_some

theorem all_requires : ∀ c, program.requires c = .tru := by
  have hn : ∀ c : Fin unit.fns.length, (fnAt unit c).needs = [] := by
    intro c
    match c with
    | ⟨0, _⟩ => exact (by kernel_rfl : (fnAt unit ⟨0, by decide⟩).needs = [])
    | ⟨1, _⟩ => exact (by kernel_rfl : (fnAt unit ⟨1, by decide⟩).needs = [])
    | ⟨2, _⟩ => exact (by kernel_rfl : (fnAt unit ⟨2, by decide⟩).needs = [])
    | ⟨n + 3, h⟩ =>
      have h' : n + 3 < 3 := h
      omega
  exact lowerAllg_requires unit program functions hn lowered

theorem interfaces (pointer_refinement : PtrVerfeinert program) : SchnittstellenPflicht unit := by
  intro P fs hlow
  have pair : (program, functions) = (P, fs) := by
    simpa only [Except.ok.injEq] using lowered.symm.trans hlow
  have hP : program = P := congrArg Prod.fst pair
  rw [← hP]
  exact pointer_refinement

theorem offenePflicht_zeuge (pointer_refinement : PtrVerfeinert program)
    (hBody : ∀ passes, KoerperGutS program passes (axWahr (declOf unit))
      (SperrInv.leer (declOf unit)) ⟨2, by decide⟩) : OffenePflicht unit carried := by
  intro c hc P fs hlow
  have cv : c.val = 2 := by
    have bound : c.val < 3 := c.isLt
    change ¬ c.val < 2 at hc
    omega
  have ce : c = ⟨2, by decide⟩ := Fin.ext cv
  subst c
  have pair : (program, functions) = (P, fs) := by
    simpa only [Except.ok.injEq] using lowered.symm.trans hlow
  have hP : program = P := congrArg Prod.fst pair
  rw [← hP]
  exact ⟨hBody, pointer_refinement _⟩

theorem starts_zeuge : startsAllg unit =
    [⟨⟨1, by decide⟩, Env.nil⟩, ⟨⟨2, by decide⟩, Env.nil⟩] := by kernel_rfl

theorem offeneStarts_zeuge : OffeneStartPflicht unit carried program (by decide +kernel) := by
  intro a _ _
  unfold ReqAmEintritt
  rw [all_requires a.1]
  rfl

/-- All premises of the unit-level theorem coexist with bindings, branching, closure and an
    open start. The two remaining user obligations are stated, never manufactured. -/
theorem kettenpflichten_zeuge (pointer_refinement : PtrVerfeinert program)
    (hBody : ∀ passes, KoerperGutS program passes (axWahr (declOf unit))
      (SperrInv.leer (declOf unit)) ⟨2, by decide⟩) :
    nullB unit = true ∧ GetragenG unit carried ∧ rangB unit (rangAuto unit) = true ∧
    SchnittstellenPflichtTeil unit carried ∧
    (∀ c : Fin unit.fns.length, carried c → ∃ body,
      zuBodyZ unit (fnAt unit c) = some body ∧ meetsU unit (wfU unit) (fnAt unit c) body) ∧
    OffenePflicht unit carried ∧
    OffeneStartPflicht unit carried program (by decide +kernel) ∧
    startsAllg unit = [⟨⟨1, by decide⟩, Env.nil⟩, ⟨⟨2, by decide⟩, Env.nil⟩] ∧
    carried ⟨0, by decide⟩ ∧ carried ⟨1, by decide⟩ ∧ ¬ carried ⟨2, by decide⟩ ∧
    stimmigB unit = false ∧
    Zielsatz.NutzerPflicht (einheitAllg unit program (by decide +kernel)) := by
  have hPtr : SchnittstellenPflichtTeil unit carried :=
    fun P fs hlow c _ => interfaces pointer_refinement P fs hlow c
  have hOpen := offenePflicht_zeuge pointer_refinement hBody
  exact ⟨by decide +kernel, getragen_zeuge, by decide +kernel, hPtr, body_duties_zeuge,
    hOpen, offeneStarts_zeuge, starts_zeuge, by decide, by decide, by decide,
    by decide +kernel,
    bruecke_nutzer_G lowered getragen_zeuge (rangAuto unit) (rang_of (by decide +kernel))
      body_duties_zeuge hPtr hOpen (by decide +kernel) offeneStarts_zeuge⟩

end Gabbro.Bruecke.KetteZeuge
