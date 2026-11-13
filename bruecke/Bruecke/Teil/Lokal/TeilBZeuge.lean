module
public import Bruecke.Teil.Lokal.Quelle
public import Bruecke.Anweisung.Lokal.LokalZeuge
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
# Joint partial witness with local bindings and an open function

The carried routine is the built local-binding fixture: `let`, `let mut`, reassignment,
a table write and a return. The additional Boolean function is open and is a declared
start. Only its G body duty remains a hypothesis. This is a lowered-unit witness for
`bruecke_nutzer_teilB`, without a claim about parsing a source text.
-/

namespace Gabbro.Bruecke.TeilBZeuge

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def openFn : UFn :=
  { name := "open", params := [], kinds := [], res := none, resBool := true,
    held := [], puts := [], gives := [], body := [], ret := .bool .tru }

def unit : UProg :=
  { LokalZeuge.unit with fns := [LokalZeuge.routine, openFn], roots := ["open"] }

abbrev carried (c : Fin unit.fns.length) : Prop := c.val = 0

theorem carried_eq (c : Fin unit.fns.length) (hc : carried c) : c = ⟨0, by decide⟩ :=
  Fin.ext hc

theorem carried_fn (c : Fin unit.fns.length) (hc : carried c) :
    fnAt unit c = LokalZeuge.routine := by
  rw [carried_eq c hc]
  rfl

theorem routine_checks :
    artB LokalZeuge.routine = true ∧ namenB LokalZeuge.routine = true ∧
    freiB LokalZeuge.routine = true ∧ oldsB unit LokalZeuge.routine = true ∧
    postB unit LokalZeuge.routine = true ∧ schreibtB unit LokalZeuge.routine = true ∧
    bindFrischB LokalZeuge.routine = true :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem getragen_zeuge : GetragenB unit carried := by
  refine { toGetragen := {
    geschlossen := ?_
    boolTab := ?_
    boolErg := ?_
    tab := tabB_ok (by decide +kernel)
    art := ?_
    namen := ?_
    frei := ?_
    olds := ?_
    post := ?_
    schreibt := ?_
    ohneReq := ?_
    ohneGrund := ?_
    ohneInv := rfl
    ohneGlob := rfl
    ohneTransition := fun c _ => ohneTransitionB_ok (by decide +kernel) c }
           frisch := ?_ }
  · intro c hc n hn d _
    rw [carried_fn c hc] at hn
    have empty : calleesOf LokalZeuge.routine = [] := by kernel_rfl
    rw [empty] at hn
    cases hn
  · exact (keinBoolB_ok (u := LokalZeuge.unit) (by decide +kernel)).1
  · intro c hc
    rw [carried_fn c hc]
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · intro c hc
    rw [carried_fn c hc]
    exact artB_ok routine_checks.1
  · intro c hc
    rw [carried_fn c hc]
    exact (of_decide_eq_true routine_checks.2.1 :
      (LokalZeuge.routine.params.map (·.1)).Nodup)
  · intro c hc
    rw [carried_fn c hc]
    exact freiB_ok routine_checks.2.2.1
  · intro c hc
    rw [carried_fn c hc]
    exact oldsB_ok routine_checks.2.2.2.1
  · intro c hc
    rw [carried_fn c hc]
    exact postB_ok routine_checks.2.2.2.2.1
  · intro c hc
    rw [carried_fn c hc]
    exact schreibtB_ok routine_checks.2.2.2.2.2.1
  · intro c hc
    rw [carried_fn c hc]
    rfl
  · intro c hc
    rw [carried_fn c hc]
    rfl
  · intro c hc
    rw [carried_fn c hc]
    exact bindFrischB_ok routine_checks.2.2.2.2.2.2

/-- Extending the function list preserves the existing routine's Body duty. -/
theorem body_duties_zeuge :
    ∀ c : Fin unit.fns.length, carried c →
      ∃ body, zuBodyB unit (fnAt unit c) = some body ∧
        meetsU unit (wfU unit) (fnAt unit c) body := by
  intro c hc
  rw [carried_fn c hc]
  refine ⟨LokalZeuge.koerper, ?_, ?_⟩
  · kernel_rfl
  · exact LokalZeuge.routine_meets

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
    | ⟨n + 2, h⟩ =>
      have h' : n + 2 < 2 := h
      omega
  exact lowerAllg_requires unit program functions hn lowered

/-- The interface duty of the unit, from the refinement of its pointer contracts. As in the
    instance files of this package, that refinement is a premise the user discharges. -/
theorem interfaces (pointer_refinement : PtrVerfeinert program) : SchnittstellenPflicht unit := by
  intro P fs hlow
  have pair : (program, functions) = (P, fs) := by
    simpa only [Except.ok.injEq] using lowered.symm.trans hlow
  have hP : program = P := congrArg Prod.fst pair
  rw [← hP]
  exact pointer_refinement

/-- No proof of the open function's G body is hidden in the fixture. -/
theorem offenePflicht_zeuge (pointer_refinement : PtrVerfeinert program)
    (hBody : ∀ passes, KoerperGutS program passes (axWahr (declOf unit))
      (SperrInv.leer (declOf unit)) ⟨1, by decide⟩) : OffenePflicht unit carried := by
  intro c hc P fs hlow
  have cv : c.val = 1 := by
    have bound : c.val < 2 := c.isLt
    change ¬ c.val = 0 at hc
    omega
  have ce : c = ⟨1, by decide⟩ := Fin.ext cv
  subst c
  have pair : (program, functions) = (P, fs) := by
    simpa only [Except.ok.injEq] using lowered.symm.trans hlow
  have hP : program = P := congrArg Prod.fst pair
  rw [← hP]
  exact ⟨hBody, pointer_refinement _⟩

theorem starts_zeuge : startsAllg unit = [⟨⟨1, by decide⟩, Env.nil⟩] := by kernel_rfl

theorem offeneStarts_zeuge : OffeneStartPflicht unit carried program (by decide +kernel) := by
  intro a _ _
  unfold ReqAmEintritt
  rw [all_requires a.1]
  rfl

/-- All unit-level partial-binding premises hold together, including a nonempty open start.
    Only the open body's G duty is assumed. -/
theorem teilBpflichten_zeuge (pointer_refinement : PtrVerfeinert program)
    (hBody : ∀ passes, KoerperGutS program passes (axWahr (declOf unit))
      (SperrInv.leer (declOf unit)) ⟨1, by decide⟩) :
    nullB unit = true ∧ GetragenB unit carried ∧ rangB unit (rangAuto unit) = true ∧
    SchnittstellenPflichtTeil unit carried ∧
    (∀ c : Fin unit.fns.length, carried c →
      ∃ body, zuBodyB unit (fnAt unit c) = some body ∧
        meetsU unit (wfU unit) (fnAt unit c) body) ∧
    OffenePflicht unit carried ∧
    OffeneStartPflicht unit carried program (by decide +kernel) ∧
    startsAllg unit = [⟨⟨1, by decide⟩, Env.nil⟩] ∧
    carried ⟨0, by decide⟩ ∧ ¬ carried ⟨1, by decide⟩ ∧
    zuBody unit LokalZeuge.routine = none ∧ stimmigB unit = false ∧
    Zielsatz.NutzerPflicht (einheitAllg unit program (by decide +kernel)) := by
  have hPtr : SchnittstellenPflichtTeil unit carried := fun P fs hlow c _ => interfaces pointer_refinement P fs hlow c
  have hOpen := offenePflicht_zeuge pointer_refinement hBody
  exact ⟨by decide +kernel, getragen_zeuge, by decide +kernel, hPtr, body_duties_zeuge,
    hOpen, offeneStarts_zeuge, starts_zeuge, by decide, by decide, by kernel_rfl,
    by decide +kernel,
    bruecke_nutzer_teilB lowered getragen_zeuge (rangAuto unit) (rang_of (by decide +kernel))
      body_duties_zeuge hPtr hOpen (by decide +kernel) offeneStarts_zeuge⟩

end Gabbro.Bruecke.TeilBZeuge
