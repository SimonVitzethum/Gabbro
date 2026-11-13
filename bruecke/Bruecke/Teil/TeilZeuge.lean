module
public import Bruecke.Teil.Quelle
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
# Joint carried-call witness with a separate open function

The leaf and its caller have actual Body duties and a nonempty call graph. The third function
returns a Boolean and is not a root, so the old global shape check refuses the unit. Its
G body duty remains an explicit hypothesis; this witness does not claim to discharge that duty.
All interface refinements and all start requirements are proved for the same lowered unit.
-/

namespace Gabbro.Bruecke.TeilZeuge

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def leaf : UFn :=
  { name := "leaf", params := [], kinds := [], res := none, held := [], puts := [],
    gives := [], body := [], ret := .empty }

def caller : UFn := { leaf with name := "caller", body := [.call "leaf" []] }

def openFn : UFn := { leaf with name := "open", resBool := true, ret := .bool .tru }

def unit : UProg :=
  { tabs := [], locks := [], fns := [leaf, caller, openFn], roots := ["caller"] }

abbrev carried (c : Fin unit.fns.length) : Prop := c.val < 2

theorem carried_indices (c : Fin unit.fns.length) (hc : carried c) :
    c = ⟨0, by decide⟩ ∨ c = ⟨1, by decide⟩ := by
  have h : c.val = 0 ∨ c.val = 1 := by
    unfold carried at hc
    omega
  exact h.elim (fun h => .inl (Fin.ext h)) (fun h => .inr (Fin.ext h))

theorem getragen_zeuge : Getragen unit carried := by
  have checks : ∀ c : Fin unit.fns.length, carried c →
      artB (fnAt unit c) = true ∧ namenB (fnAt unit c) = true ∧
      freiB (fnAt unit c) = true ∧ oldsB unit (fnAt unit c) = true ∧
      postB unit (fnAt unit c) = true ∧ schreibtB unit (fnAt unit c) = true := by
    intro c hc
    rcases carried_indices c hc with rfl | rfl
    · decide +kernel
    · decide +kernel
  refine {
    geschlossen := ?_
    boolTab := fun t => Fin.elim0 t
    boolErg := ?_
    tab := tabB_ok (by decide +kernel)
    art := fun c hc => artB_ok (checks c hc).1
    namen := fun c hc => (of_decide_eq_true (checks c hc).2.1 :
      ((fnAt unit c).params.map (·.1)).Nodup)
    frei := fun c hc => freiB_ok (checks c hc).2.2.1
    olds := fun c hc => oldsB_ok (checks c hc).2.2.2.1
    post := fun c hc => postB_ok (checks c hc).2.2.2.2.1
    schreibt := fun c hc => schreibtB_ok (checks c hc).2.2.2.2.2
    ohneReq := ?_
    ohneGrund := ?_
    ohneInv := rfl
    ohneGlob := rfl
    ohneTransition := fun c _ => ohneTransitionB_ok (by decide +kernel) c }
  · intro c hc n hn d hd
    rcases carried_indices c hc with rfl | rfl
    · have hn' : n ∈ ([] : List String) := hn
      cases hn'
    · have hn' : n = "leaf" := List.mem_singleton.mp hn
      subst n
      match d with
      | ⟨0, _⟩ => show (0 : Nat) < 2; omega
      | ⟨1, _⟩ => show (1 : Nat) < 2; omega
      | ⟨2, _⟩ =>
        have hd' : fnSuch unit "leaf" = some openFn := hd
        have hl : fnSuch unit "leaf" = some leaf := by kernel_rfl
        rw [hl] at hd'
        have names := congrArg UFn.name (Option.some.inj hd')
        exact False.elim ((by decide : leaf.name ≠ openFn.name) names)
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

theorem leaf_meets : meetsU unit (wfU unit) leaf [] := by
  intro ρ s hW _
  exact ⟨s, rfl, hW⟩

theorem caller_meets : meetsU unit (wfU unit) caller
    [.call "leaf" [] [] (.lit (.bool true))] := by
  intro ρ s hW _
  change Gabbro.Body.Contract ρ "leaf" (preProp (wfU unit) leaf)
      (fun s s' r => (postU unit (wfU unit) leaf s s' r).getD False) →
    Gabbro.Body.Frame ρ "leaf" [] → _
  intro _ hFrame
  have hw : (ρ "leaf" ⟨s.world, fun _ => .absent⟩).1.world = s.world := by
    funext p
    exact hFrame ⟨s.world, fun _ => .absent⟩ p (by simp)
  have run : Gabbro.Body.exec ρ [.call "leaf" [] [] (.lit (.bool true))] s = .running s := by
    change Gabbro.Body.Outcome.running
      ⟨(ρ "leaf" ⟨s.world, fun _ => .absent⟩).1.world, s.local'⟩ = .running s
    rw [hw]
  refine ⟨s, ?_, ?_⟩
  · rw [run]; rfl
  · exact hW

theorem body_duties_zeuge :
    ∀ c : Fin unit.fns.length, carried c →
      ∃ body, zuBody unit (fnAt unit c) = some body ∧
        meetsU unit (wfU unit) (fnAt unit c) body := by
  intro c hc
  rcases carried_indices c hc with rfl | rfl
  · exact ⟨[], by kernel_rfl, leaf_meets⟩
  · exact ⟨[.call "leaf" [] [] (.lit (.bool true))], by kernel_rfl, caller_meets⟩

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

/-- The interface duty of the unit, from the refinement of its pointer contracts. As in the
    instance files of this package, that refinement is a premise the user discharges. -/
theorem interfaces (pointer_refinement : PtrVerfeinert program) : SchnittstellenPflicht unit := by
  intro P fs hlow
  have pair : (program, functions) = (P, fs) := by
    simpa only [Except.ok.injEq] using lowered.symm.trans hlow
  have hP : program = P := congrArg Prod.fst pair
  rw [← hP]
  exact pointer_refinement

/-- The open G body duty is explicit, not inferred from its shape or from caller duties. -/
theorem offenePflicht_zeuge (pointer_refinement : PtrVerfeinert program)
    (hBody : ∀ passes, KoerperGutS program passes (axWahr (declOf unit))
      (SperrInv.leer (declOf unit)) ⟨2, by decide⟩) : OffenePflicht unit carried := by
  intro c hc P fs hlow
  have cv : c.val = 2 := by
    have bound : c.val < 3 := c.isLt
    unfold carried at hc
    omega
  have ce : c = ⟨2, by decide⟩ := Fin.ext cv
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

/-- Joint premises, a real carried edge, an open function, and the final unit obligation.
    Only the displayed open body's G duty is left to the user. This is a lowered-unit witness. -/
theorem teilpflichten_zeuge (pointer_refinement : PtrVerfeinert program)
    (hBody : ∀ passes, KoerperGutS program passes (axWahr (declOf unit))
      (SperrInv.leer (declOf unit)) ⟨2, by decide⟩) :
    nullB unit = true ∧ Getragen unit carried ∧ rangB unit (rangAuto unit) = true ∧
    SchnittstellenPflichtTeil unit carried ∧
    (∀ c : Fin unit.fns.length, carried c → ∃ body, zuBody unit (fnAt unit c) = some body ∧
      meetsU unit (wfU unit) (fnAt unit c) body) ∧
    OffenePflicht unit carried ∧
    OffeneStartPflicht unit carried program (by decide +kernel) ∧
    "leaf" ∈ calleesOf (fnAt unit ⟨1, by decide⟩) ∧
    carried ⟨0, by decide⟩ ∧ carried ⟨1, by decide⟩ ∧ ¬ carried ⟨2, by decide⟩ ∧
    stimmigB unit = false ∧
    Zielsatz.NutzerPflicht (einheitAllg unit program (by decide +kernel)) := by
  have hPtr : SchnittstellenPflichtTeil unit carried := fun P fs hlow c _ => interfaces pointer_refinement P fs hlow c
  have hOpen := offenePflicht_zeuge pointer_refinement hBody
  exact ⟨by decide +kernel, getragen_zeuge, by decide +kernel, hPtr, body_duties_zeuge,
    hOpen, offeneStarts_zeuge, by decide +kernel, by decide, by decide, by decide,
    by decide +kernel,
    bruecke_nutzer_teil lowered getragen_zeuge (rangAuto unit) (rang_of (by decide +kernel))
      body_duties_zeuge hPtr hOpen (by decide +kernel) offeneStarts_zeuge⟩

/-- An open start with a false requirement is still refused, independently of its body duty. -/
def badUnit : UProg :=
  { unit with fns := [leaf, caller, { openFn with needs := [.fls] }], roots := ["open"] }

abbrev badCarried (c : Fin badUnit.fns.length) : Prop := c.val < 2

theorem bad_lowered_some : (lowerAllg badUnit).toOption.isSome = true := by decide +kernel

def badProgram : Programm (declOf badUnit) :=
  ((lowerAllg badUnit).toOption.get bad_lowered_some).1

theorem bad_requires : badProgram.requires ⟨2, by decide⟩ = .fls := by kernel_rfl

theorem offeneStarts_refused :
    ¬ OffeneStartPflicht badUnit badCarried badProgram (by decide +kernel) := by
  apply offeneStartPflicht_refused_teil ⟨⟨2, by decide⟩, Env.nil⟩
  · have hs : startsAllg badUnit = [⟨⟨2, by decide⟩, Env.nil⟩] := by kernel_rfl
    show (⟨⟨2, by decide⟩, Env.nil⟩ :
      Σ c : (declOf badUnit).Fn, Env (declOf badUnit) ((declOf badUnit).params c)) ∈
        startsAllg badUnit ++ []
    rw [hs]
    exact List.mem_cons_self ..
  · decide
  · intro h
    unfold ReqAmEintritt at h
    rw [bad_requires] at h
    have impossible : (false : Bool) = true := h
    exact Bool.false_ne_true impossible

end Gabbro.Bruecke.TeilZeuge
