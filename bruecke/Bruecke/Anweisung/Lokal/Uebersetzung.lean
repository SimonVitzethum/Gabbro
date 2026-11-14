module
public import Bruecke.Nachbedingung
public import Bruecke.Anweisung.Lokal.Namen
@[expose] public section

/-! # Source-scope views, including positional lookup alignment -/

namespace Gabbro.Bruecke

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg}

/-! ## 4. The view of a scope: what the Body reading sees of it -/

/-- Two scopes the Body reading cannot tell apart: the same numbers, the same pointer tables and
    the same table pointers and source lookup positions. -/
def Sicht (u : UProg) (fT fn : UFn) : Prop :=
  (∀ p, numericParam fT p = numericParam fn p) ∧ (∀ p, ptrTab u fT p = ptrTab u fn p) ∧
    (∀ t, ptrParam u fT t = ptrParam u fn t) ∧
    (∀ p, paramPos fT.params p = paramPos fn.params p) ∧
    ∀ p, valueParamTy fT p = valueParamTy fn p

theorem Sicht.refl (fn : UFn) : Sicht u fn fn := ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

theorem numericParam_mitBindung (f : UFn) (x : String) (w : Int × Int) (p : String) :
    numericParam (f.mitBindung x w) p = if x = p then true else numericParam f p := by
  by_cases h : x = p
  · subst h
    simp [numericParam, UFn.mitBindung]
  · simp [numericParam, UFn.mitBindung, h]

theorem ptrTab_mitBindung (f : UFn) (x : String) (w : Int × Int) (p : String) :
    ptrTab u (f.mitBindung x w) p = if x = p then none else ptrTab u f p := by
  by_cases h : x = p
  · subst h
    simp [ptrTab, UFn.mitBindung]
  · simp [ptrTab, UFn.mitBindung, h]

theorem ptrParam_mitBindung (f : UFn) (x : String) (w : Int × Int) (t : String) :
    ptrParam u (f.mitBindung x w) t = ptrParam u f t := by
  first
    | rfl
    | simp [ptrParam, UFn.mitBindung]

/-- Binding one name in both scopes keeps the view, whatever the two ranges. -/
theorem Sicht.bind {fT fn : UFn} (h : Sicht u fT fn) (x : String) (w w' : Int × Int) :
    Sicht u (fT.mitBindung x w) (fn.mitBindung x w') := by
  refine ⟨fun p => ?_, fun p => ?_, fun t => ?_, fun p => ?_, fun p => ?_⟩
  · rw [numericParam_mitBindung, numericParam_mitBindung, h.1 p]
  · rw [ptrTab_mitBindung, ptrTab_mitBindung, h.2.1 p]
  · rw [ptrParam_mitBindung, ptrParam_mitBindung, h.2.2.1 t]
  · change paramPos ((x, .int w.1 w.2) :: fT.params) p =
      paramPos ((x, .int w'.1 w'.2) :: fn.params) p
    unfold paramPos
    rw [h.2.2.2.1 p]
  · by_cases hp : (x == p) = true
    · simp [valueParamTy, UFn.mitBindung, hp]
    · have hp' : (x == p) = false := Bool.eq_false_iff.mpr hp
      simpa only [valueParamTy, UFn.mitBindung, List.find?_cons, hp', Bool.false_eq_true,
        ↓reduceIte] using h.2.2.2.2 p

theorem assignableParam_sicht {fT fn : UFn} (h : Sicht u fT fn) (x : String) :
    assignableParam fT x = assignableParam fn x := by
  simp only [assignableParam, h.1 x, h.2.2.2.2 x]

theorem BodyNames.lookup_sicht {fT fn : UFn} (h : Sicht u fT fn) (ns : BodyNames) (p : String) :
    ns.lookup fT p = ns.lookup fn p := by
  unfold BodyNames.lookup
  rw [h.2.2.2.1 p]

theorem slotPlace_sicht {fT fn : UFn} (h : Sicht u fT fn) (s : USide) :
    slotPlace u fT s = slotPlace u fn s := by
  cases s <;> simp [slotPlace, h.2.1]

theorem numericSideExprG_sicht {fT fn : UFn} (h : Sicht u fT fn) (sd : USide) :
    numericSideExprG u fT sd = numericSideExprG u fn sd := by
  have recurse (sd' : USide) (hlt : sizeOf sd' < sizeOf sd) :
      numericSideExprG u fT sd' = numericSideExprG u fn sd' :=
    numericSideExprG_sicht h sd'
  cases sd with
  | param p => simp only [numericSideExprG, h.1 p]
  | slot p fld i => simp only [numericSideExprG, slotPlace_sicht h]
  | add x y =>
    have hx := recurse x (by simp_wf; omega)
    have hy := recurse y (by simp_wf; omega)
    simp only [numericSideExprG, hx, hy]
  | sub x y =>
    have hx := recurse x (by simp_wf; omega)
    have hy := recurse y (by simp_wf; omega)
    simp only [numericSideExprG, hx, hy]
  | mul x y =>
    have hx := recurse x (by simp_wf; omega)
    have hy := recurse y (by simp_wf; omega)
    simp only [numericSideExprG, hx, hy]
  | conv lo hi x =>
    have hx := recurse x (by simp_wf; omega)
    simp only [numericSideExprG, hx]
  | band x y =>
    have hx := recurse x (by simp_wf; omega)
    have hy := recurse y (by simp_wf; omega)
    simp only [numericSideExprG, hx, hy]
  | bor x y =>
    have hx := recurse x (by simp_wf; omega)
    have hy := recurse y (by simp_wf; omega)
    simp only [numericSideExprG, hx, hy]
  | bxor x y =>
    have hx := recurse x (by simp_wf; omega)
    have hy := recurse y (by simp_wf; omega)
    simp only [numericSideExprG, hx, hy]
  | _ => simp [numericSideExprG, slotPlace_sicht h]
termination_by sizeOf sd
decreasing_by assumption

mutual
theorem recordRead_sicht {fT fn : UFn} (h : Sicht u fT fn) (sd : USide) :
    recordRead u fT (numericSideExprG u fT) sd = recordRead u fn (numericSideExprG u fn) sd := by
  cases sd with
  | param p => simp only [recordRead, h.2.2.2.2 p, numericSideExprG_sicht h]
  | product id order fields => simp only [recordRead, recordReads_sicht h fields]
  | field base name => simp only [recordRead, recordRead_sicht h base]
  | replace base name value =>
      simp only [recordRead, recordRead_sicht h base, recordRead_sicht h value]
  | _ => simp only [recordRead, numericSideExprG_sicht h]
termination_by 3 * sizeOf sd
decreasing_by all_goals (simp_wf <;> omega)

theorem recordReads_sicht {fT fn : UFn} (h : Sicht u fT fn) (fields : List (Ty × USide)) :
    recordReads u fT (numericSideExprG u fT) fields =
      recordReads u fn (numericSideExprG u fn) fields := by
  match fields with
  | [] => simp only [recordReads]
  | (ty, sd) :: rest => simp only [recordReads, recordRead_sicht h sd, recordReads_sicht h rest]
termination_by 3 * sizeOf fields + 1
decreasing_by all_goals (simp_wf <;> omega)
end

theorem sideExprG_sicht {fT fn : UFn} (h : Sicht u fT fn) (sd : USide) :
    sideExprG u fT sd = sideExprG u fn sd := by
  simp only [sideExprG, recordRead_sicht h]

theorem ensSide_sicht {fT fn : UFn} (h : Sicht u fT fn) (a : Acc) (sd : USide) :
    ensSide u fT a sd = ensSide u fn a sd := by
  cases sd <;> simp [ensSide, slotPlace_sicht h, numericSideExprG_sicht h]

theorem ensExpr_sicht {fT fn : UFn} (h : Sicht u fT fn) (e : UEns) (a : Acc) :
    ensExpr u fT a e = ensExpr u fn a e := by
  have recurse (e' : UEns) (hlt : sizeOf e' < sizeOf e) (a' : Acc) :
      ensExpr u fT a' e' = ensExpr u fn a' e' :=
    ensExpr_sicht h e' a'
  cases e with
  | cmp op l r =>
    simp only [ensExpr, ensSide_sicht h]
  | and x y =>
    have hx := recurse x (by simp_wf <;> omega)
    have hy := recurse y (by simp_wf <;> omega)
    simp only [ensExpr]
    rw [hx a]
    cases ensExpr u fn a x with
    | none => rfl
    | some p =>
      obtain ⟨xe, a1⟩ := p
      (try dsimp only)
      rw [hy a1]
  | or x y =>
    have hx := recurse x (by simp_wf <;> omega)
    have hy := recurse y (by simp_wf <;> omega)
    simp only [ensExpr]
    rw [hx a]
    cases ensExpr u fn a x with
    | none => rfl
    | some p =>
      obtain ⟨xe, a1⟩ := p
      (try dsimp only)
      rw [hy a1]
  | not x =>
    have hx := recurse x (by simp_wf <;> omega)
    simp only [ensExpr]
    rw [hx a]
  | _ => rfl
termination_by sizeOf e
decreasing_by assumption

theorem argExpr_sicht {fT fn : UFn} (h : Sicht u fT fn) (a : UArg) :
    argExpr u fT a = argExpr u fn a := by
  cases a <;> simp only [argExpr, rawCond, ensExpr_sicht h, h.2.2.1, sideExprG_sicht h]

theorem argsExpr_sicht {fT fn : UFn} (h : Sicht u fT fn) :
    ∀ as : List UArg, argsExpr u fT as = argsExpr u fn as
  | [] => rfl
  | a :: as => by simp only [argsExpr, argExpr_sicht h a, argsExpr_sicht h as]

theorem stmtBody_sicht {fT fn : UFn} (h : Sicht u fT fn) (s : UStmt) :
    stmtBody u fT s = stmtBody u fn s := by
  cases s <;> simp [stmtBody, h.2.1, sideExprG_sicht h, argsExpr_sicht h]


end Gabbro.Bruecke
