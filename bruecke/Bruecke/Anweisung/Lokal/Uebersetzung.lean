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
    ∀ p, paramPos fT.params p = paramPos fn.params p

theorem Sicht.refl (fn : UFn) : Sicht u fn fn := ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

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
  refine ⟨fun p => ?_, fun p => ?_, fun t => ?_, fun p => ?_⟩
  · rw [numericParam_mitBindung, numericParam_mitBindung, h.1 p]
  · rw [ptrTab_mitBindung, ptrTab_mitBindung, h.2.1 p]
  · rw [ptrParam_mitBindung, ptrParam_mitBindung, h.2.2.1 t]
  · change paramPos ((x, .int w.1 w.2) :: fT.params) p =
      paramPos ((x, .int w'.1 w'.2) :: fn.params) p
    unfold paramPos
    rw [h.2.2.2 p]

theorem BodyNames.lookup_sicht {fT fn : UFn} (h : Sicht u fT fn) (ns : BodyNames) (p : String) :
    ns.lookup fT p = ns.lookup fn p := by
  unfold BodyNames.lookup
  rw [h.2.2.2 p]

theorem slotPlace_sicht {fT fn : UFn} (h : Sicht u fT fn) (s : USide) :
    slotPlace u fT s = slotPlace u fn s := by
  cases s <;> simp [slotPlace, h.2.1]

theorem sideExprG_sicht {fT fn : UFn} (h : Sicht u fT fn) (sd : USide) :
    sideExprG u fT sd = sideExprG u fn sd := by
  have recurse (sd' : USide) (hlt : sizeOf sd' < sizeOf sd) :
      sideExprG u fT sd' = sideExprG u fn sd' :=
    sideExprG_sicht h sd'
  cases sd with
  | param p => simp only [sideExprG, h.1 p]
  | slot p fld i => simp only [sideExprG, slotPlace_sicht h]
  | add x y =>
    have hx := recurse x (by simp_wf; omega)
    have hy := recurse y (by simp_wf; omega)
    simp only [sideExprG, hx, hy]
  | sub x y =>
    have hx := recurse x (by simp_wf; omega)
    have hy := recurse y (by simp_wf; omega)
    simp only [sideExprG, hx, hy]
  | mul x y =>
    have hx := recurse x (by simp_wf; omega)
    have hy := recurse y (by simp_wf; omega)
    simp only [sideExprG, hx, hy]
  | conv lo hi x =>
    have hx := recurse x (by simp_wf; omega)
    simp only [sideExprG, hx]
  | band x y =>
    have hx := recurse x (by simp_wf; omega)
    have hy := recurse y (by simp_wf; omega)
    simp only [sideExprG, hx, hy]
  | bor x y =>
    have hx := recurse x (by simp_wf; omega)
    have hy := recurse y (by simp_wf; omega)
    simp only [sideExprG, hx, hy]
  | bxor x y =>
    have hx := recurse x (by simp_wf; omega)
    have hy := recurse y (by simp_wf; omega)
    simp only [sideExprG, hx, hy]
  | _ => simp [sideExprG, slotPlace_sicht h]
termination_by sizeOf sd
decreasing_by assumption

theorem argExpr_sicht {fT fn : UFn} (h : Sicht u fT fn) (a : UArg) :
    argExpr u fT a = argExpr u fn a := by
  cases a <;> simp only [argExpr, h.2.2.1, sideExprG_sicht h]

theorem argsExpr_sicht {fT fn : UFn} (h : Sicht u fT fn) :
    ∀ as : List UArg, argsExpr u fT as = argsExpr u fn as
  | [] => rfl
  | a :: as => by simp only [argsExpr, argExpr_sicht h a, argsExpr_sicht h as]

theorem stmtBody_sicht {fT fn : UFn} (h : Sicht u fT fn) (s : UStmt) :
    stmtBody u fT s = stmtBody u fn s := by
  cases s <;> simp [stmtBody, h.2.1, sideExprG_sicht h, argsExpr_sicht h]

end Gabbro.Bruecke
