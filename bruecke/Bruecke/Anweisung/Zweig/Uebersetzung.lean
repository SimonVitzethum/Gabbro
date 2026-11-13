module
public import Bruecke.Anweisung.Lokal.Kopf
@[expose] public section

namespace Gabbro.Bruecke

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg}

def rawCond (u : UProg) (fn : UFn) (c : UEns) : Option Gabbro.Body.Expr :=
  match ensExpr u fn {} c with
  | some (x, a) => if a.olds.length = 0 ∧ a.result = false then some x else none
  | none => none

theorem ensSide_sicht {fT fn : UFn} (h : Sicht u fT fn) (a : Acc) (sd : USide) :
    ensSide u fT a sd = ensSide u fn a sd := by
  cases sd <;> simp [ensSide, slotPlace_sicht h, sideExprG_sicht h]

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


end Gabbro.Bruecke
