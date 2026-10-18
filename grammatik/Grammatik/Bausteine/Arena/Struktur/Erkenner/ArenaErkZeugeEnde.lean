/-
  File:      Grammatik/ArenaErkZeugeEnde.lean
  Subject:   THE RECOGNIZER ON A FUNCTION BODY, RUN (PLAN-DYNAMISCH.md section 8a.3): `ErkE` accepts an END block, the shape of
             `Programm.rumpf`. `kombiEnde` is `if true { kombiHang }; return`: the block form of `ArenaErkZeugeKombi.lean` enters the
             function body through a branch (`ErkE.ite`), the body ends in `return`. Run on the real world `wk` it returns in a world
             that meets the arena invariant, with the slot hung into the tree.
-/
import Grammatik.Bausteine.Arena.Struktur.Erkenner.ArenaErkZeugeKombi
import Grammatik.Bausteine.Arena.Struktur.Erkenner.ArenaErkEnde

namespace Gabbro.Grammatik

open Gabbro.Grammatik.ArenaDyn Gabbro.Grammatik.ArenaKette

namespace ErkKombi

/-- A function body: the block `kombiHang`, then `return`. -/
def kombiEnde : Endblock FD2 FV2 false [] [] :=
  Endblock.cons (Stmt.ite Expr.tru kombiHang Block.nil) (Endblock.ret ErgExpr.empty (List.Perm.refl _))

/-- **The recognizer accepts the function body** -- from a state that knows nothing. -/
theorem erkE_kombiEnde : ErkE K2 Abs.leer kombiEnde := by
  obtain ⟨a', h⟩ := erk_kombiHang
  exact ErkE.ite (K := K2) (V := FV2) (l := false) (Γ := []) (Λ := []) (Λ1 := []) (a := Abs.leer) (a1 := a')
    (a2 := Abs.leer) (a3 := Abs.leer) Expr.tru kombiHang Block.nil
    (Endblock.ret ErgExpr.empty (List.Perm.refl _)) h (Erk.nil _) (fun _ => Or.inr rfl) (fun _ => Or.inl rfl)
    (ErkE.ret _ _)

def kombiEndeOk : Bool :=
  match execEnd (V := FV2) oF2 0 rF2 kombiEnde wk .nil with
  | .zurueck σ' _ => decide (Lf2.wert σ' 0 = 1 ∧ Rf2.wert σ' 0 = 3 ∧ LG2.st σ' = 2 ∧ FA2.kopfSt σ' = 4)
  | _ => false

theorem kombiEndeOk_wahr : kombiEndeOk = true := by decide +kernel

/-- **Run on the real world:** the function body returns, in a world where the arena invariant holds, with the slot `1` hung
    as the left child of the root `0` -- as the recognizer promised. -/
theorem kombiEnde_zeuge : ∃ σ' : World FD2, execEnd (V := FV2) oF2 0 rF2 kombiEnde wk .nil = .zurueck σ' () ∧
    K2.Ok σ' ∧ Lf2.wert σ' 0 = 1 ∧ Rf2.wert σ' 0 = 3 ∧ LG2.st σ' = 2 ∧ FA2.kopfSt σ' = 4 := by
  have hd := kombiEndeOk_wahr
  unfold kombiEndeOk at hd
  revert hd
  generalize hx : execEnd (V := FV2) oF2 0 rF2 kombiEnde wk .nil = o
  have hpost := erkE_koerper oF2 0 rF2 K2 erkE_kombiEnde wk .nil ok_wk Abs.leer
  rw [hx] at hpost
  cases o with
  | zurueck σ' v =>
    intro hd
    have hv : v = () := rfl
    subst hv
    simp only [decide_eq_true_eq] at hd
    exact ⟨σ', rfl, hpost, hd⟩
  | why _ _ => intro hd; exact absurd hd (by simp)
  | leave _ _ _ => intro hd; exact absurd hd (by simp)
  | next _ _ _ => intro hd; exact absurd hd (by simp)
  | logik _ => intro hd; exact absurd hd (by simp)
  | hardware _ => intro hd; exact absurd hd (by simp)

end ErkKombi

end Gabbro.Grammatik

#print axioms Gabbro.Grammatik.erkE_erhaelt
#print axioms Gabbro.Grammatik.erkE_koerper
#print axioms Gabbro.Grammatik.ErkKombi.erkE_kombiEnde
#print axioms Gabbro.Grammatik.ErkKombi.kombiEnde_zeuge
