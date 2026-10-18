/- Part 3 of 3 of `ObjektRahmen` (split by instrumente/teile/lean-teilen.py; the umbrella `ObjektRahmen.lean` imports all parts). -/
import Grammatik.Logik.Vertraege.ObjektRahmen.T2

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- **THE FRAME AT A SEPARATED CALL.** For every program that keeps the object discipline,
    every function `f`, every depth, world and entry environment `ρ` whose call frame is
    `ObjGetrennt`, and every READ-ONLY object parameter `i` of `f` naming object `o`: every
    run of the model's call leaves every field of `o` as it was -- also when `o` lies in a
    table the call writes. -/
theorem obj_ruf_rahmen (P : Programm D) (O : Orakel D) (passes fuel : Nat) (hO : TreuO O)
    (objs : D.Fn → List (ObjPar D)) (hP : ProgObjOk objs P) (f : D.Fn)
    (σ : World D) (ρ : Env D (D.params f)) (σ' : World D)
    (h : (rufAt P O passes fuel f σ ρ).welt = some σ')
    (hG : ObjGetrennt (objs f) ρ) (i : Fin (objs f).length) (hi : ((objs f).get i).rw = false)
    {o : Obj D} (ho : objVon (objs f) ρ i = some o) :
    ∀ fld : D.Feld o.tab, σ'.slots o.tab o.nr fld = σ.slots o.tab o.nr fld := by
  intro fld
  apply rufAt_obj P O passes hO objs hP fuel f σ ρ σ' h
  rintro ⟨op, hop, hrw, htab, hk⟩
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp hop
  have hij : i ≠ j := by
    intro e; subst e; rw [hj] at hi; rw [hi] at hrw; cases hrw
  have hz : (rwVon (objs f) i || rwVon (objs f) j) = true := by
    simp only [rwVon, hj, hrw, Bool.or_true]
  have hoj : objVon (objs f) ρ j = some o := by
    simp only [objVon, ObjPar.obj, hj, hk, Option.map_some]
    exact congrArg some (Obj.ext' htab rfl)
  exact objGetrennt_paarweise hG i j hij hz ho hoj rfl

/-! ## 9. The borrow rule in the model: a re-view answers the object it was handed -/

/-- The integer of an answer, where the answer is a number. -/
def ergInt : (e : Option Ty) → ErgVal D e → Option Int
  | some τ, v => intVon τ v
  | none, _ => none

/-- The bottom position of an answer that is a bare variable. -/
def ErgExpr.varUnten? {Γ : Ctx} {Λ : List (Res D)} {e : Option Ty} : ErgExpr D Γ Λ e → Option Nat
  | .val x => x.varUnten?
  | .empty => Option.none

theorem ergVarUnten_eval {Γ : Ctx} {Λ : List (Res D)} {e : Option Ty} (x : ErgExpr D Γ Λ e) {b : Nat}
    (h : x.varUnten? = some b) (σ0 σ : World D) (ρ : Env D Γ) :
    ergInt e (evalErg σ0 x σ ρ) = ρ.unten b := by
  cases x with
  | empty => simp [ErgExpr.varUnten?] at h
  | val ex => exact varUnten_eval ex h σ0 σ ρ

/-- **A re-view keeps the object** (the borrow rule `R014` assumes, now a theorem of the
    model). For every program and every function `f` whose body is `return k;` with `k` a
    bare parameter at bottom position `b` -- the shape of a re-view at one table in the
    encoding -- every completed call answers the integer `ρ` holds at `b`: the answer names
    the SAME object as the argument. -/
theorem umsicht_behaelt (P : Programm D) (O : Orakel D) (passes n : Nat) (f : D.Fn)
    (x : ErgExpr D (D.params f) (Signatur.anfang D (D.signatur f)) (vertragVon D f).erg)
    (hΛ : (Signatur.anfang D (D.signatur f)).Perm (vertragVon D f).ende)
    (hr : P.rumpf f = .ret x hΛ) {b : Nat} (hx : x.varUnten? = some b)
    (σ : World D) (ρ : Env D (D.params f)) (σ' : World D) (v : ErgVal D (D.erg f))
    (h : rufAt P O passes (n + 1) f σ ρ = .ok σ' v) : ergInt (D.erg f) v = ρ.unten b := by
  simp only [rufAt] at h
  rw [hr] at h
  simp only [execEnd] at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · cases h
        exact ergVarUnten_eval x hx _ _ ρ

#print axioms Gabbro.Grammatik.stmt_obj
#print axioms Gabbro.Grammatik.block_obj
#print axioms Gabbro.Grammatik.end_obj
#print axioms Gabbro.Grammatik.rufAt_obj
#print axioms Gabbro.Grammatik.obj_ruf_rahmen
#print axioms Gabbro.Grammatik.umsicht_behaelt

#print axioms Gabbro.Grammatik.evalArgs_unten
#print axioms Gabbro.Grammatik.traverseLauf_obj


end Gabbro.Grammatik
