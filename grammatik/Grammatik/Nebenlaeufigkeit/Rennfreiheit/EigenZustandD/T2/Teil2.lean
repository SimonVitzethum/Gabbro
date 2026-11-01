module

public import Grammatik.Nebenlaeufigkeit.Rennfreiheit.EigenZustandD.T1
public import Grammatik.Nebenlaeufigkeit.Rennfreiheit.EigenZustandD.T2.Teil1

@[expose] public section

namespace Gabbro.Grammatik.EZD
open Gabbro.Grammatik
variable {D : Deklaration}

theorem advances_slots_fest (O : Orakel D) (passes : Nat)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {mm : D.Marke} {a : Nat} {h : Res.marke mm a ∈ Λ} {hs : a + 1 < D.stufen mm}
    (s : Stmt D V l Γ Λ ((Λ.erase (.marke mm a)) ++ [.marke mm (a + 1)]))
    (hs : s = Stmt.advances (V := V) (l := l) mm a h hs)
    (sg : World D) (rho : Env D Γ) (sg' : World D)
    (hstep : (execStmt O passes keinRuf s sg rho).welt = some sg')
    (t : D.Tab) (k : Int) (f : D.Feld t) :
    sg'.slots t k f = sg.slots t k f := by
  subst hs
  simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
  subst hstep
  rfl

/-- `retires` keeps every table slot (mark step, memory-free). -/
theorem retires_slots_fest (O : Orakel D) (passes : Nat)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {mm : D.Marke} {s2 : Nat} {h : Res.marke mm s2 ∈ Λ} {a : D.Annahme}
    (s : Stmt D V l Γ Λ (Λ.erase (.marke mm s2)))
    (hs : s = Stmt.retires (V := V) (l := l) mm s2 h a)
    (sg : World D) (rho : Env D Γ) (sg' : World D)
    (hstep : (execStmt O passes keinRuf s sg rho).welt = some sg')
    (t : D.Tab) (k : Int) (f : D.Feld t) :
    sg'.slots t k f = sg.slots t k f := by
  subst hs
  simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
  subst hstep
  rfl

/-- `retGrund` keeps every table slot (control step, memory-free). -/
theorem retGrund_slots_fest (O : Orakel D) (passes : Nat)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {r : Fin V.gruende} {hΛ : Λ.Perm V.ende}
    (s : Stmt D V l Γ Λ Λ)
    (hs : s = Stmt.retWhy (V := V) (l := l) r hΛ)
    (sg : World D) (rho : Env D Γ) (sg' : World D)
    (hstep : (execStmt O passes keinRuf s sg rho).welt = some sg')
    (t : D.Tab) (k : Int) (f : D.Feld t) :
    sg'.slots t k f = sg.slots t k f := by
  subst hs
  simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
  subst hstep
  rfl

/-- `leave` keeps every table slot (control step, memory-free). -/
theorem leave_slots_fest (O : Orakel D) (passes : Nat)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {h : l = true}
    (s : Stmt D V l Γ Λ Λ)
    (hs : s = Stmt.leave (V := V) (l := l) h)
    (sg : World D) (rho : Env D Γ) (sg' : World D)
    (hstep : (execStmt O passes keinRuf s sg rho).welt = some sg')
    (t : D.Tab) (k : Int) (f : D.Feld t) :
    sg'.slots t k f = sg.slots t k f := by
  subst hs
  simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
  subst hstep
  rfl


end Gabbro.Grammatik.EZD
