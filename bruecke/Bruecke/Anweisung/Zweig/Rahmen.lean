module
public import Bruecke.Anweisung.Zweig.Schritt
public import Bruecke.Anweisung.Lokal.Rahmen
@[expose] public section

/-!
# Body frames for structured branches

`Statisch` records that every write is declared, every call keeps the caller's frame, and
both arms of every branch satisfy the same discipline. `exec_statisch` derives the frame
from that evidence. The consolidated chain constructs it along the canonical lowering.
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg}

/-! ## 1. The static frame of a Body program -/

/-- Every slot write writes a carrier of `puts`; every call keeps every place outside `puts`. -/
inductive Statisch (ρB : Gabbro.Body.Env) (puts : List String) : List Gabbro.Body.Stmt → Prop where
  | nil : Statisch ρB puts []
  | assign (cn : String) (i : Gabbro.Body.Expr) (f : String) (e : Gabbro.Body.Expr)
      (xs : List Gabbro.Body.Stmt) :
      cn ∈ puts → Statisch ρB puts xs → Statisch ρB puts (.assign cn i f e :: xs)
  | bindName (x : String) (e : Gabbro.Body.Expr) (xs : List Gabbro.Body.Stmt) :
      Statisch ρB puts xs → Statisch ρB puts (.bindName x e :: xs)
  | ret (e : Option Gabbro.Body.Expr) (xs : List Gabbro.Body.Stmt) :
      Statisch ρB puts xs → Statisch ρB puts (.ret e :: xs)
  | call (cn : String) (ps : List String) (es : List Gabbro.Body.Expr) (pre : Gabbro.Body.Expr)
      (xs : List Gabbro.Body.Stmt) :
      (∀ t p, p.carrier ∉ puts → (ρB cn t).1.world p = t.world p) →
      Statisch ρB puts xs → Statisch ρB puts (.call cn ps es pre :: xs)
  | ite (ce : Gabbro.Body.Expr) (tb te xs : List Gabbro.Body.Stmt) :
      Statisch ρB puts tb → Statisch ρB puts te → Statisch ρB puts xs →
      Statisch ρB puts (.ite ce tb te :: xs)

/-- A branch that runs, then the rest: each keeps the places outside `puts`. -/
theorem rahmen_zweig {ρB : Gabbro.Body.Env} {puts : List String} {x : Gabbro.Body.Stmt}
    {tb xs : List Gabbro.Body.Stmt} {t s' : Gabbro.Body.State}
    (hs : Gabbro.Body.step ρB x t = Gabbro.Body.exec ρB tb t)
    (hb : ∀ t s', Gabbro.Body.finalState (Gabbro.Body.exec ρB tb t) = some s' →
      ∀ p, p.carrier ∉ puts → s'.world p = t.world p)
    (hxs : ∀ t s', Gabbro.Body.finalState (Gabbro.Body.exec ρB xs t) = some s' →
      ∀ p, p.carrier ∉ puts → s'.world p = t.world p)
    (h : Gabbro.Body.finalState (Gabbro.Body.exec ρB (x :: xs) t) = some s') :
    ∀ p, p.carrier ∉ puts → s'.world p = t.world p := by
  intro p hp
  cases hx : Gabbro.Body.exec ρB tb t with
  | running t1 =>
    have h' : Gabbro.Body.finalState (Gabbro.Body.exec ρB xs t1) = some s' := by
      rw [exec_cons_running ρB x xs t t1 (hs.trans hx)] at h
      exact h
    rw [hxs t1 s' h' p hp]
    exact hb t t1 (by simp only [hx, Gabbro.Body.finalState]) p hp
  | returned t1 v =>
    have h' : Gabbro.Body.exec ρB (x :: xs) t = .returned t1 v := by
      simp only [Gabbro.Body.exec, hs, hx]
    rw [h'] at h
    exact hb t s' (by rw [hx]; exact h) p hp
  | exited t1 =>
    have h' : Gabbro.Body.exec ρB (x :: xs) t = .exited t1 := by
      simp only [Gabbro.Body.exec, hs, hx]
    rw [h'] at h
    exact hb t s' (by rw [hx]; exact h) p hp
  | left t1 =>
    have h' : Gabbro.Body.exec ρB (x :: xs) t = .left t1 := by
      simp only [Gabbro.Body.exec, hs, hx]
    rw [h'] at h
    exact hb t s' (by rw [hx]; exact h) p hp
  | stuck =>
    have h' : Gabbro.Body.exec ρB (x :: xs) t = .stuck := by
      simp only [Gabbro.Body.exec, hs, hx]
    rw [h'] at h
    simp [Gabbro.Body.finalState] at h

/-- **A static Body program keeps every place outside `puts`.** -/
theorem exec_statisch {ρB : Gabbro.Body.Env} {puts : List String} {bs : List Gabbro.Body.Stmt}
    (h : Statisch ρB puts bs) : ∀ t s',
      Gabbro.Body.finalState (Gabbro.Body.exec ρB bs t) = some s' →
      ∀ p, p.carrier ∉ puts → s'.world p = t.world p := by
  induction h with
  | nil =>
    intro t s' h p _
    simp only [Gabbro.Body.exec, Gabbro.Body.finalState, Option.some.injEq] at h
    rw [h]
  | assign cn i f e xs hcn _ ih =>
    intro t s' h p hp
    rcases step_assign ρB cn i f e t with hs | ⟨k, v, hs⟩
    · simp [Gabbro.Body.exec, hs, Gabbro.Body.finalState] at h
    · simp only [Gabbro.Body.exec, hs] at h
      rw [ih _ s' h p hp]
      apply Gabbro.Body.store_elsewhere
      intro e'
      apply hp
      rw [e']
      exact hcn
  | bindName x e xs _ ih =>
    intro t s' h p hp
    rcases step_bindName ρB x e t with hs | ⟨v, hs⟩
    · simp [Gabbro.Body.exec, hs, Gabbro.Body.finalState] at h
    · simp only [Gabbro.Body.exec, hs] at h
      exact ih _ s' h p hp
  | ret e xs _ _ =>
    intro t s' h p _
    cases e with
    | none =>
      simp only [Gabbro.Body.exec, Gabbro.Body.step, Gabbro.Body.finalState,
        Option.some.injEq] at h
      rw [h]
    | some e' =>
      simp only [Gabbro.Body.exec, Gabbro.Body.step] at h
      cases hv : Gabbro.Body.eval t e' with
      | none => simp [hv, Gabbro.Body.finalState] at h
      | some v =>
        simp only [hv, Gabbro.Body.finalState, Option.some.injEq] at h
        rw [h]
  | call cn ps es pre xs hfr _ ih =>
    intro t s' h p hp
    rcases step_call ρB cn ps es pre t with hs | ⟨t', ht', hs⟩
    · simp [Gabbro.Body.exec, hs, Gabbro.Body.finalState] at h
    · simp only [Gabbro.Body.exec, hs] at h
      rw [ih _ s' h p hp]
      show (ρB cn t').1.world p = t.world p
      rw [hfr t' p hp, ht']
  | ite ce tb te xs _ _ _ ihb ihe ihx =>
    intro t s' h
    rcases step_ite_cases ρB ce tb te t with hs | hs | hs
    · exact rahmen_zweig hs ihb ihx h
    · exact rahmen_zweig hs ihe ihx h
    · have h' : Gabbro.Body.exec ρB (.ite ce tb te :: xs) t = .stuck := by
        simp only [Gabbro.Body.exec, hs]
      rw [h'] at h
      simp [Gabbro.Body.finalState] at h

theorem statisch_rets {ρB : Gabbro.Body.Env} {puts : List String} :
    ∀ (eB : List Gabbro.Body.Stmt), (∀ x ∈ eB, ∃ e, x = .ret (some e)) → Statisch ρB puts eB
  | [], _ => .nil
  | x :: rest, hx => by
      obtain ⟨e, rfl⟩ := hx x (List.mem_cons_self ..)
      exact .ret _ _ (statisch_rets rest (fun y hy => hx y (List.mem_cons_of_mem _ hy)))

end Gabbro.Bruecke
