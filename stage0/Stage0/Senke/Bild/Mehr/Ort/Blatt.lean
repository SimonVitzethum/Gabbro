/-
  File:      stage0/Stage0/Senke/Bild/Mehr/Ort/Blatt.lean
  Subject:   The memory statements run alike on worlds that agree on their carriers (multi-thread image theorem,
             package MT2: the G frame lemma at the statement level). `OrtPrem C s`: `s` is one of the eight memory
             statements -- a write to a table (`assignSlot`, `assignThru`, `assignThruOwn`, `assignSlotRef`), to a
             global (`assignGlob`), of bytes (`putBytes`), to a local (`assignVar`), a state shift (`shift`) -- and
             every place it reads lies in `C`. These are the statements of a segment between two synchronisation
             points that touch memory; locks, atomics, calls, register and outside accesses end a segment and are
             not here. `ort_stmt`: from two worlds that agree on `C` (`OrtGleich`), such a statement has the same
             outcome -- the same environment, worlds that agree on `C` again, or the same logic failure -- whatever
             the worlds hold outside `C`. The write lands in BOTH worlds, so carriers outside `C` that it writes
             agree afterwards too; carriers it neither reads nor writes keep each world's own value.
-/
module
public import Stage0.Senke.Bild.Mehr.Ort.Ort
public import Grammatik.Kern.Semantik.Semantik.T2.Teil2
@[expose] public section

namespace Gabbro.Stage0.Senke.BildMehr

open Gabbro.Grammatik

variable {D : Deklaration} {V : Vertrag D}

/-- **A memory statement whose places lie in `C`**; every other statement: `False`. -/
def OrtPrem (C : D.Tab ⊕ D.Glob → Prop) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    Stmt D V l Γ Λ Λ' → Prop
  | .assignSlot t _ i e _ _ => C (.inl t) ∧ ∀ o ∈ i.orte ++ e.orte, C o
  | .assignThru p t _ _ i e _ _ => C (.inl t) ∧ ∀ o ∈ p.orte ++ i.orte ++ e.orte, C o
  | .assignThruOwn p t _ _ i e _ _ _ _ _ _ _ => C (.inl t) ∧ ∀ o ∈ p.orte ++ i.orte ++ e.orte, C o
  | .assignSlotRef r t _ _ _ e _ _ => C (.inl t) ∧ ∀ o ∈ r.orte ++ e.orte, C o
  | .assignGlob g e _ _ => C (.inr g) ∧ ∀ o ∈ e.orte, C o
  | .putBytes t _ _ _ i _ _ e _ _ => C (.inl t) ∧ ∀ o ∈ i.orte ++ e.orte, C o
  | .assignVar _ e => ∀ o ∈ e.orte, C o
  | .shift t _ _ i _ _ _ _ _ _ => ∀ o ∈ (.inl t :: i.orte : List (D.Tab ⊕ D.Glob)), C o
  | _ => False

/-- Two outcomes of a memory statement: `ok` with the same environment and worlds that agree on `C`, or the same
    logic failure. -/
inductive AusOrt (C : D.Tab ⊕ D.Glob → Prop) {l : Bool} {Γ : Ctx} : Ausgang V l Γ → Ausgang V l Γ → Prop
  | ok {σ σ' : World D} {ρ : Env D Γ} : OrtGleich C σ σ' → AusOrt C (.ok σ ρ) (.ok σ' ρ)
  | logik (e : Logik D) : AusOrt C (.logik e) (.logik e)

theorem AusOrt.ite {C : D.Tab ⊕ D.Glob → Prop} {l : Bool} {Γ : Ctx} {c : Prop} [Decidable c]
    {a₁ a₂ b₁ b₂ : Ausgang V l Γ} (ha : AusOrt C a₁ a₂) (hb : AusOrt C b₁ b₂) :
    AusOrt C (if c then a₁ else b₁) (if c then a₂ else b₂) := by
  by_cases hc : c
  · rw [if_pos hc, if_pos hc]
    exact ha
  · rw [if_neg hc, if_neg hc]
    exact hb

/-- From `ok` on the first side: `ok` on the second, with the same environment and worlds that agree on `C`. -/
theorem AusOrt.ok_inv {C : D.Tab ⊕ D.Glob → Prop} {l : Bool} {Γ : Ctx} {o₁ o₂ : Ausgang V l Γ}
    (h : AusOrt C o₁ o₂) {σ1 : World D} {ρ1 : Env D Γ} (e : o₁ = .ok σ1 ρ1) :
    ∃ σ1', o₂ = .ok σ1' ρ1 ∧ OrtGleich C σ1 σ1' := by
  cases h with
  | ok hσ =>
    cases e
    exact ⟨_, rfl, hσ⟩
  | logik _ => cases e

/-- **THE G FRAME LEMMA, one memory statement.** -/
theorem ort_stmt (O : Orakel D) (passes : Nat) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    {C : D.Tab ⊕ D.Glob → Prop} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    ∀ (s : Stmt D V l Γ Λ Λ'), OrtPrem C s → ∀ {σ σ' : World D} (ρ : Env D Γ), OrtGleich C σ σ' →
      AusOrt C (execStmt O passes R s σ ρ) (execStmt O passes R s σ' ρ)
  | .assignSlot _ _ i e _ _, hC => by
      have hC' : ∀ o ∈ i.orte ++ e.orte, C o := (show _ ∧ _ from hC).2
      intro ρ hσ
      have h' := hσ.lese Λ (i.orte ++ e.orte)
      simp only [execStmt]
      rw [h'.wert i (fun o ho => hC' o (by simp [ho])) ρ, h'.wert e (fun o ho => hC' o (by simp [ho])) ρ]
      exact .ok (h'.schreibSlot _ _ _ _ _)
  | .assignThru p _ _ _ i e _ _, hC => by
      have hC' : ∀ o ∈ p.orte ++ i.orte ++ e.orte, C o := (show _ ∧ _ from hC).2
      intro ρ hσ
      have h' := hσ.lese Λ (p.orte ++ i.orte ++ e.orte)
      simp only [execStmt]
      rw [h'.wert i (fun o ho => hC' o (by simp [ho])) ρ, h'.wert e (fun o ho => hC' o (by simp [ho])) ρ]
      exact .ok (h'.schreibSlot _ _ _ _ _)
  | .assignThruOwn p _ _ _ i e _ _ _ _ _ _ _, hC => by
      have hC' : ∀ o ∈ p.orte ++ i.orte ++ e.orte, C o := (show _ ∧ _ from hC).2
      intro ρ hσ
      have h' := hσ.lese Λ (p.orte ++ i.orte ++ e.orte)
      simp only [execStmt]
      rw [h'.wert i (fun o ho => hC' o (by simp [ho])) ρ, h'.wert e (fun o ho => hC' o (by simp [ho])) ρ]
      exact .ok (h'.schreibSlot _ _ _ _ _)
  | .assignSlotRef r _ _ _ _ e _ _, hC => by
      have hC' : ∀ o ∈ r.orte ++ e.orte, C o := (show _ ∧ _ from hC).2
      intro ρ hσ
      have h' := hσ.lese Λ (r.orte ++ e.orte)
      simp only [execStmt]
      rw [h'.wert r (fun o ho => hC' o (by simp [ho])) ρ, h'.wert e (fun o ho => hC' o (by simp [ho])) ρ]
      exact .ok (h'.schreibSlot _ _ _ _ _)
  | .assignGlob _ e _ _, hC => by
      have hC' : ∀ o ∈ e.orte, C o := (show _ ∧ _ from hC).2
      intro ρ hσ
      have h' := hσ.lese Λ e.orte
      simp only [execStmt]
      rw [h'.wert e hC' ρ]
      exact .ok (h'.schreibGlob _ _ _)
  | .putBytes t f hf _ i _ _ e _ _, hC => by
      have hC' : ∀ o ∈ i.orte ++ e.orte, C o := (show _ ∧ _ from hC).2
      intro ρ hσ
      have h' := hσ.lese Λ (i.orte ++ e.orte)
      simp only [execStmt]
      rw [h'.wert i (fun o ho => hC' o (by simp [ho])) ρ, h'.wert e (fun o ho => hC' o (by simp [ho])) ρ]
      exact .ok (OrtGleich.schreibBytes t f hf Λ _ _ h')
  | .assignVar _ e, hC => by
      have hC' : ∀ o ∈ e.orte, C o := hC
      intro ρ hσ
      have h' := hσ.lese Λ e.orte
      simp only [execStmt]
      rw [h'.wert e hC' ρ]
      exact .ok h'
  | .shift t _ _ i _ _ _ _ _ _, hC => by
      have hC' : ∀ o ∈ (.inl t :: i.orte : List (D.Tab ⊕ D.Glob)), C o := hC
      intro ρ hσ
      have h' := hσ.lese Λ (.inl t :: i.orte)
      simp only [execStmt]
      rw [h'.wert i (fun o ho => hC' o (by simp [ho])) ρ, h'.slots t (hC' _ (by simp))]
      exact AusOrt.ite (.ok (h'.schreibSlot _ _ _ _ _)) (.logik _)
  | .ite .., h => False.elim h
  | .onOption .., h => False.elim h
  | .onTag .., h => False.elim h
  | .onWhy .., h => False.elim h
  | .call .., h => False.elim h
  | .callInd .., h => False.elim h
  | .locks .., h => False.elim h
  | .breaking .., h => False.elim h
  | .traverse .., h => False.elim h
  | .retry .., h => False.elim h
  | .forever .., h => False.elim h
  | .axiomCall .., h => False.elim h
  | .regWrite .., h => False.elim h
  | .transition .., h => False.elim h
  | .publish .., h => False.elim h
  | .advances .., h => False.elim h
  | .retires .., h => False.elim h
  | .ret .., h => False.elim h
  | .retWhy .., h => False.elim h
  | .leave .., h => False.elim h
  | .next .., h => False.elim h
  | .consumeTraverse .., h => False.elim h
  | .retScoped .., h => False.elim h
  | .retWhyScoped .., h => False.elim h
  | .axiomCallElse .., h => False.elim h
  | .callIndElse .., h => False.elim h

/-- **The frame lemma, normal end**: when the statement ends normally from the first world, it ends normally from the
    second, with the same environment and worlds that agree on `C`. -/
theorem ort_stmt_ok (O : Orakel D) (passes : Nat) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    {C : D.Tab ⊕ D.Glob → Prop} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {s : Stmt D V l Γ Λ Λ'}
    (hC : OrtPrem C s) {σ σ' σ1 : World D} {ρ ρ1 : Env D Γ} (hσ : OrtGleich C σ σ')
    (hex : execStmt O passes R s σ ρ = .ok σ1 ρ1) :
    ∃ σ1', execStmt O passes R s σ' ρ = .ok σ1' ρ1 ∧ OrtGleich C σ1 σ1' :=
  (ort_stmt O passes R s hC ρ hσ).ok_inv hex

end Gabbro.Stage0.Senke.BildMehr
