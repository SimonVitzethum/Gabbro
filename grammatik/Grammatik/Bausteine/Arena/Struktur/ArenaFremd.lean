/-
  File:      Grammatik/ArenaFremd.lean
  Subject:   WHAT THE ALLOCATOR TOUCHES (PLAN-DYNAMIC.md section 8a, phase 2): the three executed forms of
             `ArenaFrei.lean` -- `free` (`freiRumpf`), `alloc` from the list (`freiNimm`), `alloc` from the counter
             (`arenaRumpf`) -- write only the counter, the head of the free list, the payload and the free-list
             link of the arena. Every other global and every other field of the table stays word for word.
             A link structure in its own fields is therefore untouched by every allocator move.
-/
import Grammatik.Bausteine.Arena.Struktur.ArenaLebt

namespace Gabbro.Grammatik

open Gabbro.Grammatik.ArenaDyn

variable {D : Deklaration}

namespace FreiForm

/-- `σ'` differs from `σ` at most in the counter, the head of the free list, the committed word, the payload and the
    free link. (The three allocator blocks do not write the committed word; `grow` writes nothing else, so the same
    frame serves the composition of `grow` with every move.) -/
def Fremd (A : FreiForm D) (σ σ' : World D) : Prop :=
  (∀ g, g ≠ A.zaehl → g ≠ A.kopf → g ≠ A.komm → σ'.globs g = σ.globs g) ∧
  (∀ k (f : D.Feld A.tab), f ≠ A.feld → f ≠ A.nxt → σ'.slots A.tab k f = σ.slots A.tab k f)

end FreiForm

section Rahmen
variable (O : Orakel D) (passes : Nat)
variable {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
variable (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)

theorem freiRumpf_fremd (A : FreiForm D)
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwK : V.gschreibt A.kopf = true) (hLK : gdarf D A.kopf Λ)
    (σ : World D) (k : Wert D (Ty.index (D.count A.tab))) (ρ : Env D Γ) :
    ∃ σ' : World D,
      execBlock (V := V) O passes R
          (Block.freiRumpf (l := l) (Λ' := Λ) A hwT hLT hwK hLK (.nil)) σ (.cons k ρ)
        = .ok σ' (.cons k ρ) ∧ A.Fremd σ σ' := by
  refine ⟨_, rfl, ?_, ?_⟩
  · intro g _ hk _
    simp [eval, hk]
  · intro k' f hf hn
    simp [eval, World.slots_schreibSlot_ne, hn]

theorem freiNimm_fremd (A : FreiForm D) (v : Expr D Γ Λ (D.typ A.tab A.feld))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwK : V.gschreibt A.kopf = true) (hLK : gdarf D A.kopf Λ)
    (voll : Endblock D V l Γ Λ) (σ : World D) (ρ : Env D Γ)
    (hne : A.kopfSt σ < D.count A.tab) :
    ∃ σ' : World D,
      execBlock (V := V) O passes R
          (Block.freiNimm (Λ' := Λ) A v hwT hLT hwK hLK voll .nil) σ ρ = .ok σ' ρ ∧ A.Fremd σ σ' := by
  have hk : (0 : Int) ≤ A.kopfSt σ ∧ A.kopfSt σ ≤ D.count A.tab - 1 :=
    ⟨A.kopfSt_nonneg σ, by omega⟩
  simp only [Block.freiNimm, execBlock, eval_umTyp, orte_umTyp, eval, Expr.orte, World.globs_lese]
  rw [dif_pos (by exact hk)]
  refine ⟨_, rfl, ?_, ?_⟩
  · intro g _ hk _
    simp [eval, hk]
  · intro k' f hf hn
    simp [eval, World.slots_schreibSlot_ne, hf]

theorem frischRumpf_fremd (A : FreiForm D) (v : Expr D Γ Λ (D.typ A.tab A.feld))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwG : V.gschreibt A.zaehl = true) (hLG : gdarf D A.zaehl Λ)
    (σ : World D) (k : Wert D (Ty.index (D.count A.tab))) (ρ : Env D Γ) :
    ∃ σ' : World D,
      execBlock (V := V) O passes R
          (Block.arenaRumpf (l := l) (Λ' := Λ) A.toArenaForm v hwT hLT hwG hLG .nil) σ (.cons k ρ)
        = .ok σ' (.cons k ρ) ∧ A.Fremd σ σ' := by
  refine ⟨_, rfl, ?_, ?_⟩
  · intro g hz _ _
    simp [eval, Block.arenaBump, hz]
  · intro k' f hf hn
    simp [eval, Block.arenaBump, World.slots_schreibSlot_ne, hf]

/-! The three allocator moves, with everything a link structure needs from them at once: the executed form, the
    frame (`Fremd`), the free list, and the liveness of the slots. -/

/-- `alloc` from the used counter. -/
theorem frisch_lebt (A : FreiForm D) (v : Expr D Γ Λ (D.typ A.tab A.feld))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwG : V.gschreibt A.zaehl = true) (hLG : gdarf D A.zaehl Λ)
    (σ : World D) (k : Wert D (Ty.index (D.count A.tab))) (ρ : Env D Γ)
    (hkn : k.n = A.stand σ) (hok : A.FreiOk σ) :
    ∃ σ' : World D,
      execBlock (V := V) O passes R
          (Block.arenaRumpf (l := l) (Λ' := Λ) A.toArenaForm v hwT hLT hwG hLG .nil) σ (.cons k ρ)
        = .ok σ' (.cons k ρ) ∧ A.Fremd σ σ' ∧
      A.FreiOk σ' ∧ (∀ j, A.Lebt σ j → A.Lebt σ' j) ∧ A.Lebt σ' k.n := by
  obtain ⟨σ', he, h1, h2, h3⟩ := frischRumpf_fakten O passes R (l := l) A v hwT hLT hwG hLG σ k ρ
  obtain ⟨σ'', he2, hf⟩ := frischRumpf_fremd O passes R (l := l) A v hwT hLT hwG hLG σ k ρ
  rw [he] at he2; cases he2
  obtain ⟨hok', hmono, hnew⟩ := A.lebt_bump hok h1 h2 (by rw [h3, hkn])
  exact ⟨σ', he, hf, hok', hmono, by rw [hkn]; exact hnew⟩

/-- `alloc` from the free list. -/
theorem nimm_lebt (A : FreiForm D) (v : Expr D Γ Λ (D.typ A.tab A.feld))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwK : V.gschreibt A.kopf = true) (hLK : gdarf D A.kopf Λ)
    (voll : Endblock D V l Γ Λ) (σ : World D) (ρ : Env D Γ)
    (hne : A.kopfSt σ < D.count A.tab) (hok : A.FreiOk σ) :
    ∃ σ' : World D,
      execBlock (V := V) O passes R
          (Block.freiNimm (Λ' := Λ) A v hwT hLT hwK hLK voll .nil) σ ρ = .ok σ' ρ ∧ A.Fremd σ σ' ∧
      A.FreiOk σ' ∧ (∀ j, A.Lebt σ j → A.Lebt σ' j) ∧ A.Lebt σ' (A.kopfSt σ) ∧
      A.AufListe σ (A.kopfSt σ) := by
  obtain ⟨σ', he, h1, h2, h3⟩ := freiNimm_fakten O passes R (l := l) A v hwT hLT hwK hLK voll σ ρ hne
  obtain ⟨σ'', he2, hf⟩ := freiNimm_fremd O passes R (l := l) A v hwT hLT hwK hLK voll σ ρ hne
  rw [he] at he2; cases he2
  obtain ⟨hok', hmono, hnew⟩ := A.lebt_abheb hne hok h1 h2 h3
  refine ⟨σ', he, hf, hok', hmono, hnew, ?_⟩
  obtain ⟨L0, hk0, _, _⟩ := hok
  generalize hg : A.kopfSt σ = kk at hk0 hne ⊢
  cases hk0 with
  | nil => exact absurd hne (Int.lt_irrefl _)
  | cons k h0 hk1 L1 h1 =>
    refine ⟨kk :: L1, ?_, List.mem_cons_self⟩
    rw [hg]; exact FreiForm.Kette.cons kk h0 hk1 L1 h1

/-- `free` of a live slot. -/
theorem frei_lebt (A : FreiForm D)
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwK : V.gschreibt A.kopf = true) (hLK : gdarf D A.kopf Λ)
    (σ : World D) (k : Wert D (Ty.index (D.count A.tab))) (ρ : Env D Γ)
    (hlebt : A.Lebt σ k.n) (hok : A.FreiOk σ) :
    ∃ σ' : World D,
      execBlock (V := V) O passes R
          (Block.freiRumpf (l := l) (Λ' := Λ) A hwT hLT hwK hLK (.nil)) σ (.cons k ρ)
        = .ok σ' (.cons k ρ) ∧ A.Fremd σ σ' ∧
      A.FreiOk σ' ∧ (∀ j, A.Lebt σ j → j ≠ k.n → A.Lebt σ' j) ∧ ¬ A.Lebt σ' k.n := by
  obtain ⟨σ', he, h1, h2, h3, h4⟩ := freiRumpf_fakten O passes R (l := l) A hwT hLT hwK hLK σ k ρ
  obtain ⟨σ'', he2, hf⟩ := freiRumpf_fremd O passes R (l := l) A hwT hLT hwK hLK σ k ρ
  rw [he] at he2; cases he2
  obtain ⟨hok', hmono, hdead⟩ := A.lebt_frei k.n hlebt hok h1 h2 h3 h4
  exact ⟨σ', he, hf, hok', hmono, hdead⟩

end Rahmen

end Gabbro.Grammatik
