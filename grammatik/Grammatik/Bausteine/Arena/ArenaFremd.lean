/-
  File:      Grammatik/ArenaFremd.lean
  Subject:   WHAT THE ALLOCATOR TOUCHES (PLAN-DYNAMISCH.md section 8a, phase 2): the three executed forms of
             `ArenaFrei.lean` -- `free` (`freiRumpf`), `alloc` from the list (`freiNimm`), `alloc` from the counter
             (`arenaRumpf`) -- write only the counter, the head of the free list, the payload and the free-list
             link of the arena. Every other global and every other field of the table stays word for word.
             A link structure in its own fields is therefore untouched by every allocator move.
-/
import Grammatik.Bausteine.Arena.ArenaLebt

namespace Gabbro.Grammatik

open Gabbro.Grammatik.ArenaDyn

variable {D : Deklaration}

namespace FreiForm

/-- `σ'` differs from `σ` at most in the counter, the head of the free list, the payload and the free link. -/
def Fremd (A : FreiForm D) (σ σ' : World D) : Prop :=
  (∀ g, g ≠ A.zaehl → g ≠ A.kopf → σ'.globs g = σ.globs g) ∧
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
  · intro g _ hk
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
  · intro g _ hk
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
  · intro g hz _
    simp [eval, Block.arenaBump, hz]
  · intro k' f hf hn
    simp [eval, Block.arenaBump, World.slots_schreibSlot_ne, hf]

end Rahmen

end Gabbro.Grammatik
