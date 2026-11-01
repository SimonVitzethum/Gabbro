module

public import Grammatik.Bausteine.Arena.ArenaDyn
public import Grammatik.Bausteine.Arena.Struktur.ArenaFrei.Teil1

@[expose] public section

namespace Gabbro.Grammatik
open Gabbro.Grammatik.ArenaDyn
variable {D : Deklaration}
section Bedeutung
variable (O : Orakel D) (passes : Nat)
variable {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
variable (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)

/-- **Taking a slot off the free list**, read off the executed form: it hands out the old head, the head becomes the
    head's link, no other link moves and the used counter stays. -/
theorem freiNimm_fakten (A : FreiForm D) (v : Expr D Γ Λ (D.typ A.tab A.feld))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwK : V.gschreibt A.kopf = true) (hLK : gdarf D A.kopf Λ)
    (voll : Endblock D V l Γ Λ) (σ : World D) (ρ : Env D Γ)
    (hne : A.kopfSt σ < D.count A.tab) :
    ∃ σ' : World D,
      execBlock (V := V) O passes R
          (Block.freiNimm (Λ' := Λ) A v hwT hLT hwK hLK voll .nil) σ ρ = .ok σ' ρ ∧
      A.kopfSt σ' = A.naechst σ (A.kopfSt σ) ∧
      (∀ j, A.naechst σ' j = A.naechst σ j) ∧ A.stand σ' = A.stand σ := by
  have hk : (0 : Int) ≤ A.kopfSt σ ∧ A.kopfSt σ ≤ D.count A.tab - 1 :=
    ⟨A.kopfSt_nonneg σ, by omega⟩
  simp only [Block.freiNimm, execBlock, eval_umTyp, orte_umTyp, eval, Expr.orte, World.globs_lese]
  rw [dif_pos (by exact hk)]
  refine ⟨_, rfl, ?_, ?_, ?_⟩
  all_goals simp only [eval, Block.freiKopfWeiter, eval_umTyp, Expr.orte, orte_umTyp, List.nil_append,
    List.cons_append, List.append_nil, FreiForm.kopfSt_schreibGlob_kopf, FreiForm.kopfSt_schreibSlot_feld,
    FreiForm.naechst_schreibGlob, FreiForm.naechst_schreibSlot_feld, FreiForm.naechst_lese, FreiForm.kopfSt_lese,
    ArenaForm.stand_lese, FreiForm.stand_schreibGlob_kopf, ArenaForm.stand_schreibSlot]
  all_goals first | trivial | (intro j; trivial) | exact umTyp_trans_n _ _ _

/-- **`alloc` from the free list keeps the list well formed and never hands out a listed slot** -- on the executed form. -/
theorem freiNimm_erhaelt (A : FreiForm D) (v : Expr D Γ Λ (D.typ A.tab A.feld))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwK : V.gschreibt A.kopf = true) (hLK : gdarf D A.kopf Λ)
    (voll : Endblock D V l Γ Λ) (σ : World D) (ρ : Env D Γ)
    (hne : A.kopfSt σ < D.count A.tab) (hok : A.FreiOk σ) :
    ∃ σ' : World D,
      execBlock (V := V) O passes R
          (Block.freiNimm (Λ' := Λ) A v hwT hLT hwK hLK voll .nil) σ ρ = .ok σ' ρ ∧
      A.FreiOk σ' ∧ ¬ A.AufListe σ' (A.kopfSt σ) := by
  obtain ⟨σ', he, h1, h2, h3⟩ := freiNimm_fakten O passes R (l := l) A v hwT hLT hwK hLK voll σ ρ hne
  exact ⟨σ', he, (A.abheben_sicher σ σ' hne hok h1 h2 h3).1, (A.abheben_sicher σ σ' hne hok h1 h2 h3).2⟩

/-- **A fresh slot from the used counter** (the list is empty or ignored): `dynAlloc`'s rest stores the payload and
    bumps the counter. The facts about the world it leaves: the head and every link stay, the counter grows by one. -/
theorem frischRumpf_fakten (A : FreiForm D) (v : Expr D Γ Λ (D.typ A.tab A.feld))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwG : V.gschreibt A.zaehl = true) (hLG : gdarf D A.zaehl Λ)
    (σ : World D) (k : Wert D (Ty.index (D.count A.tab))) (ρ : Env D Γ) :
    ∃ σ' : World D,
      execBlock (V := V) O passes R
          (Block.arenaRumpf (l := l) (Λ' := Λ) A.toArenaForm v hwT hLT hwG hLG .nil) σ (.cons k ρ)
        = .ok σ' (.cons k ρ) ∧
      A.kopfSt σ' = A.kopfSt σ ∧ (∀ j, A.naechst σ' j = A.naechst σ j) ∧ A.stand σ' = k.n + 1 := by
  refine ⟨_, rfl, ?_, ?_, ?_⟩
  all_goals simp only [eval, Block.arenaRumpf, Block.arenaBump, eval_umTyp, orte_umTyp, Expr.orte,
    List.nil_append, FreiForm.kopfSt_schreibGlob_zaehl, FreiForm.kopfSt_schreibSlot_feld,
    FreiForm.naechst_schreibGlob, FreiForm.naechst_schreibSlot_feld, FreiForm.naechst_lese,
    FreiForm.kopfSt_lese, ArenaForm.stand_lese, ArenaForm.stand_schreibGlob, Wert.umTyp_hin_her]
  all_goals first | trivial | (intro j; trivial) | exact umTyp_trans_n _ _ _ | rfl

end Bedeutung

end Gabbro.Grammatik
