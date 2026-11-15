module

public import Grammatik.Nebenlaeufigkeit.Rennfreiheit.RennfreiOrte.T2a

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- The event bound for group 6, including its complete cleanup trace. -/
theorem schritt_ev_g6 {P : Programm D} {O : Orakel D} {passes : Nat} (hO : GutO O)
    {M M' : RufMaschineG D} {f : Faden} (hs : RufSchrittG6 P O passes M f M')
    {C : D.Tab ⊕ D.Glob → Bool} (hC : (M.faeden f).kopf.rest.2.2.2.2.oR P C) :
    ∃ X, (M'.faeden f).spur = X ++ (M.faeden f).spur ∧
      EvOk C (TraegerSchreibt (M.faeden f).kopf.f) X := by
  have hW : ∀ c, schreibV (vertragVon D (M.faeden f).kopf.f) c =
      TraegerSchreibt (M.faeden f).kopf.f c := schreibV_vertragVon _
  cases hs with
  | endeBindAxiomElseOk l Γ Λ τ a args he hr hw hg hd hgd err rest ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
      simp only [rufUpdateG_self]
      rw [hhead] at hC
      simp only [GRest.oR, endblockOrteP, List.all_append, Bool.and_eq_true] at hC
      subst hs₁
      have hl := gut_lese (W := fun _ => true) (G := fun _ => true) (M.weltVon f) Λ _
        (Args.orte_darf args) hΛ
      have e2 : σ₂ = (O.wirkt a (((M.weltVon f).lese Λ args.orte).fragt (.inl a))
          (evalArgs ((M.weltVon f).lese Λ args.orte) args ((M.weltVon f).lese Λ args.orte) ρ)).1 := by
        have := congrArg Prod.fst hax
        simp only [axiomAntwortSonst] at this
        exact this.symm
      obtain ⟨X, hX, hok⟩ := axiom_ev (C := C) (W := TraegerSchreibt (M.faeden f).kopf.f) O hO a
        (((M.weltVon f).lese Λ args.orte).fragt (.inl a))
        (evalArgs ((M.weltVon f).lese Λ args.orte) args ((M.weltVon f).lese Λ args.orte) ρ) hd hgd
        (hl.heldIn hΛ) (fun t ht => hw t ht) (fun g hgg => hg g hgg)
      refine ⟨X ++ ([Ereignis.fremd (.inl a)] ++ leseEv (M.weltVon f) Λ args.orte), ?_,
        evOk_append hok (evOk_append (evOk_fremd _) (evOk_lese _ _ hC.1.1))⟩
      rw [e2, hX, List.append_assoc]
      rfl
  | endeBindAxiomElseGrund l Γ Λ τ a args he hr hw hg hd hgd err rest ρ hhead σ₁ hs₁ σ₂ r hax neu hneu hΛ =>
      simp only [rufUpdateG_self]
      rw [hhead] at hC
      simp only [GRest.oR, endblockOrteP, List.all_append, Bool.and_eq_true] at hC
      subst hs₁
      have hl := gut_lese (W := fun _ => true) (G := fun _ => true) (M.weltVon f) Λ _
        (Args.orte_darf args) hΛ
      have e2 : σ₂ = (O.wirkt a (((M.weltVon f).lese Λ args.orte).fragt (.inl a))
          (evalArgs ((M.weltVon f).lese Λ args.orte) args ((M.weltVon f).lese Λ args.orte) ρ)).1 := by
        have := congrArg Prod.fst hax
        simp only [axiomAntwortSonst] at this
        exact this.symm
      obtain ⟨X, hX, hok⟩ := axiom_ev (C := C) (W := TraegerSchreibt (M.faeden f).kopf.f) O hO a
        (((M.weltVon f).lese Λ args.orte).fragt (.inl a))
        (evalArgs ((M.weltVon f).lese Λ args.orte) args ((M.weltVon f).lese Λ args.orte) ρ) hd hgd
        (hl.heldIn hΛ) (fun t ht => hw t ht) (fun g hgg => hg g hgg)
      refine ⟨X ++ ([Ereignis.fremd (.inl a)] ++ leseEv (M.weltVon f) Λ args.orte), ?_,
        evOk_append hok (evOk_append (evOk_fremd _) (evOk_lese _ _ hC.1.1))⟩
      rw [e2, hX, List.append_assoc]
      rfl

  | endeBindAxiomOptElseOk l Γ Λ e a args he hr hp hd hgd err rest ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
      simp only [rufUpdateG_self]
      rw [hhead] at hC
      simp only [GRest.oR, endblockOrteP, List.all_append, Bool.and_eq_true] at hC
      subst hs₁
      have hl := gut_lese (W := fun _ => true) (G := fun _ => true) (M.weltVon f) Λ _
        (Args.orte_darf args) hΛ
      have e2 : σ₂ = (O.wirkt a (((M.weltVon f).lese Λ args.orte).fragt (.inl a))
          (evalArgs ((M.weltVon f).lese Λ args.orte) args ((M.weltVon f).lese Λ args.orte) ρ)).1 := by
        have := congrArg Prod.fst hax
        simp only [axiomAntwortSonst] at this
        exact this.symm
      obtain ⟨X, hX, hok⟩ := axiom_ev (C := C) (W := TraegerSchreibt (M.faeden f).kopf.f) O hO a
        (((M.weltVon f).lese Λ args.orte).fragt (.inl a))
        (evalArgs ((M.weltVon f).lese Λ args.orte) args ((M.weltVon f).lese Λ args.orte) ρ) hd hgd
        (hl.heldIn hΛ) (fun t ht => hp.hw t ht) (fun g hgg => hp.hg g hgg)
      refine ⟨X ++ ([Ereignis.fremd (.inl a)] ++ leseEv (M.weltVon f) Λ args.orte), ?_,
        evOk_append hok (evOk_append (evOk_fremd _) (evOk_lese _ _ hC.1.1))⟩
      rw [e2, hX, List.append_assoc]
      rfl
  | endeBindAxiomOptElseGrund l Γ Λ e a args he hr hp hd hgd err rest ρ hhead σ₁ hs₁ σ₂ r hax neu hneu hΛ =>
      simp only [rufUpdateG_self]
      rw [hhead] at hC
      simp only [GRest.oR, endblockOrteP, List.all_append, Bool.and_eq_true] at hC
      subst hs₁
      have hl := gut_lese (W := fun _ => true) (G := fun _ => true) (M.weltVon f) Λ _
        (Args.orte_darf args) hΛ
      have e2 : σ₂ = (O.wirkt a (((M.weltVon f).lese Λ args.orte).fragt (.inl a))
          (evalArgs ((M.weltVon f).lese Λ args.orte) args ((M.weltVon f).lese Λ args.orte) ρ)).1 := by
        have := congrArg Prod.fst hax
        simp only [axiomAntwortSonst] at this
        exact this.symm
      obtain ⟨X, hX, hok⟩ := axiom_ev (C := C) (W := TraegerSchreibt (M.faeden f).kopf.f) O hO a
        (((M.weltVon f).lese Λ args.orte).fragt (.inl a))
        (evalArgs ((M.weltVon f).lese Λ args.orte) args ((M.weltVon f).lese Λ args.orte) ρ) hd hgd
        (hl.heldIn hΛ) (fun t ht => hp.hw t ht) (fun g hgg => hp.hg g hgg)
      refine ⟨X ++ ([Ereignis.fremd (.inl a)] ++ leseEv (M.weltVon f) Λ args.orte), ?_,
        evOk_append hok (evOk_append (evOk_fremd _) (evOk_lese _ _ hC.1.1))⟩
      rw [e2, hX, List.append_assoc]
      rfl

  | endeGleit | endeGleitLit | endeGleitVon | endeGleitNarrowOk | endeGleitNarrowElse => leseO

end Gabbro.Grammatik
