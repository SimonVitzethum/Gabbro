module

public import Grammatik.Nebenlaeufigkeit.Rennfreiheit.RennfreiG
public import Grammatik.Nebenlaeufigkeit.Rennfreiheit.RennfreiVoll.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}
section Delta
variable {P : Programm D} {O : Orakel D} {passes : Nat}

/-- **The trace delta of one step.** Every step of thread `f` either is an
    access step (`ZugriffsDelta`: no lock taken, held locks unchanged, new
    access events good) or a lock step (`SperrDelta`: only lock events, and
    shared memory unchanged). The lock steps are exactly `dannLocks`,
    `freiGib` and the two `frei` peels. -/
theorem schritt_delta (hO : GutO O) {M M' : RufMaschineG D} {f : Faden}
    (hs : RufSchrittG P O passes M f M') :
    ZugriffsDelta (M.faeden f).spur (M'.faeden f).spur ∨
      (SperrDelta (M.faeden f).spur (M'.faeden f).spur ∧ M'.speicher = M.speicher) := by
  cases hs with
  | g1 hs =>
    cases hs with
    | blatt l Γ Λ Λ' s rest ρ hleaf hhead hΛ σ' ρ' neu hstep hneu hkein =>
        simp only [rufUpdateG_self]
        left
        have hw : (execStmt O passes keinRuf s (M.weltVon f) ρ).welt = some σ' := by
          rw [hstep]; rfl
        exact zugriffsDelta_brav ((Stmt.gut_blatt O passes keinRuf hO s hleaf (M.weltVon f) ρ hΛ)
          σ' hw).2 neu hneu hkein
    | dannBlatt l Γ Λ Λ' Λ'' s rest k ρ hleaf hhead hΛ σ' ρ' neu hstep hneu hkein =>
        simp only [rufUpdateG_self]
        left
        have hw : (execStmt O passes keinRuf s (M.weltVon f) ρ).welt = some σ' := by
          rw [hstep]; rfl
        exact zugriffsDelta_brav ((Stmt.gut_blatt O passes keinRuf hO s hleaf (M.weltVon f) ρ hΛ)
          σ' hw).2 neu hneu hkein
    | endeBindAxiom l Γ Λ τ a args he hw hg hd hgd rest ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
        simp only [rufUpdateG_self]
        left
        subst hs₁
        have hl := gut_lese (W := fun _ => true) (G := fun _ => true) (M.weltVon f) Λ _
          (Args.orte_darf args) hΛ
        have hh1 : HeldIn Λ ((M.weltVon f).lese Λ args.orte).haelt := hl.heldIn hΛ
        have ha := axiomAntwort_gut O hO a ((M.weltVon f).lese Λ args.orte)
          (evalArgs ((M.weltVon f).lese Λ args.orte) args ((M.weltVon f).lese Λ args.orte) ρ)
          hd hgd hh1
        have e2 : σ₂ = (O.wirkt a (((M.weltVon f).lese Λ args.orte).fragt (.inl a))
            (evalArgs ((M.weltVon f).lese Λ args.orte) args ((M.weltVon f).lese Λ args.orte) ρ)).1 := by
          have := congrArg Prod.fst hax
          simp only [axiomAntwort] at this
          exact this.symm
        have hgt : ∀ t, D.aschreibt a t = true → ∀ L, Sum.inl L ∈ D.braucht t →
            L ∈ ((M.weltVon f).lese Λ args.orte).haelt :=
          fun t hwr L hL => hh1 L (hd t hwr _ hL)
        have hgg : ∀ g, D.agschreibt a g = true → ∀ L, Sum.inl L ∈ D.gbraucht g →
            L ∈ ((M.weltVon f).lese Λ args.orte).haelt :=
          fun g hwr L hL => hh1 L (hgd g hwr _ hL)
        obtain ⟨_, _, hcond⟩ := hO a (((M.weltVon f).lese Λ args.orte).fragt (.inl a))
          (evalArgs ((M.weltVon f).lese Λ args.orte) args ((M.weltVon f).lese Λ args.orte) ρ)
        obtain ⟨tabs, globs, Λe, _, _, _, _, _, _, hspur⟩ := hcond hgt hgg
        have hB : Brav (M.weltVon f) σ₂ := by
          have := hl.2.trans ha.2
          simp only [axiomAntwort] at this
          rw [e2]
          exact this
        refine zugriffsDelta_brav hB
          (axiomSpur tabs globs a Λe ((M.weltVon f).lese Λ args.orte).haelt ++
            (Ereignis.fremd (.inl a) :: leseEv (M.weltVon f) Λ args.orte))
          (by rw [e2, hspur, List.append_assoc]; rfl) ?_
        intro L h hm
        rcases List.mem_append.mp hm with hm | hm
        · rcases axiomSpur_mem hm with ⟨_, _, _, e⟩ | ⟨_, _, _, e⟩ <;> cases e
        · rcases List.mem_cons.mp hm with e | hm
          · cases e
          · exact kein_nimmt (leseEv_zugriff _ _ _) L h hm
    | _ =>
        simp only [rufUpdateG_self]
        subst_vars
        left
        first
          | exact zugriffsDelta_refl _
          | exact zugriffsDelta_lese _ _ _ (Expr.orte_darf _) (heldIn_weltVon (by assumption))
          | exact zugriffsDelta_lese _ _ _ (Args.orte_darf _) (heldIn_weltVon (by assumption))
          | exact zugriffsDelta_lese _ _ _ (ErgExpr.orte_darf _) (heldIn_weltVon (by assumption))
          | exact zugriffsDelta_lese _ _ _ (orte_append (Expr.orte_darf _) (Args.orte_darf _))
              (heldIn_weltVon (by assumption))
          | exact zugriffsDelta_lese _ _ _ (orte_append (Expr.orte_darf _) (Expr.orte_darf _))
              (heldIn_weltVon (by assumption))
          | exact zugriffsDelta_lese _ _ _
              (fun o ho => by
                rw [List.mem_singleton] at ho
                subst ho
                assumption)
              (heldIn_weltVon (by assumption))
  | g2 hs =>
    cases hs with
    | dannLocks l Γ Λ Λ'' L hr body rest k ρ hhead hself hrang hfrei =>
        simp only [rufUpdateG_self]
        exact Or.inr ⟨sperrDelta_nimmt _ L, trivial⟩
    | freiGib l Γ Λ L k ρ hhead =>
        simp only [rufUpdateG_self]
        exact Or.inr ⟨sperrDelta_gibt _ L, trivial⟩
    | _ =>
        simp only [rufUpdateG_self]
        subst_vars
        left
        first
          | exact zugriffsDelta_refl _
          | exact zugriffsDelta_lese _ _ _ (Expr.orte_darf _) (heldIn_weltVon (by assumption))
          | exact zugriffsDelta_lese _ _ _ (Args.orte_darf _) (heldIn_weltVon (by assumption))
          | exact zugriffsDelta_lese _ _ _ (ErgExpr.orte_darf _) (heldIn_weltVon (by assumption))
          | exact zugriffsDelta_lese _ _ _ (orte_append (Expr.orte_darf _) (Args.orte_darf _))
              (heldIn_weltVon (by assumption))
          | exact zugriffsDelta_lese _ _ _ (orte_append (Expr.orte_darf _) (Expr.orte_darf _))
              (heldIn_weltVon (by assumption))
          | exact zugriffsDelta_lese _ _ _
              (fun o ho => by
                rw [List.mem_singleton] at ho
                subst ho
                assumption)
              (heldIn_weltVon (by assumption))
  | g3 hs =>
    cases hs with
    | dannLeaveTrav l Γ Λ t inv body is k rest i ρ hl hhead σ' ρ' neu hstep hneu hkein σ₁ hs₁ hw
        neu₁ hneu₁ hΛ =>
        simp only [rufUpdateG_self]
        left
        rw [hs₁, leave_welt' _ _ _ _ _ _ _ _ hstep]
        exact zugriffsDelta_lese _ Λ _ (Expr.orte_darf inv)
          (fun L hL => hΛ L (Block.held_mono rest L hL))
    | dannNextTrav l Γ Λ t inv body is k rest i ρ hl hhead σ' ρ' neu hstep =>
        simp only [rufUpdateG_self]
        left
        rw [next_welt' _ _ _ _ _ _ _ _ hstep]
        exact zugriffsDelta_refl _
    | dannLeaveWieder l Γ Λ n bis body ueber k rest ρ hl hhead σ' ρ' neu hstep =>
        simp only [rufUpdateG_self]
        left
        rw [leave_welt' _ _ _ _ _ _ _ _ hstep]
        exact zugriffsDelta_refl _
    | dannNextWieder l Γ Λ n bis body ueber k rest ρ hl hhead σ' ρ' neu hstep =>
        simp only [rufUpdateG_self]
        left
        rw [next_welt' _ _ _ _ _ _ _ _ hstep]
        exact zugriffsDelta_refl _
    | dannLeaveEwig l Γ Λ a n inv body k rest ρ hl hhead σ' ρ' neu hstep =>
        simp only [rufUpdateG_self]
        left
        rw [leave_welt' _ _ _ _ _ _ _ _ hstep]
        exact zugriffsDelta_refl _
    | _ =>
        simp only [rufUpdateG_self]
        subst_vars
        left
        first
          | exact zugriffsDelta_refl _
          | exact zugriffsDelta_lese _ _ _ (Expr.orte_darf _) (heldIn_weltVon (by assumption))
          | exact zugriffsDelta_lese _ _ _ (Args.orte_darf _) (heldIn_weltVon (by assumption))
          | exact zugriffsDelta_lese _ _ _ (ErgExpr.orte_darf _) (heldIn_weltVon (by assumption))
          | exact zugriffsDelta_lese _ _ _ (orte_append (Expr.orte_darf _) (Args.orte_darf _))
              (heldIn_weltVon (by assumption))
          | exact zugriffsDelta_lese _ _ _ (orte_append (Expr.orte_darf _) (Expr.orte_darf _))
              (heldIn_weltVon (by assumption))
          | exact zugriffsDelta_lese _ _ _
              (fun o ho => by
                rw [List.mem_singleton] at ho
                subst ho
                assumption)
              (heldIn_weltVon (by assumption))
  | g4 hs =>
    cases hs with
    | peelFreiLeave l Γ Λ L rest k ρ hl hhead =>
        simp only [rufUpdateG_self]
        exact Or.inr ⟨sperrDelta_gibt _ L, trivial⟩
    | peelFreiNext l Γ Λ L rest k ρ hl hhead =>
        simp only [rufUpdateG_self]
        exact Or.inr ⟨sperrDelta_gibt _ L, trivial⟩
    | dannNextEwig l Γ Λ a n inv body k rest ρ hl hhead σ' ρ' neu hstep =>
        simp only [rufUpdateG_self]
        left
        rw [next_welt' _ _ _ _ _ _ _ _ hstep]
        exact zugriffsDelta_refl _
    | _ =>
        simp only [rufUpdateG_self]
        subst_vars
        left
        first
          | exact zugriffsDelta_refl _
          | exact zugriffsDelta_lese _ _ _ (Expr.orte_darf _) (heldIn_weltVon (by assumption))
          | exact zugriffsDelta_lese _ _ _ (Args.orte_darf _) (heldIn_weltVon (by assumption))
          | exact zugriffsDelta_lese _ _ _ (ErgExpr.orte_darf _) (heldIn_weltVon (by assumption))
          | exact zugriffsDelta_lese _ _ _ (orte_append (Expr.orte_darf _) (Args.orte_darf _))
              (heldIn_weltVon (by assumption))
          | exact zugriffsDelta_lese _ _ _ (orte_append (Expr.orte_darf _) (Expr.orte_darf _))
              (heldIn_weltVon (by assumption))
          | exact zugriffsDelta_lese _ _ _
              (fun o ho => by
                rw [List.mem_singleton] at ho
                subst ho
                assumption)
              (heldIn_weltVon (by assumption))
  | g5 hs =>
    cases hs with
    | dannExchange l Γ Λ Λ' g neuE hw hL rest k ρ hhead σ₁ hs₁ σ₂ hs₂ neu hneu hΛ =>
        simp only [rufUpdateG_self]
        left
        subst hs₂ hs₁
        have ho : ∀ o ∈ (Sum.inr g :: neuE.orte), OrtDarf Λ o := by
          intro o ho
          rcases List.mem_cons.mp ho with rfl | ho
          · exact hL
          · exact Expr.orte_darf neuE o ho
        have hl := gut_lese (W := fun _ => true) (G := fun _ => true) (M.weltVon f) Λ _ ho hΛ
        have hs := gut_schreibGlob (W := fun _ => true) (G := fun _ => true)
          ((M.weltVon f).lese Λ (Sum.inr g :: neuE.orte)) g Λ
          (eval ((M.weltVon f).lese Λ (Sum.inr g :: neuE.orte)) neuE
            ((M.weltVon f).lese Λ (Sum.inr g :: neuE.orte))
            (.cons (((M.weltVon f).lese Λ (Sum.inr g :: neuE.orte)).globs g) ρ)) rfl hL
          (hl.heldIn hΛ)
        refine zugriffsDelta_brav (hl.2.trans hs.2)
          (Ereignis.gzugriff g true Λ ((M.weltVon f).lese Λ (Sum.inr g :: neuE.orte)).haelt ::
            leseEv (M.weltVon f) Λ (Sum.inr g :: neuE.orte)) rfl ?_
        intro L h hm
        rcases List.mem_cons.mp hm with hm | hm
        · cases hm
        · exact kein_nimmt (leseEv_zugriff _ _ _) L h hm
    | dannBindAxiom l Γ Λ Λ' τ a args he hw hg hd hgd rest k ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
        simp only [rufUpdateG_self]
        left
        subst hs₁
        have hl := gut_lese (W := fun _ => true) (G := fun _ => true) (M.weltVon f) Λ _
          (Args.orte_darf args) hΛ
        have hh1 : HeldIn Λ ((M.weltVon f).lese Λ args.orte).haelt := hl.heldIn hΛ
        have ha := axiomAntwort_gut O hO a ((M.weltVon f).lese Λ args.orte)
          (evalArgs ((M.weltVon f).lese Λ args.orte) args ((M.weltVon f).lese Λ args.orte) ρ)
          hd hgd hh1
        have e2 : σ₂ = (O.wirkt a (((M.weltVon f).lese Λ args.orte).fragt (.inl a))
            (evalArgs ((M.weltVon f).lese Λ args.orte) args ((M.weltVon f).lese Λ args.orte) ρ)).1 := by
          have := congrArg Prod.fst hax
          simp only [axiomAntwort] at this
          exact this.symm
        have hgt : ∀ t, D.aschreibt a t = true → ∀ L, Sum.inl L ∈ D.braucht t →
            L ∈ ((M.weltVon f).lese Λ args.orte).haelt :=
          fun t hwr L hL => hh1 L (hd t hwr _ hL)
        have hgg : ∀ g, D.agschreibt a g = true → ∀ L, Sum.inl L ∈ D.gbraucht g →
            L ∈ ((M.weltVon f).lese Λ args.orte).haelt :=
          fun g hwr L hL => hh1 L (hgd g hwr _ hL)
        obtain ⟨_, _, hcond⟩ := hO a (((M.weltVon f).lese Λ args.orte).fragt (.inl a))
          (evalArgs ((M.weltVon f).lese Λ args.orte) args ((M.weltVon f).lese Λ args.orte) ρ)
        obtain ⟨tabs, globs, Λe, _, _, _, _, _, _, hspur⟩ := hcond hgt hgg
        have hB : Brav (M.weltVon f) σ₂ := by
          have := hl.2.trans ha.2
          simp only [axiomAntwort] at this
          rw [e2]
          exact this
        refine zugriffsDelta_brav hB
          (axiomSpur tabs globs a Λe ((M.weltVon f).lese Λ args.orte).haelt ++
            (Ereignis.fremd (.inl a) :: leseEv (M.weltVon f) Λ args.orte))
          (by rw [e2, hspur, List.append_assoc]; rfl) ?_
        intro L h hm
        rcases List.mem_append.mp hm with hm | hm
        · rcases axiomSpur_mem hm with ⟨_, _, _, e⟩ | ⟨_, _, _, e⟩ <;> cases e
        · rcases List.mem_cons.mp hm with e | hm
          · cases e
          · exact kein_nimmt (leseEv_zugriff _ _ _) L h hm
    | dannBindAxiomElseOk l Γ Λ Λ' τ a args he hr hw hg hd hgd err rest k ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
        simp only [rufUpdateG_self]
        left
        subst hs₁
        have hl := gut_lese (W := fun _ => true) (G := fun _ => true) (M.weltVon f) Λ _
          (Args.orte_darf args) hΛ
        have hh1 : HeldIn Λ ((M.weltVon f).lese Λ args.orte).haelt := hl.heldIn hΛ
        have ha := axiomAntwort_gut O hO a ((M.weltVon f).lese Λ args.orte)
          (evalArgs ((M.weltVon f).lese Λ args.orte) args ((M.weltVon f).lese Λ args.orte) ρ)
          hd hgd hh1
        have e2 : σ₂ = (O.wirkt a (((M.weltVon f).lese Λ args.orte).fragt (.inl a))
            (evalArgs ((M.weltVon f).lese Λ args.orte) args ((M.weltVon f).lese Λ args.orte) ρ)).1 := by
          have := congrArg Prod.fst hax
          simp only [axiomAntwortSonst] at this
          exact this.symm
        have hgt : ∀ t, D.aschreibt a t = true → ∀ L, Sum.inl L ∈ D.braucht t →
            L ∈ ((M.weltVon f).lese Λ args.orte).haelt :=
          fun t hwr L hL => hh1 L (hd t hwr _ hL)
        have hgg : ∀ g, D.agschreibt a g = true → ∀ L, Sum.inl L ∈ D.gbraucht g →
            L ∈ ((M.weltVon f).lese Λ args.orte).haelt :=
          fun g hwr L hL => hh1 L (hgd g hwr _ hL)
        obtain ⟨_, _, hcond⟩ := hO a (((M.weltVon f).lese Λ args.orte).fragt (.inl a))
          (evalArgs ((M.weltVon f).lese Λ args.orte) args ((M.weltVon f).lese Λ args.orte) ρ)
        obtain ⟨tabs, globs, Λe, _, _, _, _, _, _, hspur⟩ := hcond hgt hgg
        have hB : Brav (M.weltVon f) σ₂ := by
          have := hl.2.trans ha.2
          simp only [axiomAntwort] at this
          rw [e2]
          exact this
        refine zugriffsDelta_brav hB
          (axiomSpur tabs globs a Λe ((M.weltVon f).lese Λ args.orte).haelt ++
            (Ereignis.fremd (.inl a) :: leseEv (M.weltVon f) Λ args.orte))
          (by rw [e2, hspur, List.append_assoc]; rfl) ?_
        intro L h hm
        rcases List.mem_append.mp hm with hm | hm
        · rcases axiomSpur_mem hm with ⟨_, _, _, e⟩ | ⟨_, _, _, e⟩ <;> cases e
        · rcases List.mem_cons.mp hm with e | hm
          · cases e
          · exact kein_nimmt (leseEv_zugriff _ _ _) L h hm
    | dannBindAxiomElseGrund l Γ Λ Λ' τ a args he hr hw hg hd hgd err rest k ρ hhead σ₁ hs₁ σ₂ r hax neu hneu hΛ =>
        simp only [rufUpdateG_self]
        left
        subst hs₁
        have hl := gut_lese (W := fun _ => true) (G := fun _ => true) (M.weltVon f) Λ _
          (Args.orte_darf args) hΛ
        have hh1 : HeldIn Λ ((M.weltVon f).lese Λ args.orte).haelt := hl.heldIn hΛ
        have ha := axiomAntwort_gut O hO a ((M.weltVon f).lese Λ args.orte)
          (evalArgs ((M.weltVon f).lese Λ args.orte) args ((M.weltVon f).lese Λ args.orte) ρ)
          hd hgd hh1
        have e2 : σ₂ = (O.wirkt a (((M.weltVon f).lese Λ args.orte).fragt (.inl a))
            (evalArgs ((M.weltVon f).lese Λ args.orte) args ((M.weltVon f).lese Λ args.orte) ρ)).1 := by
          have := congrArg Prod.fst hax
          simp only [axiomAntwortSonst] at this
          exact this.symm
        have hgt : ∀ t, D.aschreibt a t = true → ∀ L, Sum.inl L ∈ D.braucht t →
            L ∈ ((M.weltVon f).lese Λ args.orte).haelt :=
          fun t hwr L hL => hh1 L (hd t hwr _ hL)
        have hgg : ∀ g, D.agschreibt a g = true → ∀ L, Sum.inl L ∈ D.gbraucht g →
            L ∈ ((M.weltVon f).lese Λ args.orte).haelt :=
          fun g hwr L hL => hh1 L (hgd g hwr _ hL)
        obtain ⟨_, _, hcond⟩ := hO a (((M.weltVon f).lese Λ args.orte).fragt (.inl a))
          (evalArgs ((M.weltVon f).lese Λ args.orte) args ((M.weltVon f).lese Λ args.orte) ρ)
        obtain ⟨tabs, globs, Λe, _, _, _, _, _, _, hspur⟩ := hcond hgt hgg
        have hB : Brav (M.weltVon f) σ₂ := by
          have := hl.2.trans ha.2
          simp only [axiomAntwort] at this
          rw [e2]
          exact this
        refine zugriffsDelta_brav hB
          (axiomSpur tabs globs a Λe ((M.weltVon f).lese Λ args.orte).haelt ++
            (Ereignis.fremd (.inl a) :: leseEv (M.weltVon f) Λ args.orte))
          (by rw [e2, hspur, List.append_assoc]; rfl) ?_
        intro L h hm
        rcases List.mem_append.mp hm with hm | hm
        · rcases axiomSpur_mem hm with ⟨_, _, _, e⟩ | ⟨_, _, _, e⟩ <;> cases e
        · rcases List.mem_cons.mp hm with e | hm
          · cases e
          · exact kein_nimmt (leseEv_zugriff _ _ _) L h hm
    | dannRegLies l Γ Λ Λ' r hk rest k ρ hhead v hv hz hΛ =>
        simp only [rufUpdateG_self]
        exact Or.inl (zugriffsDelta_fragt (M.weltVon f) _)
    | dannRegLiesElseWahr l Γ Λ Λ' r hk zusage sonst rest k ρ hhead v hv σ₁ hs₁ hw neu hneu hΛ =>
        simp only [rufUpdateG_self]
        subst hs₁
        exact Or.inl (zugriffsDelta_fragt_lese (M.weltVon f) _ Λ _ (Expr.orte_darf _) (heldIn_weltVon hΛ))
    | dannRegLiesElseFalsch l Γ Λ Λ' r hk zusage sonst rest k ρ hhead v hv σ₁ hs₁ hw neu hneu hΛ =>
        simp only [rufUpdateG_self]
        subst hs₁
        exact Or.inl (zugriffsDelta_fragt_lese (M.weltVon f) _ Λ _ (Expr.orte_darf _) (heldIn_weltVon hΛ))
    | dannAwaits l Γ Λ Λ' g payload hp hL hat rest k ρ hhead hvis σ₁ hs₁ neu hneu hΛ =>
        simp only [rufUpdateG_self]
        subst hs₁
        exact Or.inl (zugriffsDelta_fragt_lese (M.weltVon f) _ Λ [.inr g]
          (fun o ho => by rw [List.mem_singleton] at ho; subst ho; exact hL) (heldIn_weltVon hΛ))
    | _ =>
        simp only [rufUpdateG_self]
        subst_vars
        left
        first
          | exact zugriffsDelta_refl _
          | exact zugriffsDelta_lese _ _ _ (Expr.orte_darf _) (heldIn_weltVon (by assumption))
          | exact zugriffsDelta_lese _ _ _ (Args.orte_darf _) (heldIn_weltVon (by assumption))
          | exact zugriffsDelta_lese _ _ _ (ErgExpr.orte_darf _) (heldIn_weltVon (by assumption))
          | exact zugriffsDelta_lese _ _ _ (orte_append (Expr.orte_darf _) (Args.orte_darf _))
              (heldIn_weltVon (by assumption))
          | exact zugriffsDelta_lese _ _ _ (orte_append (Expr.orte_darf _) (Expr.orte_darf _))
              (heldIn_weltVon (by assumption))
          | exact zugriffsDelta_lese _ _ _
              (fun o ho => by
                rw [List.mem_singleton] at ho
                subst ho
                assumption)
              (heldIn_weltVon (by assumption))
  | g6 hs =>
    cases hs with
    | endeBindAxiomElseOk l Γ Λ τ a args he hr hw hg hd hgd err rest ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
        simp only [rufUpdateG_self]
        left
        subst hs₁
        have hl := gut_lese (W := fun _ => true) (G := fun _ => true) (M.weltVon f) Λ _
          (Args.orte_darf args) hΛ
        have hh1 : HeldIn Λ ((M.weltVon f).lese Λ args.orte).haelt := hl.heldIn hΛ
        have ha := axiomAntwort_gut O hO a ((M.weltVon f).lese Λ args.orte)
          (evalArgs ((M.weltVon f).lese Λ args.orte) args ((M.weltVon f).lese Λ args.orte) ρ)
          hd hgd hh1
        have e2 : σ₂ = (O.wirkt a (((M.weltVon f).lese Λ args.orte).fragt (.inl a))
            (evalArgs ((M.weltVon f).lese Λ args.orte) args ((M.weltVon f).lese Λ args.orte) ρ)).1 := by
          have := congrArg Prod.fst hax
          simp only [axiomAntwortSonst] at this
          exact this.symm
        have hgt : ∀ t, D.aschreibt a t = true → ∀ L, Sum.inl L ∈ D.braucht t →
            L ∈ ((M.weltVon f).lese Λ args.orte).haelt :=
          fun t hwr L hL => hh1 L (hd t hwr _ hL)
        have hgg : ∀ g, D.agschreibt a g = true → ∀ L, Sum.inl L ∈ D.gbraucht g →
            L ∈ ((M.weltVon f).lese Λ args.orte).haelt :=
          fun g hwr L hL => hh1 L (hgd g hwr _ hL)
        obtain ⟨_, _, hcond⟩ := hO a (((M.weltVon f).lese Λ args.orte).fragt (.inl a))
          (evalArgs ((M.weltVon f).lese Λ args.orte) args ((M.weltVon f).lese Λ args.orte) ρ)
        obtain ⟨tabs, globs, Λe, _, _, _, _, _, _, hspur⟩ := hcond hgt hgg
        have hB : Brav (M.weltVon f) σ₂ := by
          have := hl.2.trans ha.2
          simp only [axiomAntwort] at this
          rw [e2]
          exact this
        refine zugriffsDelta_brav hB
          (axiomSpur tabs globs a Λe ((M.weltVon f).lese Λ args.orte).haelt ++
            (Ereignis.fremd (.inl a) :: leseEv (M.weltVon f) Λ args.orte))
          (by rw [e2, hspur, List.append_assoc]; rfl) ?_
        intro L h hm
        rcases List.mem_append.mp hm with hm | hm
        · rcases axiomSpur_mem hm with ⟨_, _, _, e⟩ | ⟨_, _, _, e⟩ <;> cases e
        · rcases List.mem_cons.mp hm with e | hm
          · cases e
          · exact kein_nimmt (leseEv_zugriff _ _ _) L h hm
    | endeBindAxiomElseGrund l Γ Λ τ a args he hr hw hg hd hgd err rest ρ hhead σ₁ hs₁ σ₂ r hax neu hneu hΛ =>
        simp only [rufUpdateG_self]
        left
        subst hs₁
        have hl := gut_lese (W := fun _ => true) (G := fun _ => true) (M.weltVon f) Λ _
          (Args.orte_darf args) hΛ
        have hh1 : HeldIn Λ ((M.weltVon f).lese Λ args.orte).haelt := hl.heldIn hΛ
        have ha := axiomAntwort_gut O hO a ((M.weltVon f).lese Λ args.orte)
          (evalArgs ((M.weltVon f).lese Λ args.orte) args ((M.weltVon f).lese Λ args.orte) ρ)
          hd hgd hh1
        have e2 : σ₂ = (O.wirkt a (((M.weltVon f).lese Λ args.orte).fragt (.inl a))
            (evalArgs ((M.weltVon f).lese Λ args.orte) args ((M.weltVon f).lese Λ args.orte) ρ)).1 := by
          have := congrArg Prod.fst hax
          simp only [axiomAntwortSonst] at this
          exact this.symm
        have hgt : ∀ t, D.aschreibt a t = true → ∀ L, Sum.inl L ∈ D.braucht t →
            L ∈ ((M.weltVon f).lese Λ args.orte).haelt :=
          fun t hwr L hL => hh1 L (hd t hwr _ hL)
        have hgg : ∀ g, D.agschreibt a g = true → ∀ L, Sum.inl L ∈ D.gbraucht g →
            L ∈ ((M.weltVon f).lese Λ args.orte).haelt :=
          fun g hwr L hL => hh1 L (hgd g hwr _ hL)
        obtain ⟨_, _, hcond⟩ := hO a (((M.weltVon f).lese Λ args.orte).fragt (.inl a))
          (evalArgs ((M.weltVon f).lese Λ args.orte) args ((M.weltVon f).lese Λ args.orte) ρ)
        obtain ⟨tabs, globs, Λe, _, _, _, _, _, _, hspur⟩ := hcond hgt hgg
        have hB : Brav (M.weltVon f) σ₂ := by
          have := hl.2.trans ha.2
          simp only [axiomAntwort] at this
          rw [e2]
          exact this
        refine zugriffsDelta_brav hB
          (axiomSpur tabs globs a Λe ((M.weltVon f).lese Λ args.orte).haelt ++
            (Ereignis.fremd (.inl a) :: leseEv (M.weltVon f) Λ args.orte))
          (by rw [e2, hspur, List.append_assoc]; rfl) ?_
        intro L h hm
        rcases List.mem_append.mp hm with hm | hm
        · rcases axiomSpur_mem hm with ⟨_, _, _, e⟩ | ⟨_, _, _, e⟩ <;> cases e
        · rcases List.mem_cons.mp hm with e | hm
          · cases e
          · exact kein_nimmt (leseEv_zugriff _ _ _) L h hm

end Delta

end Gabbro.Grammatik
