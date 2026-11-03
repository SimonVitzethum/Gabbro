module

public import Grammatik.Logik.Fortschritt.Fortschritt.T2.ScopeFacts

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- The checker's scope facts on the head and all suspended frames. -/
def FadenScopesG (z : RufFadenG D) : Prop :=
  z.kopf.rest.2.2.2.2.scopesGut ∧ ∀ F ∈ z.stapel, F.rest.2.2.2.2.scopesGut

private theorem antwortRestG_scopesGut {V : Vertrag D} (g : D.Fn)
    (a : ErgVal D (vertragVon D g).erg ⊕ Fin (vertragVon D g).gruende)
    (c c' : Σ l : Bool, Σ Γ : Ctx, Σ Λ : List (Res D), Env D Γ × GRest D V l Γ Λ)
    (hc : c.2.2.2.2.scopesGut) (ha : antwortRestG g a c = some c') :
    c'.2.2.2.2.scopesGut := by
  obtain ⟨l, Γ, Λ, ρ, r⟩ := c
  cases a <;> cases r <;>
    simp_all [antwortRestG, GRest.scopesGut, scopesOk_alsBlock]
  all_goals first
    | (subst ha; simp_all [GRest.scopesGut, scopesOk_alsBlock])
    | (obtain ⟨_, ha⟩ := ha; subst ha; simp_all [GRest.scopesGut, scopesOk_alsBlock])
    | (split at ha <;> simp_all [GRest.scopesGut, scopesOk_alsBlock])

private theorem rufAntwortG_scopesGut {z z' : RufFadenG D} {vor σ : World D}
    {a : ErgVal D (vertragVon D z.kopf.f).erg ⊕ Fin (vertragVon D z.kopf.f).gruende}
    (hz : FadenScopesG z) (ha : rufAntwortG z vor σ a = some z') : FadenScopesG z' := by
  cases hst : z.stapel with
  | nil =>
      simp only [rufAntwortG, hst, Option.some.injEq] at ha
      subst z'
      exact ⟨trivial, by simp⟩
  | cons c st =>
      obtain ⟨r, hr⟩ : ∃ r, antwortRestG z.kopf.f a c.rest = some r := by
        cases hr : antwortRestG z.kopf.f a c.rest with
        | none => simp [rufAntwortG, hst, hr] at ha
        | some r => exact ⟨r, rfl⟩
      simp [rufAntwortG, hst, hr] at ha
      subst z'
      refine ⟨antwortRestG_scopesGut _ _ _ _ (hz.2 c (by simp [hst])) hr, ?_⟩
      intro F hF
      exact hz.2 F (by simp only [hst, List.mem_cons]; exact Or.inr hF)

set_option maxHeartbeats 4000000 in
/-- G preserves the existing source scope check under selection, unfolding,
    call suspension and either answer channel. No new program premise. -/
theorem fadenScopesG_schritt {P : Programm D} {O : Orakel D} {pa : Nat}
    (hsc : ScopesOkProg P) {M M' : RufMaschineG D} {t : Faden}
    (hs : RufSchrittG P O pa M t M') (h : FadenScopesG (M.faeden t)) :
    FadenScopesG (M'.faeden t) := by
  obtain ⟨hk, hst⟩ := h
  cases hs with
  | g1 hs =>
      cases hs with
      | dannOnTagSome l Γ Λ Λ' Λ'' cs v arms rest k ρ hhead σ₁ hs₁ τ b nutz hwahl =>
          dsimp only
          rw [rufUpdateG_self]
          refine ⟨?_, hst⟩
          rw [hhead] at hk
          simp only [GRest.scopesGut, Block.scopesOk, Stmt.scopesOk, Bool.and_eq_true] at hk ⊢
          have hb := scopesOk_armWahlG _ _ arms (eval σ₁ v σ₁ ρ) hk.1.1
          rw [hwahl] at hb
          exact ⟨hb, hk.1.2, hk.2⟩
      | dannOnTagNone l Γ Λ Λ' Λ'' cs v arms rest k ρ hhead σ₁ hs₁ b nutz hwahl =>
          dsimp only
          rw [rufUpdateG_self]
          refine ⟨?_, hst⟩
          rw [hhead] at hk
          simp only [GRest.scopesGut, Block.scopesOk, Stmt.scopesOk, Bool.and_eq_true] at hk ⊢
          have hb := scopesOk_armWahlG _ _ arms (eval σ₁ v σ₁ ρ) hk.1.1
          rw [hwahl] at hb
          exact ⟨hb, hk.1.2, hk.2⟩
      | dannOnGrund l Γ Λ Λ' Λ'' n r arms rest k ρ hhead σ₁ hs₁ b hwahl =>
          dsimp only
          rw [rufUpdateG_self]
          refine ⟨?_, hst⟩
          rw [hhead] at hk
          simp only [GRest.scopesGut, Block.scopesOk, Stmt.scopesOk, Bool.and_eq_true] at hk ⊢
          have hb := scopesOk_grundWahlG _ _ arms (eval σ₁ r σ₁ ρ) hk.1.1
          rw [hwahl] at hb
          exact ⟨hb, hk.1.2, hk.2⟩
      | _ =>
          dsimp only
          rw [rufUpdateG_self]
          refine (fun headRest : (M.faeden t).kopf.rest = _ => ?_) (by assumption)
          rw [headRest] at hk
          simp_all [FadenScopesG, GRest.scopesGut, Endblock.scopesOk,
            Block.scopesOk, Stmt.scopesOk, scopesOk_alsBlock,
            RufDannHeadG, RufEndHeadG]
  | g7 hs =>
      cases hs with
      | rueckFreigabeLetzte _ _ _ _ z ha
      | rueckScopedWertDirekt _ _ _ _ _ _ _ _ _ _ _ _ _ z ha
      | rueckScopedGrundDirekt _ _ _ _ _ _ _ _ _ z ha =>
          dsimp only
          rw [rufUpdateG_self]
          exact rufAntwortG_scopesGut ⟨hk, hst⟩ ha
      | _ =>
          dsimp only
          rw [rufUpdateG_self]
          refine (fun headRest : (M.faeden t).kopf.rest = _ => ?_) (by assumption)
          rw [headRest] at hk
          simp_all [FadenScopesG, GRest.scopesGut, Endblock.scopesOk,
            Block.scopesOk, Stmt.scopesOk, RufDannHeadG, RufEndHeadG]
  | g2 hs | g3 hs | g4 hs | g5 hs | g6 hs =>
      cases hs <;> dsimp only <;> rw [rufUpdateG_self]
      all_goals
        refine (fun headRest : (M.faeden t).kopf.rest = _ => ?_) (by assumption)
        rw [headRest] at hk
      all_goals first
        | (refine (fun waiting : RufWartetHeadG (D := D) _ _ _ _ => ?_) (by assumption)
           rcases waiting with hc | ⟨n, err, hc⟩)
        | skip
      all_goals
        simp_all [FadenScopesG, GRest.scopesGut, Endblock.scopesOk,
          Block.scopesOk, Stmt.scopesOk, scopesOk_alsBlock, scopesGut_weiterOpt,
          RufDannHeadG, RufEndHeadG]
      all_goals try
        rw [hc] at hst
        simp_all [GRest.scopesGut, scopesOk_alsBlock]
      all_goals
        expose_names
        rw [hcaller] at hst
        simp_all [GRest.scopesGut, scopesOk_alsBlock]

/-- Scope validity at every reachable head follows from the program check,
    without adding a field or a premise to `Spec`. -/
theorem fadenScopesG_erreichbar {P : Programm D} {O : Orakel D} {pa : Nat}
    (hsc : ScopesOkProg P) {sp : Speicher D}
    {init : Faden → Σ f : D.Fn, Env D (D.params f)} {M : RufMaschineG D}
    (hr : RufErreichbarG P O pa (RufStartG P sp init) M) :
    ∀ t, FadenScopesG (M.faeden t) := by
  induction hr with
  | start =>
      intro t
      rw [start_faden]
      exact ⟨hsc _, by simp⟩
  | schritt N N' u hn hs ih =>
      intro t
      by_cases htu : t = u
      · subst t
        exact fadenScopesG_schritt hsc hs (ih u)
      · rw [rufSchrittG_fremd hs t htu]
        exact ih t

end Gabbro.Grammatik
