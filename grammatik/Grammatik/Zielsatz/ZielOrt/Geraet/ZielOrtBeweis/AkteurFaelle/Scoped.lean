module

public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtBeweis.AkteurFaelle.ScopedAntwort

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration} {P : Programm D} {O : Orakel D} {passes : Nat}

/-- Scoped returns keep the K replay through evaluation, cleanup and delivery.
    Consuming loops and reason source heads remain outside the same fragment. -/
theorem akteur_gruppe7 (hK : ∀ f, KoerperGut P O passes f) (e0 : Ereignis D)
    {M M' : RufMaschineG D} {u : Faden} (hs : RufSchrittG7 P O passes M u M')
    (hF : FadenOk P O passes (M.faeden u) (M.weltVon u))
    (hL : LogOk P (M.faeden u).log) :
    FadenOk P O passes (M'.faeden u) (M'.weltVon u) ∧ LogOk P (M'.faeden u).log := by
  cases hs with
  | rueckScopedWert ρ r e R hhead hret hscope hΛ σ₁ hs₁ neu hneu hnonempty =>
      rename_i l Γ Λ
      simp only [RufMaschineG.weltVon, rufUpdateG_self]
      refine ⟨fadenOk_lokal hF hhead ρ
        (.aufraeumen ⟨.inl (evalErg σ₁ e σ₁ ρ), σ₁⟩ R.scopes)
        σ₁.spur (fun σ hg hok => ?_), hL⟩
      subst σ₁
      have hv := evalErg_gleichAuf e (fun _ h => scopedWert_orteZ hok hret h)
        (hg.lese Λ Λ e.orte e.orte) ρ
      refine ⟨σ.lese Λ e.orte, lese_laenge σ Λ e.orte, hg, trivial, fun calls => ?_⟩
      refine ZErg.gleich_trans ?_
        (ZErg.gleich_of_eq (semZ_scopedWert O passes calls r e R hret σ ρ).symm)
      exact ⟨⟨rfl, rfl⟩, hv.symm⟩
  | rueckScopedGrund ρ r grund R hhead hret hscope hΛ hnonempty =>
      exact (scopedGrund_nicht_okZ (kopf_okZ hF.1 hhead) hret).elim
  | rueckFreigabe ρ a L remaining hhead hnonempty =>
      simp only [RufMaschineG.weltVon, rufUpdateG_self]
      refine ⟨fadenOk_lokal hF hhead ρ (.aufraeumen a remaining)
        (.gibt L :: (M.faeden u).spur) (fun σ hg hok => ?_), hL⟩
      refine ⟨σ.gibt L, Nat.le_succ _, hg, trivial, fun calls => ?_⟩
      obtain ⟨answer, vor⟩ := a
      cases answer <;> exact ZErg.gleich_refl _
  | rueckFreigabeLetzte ρ a L hhead z ha =>
      simp only [RufMaschineG.weltVon, rufUpdateG_self, rufAntwortG_spur ha]
      have hdone := fadenOk_lokal hF hhead (M.faeden u).kopf.rho
        (.zurueckgekehrt a : GRest D _ false _ _)
        (.gibt L :: (M.faeden u).spur) (W' := (M.weltVon u).gibt L) (fun σ hg hok => by
          refine ⟨σ.gibt L, Nat.le_succ _, hg, trivial, fun calls => ?_⟩
          obtain ⟨answer, vor⟩ := a
          cases answer <;> exact ZErg.gleich_refl _)
      refine fadenOk_antwort hK e0 _ hdone hL rfl ?_
      exact (rufAntwortG_rest_irrel (M.faeden u) _ _ _).trans ha
  | rueckScopedWertDirekt ρ r e R hhead hret hscope hΛ σ₁ hs₁ neu hneu hempty z ha =>
      rename_i l Γ Λ
      simp only [RufMaschineG.weltVon, rufUpdateG_self, rufAntwortG_spur ha]
      have hdone := fadenOk_lokal hF hhead (M.faeden u).kopf.rho
        (.zurueckgekehrt ⟨.inl (evalErg σ₁ e σ₁ ρ), σ₁⟩ : GRest D _ false _ _)
        σ₁.spur (W' := σ₁) (fun σ hg hok => by
          have hgl : GleichAuf (fussOrte P (M.faeden u).kopf.f) (σ.lese Λ e.orte) σ₁ := by
            rw [hs₁]
            exact hg.lese Λ Λ e.orte e.orte
          have hv := evalErg_gleichAuf e (fun _ h => scopedWert_orteZ hok hret h) hgl ρ
          refine ⟨σ.lese Λ e.orte, lese_laenge σ Λ e.orte, hgl, trivial, fun calls => ?_⟩
          refine ZErg.gleich_trans ?_
            (ZErg.gleich_of_eq (semZ_scopedWert O passes calls r e R hret σ ρ).symm)
          have hm := World.gibt_foldl_speicher (σ.lese Λ e.orte) R.scopes
          exact ⟨⟨hm.1.symm, hm.2.symm⟩, hv.symm⟩)
      have hres := fadenOk_antwort hK e0 _ hdone hL rfl
        ((rufAntwortG_rest_irrel (M.faeden u) _ _ _).trans ha)
      have hw : M.speicher.welt σ₁.spur = σ₁ := by
        subst hs₁
        exact Speicher.welt_speicher ((M.weltVon u).lese Λ e.orte)
      simpa only [hw] using hres
  | rueckScopedGrundDirekt ρ r grund R hhead hret hscope hΛ hempty z ha =>
      exact (scopedGrund_nicht_okZ (kopf_okZ hF.1 hhead) hret).elim
  | _ =>
      exact absurd (kopf_okZ hF.1 ‹(M.faeden u).kopf.rest = _›)
        (by simp only [GRest.okZ, Endblock.kOk, Bool.false_eq_true, false_and,
          not_false_eq_true, Block.kOk, Stmt.kOk, Bool.false_and, and_false, and_self])

end Gabbro.Grammatik
