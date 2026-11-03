module

public import Grammatik.Logik.Fortschritt.Fortschritt.T1

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- The progress stack invariant makes the shared answer operation total
    on both channels, including the empty-stack root. -/
theorem rufAntwortG_moeglich (z : RufFadenG D) (vor σ : World D)
    (a : ErgVal D (vertragVon D z.kopf.f).erg ⊕ Fin (vertragVon D z.kopf.f).gruende)
    (hkt : FormKette z.kopf.f z.stapel) : ∃ z', rufAntwortG z vor σ a = some z' := by
  cases hst : z.stapel with
  | nil =>
      refine ⟨_, ?_⟩
      simp only [rufAntwortG, hst]
      rfl
  | cons c st =>
      rw [hst] at hkt
      cases a with
      | inl v =>
          rcases hkt.1 with ⟨hnw, _⟩ |
              ⟨l, Γ, Λ, Λ', τ, rest, k, ρ, hc, he, _⟩ |
              ⟨l, Γ, Λ, Λ', τ, n, err, rest, k, ρ, hc, he, _⟩
          · obtain ⟨cf, crho, cs0, ⟨l, Γ, Λ, ρ, r⟩⟩ := c
            cases r <;>
              simp_all [rufAntwortG, antwortRestG, RufRahmenG.wartend, GRest.wartend]
          · have he' : (vertragVon D z.kopf.f).erg = some τ := he
            refine ⟨_, ?_⟩
            simp only [rufAntwortG, hst, hc, antwortRestG, dif_pos he']
            rfl
          · have he' : (vertragVon D z.kopf.f).erg = some τ := he
            refine ⟨_, ?_⟩
            simp only [rufAntwortG, hst, hc, antwortRestG, dif_pos he']
            rfl
      | inr grund =>
          rcases hkt.1 with ⟨_, h0⟩ |
              ⟨_, _, _, _, _, _, _, _, _, _, h0⟩ |
              ⟨l, Γ, Λ, Λ', τ, n, err, rest, k, ρ, hc, _, hn⟩
          · have hlt := grund.2
            change grund.val < D.gruende z.kopf.f at hlt
            omega
          · have hlt := grund.2
            change grund.val < D.gruende z.kopf.f at hlt
            omega
          · have hn' : (vertragVon D z.kopf.f).gruende = n := hn
            refine ⟨_, ?_⟩
            simp only [rufAntwortG, hst, hc, antwortRestG, dif_pos hn']
            rfl

section Schritt

variable {P : Programm D} {O : Orakel D} {passes : Nat}

/-- A scoped value head really steps: evaluate once, release the scopes,
    and deliver the saved value. Scope validity is an explicit premise. -/
theorem w_scopedWert {M : RufMaschineG D} {t : Faden} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} (ρ : Env D Γ)
    (r : GRest D (vertragVon D (M.faeden t).kopf.f) l Γ Λ)
    (e : ErgExpr D Γ Λ (vertragVon D (M.faeden t).kopf.f).erg)
    (R : RueckRessourcen D (vertragVon D (M.faeden t).kopf.f) Λ)
    (hx : (M.faeden t).kopf.rest = ⟨l, Γ, Λ, ρ, r⟩)
    (hret : r.scopedWert = some (e, R))
    (hscope : scopesOkScopes (vertragVon D (M.faeden t).kopf.f).haelt
      (vertragVon D (M.faeden t).kopf.f).boden R.scopes = true)
    (hΛ : HeldIn Λ (offen (M.faeden t).spur))
    (hkt : FormKette (M.faeden t).kopf.f (M.faeden t).stapel) :
    ∃ M', RufSchrittG P O passes M t M' := by
  obtain ⟨neu, hneu, _⟩ := Erw.lese (M.weltVon t) Λ e.orte
  by_cases hsc : R.scopes = []
  · obtain ⟨z, hz⟩ := rufAntwortG_moeglich (M.faeden t)
      ((M.weltVon t).lese Λ e.orte) ((M.weltVon t).lese Λ e.orte)
      (.inl (evalErg ((M.weltVon t).lese Λ e.orte) e ((M.weltVon t).lese Λ e.orte) ρ)) hkt
    exact ⟨_, RufSchrittG.rueckScopedWertDirekt M t ρ r e R hx hret hscope hΛ
      _ rfl neu hneu hsc z hz⟩
  · exact ⟨_, RufSchrittG.rueckScopedWert M t ρ r e R hx hret hscope hΛ
      _ rfl neu hneu hsc⟩

/-- The reason channel has the same cleanup step, without reading a value. -/
theorem w_scopedGrund {M : RufMaschineG D} {t : Faden} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} (ρ : Env D Γ)
    (r : GRest D (vertragVon D (M.faeden t).kopf.f) l Γ Λ)
    (grund : Fin (vertragVon D (M.faeden t).kopf.f).gruende)
    (R : RueckRessourcen D (vertragVon D (M.faeden t).kopf.f) Λ)
    (hx : (M.faeden t).kopf.rest = ⟨l, Γ, Λ, ρ, r⟩)
    (hret : r.scopedGrund = some (grund, R))
    (hscope : scopesOkScopes (vertragVon D (M.faeden t).kopf.f).haelt
      (vertragVon D (M.faeden t).kopf.f).boden R.scopes = true)
    (hΛ : HeldIn Λ (offen (M.faeden t).spur))
    (hkt : FormKette (M.faeden t).kopf.f (M.faeden t).stapel) :
    ∃ M', RufSchrittG P O passes M t M' := by
  by_cases hsc : R.scopes = []
  · obtain ⟨z, hz⟩ := rufAntwortG_moeglich (M.faeden t)
      (M.weltVon t) (M.weltVon t) (.inr grund) hkt
    exact ⟨_, RufSchrittG.rueckScopedGrundDirekt M t ρ r grund R hx hret hscope hΛ hsc z hz⟩
  · exact ⟨_, RufSchrittG.rueckScopedGrund M t ρ r grund R hx hret hscope hΛ hsc⟩

/-- Every cleanup head can step. Releases need no external answer; after
    the final release the existing stack invariant supplies answer delivery. -/
theorem w_aufraeumen {M : RufMaschineG D} {t : Faden} {l : Bool} {Γ : Ctx}
    (ρ : Env D Γ)
    (a : (ErgVal D (vertragVon D (M.faeden t).kopf.f).erg ⊕
      Fin (vertragVon D (M.faeden t).kopf.f).gruende) × World D)
    (remaining : List D.Lock) (hnonempty : remaining ≠ [])
    (hx : (M.faeden t).kopf.rest = ⟨l, Γ, _, ρ, .aufraeumen a remaining⟩)
    (hkt : FormKette (M.faeden t).kopf.f (M.faeden t).stapel) :
    ∃ M', RufSchrittG P O passes M t M' := by
  cases remaining with
  | nil => exact (hnonempty rfl).elim
  | cons L remaining =>
      by_cases hlast : remaining = []
      · subst remaining
        obtain ⟨z, hz⟩ := rufAntwortG_moeglich (M.faeden t) a.2
          ((M.weltVon t).gibt L) a.1 hkt
        exact ⟨_, RufSchrittG.rueckFreigabeLetzte M t ρ a L hx z hz⟩
      · exact ⟨_, RufSchrittG.rueckFreigabe M t ρ a L remaining hx hlast⟩

end Schritt
end Gabbro.Grammatik
