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
  | nil => exact ⟨_, by simp only [rufAntwortG, hst]⟩
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
          · simp [rufAntwortG, hst, hc, antwortRestG, he]
          · simp [rufAntwortG, hst, hc, antwortRestG, he]
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
          · simp [rufAntwortG, hst, hc, antwortRestG, hn]

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
  let vor := (M.weltVon t).lese Λ e.orte
  let nach := R.scopes.foldl World.gibt vor
  obtain ⟨nr, hr, _⟩ := Erw.lese (M.weltVon t) Λ e.orte
  have hneu : nach.spur =
      (R.scopes.reverse.map (fun L => Ereignis.gibt L) ++ nr) ++ (M.faeden t).spur := by
    rw [World.gibt_foldl_spur, hr, List.append_assoc]
  obtain ⟨z, ha⟩ := rufAntwortG_moeglich (M.faeden t) vor nach
    (.inl (evalErg vor e vor ρ)) hkt
  exact ⟨_, RufSchrittG.rueckScopedWert M t ρ r e R hx hret hscope hΛ
    vor nach rfl rfl _ hneu z ha⟩

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
  let nach := R.scopes.foldl World.gibt (M.weltVon t)
  obtain ⟨z, ha⟩ := rufAntwortG_moeglich (M.faeden t) (M.weltVon t) nach (.inr grund) hkt
  exact ⟨_, RufSchrittG.rueckScopedGrund M t ρ r grund R hx hret hscope hΛ
    nach rfl _ (World.gibt_foldl_spur _ R.scopes) z ha⟩

end Schritt
end Gabbro.Grammatik
