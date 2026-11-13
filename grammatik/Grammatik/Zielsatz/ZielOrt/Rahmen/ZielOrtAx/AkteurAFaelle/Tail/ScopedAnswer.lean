module

public import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtAxBeweis
public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtVollBeweis.Scoped

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration} {P : Programm D} {O : Orakel D} {passes : Nat} {Q : AxEns D}

/-- A completed value keeps the ordinary contract replay at the current world. -/
private theorem kopfA_fertig_ens (hO : GutO O) (hQ : AxVertragO Q O) (hK : ∀ f, KoerperGutA P passes Q f)
    {F : RufRahmenG D} {W vor : World D} {v : ErgVal D (vertragVon D F.f).erg}
    (hF : KopfA P O passes Q F W)
    (hhead : F.rest = ⟨false, D.params F.f, (vertragVon D F.f).ende, F.rho,
      .zurueckgekehrt ⟨.inl v, vor⟩⟩) : EnsAmRueck P F.f F.s0 W F.rho v := by
  obtain ⟨H, HA, σ, hreq, hf, hv, hk, hfa, hra, hqa, hka, hg, hok, heq⟩ := hF
  have h1 := heq (rufAusV H) (orakelAus O HA) (rufAusV_passt hf) (orakelAus_passt O hfa)
    rfl
  rw [hhead] at h1
  have h2 := ZErg.folgt_zurueck h1
  obtain ⟨σ', hex, hsg⟩ := zErg_gleich_zurueck h2
  have hens := (hK F.f (orakelAus O HA) (orakelAus_rahmen hO hra) (orakelAus_vertragOP (axVertragOP_of_O _ hQ) hqa) (rufAusV H) (rufAusV_respektiert hv) (rufAusV_ohneVorbedingung hv) F.s0 F.rho hreq).1 σ' v hex
  exact ens_transfer hens (GleichAuf.refl _ _)
    (GleichAuf.mono (fun _ h => fuss_ens P F.f h) ((gleichAuf_SG hsg).trans hg))

/-- Deliver a completed answer with the same generic pop used by ordinary returns. -/
theorem fadenA_antwort (hO : GutO O) (hQ : AxVertragO Q O) (hK : ∀ f, KoerperGutA P passes Q f) (e0 : Ereignis D)
    {z z' : RufFadenG D} {W vor : World D}
    (a : ErgVal D (vertragVon D z.kopf.f).erg ⊕ Fin (vertragVon D z.kopf.f).gruende)
    (hF : FadenA P O passes Q z W) (hL : LogOk P z.log)
    (hhead : z.kopf.rest = ⟨false, D.params z.kopf.f, (vertragVon D z.kopf.f).ende,
      z.kopf.rho, .zurueckgekehrt ⟨a, vor⟩⟩)

    (ha : rufAntwortG z vor W a = some z') :
    FadenA P O passes Q z' W ∧ LogOk P z'.log := by
  cases hst : z.stapel with
  | nil =>
      simp only [rufAntwortG, hst, Option.some.injEq] at ha
      subst z'
      refine ⟨⟨?_, trivial⟩, hL⟩
      have he := hF.1
      unfold KopfA at he ⊢
      rw [hhead] at he
      exact he
  | cons caller rest =>
      obtain ⟨c, hc⟩ : ∃ c, antwortRestG z.kopf.f a caller.rest = some c := by
        cases hc : antwortRestG z.kopf.f a caller.rest with
        | none => simp [rufAntwortG, hst, hc] at ha
        | some c => exact ⟨c, rfl⟩
      simp [rufAntwortG, hst, hc] at ha
      subst z'
      have hs := hF.2
      rw [hst] at hs
      obtain ⟨hW, hs⟩ := hs
      obtain ⟨l, Γ, Λ, ρ, r⟩ := c
      cases a with
      | inl v =>
          have hens := kopfA_fertig_ens hO hQ hK hF.1 hhead
          refine ⟨⟨popA_kopf e0 hW W (fun σ => .ok σ v) (Or.inl ⟨v, fun _ => rfl, hens⟩)

            ρ r (fun hok => antwortRestG_okV _ _ _ _ hok hc)
            (fun R O' σ X h => fortV_antwortRestG hc R O' σ X h) W ⟨rfl, rfl⟩, hs⟩,
            logOk_rueck hL hens⟩
      | inr grund =>
          refine ⟨⟨popA_kopf e0 hW W (fun σ => .why σ grund) (Or.inr ⟨grund, fun _ => rfl⟩)

            ρ r (fun hok => antwortRestG_okV _ _ _ _ hok hc)
            (fun R O' σ X h => fortV_antwortRestG hc R O' σ X h) W ⟨rfl, rfl⟩, hs⟩,
            logOk_grund hL⟩

end Gabbro.Grammatik
