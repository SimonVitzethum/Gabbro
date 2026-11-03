module

public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtBeweis.T1a
public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtSem.Scoped

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration} {P : Programm D} {O : Orakel D} {passes : Nat}

/-- The shared value delivery chooses the continuation of the existing replay. -/
private theorem fortZ_antwortRestG {F : RufRahmenG D} {g : D.Fn}
    {v : ErgVal D (D.erg g)}
    {c : Σ l : Bool, Σ Γ : Ctx, Σ Λ : List (Res D),
      Env D Γ × GRest D (vertragVon D F.f) l Γ Λ}
    (hok : F.rest.2.2.2.2.okZ P (fussOrte P F.f))
    (ha : antwortRestG g (.inl v) F.rest = some c)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (σ : World D) (X : ZErg (vertragVon D F.f))
    (hplain : F.wartend = false →
      X.gleich (semZ O passes R F.rest.2.2.2.2 σ F.rest.2.2.2.1))
    (hbind : ∀ (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D)) (τ : Ty)
      (rest : Block D (vertragVon D F.f) l (τ :: Γ) Λ Λ')
      (k : GRest D (vertragVon D F.f) l Γ Λ') (ρ : Env D Γ),
      F.rest = ⟨l, Γ, Λ, ρ, .wartet rest k⟩ → ∀ he : D.erg g = some τ,
      X.gleich (semZ O passes R (.dann rest (.schrumpf k)) σ (.cons (ergWert he v) ρ))) :
    X.gleich (semZ O passes R c.2.2.2.2 σ c.2.2.2.1) := by
  obtain ⟨f, rho, s0, l, Γ, Λ, ρ, r⟩ := F
  cases r with
  | wartet rest k =>
      simp only [antwortRestG] at ha
      split at ha
      · rename_i he
        simp only [Option.some.injEq] at ha
        subst c
        exact hbind _ _ _ _ _ rest k ρ rfl he
      · cases ha
  | wartetSonst => exact hok.elim
  | _ =>
      simp only [antwortRestG, Option.some.injEq] at ha
      subst c
      exact hplain rfl

/-- A completed value satisfies the callee's contract at the delivery world.
    Cleanup changes traces only; the saved value is never evaluated again. -/
private theorem kopf_fertig_ens (hK : ∀ f, KoerperGut P O passes f)
    {F : RufRahmenG D} {W vor : World D} {v : ErgVal D (vertragVon D F.f).erg}
    (hF : KopfOk P O passes F W)
    (hhead : F.rest = ⟨false, D.params F.f, (vertragVon D F.f).ende, F.rho,
      .zurueckgekehrt ⟨.inl v, vor⟩⟩) : EnsAmRueck P F.f F.s0 W F.rho v := by
  obtain ⟨H, σ, hreq, hf, hv, _, hg, _, heq⟩ := hF
  have h1 := heq (rufAus H) (rufAus_passt hf)
  have hrest := congrArg (fun c : Σ l : Bool, Σ Γ : Ctx, Σ Λ : List (Res D),
    Env D Γ × GRest D (vertragVon D F.f) l Γ Λ =>
      semZ O passes (rufAus H) c.2.2.2.2 σ c.2.2.2.1) hhead
  obtain ⟨σ', hex, hsg⟩ := zErg_gleich_zurueck
    (ZErg.gleich_trans h1 (ZErg.gleich_of_eq hrest))
  have hens := (hK F.f (rufAus H) (rufAus_respektiert hv)
    (rufAus_ohneVorbedingung H) F.s0 F.rho hreq).1 σ' v hex
  exact ens_transfer hens (GleichAuf.refl _ _)
    (GleichAuf.mono (fun _ h => fuss_ens P F.f h) ((gleichAuf_SG hsg).trans hg))

/-- Deliver a saved answer through the ordinary pop replay, or complete a root. -/
theorem fadenOk_antwort (hK : ∀ f, KoerperGut P O passes f) (e0 : Ereignis D)
    {z z' : RufFadenG D} {W vor : World D}
    (a : ErgVal D (vertragVon D z.kopf.f).erg ⊕ Fin (vertragVon D z.kopf.f).gruende)
    (hF : FadenOk P O passes z W) (hL : LogOk P z.log)
    (hhead : z.kopf.rest = ⟨false, D.params z.kopf.f, (vertragVon D z.kopf.f).ende,
      z.kopf.rho, .zurueckgekehrt ⟨a, vor⟩⟩)
    (ha : rufAntwortG z vor W a = some z') :
    FadenOk P O passes z' W ∧ LogOk P z'.log := by
  cases hst : z.stapel with
  | nil =>
      simp only [rufAntwortG, hst, Option.some.injEq] at ha
      subst z'
      refine ⟨⟨?_, trivial⟩, hL⟩
      have hk := congrArg (RufRahmenG.mk z.kopf.f z.kopf.rho z.kopf.s0) hhead
      exact hk ▸ hF.1
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
      have hok : caller.rest.2.2.2.2.okZ P (fussOrte P caller.f) := by
        obtain ⟨_, _, _, _, _, _, hok, _⟩ := hW
        exact hok
      obtain ⟨l, Γ, Λ, ρ, r⟩ := c
      cases a with
      | inl v =>
          have hens := kopf_fertig_ens hK hF.1 hhead
          refine ⟨⟨pop_kopf e0 hW W v hens ρ r
            (fun hok => antwortRestG_okZ _ _ _ _ hok hc)
            (fun R σ X hplain hbind => fortZ_antwortRestG hok hc R σ X hplain hbind)
            W ⟨rfl, rfl⟩, hs⟩, logOk_rueck hL hens⟩
      | inr grund =>
          exact (antwortRestG_grund_nicht_okZ _ _ _ _ hok hc).elim

end Gabbro.Grammatik
