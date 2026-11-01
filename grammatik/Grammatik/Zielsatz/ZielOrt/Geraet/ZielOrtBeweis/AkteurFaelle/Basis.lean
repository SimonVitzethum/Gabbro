module

public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtBeweis.T1

@[expose] public section


namespace Gabbro.Grammatik

variable {D : Deklaration}

section Push

variable {P : Programm D} {O : Orakel D} {passes : Nat}

/-- The residue a pending call leaves: how the call continues once the
    handler answers, for a plain call or a bind-call. -/
def PushWeiter (O : Orakel D) (passes : Nat) {V : Vertrag D} (g : D.Fn)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (r : GRest D V l Γ Λ) (σ : World D) (ρ : Env D Γ)
    {lc : Bool} {Γc : Ctx} {Λc : List (Res D)} (ρc : Env D Γc) (rc : GRest D V lc Γc Λc)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (σa : World D)
    (v : ErgVal D (D.erg g)) : Prop :=
  (rc.wartend = false → semZ O passes R r σ ρ = semZ O passes R rc σa ρc) ∧
  (∀ (l' : Bool) (Γ' : Ctx) (Λ₁ Λ₂ : List (Res D)) (τ : Ty)
      (restb : Block D V l' (τ :: Γ') Λ₁ Λ₂) (k : GRest D V l' Γ' Λ₂) (ρc' : Env D Γ'),
    (⟨lc, Γc, Λc, ρc, rc⟩ :
      Σ l : Bool, Σ Γ : Ctx, Σ Λ : List (Res D), Env D Γ × GRest D V l Γ Λ) =
      ⟨l', Γ', Λ₁, ρc', .wartet restb k⟩ →
    ∀ he : D.erg g = some τ,
      semZ O passes R r σ ρ = semZ O passes R (.dann restb (.schrumpf k)) σa (.cons (ergWert he v) ρc'))

/-- **A push keeps the replay.** The head frame calls `g` with `args`; it
    becomes a suspended frame with the continuation `rc`, and the callee's
    frame becomes a fresh replayed head (empty record, sequential world =
    machine entry world). The callee's `requires` holds at the machine's
    entry world (`push_req`), for the log. -/
theorem push_ok (hK : ∀ f, KoerperGut P O passes f) (hFrag : ∀ f, (P.rumpf f).kOk = true)
    {z : RufFadenG D} {W : World D} (hF : FadenOk P O passes z W)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ}
    {r : GRest D (vertragVon D z.kopf.f) l Γ Λ} (hr : z.kopf.rest = ⟨l, Γ, Λ, ρ, r⟩)
    (g : D.Fn) (args : Args D Γ Λ (D.params g))
    (hS : r.okZ P (fussOrte P z.kopf.f) → args.orte ⊆ fussOrte P z.kopf.f ∧
      (P.requires g).orte ++ (P.ensures g).orte ⊆ fussOrte P z.kopf.f)
    {lc : Bool} {Γc : Ctx} {Λc : List (Res D)} (ρc : Env D Γc)
    (rc : GRest D (vertragVon D z.kopf.f) lc Γc Λc)
    (hrc : r.okZ P (fussOrte P z.kopf.f) → rc.okZ P (fussOrte P z.kopf.f))
    (hlogik : ∀ R σ (e : Logik D),
      R g (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) =
        .logik e → semZ O passes R r σ ρ = .logik e)
    (hweiter : ∀ R σ (σa : World D) (v : ErgVal D (D.erg g)),
      R g (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) =
        .ok σa v → PushWeiter O passes g r σ ρ ρc rc R σa v) :
    FadenOk P O passes
      ⟨⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨lc, Γc, Λc, ρc, rc⟩⟩ :: z.stapel,
        ⟨g, evalArgs (W.lese Λ args.orte) args (W.lese Λ args.orte) ρ, W.lese Λ args.orte,
          ⟨false, D.params g, Signatur.anfang D (D.signatur g),
            evalArgs (W.lese Λ args.orte) args (W.lese Λ args.orte) ρ, .ende (P.rumpf g)⟩⟩,
        (W.lese Λ args.orte).spur,
        RufEreignisF.eintritt g (evalArgs (W.lese Λ args.orte) args (W.lese Λ args.orte) ρ)
          (W.lese Λ args.orte) :: z.log⟩
      (W.lese Λ args.orte) ∧
    ReqAmEintritt P g (W.lese Λ args.orte)
      (evalArgs (W.lese Λ args.orte) args (W.lese Λ args.orte) ρ) := by
  obtain ⟨⟨H, σ, hreq, hf, hv, hk, hg, hok, heq⟩, hSt⟩ := hF
  have hok' : r.okZ P (fussOrte P z.kopf.f) := by rw [hr] at hok; exact hok
  have heq' : ∀ R, Passt R H →
      (zErg (execEnd (V := vertragVon D z.kopf.f) O passes R (P.rumpf z.kopf.f) z.kopf.s0
        z.kopf.rho)).gleich (semZ O passes R r σ ρ) := by
    intro R hR
    have := heq R hR
    rw [hr] at this
    exact this
  obtain ⟨hargs, hctr⟩ := hS hok'
  have hgκ : GleichAuf (fussOrte P z.kopf.f) (σ.lese Λ args.orte) (W.lese Λ args.orte) :=
    hg.lese Λ Λ args.orte args.orte
  have hρk : evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ =
      evalArgs (W.lese Λ args.orte) args (W.lese Λ args.orte) ρ :=
    evalArgs_gleichAuf args (fun _ h => hargs h) hgκ ρ
  have hreqκ := push_req hK hreq hf hv r heq' g (σ.lese Λ args.orte)
    (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) (fun R e h => hlogik R σ e h)
  rw [hρk] at hreqκ
  have hctrκ : GleichAuf ((P.requires g).orte ++ (P.ensures g).orte) (σ.lese Λ args.orte)
      (W.lese Λ args.orte) := GleichAuf.mono (fun _ h => hctr h) hgκ
  have hreq0 := req_transfer hreqκ
    (GleichAuf.mono (fun _ h => List.mem_append_left _ h) hctrκ)
  refine ⟨⟨⟨[], W.lese Λ args.orte, hreq0, funk_nil, vertraegeOk_nil P, kurzH_nil _,
    GleichAuf.refl _ _, ⟨hFrag g, fuss_rumpf P g⟩, fun R _ => ZErg.gleich_refl _⟩,
    ⟨H, σ.lese Λ args.orte, hreq, hf, hv, kurzH_mono hk (lese_laenge _ _ _), hrc hok', hreqκ,
      hctrκ, ?_⟩, hSt⟩, hreq0⟩
  intro R hR σa v hRa
  rw [← hρk] at hRa
  obtain ⟨w1, w2⟩ := hweiter R σ σa v hRa
  exact ⟨fun hnw => ZErg.gleich_trans (heq' R hR) (ZErg.gleich_of_eq (w1 hnw)),
    fun l' Γ' Λ₁ Λ₂ τ restb k ρc' h he => ZErg.gleich_trans (heq' R hR)
      (ZErg.gleich_of_eq (w2 l' Γ' Λ₁ Λ₂ τ restb k ρc' h he))⟩

end Push
/-! ## 5. The acting thread keeps its replay -/

section Akteur

variable {P : Programm D} {O : Orakel D} {passes : Nat}

theorem teile2 {α : Type} {a b c S : List α} (h : a ++ b ++ c ⊆ S) :
    a ⊆ S ∧ b ⊆ S ∧ c ⊆ S := by
  simp only [List.append_subset] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem and_teile {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true :=
  Bool.and_eq_true _ _ |>.mp h

end Akteur
end Gabbro.Grammatik
