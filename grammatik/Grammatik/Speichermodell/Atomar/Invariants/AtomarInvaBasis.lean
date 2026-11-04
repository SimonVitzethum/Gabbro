module

public import Grammatik.Speichermodell.Atomar.Invariants.AtomarInv

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}
section Schritte
variable {P : Programm D} {O : Orakel D} {passes : Nat} {Q : AxEns D} {S : SperrInv D}
  {lok : D.Tab ⊕ D.Glob → Bool} {Tg : D.Tab ⊕ D.Glob → Prop} {m : Mass D} {zyk : D.Fn → D.Fn → Bool}

/-- **The reason-return leg for invariants** (as `popS_grund`). -/
theorem popSA_grund (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hS : SperrInvOk S)
    {sp : Speicher D} (hsp : ∀ L, S.inv L sp = true)
    (hIG : ∀ f, InvGutGrundA P passes Q S Tg f) {G : RufRahmenG D}
    {W : World D} (hG : KopfSA P O passes Q S lok Tg m zyk G W) {lr : Bool} {Γ : Ctx}
    {Λ : List (Res D)} {ρ : Env D Γ} {r : GRest D (vertragVon D G.f) lr Γ Λ}
    (hr : G.rest = ⟨lr, Γ, Λ, ρ, r⟩) (rg : Fin (vertragVon D G.f).gruende)
    (hinv : ∀ i ∈ D.invs, schuldet G.f i = true → (P.invariante i).orte ⊆ stabilS P S lok G.f Λ)
    (hsem : ∀ (O' : Orakel D) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
      (U : Umwelt D) (A : AUmwelt D) (σ : World D),
      (semHA S O' U A passes R r σ ρ).gleich (.why σ rg)) :
    InvAmRueck P G.f W := by
  obtain ⟨H, HA, HU, HX, σ, hreq, hf, hv, hm, _, hfa, hra, hqa, _, hfu, hiu, _, ⟨hfx, _⟩, hg, _,
    heq⟩ := hG
  have hPX := umweltAusA_passt Tg hfx
  have hHA := umweltAusA_ok Tg HX
  have h1 := heq (rufAusV H) (orakelAus O HA) (umweltAus S sp HU) (umweltAusA Tg HX)
    (rufAusV_passt hf) (orakelAus_passt O hfa) (umweltAus_passt S sp hfu) hPX hHA
    (gleichRS_orakelAus O HA)
  rw [hr] at h1 hg
  simp only at h1 hg
  have h2 := ZErgG.folgt_grund (ZErgG.folgt_trans h1
    (ZErgG.folgt_of_gleich (hsem _ _ _ (umweltAusA Tg HX) σ)))
  obtain ⟨σ'', hex, hsg⟩ := zErgG_gleich_grund h2
  have hE := (hIG G.f) (orakelAus O HA) (orakelAus_rahmen hO hra) (regLokal_orakelAus hRL HA)
    (orakelAus_vertrag hQ hqa) (umweltAus S sp HU) (umweltAus_ok hS hsp hiu) (umweltAusA Tg HX)
    hHA (rufAusV H) (rufAusV_rahmen hv) (rufAusV_ohneVorbedingung hv.1) G.s0 G.rho hreq σ'' rg hex
  have hG2 : GleichAuf (stabilS P S lok G.f Λ) σ'' W := (gleichAuf_SG hsg).trans hg
  intro i hi hs
  have h3 := hE i hi hs
  unfold InvHaelt at h3 ⊢
  rw [← eval_gleichAuf (P.invariante i) (fun _ h => hinv i hi hs h) hG2 .nil]
  exact h3

set_option hygiene false in
/-- A step that logs no `grund` event keeps the claim. -/
macro "ohneGrundA" : tactic => `(tactic| (
  intro ev hev
  simp only [rufUpdateG_self] at hev
  first
  | exact Or.inl hev
  | (rcases List.mem_cons.mp hev with rfl | hev
     · exact Or.inr (fun _ _ _ _ _ h => by cases h)
     · exact Or.inl hev)))

/-- Root delivery retains the log; caller delivery records exactly its answer channel. -/
private theorem antwort_invGrundLogA {z z' : RufFadenG D} {vor W : World D}
    {a : ErgVal D (vertragVon D z.kopf.f).erg ⊕ Fin (vertragVon D z.kopf.f).gruende}
    (ha : rufAntwortG z vor W a = some z')
    (hinv : ∀ r, a = .inr r → InvAmRueck P z.kopf.f W) :
    ∀ ev ∈ z'.log, ev ∈ z.log ∨
      ∀ (g : D.Fn) (rho : Env D (D.params g)) (r : Fin (D.gruende g)) (s0 s1 : World D),
        ev = RufEreignisF.why g rho r s0 s1 → InvAmRueck P g s1 := by
  cases hs : z.stapel with
  | nil =>
      simp only [rufAntwortG, hs, Option.some.injEq] at ha
      subst z'
      exact fun _ hev => Or.inl hev
  | cons caller rest =>
      cases hr : antwortRestG z.kopf.f a caller.rest with
      | none => simp [rufAntwortG, hs, hr] at ha
      | some response =>
          simp [rufAntwortG, hs, hr] at ha
          subst z'
          intro ev hev
          rcases List.mem_cons.mp hev with rfl | hev
          · refine Or.inr fun g rho r s0 s1 h => ?_
            cases a with
            | inl value => cases h
            | inr reason =>
                simp only [RufEreignisF.why.injEq] at h
                obtain ⟨rfl, -, -, -, rfl⟩ := h
                exact hinv reason rfl
          · exact Or.inl hev

/-- The last release preserves the saved reason and its owed invariants. -/
private theorem popSA_last_grund (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O)
    (hS : SperrInvOk S) {sp : Speicher D} (hsp : ∀ L, S.inv L sp = true)
    (hK : ∀ f, KoerperGutSA P passes Q S Tg f)
    (hIG : ∀ f, InvGutGrundA P passes Q S Tg f) (hFS : ∀ f, FussSX P S lok Tg f)
    (hTV : ∀ c, Tg c → VertragsFrei P c)
    {F : RufRahmenG D} {W : World D} (hF : KopfSA P O passes Q S lok Tg m zyk F W)
    {l : Bool} {Γ : Ctx} (ρ : Env D Γ) (r : Fin (vertragVon D F.f).gruende)
    (vor : World D) (L : D.Lock)
    (hr : F.rest = ⟨l, Γ, _, ρ, .aufraeumen ⟨.inr r, vor⟩ [L]⟩) :
    InvAmRueck P F.f (W.gibt L) := by
  have hW := kopfSA_frei_inv hO hRL hQ hS hsp hK hF L List.mem_cons_self hr
    (fun O' U A calls σ hi => by rw [semHA_aufraeumen_freigabe, hi]; rfl)
  obtain ⟨H, HA, HU, HX, σ, hreq, hf, hv, _, _, hfa, hra, hqa, _, hfu, hiu, _,
    ⟨hfx, _⟩, hg, _, heq⟩ := hF
  have h1 := heq (rufAusV H) (orakelAus O HA) (umweltAus S sp HU) (umweltAusA Tg HX)
    (rufAusV_passt hf) (orakelAus_passt O hfa) (umweltAus_passt S sp hfu)
    (umweltAusA_passt Tg hfx) (umweltAusA_ok Tg HX) (gleichRS_orakelAus O HA)
  rw [hr] at h1 hg
  have hiσ : S.inv L σ.speicher = true := (inv_gleich hS List.mem_cons_self hg).trans hW
  rw [semHA_aufraeumen_freigabe, hiσ] at h1
  simp only [ite_true, semHA, weiterHA, scopesInvH, List.all_nil, List.foldl_nil] at h1
  obtain ⟨σ', hex, hsg⟩ := zErgG_gleich_grund (ZErgG.folgt_grund h1)
  have hInv := (hIG F.f) (orakelAus O HA) (orakelAus_rahmen hO hra)
    (regLokal_orakelAus hRL HA) (orakelAus_vertrag hQ hqa)
    (umweltAus S sp HU) (umweltAus_ok hS hsp hiu) (umweltAusA Tg HX) (umweltAusA_ok Tg HX)
    (rufAusV H) (rufAusV_rahmen hv) (rufAusV_ohneVorbedingung hv.1) F.s0 F.rho hreq σ' r hex
  have hgl : GleichAuf (stabilS P S lok F.f (vertragVon D F.f).ende)
      (σ.gibt L) (W.gibt L) :=
    GleichAuf.mono (stabilS_mono (fun _ h => List.mem_cons_of_mem _ h)) hg
  intro i hi hs
  have h3 := hInv i hi hs
  unfold InvHaelt at h3 ⊢
  rw [← eval_gleichAuf (P.invariante i)
    (fun _ h => inv_stabilX (hFS _) hTV (List.Perm.refl _) hi hs h)
    ((gleichAuf_SG hsg).trans hgl) .nil]
  exact h3

end Schritte
end Gabbro.Grammatik
