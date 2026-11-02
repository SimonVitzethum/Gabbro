/-
  File:      Grammatik/Speichermodell/AtomarInv.lean
  Subject:   THE REPLAY WITH THE ATOMIC RELY, part 5: the invariant legs and the start legs
             over machine GX -- owed invariants at every logged value and reason return
             (`InvAmOrtG`, `InvAmGrundG`), the start function's completion (`StartEndeG`) and
             no start frame at a reason (`KeinStartGrundG`). The twins of ZielOrtInv.lean,
             ZielOrtInvGrund.lean and ZielOrtStart.lean over `KopfSA`. Opus lane O25b,
             2026-09-26. Standalone.
-/
module
public import Grammatik.Speichermodell.Atomar.AtomarW
public import Grammatik.Zielsatz.ZielOrt.Grundlage.Core.ZielOrtStart
public import Grammatik.Zielsatz.Kern.Spec
@[expose] public section


namespace Gabbro.Grammatik

variable {D : Deklaration}

section Stabil

variable {P : Programm D} {S : SperrInv D} {lok : D.Tab ⊕ D.Glob → Bool}
  {Tg : D.Tab ⊕ D.Glob → Prop} {f : D.Fn}

/-- **The carriers of an owed invariant are stable at a return** (shared atomics are in no
    invariant). -/
theorem inv_stabilX (hF : FussSX P S lok Tg f) (hTV : ∀ c, Tg c → VertragsFrei P c)
    {Λ : List (Res D)} (hperm : Λ.Perm (vertragVon D f).ende)
    {i : D.Inv} (hi : i ∈ D.invs) (hs : schuldet f i = true) :
    (P.invariante i).orte ⊆ stabilS P S lok f Λ := by
  intro c hc
  rcases stabil_of_fussX hF (fuss_teilG P f (fuss_inv P f hi hs hc)) (fun L hB => by
    obtain ⟨t, ht, hL⟩ := held_invSicht i L (bewacht_held ((P.invariante i).orte_darf c hc) hB)
    have h2 : L ∈ D.haelt f := D.invarianten_gehalten (D.sig f) i hs t ht L hL
    exact hperm.symm.mem_iff.mp (List.mem_append_left _ (List.mem_map.mpr ⟨L, h2, rfl⟩))) with h | h
  · exact h
  · exact absurd (List.mem_flatMap.mpr ⟨i, List.mem_filter.mpr ⟨hi, hs⟩, hc⟩) ((hTV c h).1 f).2.2

end Stabil

section Schritte

variable {P : Programm D} {O : Orakel D} {passes : Nat} {Q : AxEns D} {S : SperrInv D}
  {lok : D.Tab ⊕ D.Glob → Bool} {Tg : D.Tab ⊕ D.Glob → Prop} {m : Mass D} {zyk : D.Fn → D.Fn → Bool}

/-- **The return leg for invariants** (as `popS_inv`), the returned expression's read recorded. -/
theorem popSA_inv (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hS : SperrInvOk S)
    {sp : Speicher D} (hsp : ∀ L, S.inv L sp = true)
    (hI : ∀ f, InvGutSA P passes Q S Tg f) {G : RufRahmenG D}
    {W : World D} (hG : KopfSA P O passes Q S lok Tg m zyk G W) {lr : Bool} {Γ : Ctx}
    {Λ : List (Res D)} {ρ : Env D Γ} {r : GRest D (vertragVon D G.f) lr Γ Λ}
    (hr : G.rest = ⟨lr, Γ, Λ, ρ, r⟩)
    (e : ErgExpr D Γ Λ (vertragVon D G.f).erg)
    (he : ∀ c ∈ e.orte, c ∈ stabilS P S lok G.f Λ ∨ Tg c)
    (hinv : ∀ i ∈ D.invs, schuldet G.f i = true → (P.invariante i).orte ⊆ stabilS P S lok G.f Λ)
    (hsem : ∀ (O' : Orakel D) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
      (U : Umwelt D) (A : AUmwelt D) (σ : World D), (semHA S O' U A passes R r σ ρ).gleich
        (.zurueck (leseA A σ Λ e.orte) (evalErg (leseA A σ Λ e.orte) e (leseA A σ Λ e.orte) ρ))) :
    InvAmRueck P G.f (W.lese Λ e.orte) := by
  obtain ⟨H, HA, HU, HX, σ, hreq, hf, hv, hm, _, hfa, hra, hqa, _, hfu, hiu, _, ⟨hfx, hkx⟩, hg, _,
    heq⟩ := hG
  obtain ⟨HX', hfx', _, hsub, hrec⟩ := lese_schritt Tg hfx hkx Λ e.orte W.speicher
  have hPX := umweltAusA_passt Tg hfx'
  have hHA := umweltAusA_ok Tg HX'
  have h1 := heq (rufAusV H) (orakelAus O HA) (umweltAus S sp HU) (umweltAusA Tg HX')
    (rufAusV_passt hf) (orakelAus_passt O hfa) (umweltAus_passt S sp hfu) (passtX_teil hsub hPX)
    hHA (gleichRS_orakelAus O HA)
  rw [hr] at h1 hg
  simp only at h1 hg
  have h2 := ZErgG.folgt_zurueck (ZErgG.folgt_trans h1
    (ZErgG.folgt_of_gleich (hsem _ _ _ (umweltAusA Tg HX') σ)))
  obtain ⟨σ'', hex, hsg⟩ := zErgG_gleich_zurueck h2
  have hE := (hI G.f) (orakelAus O HA) (orakelAus_rahmen hO hra) (regLokal_orakelAus hRL HA)
    (orakelAus_vertrag hQ hqa) (umweltAus S sp HU) (umweltAus_ok hS hsp hiu) (umweltAusA Tg HX')
    hHA (rufAusV H) (rufAusV_rahmen hv) (rufAusV_ohneVorbedingung hv.1) G.s0 G.rho hreq σ'' _ hex
  rw [hrec _ hPX hHA] at hsg
  have hgl := mischT_gleichAuf hg he Λ Λ
  have hG2 : GleichAuf (stabilS P S lok G.f Λ) σ'' (W.lese Λ e.orte) :=
    (gleichAuf_SG hsg).trans (GleichAuf.mono (fun _ h => List.mem_append_left _ h) hgl)
  intro i hi hs
  have h3 := hE i hi hs
  unfold InvHaelt at h3 ⊢
  rw [← eval_gleichAuf (P.invariante i) (fun _ h => hinv i hi hs h) hG2 .nil]
  exact h3

set_option hygiene false in
/-- A step that logs no `rueck` event keeps the claim. -/
macro "ohneRueckA" : tactic => `(tactic| (
  intro ev hev
  simp only [rufUpdateG_self] at hev
  first
  | exact Or.inl hev
  | (rcases List.mem_cons.mp hev with rfl | hev
     · exact Or.inr (fun _ _ _ _ _ h => by cases h)
     · exact Or.inl hev)))

/-- **One step and the logged returns** (as `invLog_schritt`). -/
theorem invLogA_schritt (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hS : SperrInvOk S)
    {sp : Speicher D} (hsp : ∀ L, S.inv L sp = true)
    (hI : ∀ f, InvGutSA P passes Q S Tg f) (hFS : ∀ f, FussSX P S lok Tg f)
    (hTV : ∀ c, Tg c → VertragsFrei P c)
    {M M' : RufMaschineG D} {u : Faden}
    (hF : KopfSA P O passes Q S lok Tg m zyk (M.faeden u).kopf (M.weltVon u))
    (hs : RufSchrittG P O passes M u M') :
    ∀ ev ∈ (M'.faeden u).log, ev ∈ (M.faeden u).log ∨
      ∀ (g : D.Fn) (rho : Env D (D.params g)) (v : ErgVal D (D.erg g)) (s0 s1 : World D),
        ev = RufEreignisF.rueck g rho v s0 s1 → InvAmRueck P g s1 := by
  cases hs with
  | g1 hs =>
    cases hs with
    | rueck caller rst hpop Γ Λ e hperm ρ hhead g hfg rho hrho s0 hs0 hΛ s1 hs1 v hv neu hneu hnw =>
      intro ev hev
      simp only [rufUpdateG_self] at hev
      rcases List.mem_cons.mp hev with rfl | hev
      · refine Or.inr fun g' rho' v' s0' s1' h => ?_
        simp only [RufEreignisF.rueck.injEq] at h
        obtain ⟨rfl, -, -, -, rfl⟩ := h
        subst hfg hs1
        exact popSA_inv hO hRL hQ hS hsp hI hF hhead e
          (erg_stabilX (hFS _) e (kopfSA_okS hF hhead).2)
          (fun i hi hs => inv_stabilX (hFS _) hTV hperm hi hs)
          (fun O' R U A σ => semHA_rueck S O' U A passes R e hperm σ ρ)
      · exact Or.inl hev
    | _ => ohneRueckA
  | g2 hs =>
    cases hs with
    | _ => ohneRueckA
  | g3 hs =>
    cases hs with
    | rueckBind caller rst hpop l Γ Λ Λ' τ restb k ρc hcaller Γc Λc e hperm ρ hhead g hfg rho hrho
        s0 hs0 hΛ s1 hs1 v hv he neu hneu =>
      intro ev hev
      simp only [rufUpdateG_self] at hev
      rcases List.mem_cons.mp hev with rfl | hev
      · refine Or.inr fun g' rho' v' s0' s1' h => ?_
        simp only [RufEreignisF.rueck.injEq] at h
        obtain ⟨rfl, -, -, -, rfl⟩ := h
        subst hfg hs1
        exact popSA_inv hO hRL hQ hS hsp hI hF hhead e
          (erg_stabilX (hFS _) e (kopfSA_okS hF hhead).2)
          (fun i hi hs => inv_stabilX (hFS _) hTV hperm hi hs)
          (fun O' R U A σ => semHA_rueck S O' U A passes R e hperm σ ρ)
      · exact Or.inl hev
    | _ => ohneRueckA
  | g4 hs =>
    cases hs with
    | rueckCons caller rst hpop Γ Λ e hperm rest ρ hhead g hfg rho hrho s0 hs0 hΛ s1 hs1 v hv neu
        hneu hnw =>
      intro ev hev
      simp only [rufUpdateG_self] at hev
      rcases List.mem_cons.mp hev with rfl | hev
      · refine Or.inr fun g' rho' v' s0' s1' h => ?_
        simp only [RufEreignisF.rueck.injEq] at h
        obtain ⟨rfl, -, -, -, rfl⟩ := h
        subst hfg hs1
        exact popSA_inv hO hRL hQ hS hsp hI hF hhead e
          (erg_stabilX (hFS _) e (okS_ende_cons (kopfSA_okS hF hhead)).2.1)
          (fun i hi hs => inv_stabilX (hFS _) hTV hperm hi hs)
          (fun O' R U A σ => semHA_rueckCons S O' U A passes R e hperm rest σ ρ)
      · exact Or.inl hev
    | dannRet l Γ Λ Λ'' e hperm rest k ρ hhead caller rst hpop hΛ s1 hs1 g hfg rho hrho s0 hs0 v hv
        neu hneu hnw =>
      intro ev hev
      simp only [rufUpdateG_self] at hev
      rcases List.mem_cons.mp hev with rfl | hev
      · refine Or.inr fun g' rho' v' s0' s1' h => ?_
        simp only [RufEreignisF.rueck.injEq] at h
        obtain ⟨rfl, -, -, -, rfl⟩ := h
        subst hfg hs1
        exact popSA_inv hO hRL hQ hS hsp hI hF hhead e
          (erg_stabilX (hFS _) e (okS_dann_cons (kopfSA_okS hF hhead)).2.1)
          (fun i hi hs => inv_stabilX (hFS _) hTV hperm hi hs)
          (fun O' R U A σ => semHA_dannRet S O' U A passes R e hperm rest k σ ρ)
      · exact Or.inl hev
    | dannRetBind lk Γk Λk Λk'' e hperm restk kk ρ hhead caller rst hpop l Γ Λ Λ' τ restb k ρc
        hcaller hΛ s1 hs1 g hfg rho hrho s0 hs0 v hv he neu hneu =>
      intro ev hev
      simp only [rufUpdateG_self] at hev
      rcases List.mem_cons.mp hev with rfl | hev
      · refine Or.inr fun g' rho' v' s0' s1' h => ?_
        simp only [RufEreignisF.rueck.injEq] at h
        obtain ⟨rfl, -, -, -, rfl⟩ := h
        subst hfg hs1
        exact popSA_inv hO hRL hQ hS hsp hI hF hhead e
          (erg_stabilX (hFS _) e (okS_dann_cons (kopfSA_okS hF hhead)).2.1)
          (fun i hi hs => inv_stabilX (hFS _) hTV hperm hi hs)
          (fun O' R U A σ => semHA_dannRet S O' U A passes R e hperm restk kk σ ρ)
      · exact Or.inl hev
    | rueckConsBind lk Γk Λk e hperm restk ρ hhead caller rst hpop l Γ Λ Λ' τ restb k ρc hcaller
        hΛ s1 hs1 g hfg rho hrho s0 hs0 v hv he neu hneu =>
      intro ev hev
      simp only [rufUpdateG_self] at hev
      rcases List.mem_cons.mp hev with rfl | hev
      · refine Or.inr fun g' rho' v' s0' s1' h => ?_
        simp only [RufEreignisF.rueck.injEq] at h
        obtain ⟨rfl, -, -, -, rfl⟩ := h
        subst hfg hs1
        exact popSA_inv hO hRL hQ hS hsp hI hF hhead e
          (erg_stabilX (hFS _) e (okS_ende_cons (kopfSA_okS hF hhead)).2.1)
          (fun i hi hs => inv_stabilX (hFS _) hTV hperm hi hs)
          (fun O' R U A σ => semHA_rueckCons S O' U A passes R e hperm restk σ ρ)
      · exact Or.inl hev
    | _ => ohneRueckA
  | g5 hs =>
    cases hs with
    | _ => ohneRueckA
  | g6 hs =>
    cases hs with
    | _ => ohneRueckA

end Schritte
end Gabbro.Grammatik
