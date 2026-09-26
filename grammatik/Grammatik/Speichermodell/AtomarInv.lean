/-
  File:      Grammatik/Speichermodell/AtomarInv.lean
  Subject:   THE REPLAY WITH THE ATOMIC RELY, part 5: the invariant legs and the start legs
             over machine GX -- owed invariants at every logged value and reason return
             (`InvAmOrtG`, `InvAmGrundG`), the start function's completion (`StartEndeG`) and
             no start frame at a reason (`KeinStartGrundG`). The twins of ZielOrtInv.lean,
             ZielOrtInvGrund.lean and ZielOrtStart.lean over `KopfSA`. Opus lane O25b,
             2026-09-26. Standalone.
-/
import Grammatik.Speichermodell.AtomarW
import Grammatik.ZielOrtStart
import Grammatik.Zielsatz.Spec

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
  · exact absurd (List.mem_flatMap.mpr ⟨i, List.mem_filter.mpr ⟨hi, hs⟩, hc⟩) (hTV c h f).2.2

end Stabil

section Schritte

variable {P : Programm D} {O : Orakel D} {passes : Nat} {Q : AxEns D} {S : SperrInv D}
  {lok : D.Tab ⊕ D.Glob → Bool} {Tg : D.Tab ⊕ D.Glob → Prop}

/-- **The return leg for invariants** (as `popS_inv`), the returned expression's read recorded. -/
theorem popSA_inv (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hS : SperrInvOk S)
    {sp : Speicher D} (hsp : ∀ L, S.inv L sp = true)
    (hI : ∀ f, InvGutSA P passes Q S Tg f) {G : RufRahmenG D}
    {W : World D} (hG : KopfSA P O passes Q S lok Tg G W) {lr : Bool} {Γ : Ctx}
    {Λ : List (Res D)} {ρ : Env D Γ} {r : GRest D (vertragVon D G.f) lr Γ Λ}
    (hr : G.rest = ⟨lr, Γ, Λ, ρ, r⟩)
    (e : ErgExpr D Γ Λ (vertragVon D G.f).erg)
    (he : ∀ c ∈ e.orte, c ∈ stabilS P S lok G.f Λ ∨ Tg c)
    (hinv : ∀ i ∈ D.invs, schuldet G.f i = true → (P.invariante i).orte ⊆ stabilS P S lok G.f Λ)
    (hsem : ∀ (O' : Orakel D) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
      (U : Umwelt D) (A : AUmwelt D) (σ : World D), (semHA S O' U A passes R r σ ρ).gleich
        (.zurueck (leseA A σ Λ e.orte) (evalErg (leseA A σ Λ e.orte) e (leseA A σ Λ e.orte) ρ))) :
    InvAmRueck P G.f (W.lese Λ e.orte) := by
  obtain ⟨H, HA, HU, HX, σ, hreq, hf, hv, _, hfa, hra, hqa, _, hfu, hiu, _, ⟨hfx, hkx⟩, hg, _,
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
    (hF : KopfSA P O passes Q S lok Tg (M.faeden u).kopf (M.weltVon u))
    (hs : RufSchrittG P O passes M u M') :
    ∀ ev ∈ (M'.faeden u).log, ev ∈ (M.faeden u).log ∨
      ∀ (g : D.Fn) (rho : Env D (D.params g)) (v : ErgVal D (D.erg g)) (s0 s1 : World D),
        ev = RufEreignisF.rueck g rho v s0 s1 → InvAmRueck P g s1 := by
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

/-- **The reason-return leg for invariants** (as `popS_grund`). -/
theorem popSA_grund (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hS : SperrInvOk S)
    {sp : Speicher D} (hsp : ∀ L, S.inv L sp = true)
    (hIG : ∀ f, InvGutGrundA P passes Q S Tg f) {G : RufRahmenG D}
    {W : World D} (hG : KopfSA P O passes Q S lok Tg G W) {lr : Bool} {Γ : Ctx}
    {Λ : List (Res D)} {ρ : Env D Γ} {r : GRest D (vertragVon D G.f) lr Γ Λ}
    (hr : G.rest = ⟨lr, Γ, Λ, ρ, r⟩) (rg : Fin (vertragVon D G.f).gruende)
    (hinv : ∀ i ∈ D.invs, schuldet G.f i = true → (P.invariante i).orte ⊆ stabilS P S lok G.f Λ)
    (hsem : ∀ (O' : Orakel D) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
      (U : Umwelt D) (A : AUmwelt D) (σ : World D),
      (semHA S O' U A passes R r σ ρ).gleich (.grund σ rg)) :
    InvAmRueck P G.f W := by
  obtain ⟨H, HA, HU, HX, σ, hreq, hf, hv, _, hfa, hra, hqa, _, hfu, hiu, _, ⟨hfx, _⟩, hg, _,
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

/-- **One step and the logged reason returns** (as `invGrundLog_schritt`). -/
theorem invGrundLogA_schritt (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O)
    (hS : SperrInvOk S) {sp : Speicher D} (hsp : ∀ L, S.inv L sp = true)
    (hIG : ∀ f, InvGutGrundA P passes Q S Tg f) (hFS : ∀ f, FussSX P S lok Tg f)
    (hTV : ∀ c, Tg c → VertragsFrei P c)
    {M M' : RufMaschineG D} {u : Faden}
    (hF : KopfSA P O passes Q S lok Tg (M.faeden u).kopf (M.weltVon u))
    (hs : RufSchrittG P O passes M u M') :
    ∀ ev ∈ (M'.faeden u).log, ev ∈ (M.faeden u).log ∨
      ∀ (g : D.Fn) (rho : Env D (D.params g)) (r : Fin (D.gruende g)) (s0 s1 : World D),
        ev = RufEreignisF.grund g rho r s0 s1 → InvAmRueck P g s1 := by
  cases hs with
  | rueckGrund r hperm ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller hΛ g hfg
      rho hrho s0 hs0 rg hrg hn =>
    intro ev hev
    simp only [rufUpdateG_self] at hev
    rcases List.mem_cons.mp hev with rfl | hev
    · refine Or.inr fun g' rho' r' s0' s1' h => ?_
      simp only [RufEreignisF.grund.injEq] at h
      obtain ⟨rfl, -, -, -, rfl⟩ := h
      subst hfg
      exact popSA_grund hO hRL hQ hS hsp hIG hF hhead r
        (fun i hi hs => inv_stabilX (hFS _) hTV hperm hi hs)
        (fun O' R U A σ => semHA_rueckGrund S O' U A passes R r hperm σ ρ)
    · exact Or.inl hev
  | rueckConsGrund r hperm restk ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller hΛ
      g hfg rho hrho s0 hs0 rg hrg hn =>
    intro ev hev
    simp only [rufUpdateG_self] at hev
    rcases List.mem_cons.mp hev with rfl | hev
    · refine Or.inr fun g' rho' r' s0' s1' h => ?_
      simp only [RufEreignisF.grund.injEq] at h
      obtain ⟨rfl, -, -, -, rfl⟩ := h
      subst hfg
      exact popSA_grund hO hRL hQ hS hsp hIG hF hhead r
        (fun i hi hs => inv_stabilX (hFS _) hTV hperm hi hs)
        (fun O' R U A σ => semHA_rueckConsGrund S O' U A passes R r hperm restk σ ρ)
    · exact Or.inl hev
  | dannRetGrund r hperm restk kk ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller
      hΛ g hfg rho hrho s0 hs0 rg hrg hn =>
    intro ev hev
    simp only [rufUpdateG_self] at hev
    rcases List.mem_cons.mp hev with rfl | hev
    · refine Or.inr fun g' rho' r' s0' s1' h => ?_
      simp only [RufEreignisF.grund.injEq] at h
      obtain ⟨rfl, -, -, -, rfl⟩ := h
      subst hfg
      exact popSA_grund hO hRL hQ hS hsp hIG hF hhead r
        (fun i hi hs => inv_stabilX (hFS _) hTV hperm hi hs)
        (fun O' R U A σ => semHA_dannRetGrund S O' U A passes R r hperm restk kk σ ρ)
    · exact Or.inl hev
  | _ => ohneGrundA

/-- **A replayed head at a `return` meets `ensures` and its owed invariants** (as `kopfS_ret`). -/
theorem kopfSA_ret (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hS : SperrInvOk S)
    {sp : Speicher D} (hsp : ∀ L, S.inv L sp = true)
    (hK : ∀ f, KoerperGutSA P passes Q S Tg f) (hI : ∀ f, InvGutSA P passes Q S Tg f)
    (hFS : ∀ f, FussSX P S lok Tg f) (hTV : ∀ c, Tg c → VertragsFrei P c)
    {G : RufRahmenG D} {W : World D}
    (hG : KopfSA P O passes Q S lok Tg G W) {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ}
    {r : GRest D (vertragVon D G.f) l Γ Λ} (hr : G.rest = ⟨l, Γ, Λ, ρ, r⟩)
    (e : ErgExpr D Γ Λ (vertragVon D G.f).erg) (hk : RetKopf e r) :
    EnsAmRueck P G.f G.s0 (W.lese Λ e.orte) G.rho (evalErg (W.lese Λ e.orte) e (W.lese Λ e.orte) ρ) ∧
      InvAmRueck P G.f (W.lese Λ e.orte) := by
  obtain ⟨hperm, h | ⟨rest, h⟩ | ⟨Λ'', rest, k, h⟩⟩ := hk <;> subst h
  · have hok := kopfSA_okS hG hr
    exact ⟨popSA_ens hO hRL hQ hS hsp hK hG hr e (erg_stabilX (hFS _) e hok.2)
        (ens_stabilX (hFS _) hTV hperm)
        (fun O' R U A σ => semHA_rueck S O' U A passes R e hperm σ ρ),
      popSA_inv hO hRL hQ hS hsp hI hG hr e (erg_stabilX (hFS _) e hok.2)
        (fun i hi hs => inv_stabilX (hFS _) hTV hperm hi hs)
        (fun O' R U A σ => semHA_rueck S O' U A passes R e hperm σ ρ)⟩
  · have hok := okS_ende_cons (kopfSA_okS hG hr)
    exact ⟨popSA_ens hO hRL hQ hS hsp hK hG hr e (erg_stabilX (hFS _) e hok.2.1)
        (ens_stabilX (hFS _) hTV hperm)
        (fun O' R U A σ => semHA_rueckCons S O' U A passes R e hperm rest σ ρ),
      popSA_inv hO hRL hQ hS hsp hI hG hr e (erg_stabilX (hFS _) e hok.2.1)
        (fun i hi hs => inv_stabilX (hFS _) hTV hperm hi hs)
        (fun O' R U A σ => semHA_rueckCons S O' U A passes R e hperm rest σ ρ)⟩
  · have hok := okS_dann_cons (kopfSA_okS hG hr)
    exact ⟨popSA_ens hO hRL hQ hS hsp hK hG hr e (erg_stabilX (hFS _) e hok.2.1)
        (ens_stabilX (hFS _) hTV hperm)
        (fun O' R U A σ => semHA_dannRet S O' U A passes R e hperm rest k σ ρ),
      popSA_inv hO hRL hQ hS hsp hI hG hr e (erg_stabilX (hFS _) e hok.2.1)
        (fun i hi hs => inv_stabilX (hFS _) hTV hperm hi hs)
        (fun O' R U A σ => semHA_dannRet S O' U A passes R e hperm rest k σ ρ)⟩

end Schritte

/-! ## The legs over every GX run -/

section Lauf

variable {P : Programm D} {O : Orakel D} {passes : Nat} {Q : AxEns D} {S : SperrInv D}
  {K : Faden → D.Fn → Bool} {Tg : D.Tab ⊕ D.Glob → Prop}

/-- The bottom frame runs its start function on every GX run. -/
theorem wurzelFn_GX {sp : Speicher D} {init : Faden → Σ f : D.Fn, Env D (D.params f)}
    {M : RufMaschineG D} (hr : RufErreichbarGX P O passes Tg (RufStartG P sp init) M) :
    ∀ t, wurzelFn (M.faeden t) = (init t).1 := by
  induction hr with
  | start => intro t; rw [start_faden]; rfl
  | schritt M M' u _ hs ih =>
      obtain ⟨σ, M'', hs1, _, _, _, hfa, _, _⟩ := hs
      intro t
      rw [hfa]
      by_cases htu : t = u
      · subst htu
        rw [wurzelFn_schritt hs1]
        exact ih t
      · rw [rufSchrittG_fremd hs1 t htu]
        exact ih t

/-- **No start frame stands at a reason return**, on every GX run. -/
theorem keinStartGrundGX {sp : Speicher D} {init : Faden → Σ f : D.Fn, Env D (D.params f)}
    (hG : StartOhneGrund init) {M : RufMaschineG D}
    (hr : RufErreichbarGX P O passes Tg (RufStartG P sp init) M) : KeinStartGrundG M := by
  intro t hst l Γ Λ ρ r _ ⟨g, _, _⟩
  have hw := wurzelFn_GX hr t
  unfold wurzelFn at hw
  rw [hst] at hw
  have h0 : (vertragVon D (M.faeden t).kopf.f).gruende = 0 := by
    show D.gruende (M.faeden t).kopf.f = 0
    have e : (M.faeden t).kopf.f = (init t).1 := hw
    rw [e]
    exact hG t
  have hg : g.val < (vertragVon D (M.faeden t).kopf.f).gruende := g.2
  omega

/-- **EVERY CONTRACT LEG OVER GX.** On every machine GX reaches -- G with the shared atomics
    answered by the weak memory -- the conclusion of `ziel_ort_mehrfaden_ende` and its reason
    twin, from the obligation WITH the rely at every shared atomic read: contracts at every
    logged entry and return, every free lock's invariant in memory, no thread at a failing
    check, owed invariants at every logged value and reason return, the start function's
    `ensures` and invariants at its completion, and no start frame at a reason. -/
theorem ziel_ort_atomar_voll (P : Programm D) (O : Orakel D) (passes : Nat) (Q : AxEns D)
    (S : SperrInv D) {fs : List D.Fn} (K : Faden → D.Fn → Bool) (Tg : D.Tab ⊕ D.Glob → Prop)
    (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hlok : AxEnsLokal Q)
    (hS : SperrInvOk S) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hAbg : ∀ t, AbgK P fs (K t)) (hWurzel : ∀ t, K t (init t).1 = true)
    (hTA : ∀ c, Tg c → AtomarAusgenommen c) (hTV : ∀ c, Tg c → VertragsFrei P c)
    (hTS : ∀ c, Tg c → ∀ f Λ, c ∉ stabilS P S (lokK P K) f Λ)
    (hTO : ∀ c, Tg c → ∀ L, c ∉ S.orte L)
    (hFragS : ∀ f, (P.rumpf f).gOk (kandP P (fussOrteG P f)) (regP (sicher P (lokK P K) f)) = true)
    (hFS : ∀ f, FussSX P S (lokK P K) Tg f)
    (hK : ∀ f : D.Fn, KoerperGutSA P passes Q S Tg f)
    (hI : ∀ f : D.Fn, InvGutSA P passes Q S Tg f)
    (hIG : ∀ f : D.Fn, InvGutGrundA P passes Q S Tg f) (hStart : StartGut P sp init)
    (hsp : ∀ L, S.inv L sp = true) (hex : StartExklusiv init) (hGrund : StartOhneGrund init) :
    ∀ M : RufMaschineG D, RufErreichbarGX P O passes Tg (RufStartG P sp init) M →
      VertragAmOrtG P M ∧ SperrInvG S M ∧ KeinLogikHaltG O passes M ∧ InvAmOrtG P M ∧
      Zielsatz.InvAmGrundG P M ∧ StartEndeG P M ∧ KeinStartGrundG M := by
  have hZ := zielInvSA_erreichbarGX P O passes Q S K Tg sp init hO hRL hQ hlok hS hvoll hAbg
    hWurzel hTA hTV hTS hTO hFragS hFS hK hStart hsp hex
  intro M hr
  have hA := ziel_ort_atomar P O passes Q S K Tg sp init hO hRL hQ hlok hS hvoll hAbg hWurzel hTA
    hTV hTS hTO hFragS hFS hK hStart hsp hex M hr
  refine ⟨hA.1, hA.2.1, hA.2.2, ?_, ?_, ?_, keinStartGrundGX hGrund hr⟩
  · -- the logged value returns
    induction hr with
    | start =>
        intro t ev hev g rho v s0 s1 h
        subst h
        simp [RufStartG] at hev
    | schritt M M' u hr' hs ih =>
        have hA' := ziel_ort_atomar P O passes Q S K Tg sp init hO hRL hQ hlok hS hvoll hAbg hWurzel
          hTA hTV hTS hTO hFragS hFS hK hStart hsp hex M hr'
        have ih' := ih hA'
        obtain ⟨σ, M'', hs1, hσ, _, _, hfa, _, _⟩ := hs
        have hI0 := (hZ M hr').1.1 u
        have hFu1 : FadenSA P O passes Q S (lokK P K) Tg ((mitSpeicher M σ).faeden u)
            ((mitSpeicher M σ).weltVon u) :=
          fadenSA_speicher hI0 fun c hc => hσ c fun ht => hTS c ht _ _ hc
        intro t ev hev
        rw [hfa] at hev
        by_cases ht : t = u
        · subst ht
          rcases invLogA_schritt hO hRL hQ hS hsp hI hFS hTV hFu1.1 hs1 ev hev with h | h
          · exact ih' t ev h
          · exact h
        · rw [rufSchrittG_fremd hs1 t ht] at hev
          exact ih' t ev hev
  · -- the logged reason returns
    induction hr with
    | start =>
        intro t ev hev g rho r s0 s1 h
        subst h
        simp [RufStartG] at hev
    | schritt M M' u hr' hs ih =>
        have hA' := ziel_ort_atomar P O passes Q S K Tg sp init hO hRL hQ hlok hS hvoll hAbg hWurzel
          hTA hTV hTS hTO hFragS hFS hK hStart hsp hex M hr'
        have ih' := ih hA'
        obtain ⟨σ, M'', hs1, hσ, _, _, hfa, _, _⟩ := hs
        have hI0 := (hZ M hr').1.1 u
        have hFu1 : FadenSA P O passes Q S (lokK P K) Tg ((mitSpeicher M σ).faeden u)
            ((mitSpeicher M σ).weltVon u) :=
          fadenSA_speicher hI0 fun c hc => hσ c fun ht => hTS c ht _ _ hc
        intro t ev hev
        rw [hfa] at hev
        by_cases ht : t = u
        · subst ht
          rcases invGrundLogA_schritt hO hRL hQ hS hsp hIG hFS hTV hFu1.1 hs1 ev hev with h | h
          · exact ih' t ev h
          · exact h
        · rw [rufSchrittG_fremd hs1 t ht] at hev
          exact ih' t ev hev
  · -- the start function's completion
    intro t _ l Γ Λ ρ r e hr' hk
    exact kopfSA_ret hO hRL hQ hS hsp hK hI hFS hTV ((hZ M hr).1.1 t).1 hr' e hk

#print axioms Gabbro.Grammatik.ziel_ort_atomar_voll

end Lauf

end Gabbro.Grammatik
