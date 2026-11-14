/-
  Gabbro/Grammatik/ZielOrtInv.lean

  **Table and group invariants on machine G** (THEOREM-MAP §13.5 first item,
  carried in §15.4).

  The sequential program semantics checks, at every return of `f` in
  `rufAt`, each declared invariant `f` OWES (`schuldet f i`: `f` writes one
  of its carriers) and answers `logik (invariante i)` where it is false.
  Machine G tests no invariant, and `ziel_ort_sperre` said nothing about
  them: a program whose functions break a declared invariant was
  certified.

  Carried here like the lock invariants of §14 -- an obligation and a
  conclusion:

  * the obligation `InvGutS P passes Q S f` (per function, SEQUENTIAL,
    against the same oracles, environment moves and handlers as
    `KoerperGutS`): from `requires f`, a normal return of the body makes
    every invariant `f` owes true at the return world;
  * the conclusion `InvAmOrtG P M`: on every reachable machine, at every
    logged return `rueck g rho v s0 s1`, every invariant `g` owes holds at
    the logged return world `s1`.

  The carriers of an owed invariant are in the footprint (`fuss_inv`,
  `ZielOrtBeweis.lean`), so `fussSperreB` checks them, and at a return they
  are stable (`inv_stabil`): their guards are signature locks of `f`
  (`Deklaration.invarianten_gehalten`, the declaration's `U003`), held at
  `ret`. The replay's sequential return world then agrees with the machine's
  on them (`popS_inv`, the invariant twin of `popS_ens`).
-/
module
public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtSperre
@[expose] public section


namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. The predicates -/

/-- The invariant `i` holds in the world `σ`. -/
def InvHaelt (P : Programm D) (i : D.Inv) (σ : World D) : Prop :=
  wahr? (eval σ (P.invariante i) σ .nil) = true

/-- Every invariant `f` owes holds in `σ`: what `rufAt` checks at `f`'s
    return. -/
def InvAmRueck (P : Programm D) (f : D.Fn) (σ : World D) : Prop :=
  ∀ i ∈ D.invs, schuldet f i = true → InvHaelt P i σ

/-- **The obligation for invariants**, per function, over the SEQUENTIAL
    semantics with lock invariants (the class of `KoerperGutS`'s first
    part): from `requires f`, a normal return of the body satisfies every
    invariant `f` owes. An invariant needed at entry is the user's to put
    into `requires` (the program semantics assumes none at entry either). -/
def InvGutS (P : Programm D) (passes : Nat) (Q : AxEns D) (S : SperrInv D) (f : D.Fn) : Prop :=
  ∀ O' : Orakel D, RahmenO O' → RegLokal O' → AxVertragOP (PreQ P) Q O' →
    ∀ U : Umwelt D, HavocOk S U →
    ∀ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f),
      RespektiertRahmen P R → OhneVorbedingung R →
      ∀ (σ : World D) (ρ : Env D (D.params f)), ReqAmEintritt P f σ ρ →
        ∀ (σ' : World D) (v : ErgVal D (D.erg f)),
          execEndH (V := vertragVon D f) S O' U passes R (P.rumpf f) σ ρ =
            EndAusgang.zurueck σ' v → InvAmRueck P f σ'

/-- **The conclusion for invariants**: at every logged return, every
    invariant the returning function owes holds at the logged world. -/
def InvAmOrtG (P : Programm D) (M : RufMaschineG D) : Prop :=
  ∀ (t : Faden) (ev : RufEreignisF D), ev ∈ (M.faeden t).log →
    ∀ (g : D.Fn) (rho : Env D (D.params g)) (v : ErgVal D (D.erg g)) (s0 s1 : World D),
      ev = RufEreignisF.rueck g rho v s0 s1 → InvAmRueck P g s1

/-- A function that owes no invariant owes nothing new. -/
theorem invGutS_ohne {P : Programm D} {passes : Nat} {Q : AxEns D} {S : SperrInv D} {f : D.Fn}
    (h : ∀ i ∈ D.invs, schuldet f i = false) : InvGutS P passes Q S f := by
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ i hi hs
  rw [h i hi] at hs
  cases hs

/-! ## 2. Owed invariant carriers are stable at a return -/

/-- **The carriers of an owed invariant are stable at `ret`**: they are in
    the footprint, and every guard of theirs is a signature lock of `f`
    (`invarianten_gehalten`), held at the return. -/
theorem inv_stabil {P : Programm D} {S : SperrInv D} {lok : D.Tab ⊕ D.Glob → Bool} {f : D.Fn}
    (hF : FussS P S lok f) {Λ : List (Res D)} (hperm : Λ.Perm (vertragVon D f).ende)
    {i : D.Inv} (hi : i ∈ D.invs) (hs : schuldet f i = true) :
    (P.invariante i).orte ⊆ stabilS P S lok f Λ :=
  fun c hc => stabil_of_fuss hF (fuss_teilG P f (fuss_inv P f hi hs hc)) fun L hB => by
    obtain ⟨t, ht, hL⟩ := held_invSicht i L (bewacht_held ((P.invariante i).orte_darf c hc) hB)
    have h2 : L ∈ D.haelt f := D.invarianten_gehalten (D.sig f) i hs t ht L hL
    exact hperm.symm.mem_iff.mp (List.mem_append_left _ (List.mem_map.mpr ⟨L, h2, rfl⟩))

/-! ## 3. The return leg -/

section Schritte

variable {P : Programm D} {O : Orakel D} {passes : Nat} {Q : AxEns D} {S : SperrInv D}
  {lok : D.Tab ⊕ D.Glob → Bool}

/-- **The return leg for invariants** (the twin of `popS_ens`): a replayed
    head at a return owes its invariants at the machine's return world. -/
theorem popS_inv (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hS : SperrInvOk S)
    {sp : Speicher D} (hsp : ∀ L, S.inv L sp = true)
    (hI : ∀ f, InvGutS P passes Q S f) {G : RufRahmenG D}
    {W : World D} (hG : KopfS P O passes Q S lok G W) {lr : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {ρ : Env D Γ} {r : GRest D (vertragVon D G.f) lr Γ Λ} (hr : G.rest = ⟨lr, Γ, Λ, ρ, r⟩)
    (e : ErgExpr D Γ Λ (vertragVon D G.f).erg)
    (hinv : ∀ i ∈ D.invs, schuldet G.f i = true → (P.invariante i).orte ⊆ stabilS P S lok G.f Λ)
    (hsem : ∀ (O' : Orakel D) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
      (U : Umwelt D) (σ : World D), (semH S O' U passes R r σ ρ).gleich
        (.zurueck (σ.lese Λ e.orte) (evalErg (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ))) :
    InvAmRueck P G.f (W.lese Λ e.orte) := by
  obtain ⟨H, HA, HU, σ, hreq, hf, hv, _, hfa, hra, hqa, _, hfu, hiu, _, hg, _, heq⟩ := hG
  have h1 := heq (rufAusV H) (orakelAus O HA) (umweltAus S sp HU) (rufAusV_passt hf)
    (orakelAus_passt O hfa) (umweltAus_passt S sp hfu) (gleichRS_orakelAus O HA)
  rw [hr] at h1 hg
  simp only at h1 hg
  have h2 := ZErgG.folgt_zurueck (ZErgG.folgt_trans h1 (ZErgG.folgt_of_gleich (hsem _ _ _ σ)))
  obtain ⟨σ'', hex, hsg⟩ := zErgG_gleich_zurueck h2
  have hE := (hI G.f) (orakelAus O HA) (orakelAus_rahmen hO hra) (regLokal_orakelAus hRL HA)
    (orakelAus_vertragOP (axVertragOP_of_O _ hQ) hqa) (umweltAus S sp HU) (umweltAus_ok hS hsp hiu) (rufAusV H)
    (rufAusV_rahmen hv) (rufAusV_ohneVorbedingung hv.1) G.s0 G.rho hreq σ'' _ hex
  have hgl : GleichAuf (stabilS P S lok G.f Λ) (σ.lese Λ e.orte) (W.lese Λ e.orte) :=
    hg.lese Λ Λ e.orte e.orte
  have hG2 : GleichAuf (stabilS P S lok G.f Λ) σ'' (W.lese Λ e.orte) := (gleichAuf_SG hsg).trans hgl
  intro i hi hs
  have h3 := hE i hi hs
  unfold InvHaelt at h3 ⊢
  rw [← eval_gleichAuf (P.invariante i) (fun _ h => hinv i hi hs h) hG2 .nil]
  exact h3

/-- A root retains its log; a caller receives exactly the saved answer's event. -/
private theorem antwort_invLogS {z z' : RufFadenG D} {vor W : World D}
    {a : ErgVal D (vertragVon D z.kopf.f).erg ⊕ Fin (vertragVon D z.kopf.f).gruende}
    (ha : rufAntwortG z vor W a = some z')
    (hinv : ∀ v, a = .inl v → InvAmRueck P z.kopf.f W) :
    ∀ ev ∈ z'.log, ev ∈ z.log ∨
      ∀ (g : D.Fn) (rho : Env D (D.params g)) (v : ErgVal D (D.erg g)) (s0 s1 : World D),
        ev = RufEreignisF.rueck g rho v s0 s1 → InvAmRueck P g s1 := by
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
          · refine Or.inr fun g rho v s0 s1 h => ?_
            cases a with
            | inl value =>
                simp only [RufEreignisF.rueck.injEq] at h
                obtain ⟨rfl, -, -, -, rfl⟩ := h
                exact hinv value rfl
            | inr reason => cases h
          · exact Or.inl hev

/-- The final release checks its actual replay guard and delivers the saved value. -/
private theorem popS_last_inv (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O)
    (hS : SperrInvOk S) {sp : Speicher D} (hsp : ∀ L, S.inv L sp = true)
    (hK : ∀ f, KoerperGutS P passes Q S f)
    (hI : ∀ f, InvGutS P passes Q S f) (hFS : ∀ f, FussS P S lok f)
    {F : RufRahmenG D} {W : World D} (hF : KopfS P O passes Q S lok F W)
    {l : Bool} {Γ : Ctx} (ρ : Env D Γ) (v : ErgVal D (vertragVon D F.f).erg)
    (vor : World D) (L : D.Lock)
    (hr : F.rest = ⟨l, Γ, _, ρ, .aufraeumen ⟨.inl v, vor⟩ [L]⟩) :
    InvAmRueck P F.f (W.gibt L) := by
  have hW := kopfS_frei_inv hO hRL hQ hS hsp hK hF L List.mem_cons_self hr
    (fun O' U calls σ hi => by rw [semH_aufraeumen_freigabe, hi]; rfl)
  obtain ⟨H, HA, HU, σ, hreq, hf, hv, _, hfa, hra, hqa, _, hfu, hiu, _, hg, _, heq⟩ := hF
  have h1 := heq (rufAusV H) (orakelAus O HA) (umweltAus S sp HU) (rufAusV_passt hf)
    (orakelAus_passt O hfa) (umweltAus_passt S sp hfu) (gleichRS_orakelAus O HA)
  rw [hr] at h1 hg
  have hiσ : S.inv L σ.speicher = true := (inv_gleich hS List.mem_cons_self hg).trans hW
  rw [semH_aufraeumen_freigabe, hiσ] at h1
  simp only [ite_true, semH, weiterH, scopesInvH, List.all_nil, List.foldl_nil] at h1
  obtain ⟨σ', hex, hsg⟩ := zErgG_gleich_zurueck (ZErgG.folgt_zurueck h1)
  have hInv := (hI F.f) (orakelAus O HA) (orakelAus_rahmen hO hra)
    (regLokal_orakelAus hRL HA) (orakelAus_vertragOP (axVertragOP_of_O _ hQ) hqa)
    (umweltAus S sp HU) (umweltAus_ok hS hsp hiu)
    (rufAusV H) (rufAusV_rahmen hv) (rufAusV_ohneVorbedingung hv.1) F.s0 F.rho hreq σ' v hex
  have hgl : GleichAuf (stabilS P S lok F.f (vertragVon D F.f).ende)
      (σ.gibt L) (W.gibt L) :=
    GleichAuf.mono (stabilS_mono (fun _ h => List.mem_cons_of_mem _ h)) hg
  intro i hi hs
  have h3 := hInv i hi hs
  unfold InvHaelt at h3 ⊢
  rw [← eval_gleichAuf (P.invariante i)
    (fun _ h => inv_stabil (hFS _) (List.Perm.refl _) hi hs h)
    ((gleichAuf_SG hsg).trans hgl) .nil]
  exact h3

set_option hygiene false in
/-- A step that logs no `rueck` event keeps the claim. -/
macro "ohneRueck" : tactic => `(tactic| (
  intro ev hev
  simp only [rufUpdateG_self] at hev
  first
  | exact Or.inl hev
  | (rcases List.mem_cons.mp hev with rfl | hev
     · exact Or.inr (fun _ _ _ _ _ h => by cases h)
     · exact Or.inl hev)))

/-- **One step and the logged returns**: every event of the acting thread
    after the step is an old event, or a return whose function owes its
    invariants at the logged world. -/
theorem invLog_schritt (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hS : SperrInvOk S)
    {sp : Speicher D} (hsp : ∀ L, S.inv L sp = true)
    (hK : ∀ f, KoerperGutS P passes Q S f)
    (hI : ∀ f, InvGutS P passes Q S f) (hFS : ∀ f, FussS P S lok f)
    {M M' : RufMaschineG D} {u : Faden}
    (hF : KopfS P O passes Q S lok (M.faeden u).kopf (M.weltVon u))
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
        exact popS_inv hO hRL hQ hS hsp hI hF hhead e (fun i hi hs => inv_stabil (hFS _) hperm hi hs)
          (fun O' R U σ => semH_rueck S O' U passes R e hperm σ ρ)
      · exact Or.inl hev
    | _ => ohneRueck
  | g2 hs =>
    cases hs with
    | _ => ohneRueck
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
        exact popS_inv hO hRL hQ hS hsp hI hF hhead e (fun i hi hs => inv_stabil (hFS _) hperm hi hs)
          (fun O' R U σ => semH_rueck S O' U passes R e hperm σ ρ)
      · exact Or.inl hev
    | _ => ohneRueck
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
        exact popS_inv hO hRL hQ hS hsp hI hF hhead e (fun i hi hs => inv_stabil (hFS _) hperm hi hs)
          (fun O' R U σ => semH_rueckCons S O' U passes R e hperm rest σ ρ)
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
        exact popS_inv hO hRL hQ hS hsp hI hF hhead e (fun i hi hs => inv_stabil (hFS _) hperm hi hs)
          (fun O' R U σ => semH_dannRet S O' U passes R e hperm rest k σ ρ)
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
        exact popS_inv hO hRL hQ hS hsp hI hF hhead e (fun i hi hs => inv_stabil (hFS _) hperm hi hs)
          (fun O' R U σ => semH_dannRet S O' U passes R e hperm restk kk σ ρ)
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
        exact popS_inv hO hRL hQ hS hsp hI hF hhead e (fun i hi hs => inv_stabil (hFS _) hperm hi hs)
          (fun O' R U σ => semH_rueckCons S O' U passes R e hperm restk σ ρ)
      · exact Or.inl hev
    | _ => ohneRueck
  | g5 hs =>
    cases hs with
    | _ => ohneRueck
  | g6 hs =>
    cases hs with
    | _ => ohneRueck
  | g7 hs =>
    cases hs with
    | rueckFreigabeLetzte ρ a L hhead z ha =>
      simp only [rufUpdateG_self]
      apply antwort_invLogS ha
      intro v hv
      rcases a with ⟨answer, vor⟩
      dsimp only at hv hhead
      cases hv
      exact popS_last_inv hO hRL hQ hS hsp hK hI hFS hF ρ v vor L hhead
    | rueckScopedWertDirekt ρ r e R hhead hret hscope hΛ σ₁ hs₁ neu hneu hempty z ha =>
      rename_i l Γ Λ
      simp only [rufUpdateG_self]
      apply antwort_invLogS ha
      intro v hv
      cases hv
      subst σ₁
      have hperm : Λ.Perm (vertragVon D (M.faeden u).kopf.f).ende := by
        simpa only [hempty, List.map_nil, List.append_nil] using R.genau
      refine popS_inv hO hRL hQ hS hsp hI hF hhead e
        (fun i hi hs => inv_stabil (hFS _) hperm hi hs) ?_
      intro O' calls U σ
      exact semH_scopedWert S O' U passes calls r e R hret σ ρ
        (by simp only [hempty, scopesInvH, List.all_nil])
    | rueckScopedGrundDirekt ρ r grund R hhead hret hscope hΛ hempty z ha =>
      simp only [rufUpdateG_self]
      exact antwort_invLogS ha (fun _ h => by cases h)
    | _ => ohneRueck

end Schritte

/-! ## 4. The theorem -/

/-- **`ziel_ort_sperre` with table and group invariants.** Under the
    premises of `ziel_ort_sperre` and the obligation `InvGutS` for every
    function, every reachable machine satisfies the conclusion of
    `ziel_ort_sperre` AND every logged return meets the invariants its
    function owes (`InvAmOrtG`). -/
theorem ziel_ort_sperre_inv (P : Programm D) (O : Orakel D) (passes : Nat) (Q : AxEns D)
    (S : SperrInv D) (fs : List D.Fn) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hlok : AxEnsLokal Q)
    (hS : SperrInvOk S) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hFrag : programmImFragmentG P fs = true) (hFuss : fussSperreB P S fs = true)
    (hK : ∀ f : D.Fn, KoerperGutS P passes Q S f) (hStart : StartGut P sp init)
    (hSstart : ∀ L, S.inv L sp = true) (hex : StartExklusiv init)
    (hI : ∀ f : D.Fn, InvGutS P passes Q S f) :
    ∀ M : RufMaschineG D, RufErreichbarG P O passes (RufStartG P sp init) M →
      (VertragAmOrtG P M ∧ SperrInvG S M ∧ KeinLogikHaltG O passes M ∧
        ∀ t : Faden, HeldGenau (M.faeden t).kopf.rest.2.2.1 (offen (M.faeden t).spur) →
          AnPruefungG M t → ∃ M', RufSchrittG P O passes M t M') ∧
      InvAmOrtG P M := by
  intro M hr
  refine ⟨ziel_ort_sperre P O passes Q S fs sp init hO hRL hQ hlok hS hvoll hFrag hFuss hK
    hStart hSstart hex M hr, ?_⟩
  have hFS : ∀ f, FussS P S (freiB fs) f := fussSperreB_ok hvoll hFuss
  induction hr with
  | start =>
      intro t ev hev g rho v s0 s1 h
      subst h
      simp only [RufStartG, List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self] at hev
  | schritt M M' u hr' hs ih =>
      have hZ := (zielInvS_erreichbar P O passes Q S fs sp init hO hRL hQ hlok hS hvoll hFrag
        hFuss hK hStart hSstart hex M hr').1
      intro t ev hev
      by_cases ht : t = u
      · subst ht
        rcases invLog_schritt hO hRL hQ hS hSstart hK hI hFS (hZ.1 t).1 hs ev hev with h | h
        · exact ih t ev h
        · exact h
      · rw [rufSchrittG_fremd hs t ht] at hev
        exact ih t ev hev

/-- **`ziel_ort_sperre` is the special case without owed invariants.** -/
theorem invGutS_leer {P : Programm D} {passes : Nat} {Q : AxEns D} {S : SperrInv D}
    (h : D.invs = []) (f : D.Fn) : InvGutS P passes Q S f :=
  invGutS_ohne fun i hi => by rw [h] at hi; cases hi

#print axioms Gabbro.Grammatik.inv_stabil
#print axioms Gabbro.Grammatik.popS_inv
#print axioms Gabbro.Grammatik.invLog_schritt
#print axioms Gabbro.Grammatik.ziel_ort_sperre_inv

end Gabbro.Grammatik
