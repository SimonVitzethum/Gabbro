/- Part 3 of 3 of `AtomarReplay` (split by instrumente/teile/lean-teilen.py; the umbrella `AtomarReplay.lean` imports all parts). -/
import Grammatik.Speichermodell.Atomar.AtomarReplay.T2

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 5. The head never predicts a `logik` outcome; the release steps -/

section Frei

variable {P : Programm D} {O : Orakel D} {passes : Nat} {Q : AxEns D} {S : SperrInv D}
  {lok : D.Tab ⊕ D.Glob → Bool} {Tg : D.Tab ⊕ D.Glob → Prop} {m : Mass D} {zyk : D.Fn → D.Fn → Bool}

/-- **The head's prediction is never a `logik` outcome** (as `kopfS_keineLogik`), against the
    record handler, oracle, lock move and atomic environment. -/
theorem kopfSA_keineLogik (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O)
    (hS : SperrInvOk S) {sp : Speicher D} (hsp : ∀ L, S.inv L sp = true)
    (hK : ∀ f, KoerperGutSA P passes Q S Tg f) {F : RufRahmenG D} {W : World D}
    (hG : KopfSA P O passes Q S lok Tg m zyk F W) :
    ∃ (H : List (EintragV D)) (HA : List (AxEintrag D)) (HU : List (UEintrag D))
      (HX : List (XEintrag D)) (σ : World D),
      FunkX HX ∧ KurzX σ.spur.length HX ∧
      GleichAuf (stabilS P S lok F.f F.rest.2.2.1) σ W ∧
      F.rest.2.2.2.2.okS P (fussOrteG P F.f) (sicher P lok F.f) ∧
      ∀ (A : AUmwelt D), PasstX Tg A HX → HavocA Tg A → ∀ e : Logik D,
        semHA S (orakelAus O HA) (umweltAus S sp HU) A passes (rufAusL H) F.rest.2.2.2.2 σ
          F.rest.2.2.2.1 ≠ .logik e := by
  obtain ⟨H, HA, HU, HX, σ, hreq, hf, hv, hm, _, hfa, hra, hqa, _, hfu, hiu, _, ⟨hfx, hkx⟩, hg, hok,
    heq⟩ := hG
  refine ⟨H, HA, HU, HX, σ, hfx, hkx, hg, hok, fun A hPX hHA e he => ?_⟩
  have h1 := heq (rufAusL H) (orakelAus O HA) (umweltAus S sp HU) A (rufAusL_passt hf)
    (orakelAus_passt O hfa) (umweltAus_passt S sp hfu) hPX hHA (gleichRS_orakelAus O HA)
  rw [he] at h1
  exact (hK F.f).2 (orakelAus O HA) (orakelAus_rahmen hO hra) (regLokal_orakelAus hRL HA)
    (orakelAus_vertrag hQ hqa) (umweltAus S sp HU) (umweltAus_ok hS hsp hiu) A hHA (rufAusL H)
    (rufAusL_rahmen hv) (rufAusL_ohneLogik hv.1) F.s0 F.rho hreq e
    (zErgG_gleich_logik (ZErgG.folgt_logik h1))

/-- The same, for a residue named by its shape. -/
theorem kopfSA_keineLogik' (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O)
    (hS : SperrInvOk S) {sp : Speicher D} (hsp : ∀ L, S.inv L sp = true)
    (hK : ∀ f, KoerperGutSA P passes Q S Tg f) {F : RufRahmenG D} {W : World D}
    (hG : KopfSA P O passes Q S lok Tg m zyk F W) {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ}
    {r : GRest D (vertragVon D F.f) l Γ Λ} (hr : F.rest = ⟨l, Γ, Λ, ρ, r⟩) :
    ∃ (H : List (EintragV D)) (HA : List (AxEintrag D)) (HU : List (UEintrag D))
      (HX : List (XEintrag D)) (σ : World D),
      FunkX HX ∧ KurzX σ.spur.length HX ∧
      GleichAuf (stabilS P S lok F.f Λ) σ W ∧ r.okS P (fussOrteG P F.f) (sicher P lok F.f) ∧
      ∀ (A : AUmwelt D), PasstX Tg A HX → HavocA Tg A → ∀ e : Logik D,
        semHA S (orakelAus O HA) (umweltAus S sp HU) A passes (rufAusL H) r σ ρ ≠ .logik e := by
  obtain ⟨H, HA, HU, HX, σ, hfx, hkx, hg, hok, hno⟩ := kopfSA_keineLogik hO hRL hQ hS hsp hK hG
  rw [hr] at hok hno hg
  exact ⟨H, HA, HU, HX, σ, hfx, hkx, hg, hok, hno⟩

/-- **At a release the invariant holds in the machine** (as `kopfS_frei_inv`). -/
theorem kopfSA_frei_inv (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O)
    (hS : SperrInvOk S) {sp : Speicher D} (hsp : ∀ L, S.inv L sp = true)
    (hK : ∀ f, KoerperGutSA P passes Q S Tg f) {F : RufRahmenG D} {W : World D}
    (hG : KopfSA P O passes Q S lok Tg m zyk F W) {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {ρ : Env D Γ} (L : D.Lock) (hL : Res.held L ∈ Λ) {r : GRest D (vertragVon D F.f) l Γ Λ}
    (hr : F.rest = ⟨l, Γ, Λ, ρ, r⟩)
    (hlog : ∀ (O' : Orakel D) (U : Umwelt D) (A : AUmwelt D) R (σ : World D),
      S.inv L σ.speicher = false → semHA S O' U A passes R r σ ρ = .logik .schleife) :
    S.inv L W.speicher = true := by
  obtain ⟨H, HA, HU, HX, σ, hfx, _, hg, _, hno⟩ := kopfSA_keineLogik' hO hRL hQ hS hsp hK hG hr
  have hi : S.inv L σ.speicher = true := by
    cases h : S.inv L σ.speicher with
    | true => rfl
    | false => exact absurd (hlog (orakelAus O HA) (umweltAus S sp HU) (umweltAusA Tg HX)
        (rufAusL H) σ h) (hno _ (umweltAusA_passt Tg hfx) (umweltAusA_ok Tg HX) .schleife)
  rw [← hi]
  refine hS.2 L _ _ fun c hc => ?_
  have hcs : c ∈ stabilS P S lok F.f Λ := stabilS_mem.mpr (Or.inr ⟨L, hL, hc⟩)
  cases c with
  | inl t => exact (hg.1 t hcs).symm
  | inr g => exact (hg.2 g hcs).symm

/-- **The release after the body keeps the replay** (`freiGib`). -/
theorem fadenSA_frei (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O)
    (hS : SperrInvOk S) {sp : Speicher D} (hsp : ∀ L, S.inv L sp = true)
    (hK : ∀ f, KoerperGutSA P passes Q S Tg f) {z : RufFadenG D} {W : World D}
    (hF : FadenSA P O passes Q S lok Tg m zyk z W) {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (L : D.Lock)
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ) (ρ : Env D Γ)
    (hr : z.kopf.rest = ⟨l, Γ, Res.held L :: Λ, ρ, .frei L k⟩) (spur' : List (Ereignis D)) :
    FadenSA P O passes Q S lok Tg m zyk
      ⟨z.stapel, ⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨l, Γ, Λ, ρ, k⟩⟩, spur', z.log⟩
      (W.speicher.welt spur') := by
  have hW := kopfSA_frei_inv hO hRL hQ hS hsp hK hF.1 L List.mem_cons_self hr
    (fun O' U A R σ h => semHA_frei_falsch S O' U A passes R L k σ ρ h)
  refine fadenSA_lokalQ hF hr ρ k spur' (fun σ HX hfx hkx hg hok => ?_)
  have hiσ : S.inv L σ.speicher = true := (inv_gleich hS List.mem_cons_self hg).trans hW
  exact ⟨σ.gibt L, HX, hfx, kurzX_mono hkx (Nat.le_succ _), fun _ h => h, Nat.le_succ _,
    gleichAuf_frei hg spur', hok,
    fun R O' U A _ _ _ => ZErgG.folgt_of_eq (semHA_frei S O' U A passes R L k σ ρ hiσ)⟩

/-- **A `leave`/`next` out of a `locks` body keeps the replay**. -/
theorem fadenSA_peelFrei (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O)
    (hS : SperrInvOk S) {sp : Speicher D} (hsp : ∀ L, S.inv L sp = true)
    (hK : ∀ f, KoerperGutSA P passes Q S Tg f) {z : RufFadenG D} {W : World D}
    (hF : FadenSA P O passes Q S lok Tg m zyk z W) {Γ : Ctx} {Λ Λ1 : List (Res D)} (L : D.Lock)
    (rest : Block D (vertragVon D z.kopf.f) true Γ Λ (Res.held L :: Λ1))
    (k : GRest D (vertragVon D z.kopf.f) true Γ Λ1) (ρ : Env D Γ) (h : true = true) (x : Bool)
    (hr : z.kopf.rest =
      ⟨true, Γ, Λ, ρ, .dann (.cons (if x then .leave h else .next h) rest) (.frei L k)⟩)
    (spur' : List (Ereignis D)) :
    FadenSA P O passes Q S lok Tg m zyk
      ⟨z.stapel, ⟨z.kopf.f, z.kopf.rho, z.kopf.s0,
        ⟨true, Γ, Λ1, ρ, .dann (.cons (if x then .leave h else .next h) .nil) k⟩⟩, spur', z.log⟩
      (W.speicher.welt spur') := by
  have hLΛ : Res.held L ∈ Λ := (Block.held_iff rest L).mp List.mem_cons_self
  have hΛ1 : ∀ M, Res.held M ∈ Λ1 → Res.held M ∈ Λ :=
    fun M hM => (Block.held_iff rest M).mp (List.mem_cons_of_mem _ hM)
  have hW := kopfSA_frei_inv hO hRL hQ hS hsp hK hF.1 L hLΛ hr
    (fun O' U A R σ hi => semHA_peelFrei_falsch S O' U A passes R L rest k σ ρ h x hi)
  refine fadenSA_lokalQ hF hr ρ _ spur' (fun σ HX hfx hkx hg hok => ?_)
  have hiσ : S.inv L σ.speicher = true := (inv_gleich hS hLΛ hg).trans hW
  obtain ⟨_, _, hk⟩ := hok
  refine ⟨σ.gibt L, HX, hfx, kurzX_mono hkx (Nat.le_succ _), fun _ h => h, Nat.le_succ _,
    GleichAuf.mono (fun _ hc => stabilS_mono hΛ1 hc) ⟨fun t ht => hg.1 t ht, fun g hg' => hg.2 g hg'⟩,
    ⟨by cases x <;> rfl, fun _ hc => by cases x <;> simp only [blockOrteP, Bool.false_eq_true, ↓reduceIte, stmtOrteP, List.append_nil, List.not_mem_nil] at hc, hk⟩,
    fun R O' U A _ _ _ => ZErgG.folgt_of_eq (semHA_peelFrei S O' U A passes R L rest k σ ρ h x hiσ)⟩

end Frei

end Gabbro.Grammatik
