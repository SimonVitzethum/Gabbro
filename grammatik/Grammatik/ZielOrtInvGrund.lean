/-
  Gabbro/Grammatik/ZielOrtInvGrund.lean

  **Owed invariants at REASON returns** (SATZKARTE §18.5, §19.1).

  SYNTAX.md: a function owes its invariants "at every `return`". `InvGutS`
  and `InvAmOrtG` (`ZielOrtInv.lean`) check VALUE returns only, so a
  function could break a table invariant, leave by a reason, and after the
  lock release another thread saw the invariant broken with every premise
  of `ziel_ort_sperre_inv` met.

  Carried here like the value case -- an obligation and a conclusion, both
  stated in `Zielsatz/Spec.lean`:

  * the obligation `Zielsatz.InvGutGrund P passes Q S f` (per function,
    SEQUENTIAL, against the same oracles, environment moves and handlers as
    `InvGutS`): from `requires f`, a REASON exit of the body makes every
    invariant `f` owes true at the exit world;
  * the conclusion `Zielsatz.InvAmGrundG P M`: on every reachable machine,
    at every logged reason return `grund g rho r s0 s1`, every invariant
    `g` owes holds at `s1`.

  The replay had to learn the reason channel first: its frame results
  (`ZErg`) collapsed a reason exit into "anything else", so no reason
  return of the machine was related to a sequential one. `ZErgG`
  (`SperreSem.lean` §2a) keeps `grund σ r`, and the lock-invariant replay
  (`semH`, `KopfS`, `ziel_ort_sperre`) now predicts in `ZErgG`; every
  theorem of that chain kept its statement. Then the reason pop is the twin
  of the value pop: `popS_grund` (twin of `popS_inv`), `invGrundLog_schritt`
  (twin of `invLog_schritt`), `ziel_ort_sperre_invGrund`.
-/
import Grammatik.Zielsatz.Spec

namespace Gabbro.Grammatik

variable {D : Deklaration}

section Schritte

variable {P : Programm D} {O : Orakel D} {passes : Nat} {Q : AxEns D} {S : SperrInv D}
  {lok : D.Tab ⊕ D.Glob → Bool}

/-- **The reason-return leg for invariants** (the twin of `popS_inv`): a
    replayed head at a reason return owes its invariants at the machine's
    world -- the world the pop logs. -/
theorem popS_grund (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hS : SperrInvOk S)
    {sp : Speicher D} (hsp : ∀ L, S.inv L sp = true)
    (hIG : ∀ f, Zielsatz.InvGutGrund P passes Q S f) {G : RufRahmenG D}
    {W : World D} (hG : KopfS P O passes Q S lok G W) {lr : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {ρ : Env D Γ} {r : GRest D (vertragVon D G.f) lr Γ Λ} (hr : G.rest = ⟨lr, Γ, Λ, ρ, r⟩)
    (rg : Fin (vertragVon D G.f).gruende)
    (hinv : ∀ i ∈ D.invs, schuldet G.f i = true → (P.invariante i).orte ⊆ stabilS P S lok G.f Λ)
    (hsem : ∀ (O' : Orakel D) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
      (U : Umwelt D) (σ : World D), (semH S O' U passes R r σ ρ).gleich (.grund σ rg)) :
    InvAmRueck P G.f W := by
  obtain ⟨H, HA, HU, σ, hreq, hf, hv, _, hfa, hra, hqa, _, hfu, hiu, _, hg, _, heq⟩ := hG
  have h1 := heq (rufAusV H) (orakelAus O HA) (umweltAus S sp HU) (rufAusV_passt hf)
    (orakelAus_passt O hfa) (umweltAus_passt S sp hfu) (gleichRS_orakelAus O HA)
  rw [hr] at h1 hg
  simp only at h1 hg
  have h2 := ZErgG.folgt_grund (ZErgG.folgt_trans h1 (ZErgG.folgt_of_gleich (hsem _ _ _ σ)))
  obtain ⟨σ'', hex, hsg⟩ := zErgG_gleich_grund h2
  have hE := (hIG G.f) (orakelAus O HA) (orakelAus_rahmen hO hra) (regLokal_orakelAus hRL HA)
    (orakelAus_vertrag hQ hqa) (umweltAus S sp HU) (umweltAus_ok hS hsp hiu) (rufAusV H)
    (rufAusV_rahmen hv) (rufAusV_ohneVorbedingung hv.1) G.s0 G.rho hreq σ'' rg hex
  have hG2 : GleichAuf (stabilS P S lok G.f Λ) σ'' W := (gleichAuf_SG hsg).trans hg
  intro i hi hs
  have h3 := hE i hi hs
  unfold InvHaelt at h3 ⊢
  rw [← eval_gleichAuf (P.invariante i) (fun _ h => hinv i hi hs h) hG2 .nil]
  exact h3

set_option hygiene false in
/-- A step that logs no `grund` event keeps the claim. -/
macro "ohneGrund" : tactic => `(tactic| (
  intro ev hev
  simp only [rufUpdateG_self] at hev
  first
  | exact Or.inl hev
  | (rcases List.mem_cons.mp hev with rfl | hev
     · exact Or.inr (fun _ _ _ _ _ h => by cases h)
     · exact Or.inl hev)))

/-- **One step and the logged reason returns**: every event of the acting
    thread after the step is an old event, or a reason return whose
    function owes its invariants at the logged world. -/
theorem invGrundLog_schritt (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O)
    (hS : SperrInvOk S) {sp : Speicher D} (hsp : ∀ L, S.inv L sp = true)
    (hIG : ∀ f, Zielsatz.InvGutGrund P passes Q S f) (hFS : ∀ f, FussS P S lok f)
    {M M' : RufMaschineG D} {u : Faden}
    (hF : KopfS P O passes Q S lok (M.faeden u).kopf (M.weltVon u))
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
      exact popS_grund hO hRL hQ hS hsp hIG hF hhead r
        (fun i hi hs => inv_stabil (hFS _) hperm hi hs)
        (fun O' R U σ => semH_rueckGrund S O' U passes R r hperm σ ρ)
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
      exact popS_grund hO hRL hQ hS hsp hIG hF hhead r
        (fun i hi hs => inv_stabil (hFS _) hperm hi hs)
        (fun O' R U σ => semH_rueckConsGrund S O' U passes R r hperm restk σ ρ)
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
      exact popS_grund hO hRL hQ hS hsp hIG hF hhead r
        (fun i hi hs => inv_stabil (hFS _) hperm hi hs)
        (fun O' R U σ => semH_dannRetGrund S O' U passes R r hperm restk kk σ ρ)
    · exact Or.inl hev
  | _ => ohneGrund

end Schritte

/-! ## The theorem -/

/-- **`ziel_ort_sperre` with invariants at REASON returns.** Under the
    premises of `ziel_ort_sperre` and the obligation `InvGutGrund` for
    every function, every reachable machine satisfies `InvAmGrundG`: at
    every logged reason return, every invariant the function owes holds at
    the logged world. -/
theorem ziel_ort_sperre_invGrund (P : Programm D) (O : Orakel D) (passes : Nat) (Q : AxEns D)
    (S : SperrInv D) (fs : List D.Fn) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hlok : AxEnsLokal Q)
    (hS : SperrInvOk S) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hFrag : programmImFragmentG P fs = true) (hFuss : fussSperreB P S fs = true)
    (hK : ∀ f : D.Fn, KoerperGutS P passes Q S f) (hStart : StartGut P sp init)
    (hSstart : ∀ L, S.inv L sp = true) (hex : StartExklusiv init)
    (hIG : ∀ f : D.Fn, Zielsatz.InvGutGrund P passes Q S f) :
    ∀ M : RufMaschineG D, RufErreichbarG P O passes (RufStartG P sp init) M →
      Zielsatz.InvAmGrundG P M := by
  intro M hr
  have hFS : ∀ f, FussS P S (freiB fs) f := fussSperreB_ok hvoll hFuss
  induction hr with
  | start =>
      intro t ev hev g rho r s0 s1 h
      subst h
      simp [RufStartG] at hev
  | schritt M M' u hr' hs ih =>
      have hZ := (zielInvS_erreichbar P O passes Q S fs sp init hO hRL hQ hlok hS hvoll hFrag
        hFuss hK hStart hSstart hex M hr').1
      intro t ev hev
      by_cases ht : t = u
      · subst ht
        rcases invGrundLog_schritt hO hRL hQ hS hSstart hIG hFS (hZ.1 t).1 hs ev hev with h | h
        · exact ih t ev h
        · exact h
      · rw [rufSchrittG_fremd hs t ht] at hev
        exact ih t ev hev

/-- **Both return kinds at once**: `ziel_ort_sperre_inv` and the reason
    twin -- the invariants owed at EVERY return of `SYNTAX.md`. -/
theorem ziel_ort_sperre_invAlle (P : Programm D) (O : Orakel D) (passes : Nat) (Q : AxEns D)
    (S : SperrInv D) (fs : List D.Fn) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hlok : AxEnsLokal Q)
    (hS : SperrInvOk S) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hFrag : programmImFragmentG P fs = true) (hFuss : fussSperreB P S fs = true)
    (hK : ∀ f : D.Fn, KoerperGutS P passes Q S f) (hStart : StartGut P sp init)
    (hSstart : ∀ L, S.inv L sp = true) (hex : StartExklusiv init)
    (hI : ∀ f : D.Fn, InvGutS P passes Q S f)
    (hIG : ∀ f : D.Fn, Zielsatz.InvGutGrund P passes Q S f) :
    ∀ M : RufMaschineG D, RufErreichbarG P O passes (RufStartG P sp init) M →
      InvAmOrtG P M ∧ Zielsatz.InvAmGrundG P M := fun M hr =>
  ⟨(ziel_ort_sperre_inv P O passes Q S fs sp init hO hRL hQ hlok hS hvoll hFrag hFuss hK hStart
      hSstart hex hI M hr).2,
    ziel_ort_sperre_invGrund P O passes Q S fs sp init hO hRL hQ hlok hS hvoll hFrag hFuss hK
      hStart hSstart hex hIG M hr⟩

/-- **Generic in the local carriers** (the replay of `zielInvS_erreichbarL`):
    the reason twin under every flagship built on that replay. -/
theorem invAmGrundG_erreichbarL (P : Programm D) (O : Orakel D) (passes : Nat) (Q : AxEns D)
    (S : SperrInv D) (lok : D.Tab ⊕ D.Glob → Bool) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hlok : AxEnsLokal Q)
    (hS : SperrInvOk S)
    (hFragS : ∀ f, (P.rumpf f).gOk (kandP P (fussOrteG P f)) (regP (sicher P lok f)) = true)
    (hFS : ∀ f, FussS P S lok f) (hLok : LokOk P O passes lok sp init)
    (hK : ∀ f : D.Fn, KoerperGutS P passes Q S f) (hStart : StartGut P sp init)
    (hSstart : ∀ L, S.inv L sp = true) (hex : StartExklusiv init)
    (hIG : ∀ f : D.Fn, Zielsatz.InvGutGrund P passes Q S f) :
    ∀ M : RufMaschineG D, RufErreichbarG P O passes (RufStartG P sp init) M →
      Zielsatz.InvAmGrundG P M := by
  have hZ := zielInvS_erreichbarL P O passes Q S lok sp init hO hRL hQ hlok hS hFragS hFS
    hLok hK hStart hSstart hex
  intro M hr
  induction hr with
  | start =>
      intro t ev hev g rho r s0 s1 h
      subst h
      simp [RufStartG] at hev
  | schritt M M' u hr' hs ih =>
      have hZ' := (hZ M hr').1
      intro t ev hev
      by_cases ht : t = u
      · subst ht
        rcases invGrundLog_schritt hO hRL hQ hS hSstart hIG hFS (hZ'.1 t).1 hs ev hev with h | h
        · exact ih t ev h
        · exact h
      · rw [rufSchrittG_fremd hs t ht] at hev
        exact ih t ev hev

/-- **The reason twin under the premises of `ziel_ort_mehrfaden`** (several
    active threads with thread-local carriers, obligations at every
    `forever` budget) -- the premise set `GabbroZiel` builds on. -/
theorem ziel_ort_mehrfaden_invGrund (P : Programm D) (O : Orakel D) (Q : AxEns D)
    (S : SperrInv D) (fs : List D.Fn) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (K : Faden → D.Fn → Bool)
    (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hlok : AxEnsLokal Q)
    (hS : SperrInvOk S) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hFrag : programmImFragmentG P fs = true)
    (hAbg : ∀ t, AbgK P fs (K t)) (hWurzel : ∀ t, K t (init t).1 = true)
    (hFuss : ∀ f, FussS P S (lokK P K) f)
    (hK : ∀ (passes : Nat) (f : D.Fn), KoerperGutS P passes Q S f) (hStart : StartGut P sp init)
    (hSstart : ∀ L, S.inv L sp = true) (hex : StartExklusiv init)
    (hIG : ∀ (passes : Nat) (f : D.Fn), Zielsatz.InvGutGrund P passes Q S f) :
    ∀ (passes : Nat) (M : RufMaschineG D), RufErreichbarG P O passes (RufStartG P sp init) M →
      Zielsatz.InvAmGrundG P M := fun passes =>
  invAmGrundG_erreichbarL P O passes Q S (lokK P K) sp init hO hRL hQ hlok hS
    (programmImFragmentS_ok P S hvoll hFrag hFuss) hFuss
    (lokOk_mehr hO hvoll sp init K hAbg hWurzel) (hK passes) hStart hSstart hex (hIG passes)

/-- A function that owes no invariant owes nothing at a reason exit. -/
theorem invGutGrund_ohne {P : Programm D} {passes : Nat} {Q : AxEns D} {S : SperrInv D}
    {f : D.Fn} (h : ∀ i ∈ D.invs, schuldet f i = false) : Zielsatz.InvGutGrund P passes Q S f := by
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ i hi hs
  rw [h i hi] at hs
  cases hs

/-- A function without reasons owes nothing at a reason exit. -/
theorem invGutGrund_ohneGrund {P : Programm D} {passes : Nat} {Q : AxEns D} {S : SperrInv D}
    {f : D.Fn} (h : D.gruende f = 0) : Zielsatz.InvGutGrund P passes Q S f := by
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ r
  have h2 : r.val < D.gruende f := r.2
  omega

#print axioms Gabbro.Grammatik.popS_grund
#print axioms Gabbro.Grammatik.invGrundLog_schritt
#print axioms Gabbro.Grammatik.ziel_ort_sperre_invGrund
#print axioms Gabbro.Grammatik.ziel_ort_sperre_invAlle
#print axioms Gabbro.Grammatik.invAmGrundG_erreichbarL
#print axioms Gabbro.Grammatik.ziel_ort_mehrfaden_invGrund
#print axioms Gabbro.Grammatik.invGutGrund_ohne
#print axioms Gabbro.Grammatik.invGutGrund_ohneGrund

end Gabbro.Grammatik
