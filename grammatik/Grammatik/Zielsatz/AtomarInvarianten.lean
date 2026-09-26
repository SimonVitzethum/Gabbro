/-
  File:      Grammatik/Zielsatz/AtomarInvarianten.lean
  Subject:   THE INVARIANT LEGS OF OPUS AGENT D WITH SHARED ATOMICS -- `InvRuheG`, `InvSichtG`, and
             the lock-move legs over GX steps (Opus lane O25b, 2026-09-26). Standalone.

  Opus agent D proved four legs over G (Zielsatz/Invarianten.lean). Over GX -- G with the shared
  atomics `Tg` answered by the weak memory -- the same arguments go through, because a GX step
  differs from a G step only at carriers of `Tg`, and none of them is in an invariant:
  * a table/group invariant reads tables only (`InvTraeger`), and `Tg` holds atomics, which are
    globals (`hTA`);
  * a lock invariant reads its lock's carriers, which are guarded (`sperrOrte`), and `Tg` holds
    unguarded carriers only (`hTO`).

  * `gx_traeger` -- `schritt_traeger` for a GX step at a carrier outside `Tg`;
  * `gx_innen` -- a GX step's successor agrees with the inner G step's outside `Tg`;
  * `schritt_schluesselX` -- `schritt_schluessel` over GX (the popped frame's return world
    carries the successor's memory outside `Tg`);
  * `invRuhe_erreichbarX`, `invSicht_ausX` -- `InvRuheG`, `InvSichtG` at every machine GX
    reaches;
  * `SperrWechselGX`, `SperrSichtGX` -- the lock-move legs with GX steps in place of G steps,
    and their proofs `sperrWechsel_ausX`, `sperrSicht_ausX`.
-/
import Grammatik.Speichermodell.AtomarZiel
import Grammatik.Zielsatz.Invarianten

namespace Gabbro.Grammatik.Zielsatz

open Gabbro.Grammatik Speichermodell

variable {D : Deklaration}

/-- **Lock invariants at every lock move, over GX steps** (`SperrWechselG` with `RufSchrittGX`). -/
def SperrWechselGX (P : Programm D) (O : Orakel D) (passes : Nat) (Tg : D.Tab ⊕ D.Glob → Prop)
    (S : SperrInv D) (M : RufMaschineG D) : Prop :=
  ∀ (u : Faden) (M' : RufMaschineG D) (L : D.Lock), RufSchrittGX P O passes Tg M u M' →
    (L ∉ offen (M.faeden u).spur → L ∈ offen (M'.faeden u).spur →
      S.inv L M.speicher = true ∧ S.inv L M'.speicher = true) ∧
    (L ∈ offen (M.faeden u).spur → L ∉ offen (M'.faeden u).spur → S.inv L M'.speicher = true)

/-- **A held lock's invariant is observed by its holder alone, over GX steps.** -/
def SperrSichtGX (P : Programm D) (O : Orakel D) (passes : Nat) (Tg : D.Tab ⊕ D.Glob → Prop)
    (S : SperrInv D) (M : RufMaschineG D) : Prop :=
  ∀ (u : Faden) (M' : RufMaschineG D), RufSchrittGX P O passes Tg M u M' →
    ∀ (L : D.Lock) (c : D.Tab ⊕ D.Glob), c ∈ S.orte L →
      (ZugriffG M M' u c → L ∈ offen (M.faeden u).spur) ∧
      (∀ t, t ≠ u → L ∈ offen (M.faeden t).spur → TraegerGleich M'.speicher M.speicher c)

section GX

variable {P : Programm D} {O : Orakel D} {passes : Nat} {Tg : D.Tab ⊕ D.Glob → Prop}

/-- **`schritt_traeger` for a GX step**, at a carrier outside `Tg`. -/
theorem gx_traeger (hO : GutO O) {M M' : RufMaschineG D} {u : Faden}
    (h : RufSchrittGX P O passes Tg M u M') (c : D.Tab ⊕ D.Glob) (hT : ¬ Tg c)
    (hc : (∃ L, Bewacht c L ∧ L ∉ offen (M.faeden u).spur) ∨
      TraegerSchreibt (M.faeden u).kopf.f c = false) :
    TraegerGleich M'.speicher M.speicher c := by
  obtain ⟨σ, M'', hs, hσ, h1, h2, _, _, _⟩ := h
  by_cases hw : SchreibG (mitSpeicher M σ) M'' u c
  · exact Gabbro.Grammatik.traegerGleich_trans (h1 c hw)
      (Gabbro.Grammatik.traegerGleich_trans (schritt_traeger hO hs c hc) (hσ c hT))
  · exact h2 c hw

/-- A thread other than the actor keeps its state over a GX step. -/
theorem gx_fremd {M M' : RufMaschineG D} {u : Faden} (h : RufSchrittGX P O passes Tg M u M')
    (t : Faden) (htu : t ≠ u) : M'.faeden t = M.faeden t := by
  obtain ⟨σ, M'', hs, _, _, _, hfa, _, _⟩ := h
  rw [hfa]
  exact rufSchrittG_fremd hs t htu

/-- The lock-exclusivity, trace and matching invariants on every GX run (over GA). -/
theorem gx_passt (hTA : ∀ c, Tg c → AtomarAusgenommen c) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) {M : RufMaschineG D}
    (hr : RufErreichbarGX P O passes Tg (RufStartG P sp init) M) : RufMaschinePasstG M :=
  gaInvF (J := fun fa => ∀ f, RufFadenPasstG (fa f)) (rufStartG_passt P sp init)
    (fun M M' u h hs => rufSchrittG_passt P O passes M M' u h hs) (gx_ga_lauf hTA hr)

/-- **`schritt_schluessel` over GX**: how a GX step moves a thread's key stack; a pop's return
    world carries the successor's memory at every carrier outside `Tg`. -/
theorem schritt_schluesselX {M M' : RufMaschineG D} {u : Faden}
    (hP0 : RufMaschinePasstG M) (hP1 : RufMaschinePasstG M')
    (h : RufSchrittGX P O passes Tg M u M') :
    RufFadenSchluesselG (M'.faeden u) = RufFadenSchluesselG (M.faeden u) ∨
    (∃ k, RufFadenSchluesselG (M'.faeden u) = k :: RufFadenSchluesselG (M.faeden u)) ∨
    (∃ (g : D.Fn) (rho : Env D (D.params g)) (v : ErgVal D (D.erg g)) (s0 s1 : World D),
      RufFadenSchluesselG (M.faeden u) = ⟨g, rho, s0⟩ :: RufFadenSchluesselG (M'.faeden u) ∧
      RufEreignisF.rueck g rho v s0 s1 ∈ (M'.faeden u).log ∧
      ∀ c, ¬ Tg c → TraegerGleich s1.speicher M'.speicher c) ∨
    (∃ (g : D.Fn) (rho : Env D (D.params g)) (r : Fin (D.gruende g)) (s0 s1 : World D),
      RufFadenSchluesselG (M.faeden u) = ⟨g, rho, s0⟩ :: RufFadenSchluesselG (M'.faeden u) ∧
      RufEreignisF.grund g rho r s0 s1 ∈ (M'.faeden u).log ∧
      ∀ c, ¬ Tg c → TraegerGleich s1.speicher M'.speicher c) := by
  obtain ⟨σ, M'', hs, hσ, hw1, hw2, hfa, _, _⟩ := h
  have hin : ∀ c, ¬ Tg c → TraegerGleich M''.speicher M'.speicher c := by
    intro c hT
    by_cases hw : SchreibG (mitSpeicher M σ) M'' u c
    · exact traegerGleich_symm (hw1 c hw)
    · have e1 : TraegerGleich M''.speicher σ c := by
        unfold SchreibG at hw
        exact Classical.byContradiction fun hn => hw (Or.inr hn)
      exact Gabbro.Grammatik.traegerGleich_trans e1
        (Gabbro.Grammatik.traegerGleich_trans (hσ c hT) (traegerGleich_symm (hw2 c hw)))
  have h0 := hP0 u
  have h1 := hP1 u
  unfold RufFadenPasstG at h0 h1
  rw [hfa] at h1 ⊢
  rcases schritt_logArt hs with he | ⟨g, rho, s0, he⟩ | ⟨g, rho, v, s0, s1, he, hsp⟩ |
      ⟨g, rho, r, s0, s1, he, hsp⟩
  · rw [he] at h1
    exact Or.inl (rufLogPasstG_eind h1 h0)
  · rw [he] at h1
    generalize RufFadenSchluesselG (M''.faeden u) = ks at h1 ⊢
    cases h1 with
    | eintritt _ _ _ _ _ h2 => exact Or.inr (Or.inl ⟨_, by rw [rufLogPasstG_eind h2 h0]⟩)
  · refine Or.inr (Or.inr (Or.inl ⟨g, rho, v, s0, s1, ?_, by rw [he]; exact List.mem_cons_self,
      fun c hT => by rw [hsp]; exact hin c hT⟩))
    rw [he] at h1
    generalize RufFadenSchluesselG (M''.faeden u) = ks at h1 ⊢
    cases h1 with
    | rueck _ _ _ _ _ _ _ h2 => exact (rufLogPasstG_eind h2 h0).symm
  · refine Or.inr (Or.inr (Or.inr ⟨g, rho, r, s0, s1, ?_, by rw [he]; exact List.mem_cons_self,
      fun c hT => by rw [hsp]; exact hin c hT⟩))
    rw [he] at h1
    generalize RufFadenSchluesselG (M''.faeden u) = ks at h1 ⊢
    cases h1 with
    | grund _ _ _ _ _ _ _ h2 => exact (rufLogPasstG_eind h2 h0).symm

/-- An invariant reading tables only is read equally at two memories agreeing outside `Tg`. -/
theorem invHaelt_aussen (hTA : ∀ c, Tg c → AtomarAusgenommen c) {i : D.Inv}
    (hT : InvTraeger P i) {σ σ' : World D}
    (h : ∀ c, ¬ Tg c → TraegerGleich σ.speicher σ'.speicher c) :
    InvHaelt P i σ ↔ InvHaelt P i σ' := by
  have hgl : GleichAuf (P.invariante i).orte σ σ' := by
    refine ⟨fun tb htb => ?_, fun g hg => ?_⟩
    · exact h (.inl tb) fun ht => by obtain ⟨_, e, _⟩ := hTA _ ht; cases e
    · obtain ⟨_, _, he⟩ := hT _ hg
      cases he
  unfold InvHaelt
  rw [eval_gleichAuf (P.invariante i) (fun _ h => h) hgl .nil]

/-- **`InvRuheG` over GX.** -/
theorem invRuhe_erreichbarX (hO : GutO O) (hTA : ∀ c, Tg c → AtomarAusgenommen c)
    (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (hIR : ∀ M, RufErreichbarGX P O passes Tg (RufStartG P sp init) M →
      InvAmOrtG P M ∧ InvAmGrundG P M ∧ StartEndeG P M ∧ KeinStartGrundG M)
    {i : D.Inv} (hi : i ∈ D.invs) (hT : InvTraeger P i) (h0 : InvHaelt P i (sp.welt [])) :
    ∀ {M : RufMaschineG D}, RufErreichbarGX P O passes Tg (RufStartG P sp init) M →
      InvZu M i → InvHaelt P i (M.speicher.welt []) := by
  intro M hr
  induction hr with
  | start => intro _; exact h0
  | schritt M M' u hr hs ih =>
      intro hZ'
      have hr' : RufErreichbarGX P O passes Tg (RufStartG P sp init) M' := .schritt _ _ _ hr hs
      have hwelt : ∀ s1 : World D, (∀ c, ¬ Tg c → TraegerGleich s1.speicher M'.speicher c) →
          InvHaelt P i s1 → InvHaelt P i (M'.speicher.welt []) := fun s1 hs1 h =>
        (invHaelt_aussen hTA hT fun c hc => by
          rw [speicher_welt_speicher]; exact hs1 c hc).mp h
      by_cases hU : ∀ F ∈ (M.faeden u).kopf :: (M.faeden u).stapel, schuldet F.f i = false
      · have hZ : InvZu M i := by
          intro t hFt F hF
          by_cases htu : t = u
          · subst htu; exact hU F hF
          · have he := gx_fremd hs t htu
            refine hZ' t (fun h => hFt ?_) F (by rw [he]; exact hF)
            unfold FertigG at h ⊢
            rw [he] at h
            exact h
        have hIH := ih hZ
        have hkopf : schuldet (M.faeden u).kopf.f i = false := hU _ List.mem_cons_self
        have hgl : GleichAuf (P.invariante i).orte (M'.speicher.welt []) (M.speicher.welt []) := by
          refine ⟨fun tb htb => ?_, fun g hg => ?_⟩
          · obtain ⟨t', ht', he⟩ := hT _ htb
            cases he
            have hw : TraegerSchreibt (M.faeden u).kopf.f (Sum.inl tb) = false := by
              show D.schreibt (M.faeden u).kopf.f tb = false
              unfold schuldet at hkopf
              exact Bool.eq_false_iff.mpr fun hw =>
                Bool.false_ne_true (hkopf ▸ List.any_eq_true.mpr ⟨tb, ht', hw⟩)
            exact gx_traeger hO hs (.inl tb) (fun ht => by obtain ⟨_, e, _⟩ := hTA _ ht; cases e)
              (Or.inr hw)
          · obtain ⟨_, _, he⟩ := hT _ hg
            cases he
        unfold InvHaelt at hIH ⊢
        rw [eval_gleichAuf (P.invariante i) (fun _ h => h) hgl .nil]
        exact hIH
      · have hne : ¬ ∀ k ∈ RufFadenSchluesselG (M.faeden u), schuldet k.1 i = false :=
          fun h => hU (invZu_schluessel.mpr h)
        obtain ⟨k0, hk0, hs0⟩ : ∃ k0 ∈ RufFadenSchluesselG (M.faeden u), schuldet k0.1 i = true :=
          Classical.byContradiction fun hn =>
            hne fun k hk => Bool.eq_false_iff.mpr fun h => hn ⟨k, hk, h⟩
        by_cases hk : k0 ∈ RufFadenSchluesselG (M'.faeden u)
        · by_cases hFu : FertigG M' u
          · have hst := hFu.1
            have hkk : k0 = RufSchluesselG (M'.faeden u).kopf := by
              unfold RufFadenSchluesselG at hk
              rw [hst] at hk
              exact List.mem_singleton.mp hk
            obtain ⟨-, -, hSE, hKS⟩ := hIR M' hr'
            obtain ⟨l, Γ, Λ, ρ, r, e, hrest, hret⟩ := fertig_retKopf hFu hKS
            have hI := (hSE u hst l Γ Λ ρ r e hrest hret).2
            refine hwelt _ (fun c _ => ?_) (hI i hi ?_)
            · show TraegerGleich (M'.weltVon u).speicher M'.speicher c
              have e : (M'.weltVon u).speicher = M'.speicher := speicher_welt_speicher _ _
              rw [e]
              exact traegerGleich_refl _ c
            · rw [hkk] at hs0; exact hs0
          · exact absurd hs0 (by
              rw [(invZu_schluessel (z := M'.faeden u)).mp (hZ' u hFu) k0 hk]; decide)
        · rcases schritt_schluesselX (gx_passt hTA sp init hr) (gx_passt hTA sp init hr') hs with
              he | ⟨k, he⟩ | ⟨g, rho, v, s0, s1, he, hmem, hsp⟩ | ⟨g, rho, r, s0, s1, he, hmem, hsp⟩
          · exact absurd (he ▸ hk0) hk
          · exact absurd (he ▸ List.mem_cons_of_mem _ hk0) hk
          · rw [he] at hk0
            rcases List.mem_cons.mp hk0 with rfl | hk'
            · exact hwelt s1 hsp ((hIR M' hr').1 u _ hmem g rho v s0 s1 rfl i hi hs0)
            · exact absurd hk' hk
          · rw [he] at hk0
            rcases List.mem_cons.mp hk0 with rfl | hk'
            · exact hwelt s1 hsp ((hIR M' hr').2.1 u _ hmem g rho r s0 s1 rfl i hi hs0)
            · exact absurd hk' hk

/-- **`InvSichtG` over GX**: `invRuhe` plus lock exclusivity and the signature locks (`U003`). -/
theorem invSicht_ausX (hO : GutO O) (hTA : ∀ c, Tg c → AtomarAusgenommen c) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (hex : StartExklusiv init)
    {M : RufMaschineG D} (hr : RufErreichbarGX P O passes Tg (RufStartG P sp init) M)
    {i : D.Inv} (hJ : InvZu M i → InvHaelt P i (M.speicher.welt [])) (t : Faden)
    (ht : ∀ F ∈ (M.faeden t).kopf :: (M.faeden t).stapel, schuldet F.f i = false)
    (hL : ∃ tb ∈ D.traeger i, ∃ L, Sum.inl L ∈ D.braucht tb ∧ L ∈ offen (M.faeden t).spur) :
    InvHaelt P i (M.speicher.welt []) := by
  have hA := gx_ga_lauf hTA hr
  obtain ⟨tb, htb, L, hLb, hLt⟩ := hL
  refine hJ fun u _ F hF => ?_
  by_cases hut : u = t
  · subst hut; exact ht F hF
  · refine Bool.eq_false_iff.mpr fun hs => ?_
    have hLF : L ∈ D.haelt F.f := D.invarianten_gehalten (D.sig F.f) i hs tb htb L hLb
    have hLu := (ga_haeltInv hO sp init hA u).signatur F hF L hLF
    exact gaInv_exklusiv hO sp init hex hA t u (fun e => hut e.symm) L hLt hLu

/-- **`SperrWechselGX`**: at every lock move of a GX step the lock's invariant holds. -/
theorem sperrWechsel_ausX (hO : GutO O) (hTA : ∀ c, Tg c → AtomarAusgenommen c)
    {S : SperrInv D} (hTO : ∀ c, Tg c → ∀ L, c ∉ S.orte L) (hS : SperrInvOk S) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (hex : StartExklusiv init)
    (hSG : ∀ M, RufErreichbarGX P O passes Tg (RufStartG P sp init) M → SperrInvG S M)
    {M : RufMaschineG D} (hr : RufErreichbarGX P O passes Tg (RufStartG P sp init) M) :
    SperrWechselGX P O passes Tg S M := by
  intro u M' L hs
  have hr' : RufErreichbarGX P O passes Tg (RufStartG P sp init) M' := .schritt _ _ _ hr hs
  have hx := gaInv_exklusiv hO sp init hex (gx_ga_lauf hTA hr)
  have hx' := gaInv_exklusiv hO sp init hex (gx_ga_lauf hTA hr')
  refine ⟨fun hn hj => ?_, fun hj hn => ?_⟩
  · have hfrei : ∀ t, L ∉ offen (M.faeden t).spur := by
      intro t
      by_cases htu : t = u
      · subst htu; exact hn
      · rw [← gx_fremd hs t htu]
        exact hx' u t (fun e => htu e.symm) L hj
    have h1 := hSG M hr L hfrei
    refine ⟨h1, ?_⟩
    rw [hS.2 L M'.speicher M.speicher fun c hc =>
      gx_traeger hO hs c (fun ht => hTO c ht L hc) (Or.inl ⟨L, hS.1 L c hc, hn⟩)]
    exact h1
  · refine hSG M' hr' L fun t => ?_
    by_cases htu : t = u
    · subst htu; exact hn
    · rw [gx_fremd hs t htu]
      exact hx u t (fun e => htu e.symm) L hj

/-- **`SperrSichtGX`**: a GX step touches a carrier of `L` only when its thread holds `L`, and
    no GX step of another thread moves it while `L` is held. -/
theorem sperrSicht_ausX (hO : GutO O) (hTA : ∀ c, Tg c → AtomarAusgenommen c)
    {S : SperrInv D} (hTO : ∀ c, Tg c → ∀ L, c ∉ S.orte L) (hS : SperrInvOk S) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (hex : StartExklusiv init)
    {M : RufMaschineG D} (hr : RufErreichbarGX P O passes Tg (RufStartG P sp init) M) :
    SperrSichtGX P O passes Tg S M := by
  intro u M' hs L c hc
  have hr' : RufErreichbarGX P O passes Tg (RufStartG P sp init) M' := .schritt _ _ _ hr hs
  have hx := gaInv_exklusiv hO sp init hex (gx_ga_lauf hTA hr)
  refine ⟨fun hz => ?_, fun t htu hLt => ?_⟩
  · obtain ⟨σ, M'', hs', hfa, hZ, _, _⟩ := schrittGA_zerlegen (gx_ga hTA hs)
    have hSp' : SpurInv M'' := by
      have := gaInv_spur hO sp init (gx_ga_lauf hTA hr')
      intro t; rw [← hfa]; exact this t
    exact (zugriff_haeltA hO hs' hSp' (hS.1 L c hc) (hZ c hz)).1
  · exact gx_traeger hO hs c (fun ht => hTO c ht L hc)
      (Or.inl ⟨L, hS.1 L c hc, hx t u htu L hLt⟩)

end GX

/-- **The four invariant legs at every machine GX reaches**, under the premises of
    `ziel_ort_atomar_voll`. -/
theorem invarianten_atomar (P : Programm D) (O : Orakel D) (passes : Nat) (Q : AxEns D)
    (S : SperrInv D) {fs : List D.Fn} (K : Faden → D.Fn → Bool) (Tg : D.Tab ⊕ D.Glob → Prop)
    (lok : D.Tab ⊕ D.Glob → Bool) (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hlok : AxEnsLokal Q)
    (hS : SperrInvOk S) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hAbg : ∀ t, AbgK P fs (K t)) (hWurzel : ∀ t, K t (init t).1 = true)
    (hTA : ∀ c, Tg c → AtomarAusgenommen c) (hTV : ∀ c, Tg c → VertragsFrei P c)
    (hTS : ∀ c, Tg c → ∀ f Λ, c ∉ stabilS P S lok f Λ)
    (hTO : ∀ c, Tg c → ∀ L, c ∉ S.orte L)
    (hFragS : ∀ f, (P.rumpf f).gOk (kandP P (fussOrteG P f)) (regP (sicher P lok f)) = true)
    (hFS : ∀ f, FussSX P S lok Tg f) (hlokK : ∀ c, lok c = true → GetrenntK P K c)
    (hK : ∀ f : D.Fn, KoerperGutSA P passes Q S Tg f)
    (hI : ∀ f : D.Fn, InvGutSA P passes Q S Tg f)
    (hIG : ∀ f : D.Fn, InvGutGrundA P passes Q S Tg f) (hStart : StartGut P sp init)
    (hsp : ∀ L, S.inv L sp = true) (hex : StartExklusiv init) (hGrund : StartOhneGrund init) :
    ∀ M : RufMaschineG D, RufErreichbarGX P O passes Tg (RufStartG P sp init) M →
      InvRuheG P (RufStartG P sp init) M ∧ InvSichtG P (RufStartG P sp init) M ∧
      SperrWechselGX P O passes Tg S M ∧ SperrSichtGX P O passes Tg S M := by
  have hV := ziel_ort_atomar_voll P O passes Q S K Tg lok sp init hO hRL hQ hlok hS hvoll hAbg
    hWurzel hTA hTV hTS hTO hFragS hFS hlokK hK hI hIG hStart hsp hex hGrund
  have hIR : ∀ M, RufErreichbarGX P O passes Tg (RufStartG P sp init) M →
      InvAmOrtG P M ∧ InvAmGrundG P M ∧ StartEndeG P M ∧ KeinStartGrundG M := fun M hr =>
    ⟨(hV M hr).2.2.2.1, (hV M hr).2.2.2.2.1, (hV M hr).2.2.2.2.2.1, (hV M hr).2.2.2.2.2.2⟩
  intro M hr
  exact ⟨fun _ hi hT h0 hZ => invRuhe_erreichbarX hO hTA sp init hIR hi hT h0 hr hZ,
    fun _ hi hT h0 t ht hL => invSicht_ausX hO hTA sp init hex hr
      (invRuhe_erreichbarX hO hTA sp init hIR hi hT h0 hr) t ht hL,
    sperrWechsel_ausX hO hTA hTO hS sp init hex (fun M hr => (hV M hr).2.1) hr,
    sperrSicht_ausX hO hTA hTO hS sp init hex hr⟩

#print axioms Gabbro.Grammatik.Zielsatz.invRuhe_erreichbarX
#print axioms Gabbro.Grammatik.Zielsatz.invarianten_atomar

end Gabbro.Grammatik.Zielsatz
