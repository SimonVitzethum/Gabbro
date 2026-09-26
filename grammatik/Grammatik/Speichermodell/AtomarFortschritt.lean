/-
  File:      Grammatik/Speichermodell/AtomarFortschritt.lean
  Subject:   PROGRESS WITH SHARED ATOMICS: `FortschrittG` on every machine GX reaches (Opus lane
             O25b, 2026-09-26). Standalone.

  `fortschrittG_aus` (Fortschritt.lean) needs five facts about the reached machine: the thread
  invariants `FortInvG`, `RufFadenSauberG`, `HaeltInvG`, `RangInvG`, `AntInvG` -- each read only
  a thread's own state and is preserved by every G step -- plus `KeinLogikHaltG` and `BereichG`
  (no float range check fails), which come from the replay.

  * `gaInvF` -- a property of the thread vector that every G step preserves holds on every GA
    run (and so on every GX run, `gx_ga_lauf`): a GA step is a G step from the machine with its
    memory replaced, and the threads are the machine's own.
  * `fadenSA_bereich` -- the twin of `fadenS_bereich` over the replay with the atomic rely: a
    failing float range check at the head would make the head predict `logik bereich` against
    the environment that answers the check's shared atomic reads as the machine did, which
    `KoerperGutSA` excludes.
  * `fortschrittG_GX` -- `FortschrittG` at every machine GX reaches.
-/
import Grammatik.Speichermodell.AtomarLauf
import Grammatik.Speichermodell.AtomarZeuge
import Grammatik.Fortschritt
import Grammatik.AntwortOrte
import Grammatik.RufHaeltG

namespace Gabbro.Grammatik

open Speichermodell Zielsatz

variable {D : Deklaration}

section Faeden

variable {P : Programm D} {O : Orakel D} {passes : Nat}

/-- **A thread-vector property every G step preserves holds on every GA run.** -/
theorem gaInvF {J : (Faden → RufFadenG D) → Prop} {M0 : RufMaschineG D} (h0 : J M0.faeden)
    (hs : ∀ (M M' : RufMaschineG D) (u : Faden), J M.faeden → RufSchrittG P O passes M u M' →
      J M'.faeden)
    {M : RufMaschineG D} (hr : RufErreichbarGA P O passes M0 M) : J M.faeden :=
  gaInv (I := fun M => J M.faeden) (fun _ _ e h => e ▸ h) h0 hs hr

theorem ga_fortInv (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f))
    {M : RufMaschineG D} (hr : RufErreichbarGA P O passes (RufStartG P sp init) M) :
    ∀ t, FortInvG (M.faeden t) :=
  gaInvF (J := fun fa => ∀ t, FortInvG (fa t))
    (fortInvG_erreichbar (O := O) (passes := passes) sp init .start)
    (fun _ _ _ h hs => fortInvG_schritt_alle hs h) hr

theorem ga_sauber (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f))
    {M : RufMaschineG D} (hr : RufErreichbarGA P O passes (RufStartG P sp init) M) :
    ∀ t, RufFadenSauberG (M.faeden t) :=
  gaInvF (J := fun fa => ∀ t, RufFadenSauberG (fa t)) (rufStartG_sauber P sp init)
    (fun _ _ _ h hs => rufSchrittG_sauber hs h) hr

theorem ga_haeltInv (hO : GutO O) (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f))
    {M : RufMaschineG D} (hr : RufErreichbarGA P O passes (RufStartG P sp init) M) :
    ∀ t, HaeltInvG (M.faeden t) :=
  gaInvF (J := fun fa => ∀ t, HaeltInvG (fa t)) (haeltInvG_start P sp init)
    (fun M M' g h hs t => by
      by_cases htg : t = g
      · subst htg
        exact rufSchrittG_haeltInv hO hs (h t)
      · rw [rufSchrittG_passt_anders P O passes M M' g t htg hs]
        exact h t) hr

theorem ga_antInv {C : D.Ax ⊕ D.Reg → Bool} (hB : ∀ g, (P.rumpf g).ants.all C = true)
    (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f))
    {M : RufMaschineG D} (hr : RufErreichbarGA P O passes (RufStartG P sp init) M) :
    ∀ t, AntInvG C (M.faeden t) :=
  gaInvF (J := fun fa => ∀ t, AntInvG C (fa t))
    (antInvG_erreichbar (O := O) (pa := passes) hB sp init .start)
    (fun M M' u h hs t => by
      by_cases htu : t = u
      · subst htu
        exact antInvG_schritt hB hs (h t)
      · rw [rufSchrittG_fremd hs t htu]
        exact h t) hr

end Faeden

section Bereich

variable {P : Programm D} {O : Orakel D} {passes : Nat} {Q : AxEns D} {S : SperrInv D}
  {lok : D.Tab ⊕ D.Glob → Bool} {Tg : D.Tab ⊕ D.Glob → Prop}

/-- **A replayed thread passes every float range check at its head, under the atomic rely**
    (the twin of `fadenS_bereich`). -/
theorem fadenSA_bereich (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O)
    (hS : SperrInvOk S) {sp : Speicher D} (hsp : ∀ L, S.inv L sp = true)
    (hK : ∀ f, KoerperGutSA P passes Q S Tg f) (hFS : ∀ f, FussSX P S lok Tg f)
    {M : RufMaschineG D} (t : Faden)
    (hF : FadenSA P O passes Q S lok Tg (M.faeden t) (M.weltVon t)) :
    BereichG M t := by
  refine ⟨fun l Γ Λ Λ' ρ op l1 h1 l2 h2 lo hi a b rest k hr hv => ?_,
    fun l Γ Λ Λ' ρ q lo hi rest k hr hv => ?_,
    fun l Γ Λ Λ' ρ l1 h1 e lo hi rest k hr hv => ?_⟩
  · obtain ⟨H, HA, HU, HX, σ, hfx, hkx, hg, hok, hno⟩ :=
      kopfSA_keineLogik' hO hRL hQ hS hsp hK hF.1 hr
    have hab : a.orte ++ b.orte ⊆ fussOrteG P (M.faeden t).kopf.f :=
      fun _ h => hok.2.1 (List.mem_append_left _ h)
    have hd : ∀ o ∈ a.orte ++ b.orte, OrtDarf Λ o := fun o ho =>
      (List.mem_append.mp ho).elim (a.orte_darf o) (b.orte_darf o)
    obtain ⟨HX', hfx', _, hsub, hrec⟩ :=
      lese_schritt Tg hfx hkx Λ (a.orte ++ b.orte) (M.weltVon t).speicher
    have hPX := umweltAusA_passt Tg hfx'
    have hHA := umweltAusA_ok Tg HX'
    have hgl := mischT_gleichAuf hg (orte_stabilX (hFS _) hd hab) Λ Λ
    have ea := eval_gleichAuf a (fun _ h => List.mem_append_right _ (List.mem_append_left _ h))
      hgl ρ
    have eb := eval_gleichAuf b (fun _ h => List.mem_append_right _ (List.mem_append_right _ h))
      hgl ρ
    refine hno _ (passtX_teil hsub hPX) hHA .bereich ?_
    rw [semHA_dann]
    simp only [execBlockHA, hrec _ hPX hHA, ea, eb, hv]
    exact weiterHA_logik _ _ _ _ _ _ _ _
  · obtain ⟨H, HA, HU, HX, σ, hfx, hkx, hg, hok, hno⟩ :=
      kopfSA_keineLogik' hO hRL hQ hS hsp hK hF.1 hr
    refine hno _ (umweltAusA_passt Tg hfx) (umweltAusA_ok Tg HX) .bereich ?_
    rw [semHA_dann]
    simp only [execBlockHA, hv]
    exact weiterHA_logik _ _ _ _ _ _ _ _
  · obtain ⟨H, HA, HU, HX, σ, hfx, hkx, hg, hok, hno⟩ :=
      kopfSA_keineLogik' hO hRL hQ hS hsp hK hF.1 hr
    have he : e.orte ⊆ fussOrteG P (M.faeden t).kopf.f :=
      fun _ h => hok.2.1 (List.mem_append_left _ h)
    obtain ⟨HX', hfx', _, hsub, hrec⟩ := lese_schritt Tg hfx hkx Λ e.orte (M.weltVon t).speicher
    have hPX := umweltAusA_passt Tg hfx'
    have hHA := umweltAusA_ok Tg HX'
    have ee := eval_gleichAuf e (fun _ h => List.mem_append_right _ h)
      (mischT_gleichAuf hg (expr_stabilX (hFS _) e he) Λ Λ) ρ
    refine hno _ (passtX_teil hsub hPX) hHA .bereich ?_
    rw [semHA_dann]
    simp only [execBlockHA, hrec _ hPX hHA, ee, hv]
    exact weiterHA_logik _ _ _ _ _ _ _ _

end Bereich

section Fort

variable {P : Programm D} {O : Orakel D} {passes : Nat}

/-- **`FortschrittG` on every GA-reached machine** at which no `logik` check and no float range
    check fails (the argument of `fortschrittG_aus`, from the thread invariants over GA). -/
theorem fortschrittG_GA (hO : GutO O) (hSt : StufenM P) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (hND : ∀ t, (offen (startSpur (D := D) (init t).1)).Nodup) {M : RufMaschineG D}
    (hr : RufErreichbarGA P O passes (RufStartG P sp init) M) (hL : KeinLogikHaltG O passes M)
    (hB : ∀ t, BereichG M t) (hAnt : ∀ g, ∀ x ∈ (P.rumpf g).ants, StelleOk D x) :
    Zielsatz.FortschrittG P O passes M := fun t =>
  fortschritt_faden hO (ga_fortInv sp init hr t) (ga_sauber sp init hr t).kopf_wartend
    (fun L hL' => (ga_haeltInv hO sp init hr t).alle _ List.mem_cons_self L hL') (hL t) (hB t)
    (gaInv_rang hO hSt sp init hND hr t)
    (ga_antInv (fun g => List.all_eq_true.mpr fun x hx => stelleC_iff.mpr (hAnt g x hx)) sp init
      hr t _ List.mem_cons_self)

end Fort

#print axioms Gabbro.Grammatik.fadenSA_bereich
#print axioms Gabbro.Grammatik.fortschrittG_GA

end Gabbro.Grammatik
