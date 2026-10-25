/-
  WITNESS (Logik/WP/HA): the user obligation of the certificate of `beispiele/104` (the reference unit), whose
  certificate the tree keeps as `Korpus/Programme/GenOblig104.lean`, proved in GabbroV.
-/
import Grammatik.Korpus.Programme.GenOblig104
import Grammatik.Logik.WP.HA.Pflicht
import Grammatik.Kern.Syntax.Koernung

namespace Gabbro.Grammatik

namespace G104_referenz_oblig

/-! ## The user obligation, discharged in GabbroV: a call against a contract and a frame -/

open Gabbro.Grammatik.WP Gabbro.Grammatik.Zielsatz

theorem keinAtomar : ∀ g : gD.Glob, gD.atomar g = false := fun g => nomatch g

/-- `lies`: the body returns the slot it reads. -/
theorem lies_lauf (O : Orakel gD) (U : Umwelt gD) (A : AUmwelt gD) (hA : HavocA (GeteiltA gP gE.ws) A)
    (passes : Nat) (R : ∀ f : gD.Fn, World gD → Env gD (gD.params f) → RufAusgang f) (σ : World gD)
    (ρ : Env gD gCtx_lies) :
    ∃ σ' v, execEndHA (V := vertragVon gD g_lies) gS O U A passes R gBody_lies σ ρ = .zurueck σ' v ∧
      EnsAmRueck gP g_lies σ σ' ρ v := by
  refine ⟨_, _, rfl, ?_⟩
  simp only [EnsAmRueck, gP, g_lies, gEns_lies, leseA_ohneAtomar keinAtomar hA, evalErg, ergEnv]
  simp only [eval, wahr?]
  exact decide_eq_true rfl

/-- `einzahlen` under a call meaning that keeps the contracts and frames: a return meets `old(K[i]) ≤ K[i]`. -/
theorem einzahlen_post (O : Orakel gD) (U : Umwelt gD) (A : AUmwelt gD) (hA : HavocA (GeteiltA gP gE.ws) A)
    (passes : Nat) (R : ∀ f : gD.Fn, World gD → Env gD (gD.params f) → RufAusgang f)
    (hRR : RespektiertRahmen gP R) (σ : World gD) (ρ : Env gD gCtx_einzahlen) :
    RueckPost gP g_einzahlen σ ρ
      (execEndHA (V := vertragVon gD g_einzahlen) gS O U A passes R gBody_einzahlen σ ρ) := by
  simp only [gBody_einzahlen, execEndHA, execStmtHA, leseA_ohneAtomar keinAtomar hA]
  generalize hout : R g_lies _ _ = out
  cases out with
  | ok σ2 v =>
    have hfr := (hRR.2 _ _ _ _ _ hout).1.1 GTab.Konto rfl
    unfold RueckPost
    refine ⟨fun σ' w h => ?_, fun σ' r h => by cases h⟩
    cases h
    refine ⟨?_, fun i _ => nomatch i⟩
    simp only [EnsAmRueck, gP, g_einzahlen, gEns_einzahlen, eval, wahr?, ergEnv]
    simp only [lese_slots_gleich, hfr]
    erw [schreibSlot_slots_same]
    exact decide_eq_true (σ.slots _ _ _).le_hi
  | why _ r => exact (Fin.cast rfl r).elim0
  | logik e => unfold RueckPost; exact ⟨fun _ _ h => (by simp at h), fun _ _ h => (by simp at h)⟩
  | hardware e => unfold RueckPost; exact ⟨fun _ _ h => (by simp at h), fun _ _ h => (by simp at h)⟩

/-- `einzahlen` under the gated call meaning ends in no precondition stop. -/
theorem einzahlen_kein_vor (O : Orakel gD) (U : Umwelt gD) (A : AUmwelt gD) (hA : HavocA (GeteiltA gP gE.ws) A)
    (passes : Nat) (R : ∀ f : gD.Fn, World gD → Env gD (gD.params f) → RufAusgang f)
    (hOV : OhneVorbedingung R) (σ : World gD) (ρ : Env gD gCtx_einzahlen) (g : gD.Fn) :
    execEndHA (V := vertragVon gD g_einzahlen) gS O U A passes (torRuf gP R) gBody_einzahlen σ ρ ≠
      .logik (.vorbedingung g) := by
  simp only [gBody_einzahlen, execEndHA, execStmtHA, leseA_ohneAtomar keinAtomar hA, torRuf, gP, g_lies]
  simp only [eval, wahr?, if_true]
  generalize hout : R GFn.lies _ _ = out
  cases out with
  | ok σ2 v => simp
  | why _ r => exact (Fin.cast rfl r).elim0
  | logik e => simpa using hOV _ _ _ e hout g
  | hardware e => simp

/-- `einzahlen` under a call meaning without `logik` ends in no `logik` stop at all. -/
theorem einzahlen_kein_logik (O : Orakel gD) (U : Umwelt gD) (A : AUmwelt gD) (hA : HavocA (GeteiltA gP gE.ws) A)
    (passes : Nat) (R : ∀ f : gD.Fn, World gD → Env gD (gD.params f) → RufAusgang f)
    (hOL : OhneLogik R) (σ : World gD) (ρ : Env gD gCtx_einzahlen) (e : Logik gD) :
    execEndHA (V := vertragVon gD g_einzahlen) gS O U A passes R gBody_einzahlen σ ρ ≠ .logik e := by
  simp only [gBody_einzahlen, execEndHA, execStmtHA, leseA_ohneAtomar keinAtomar hA]
  generalize hout : R g_lies _ _ = out
  cases out with
  | ok σ2 v => simp
  | why _ r => exact (Fin.cast rfl r).elim0
  | logik e' => exact absurd hout (hOL _ _ _ e')
  | hardware e' => simp

/-- **The body obligations, as weakest preconditions**, at every budget. -/
theorem pflicht (passes : Nat) (f : gD.Fn) : PflichtWP gP passes gE.Q gS (GeteiltA gP gE.ws) f := by
  cases f with
  | einzahlen =>
    refine ⟨fun O' _ _ _ U _ A hA R hRR hOV σ ρ _ => ⟨?_, ?_⟩, fun O' _ _ _ U _ A hA R _ hOL σ ρ _ => ?_⟩
    · exact einzahlen_post O' U A hA passes R hRR σ ρ
    · exact einzahlen_kein_vor O' U A hA passes R hOV σ ρ
    · exact einzahlen_kein_logik O' U A hA passes R hOL σ ρ
  | lies =>
    refine ⟨fun O' _ _ _ U _ A hA R _ _ σ ρ _ => ⟨?_, ?_⟩, fun O' _ _ _ U _ A hA R _ _ σ ρ _ => ?_⟩
    · obtain ⟨σ', v, h, hens⟩ := lies_lauf O' U A hA passes R σ ρ
      unfold wpEA
      erw [h]
      exact ⟨fun σ'' w hw => by cases hw; exact ⟨hens, fun i _ => nomatch i⟩, fun _ _ hw => by cases hw⟩
    · obtain ⟨σ', v, h, _⟩ := lies_lauf O' U A hA passes (torRuf gP R) σ ρ
      unfold wpEA
      erw [h]
      intro g hg
      cases hg
    · obtain ⟨σ', v, h, _⟩ := lies_lauf O' U A hA passes R σ ρ
      unfold wpEA
      erw [h]
      intro e he
      cases he

theorem sperrInvLokal : SperrInvLokal gS := by
  intro L _ _ _
  cases L
  rfl

theorem startPflicht : StartPflicht gE :=
  ⟨fun L => by cases L; rfl, fun a ha => by simp [gE] at ha⟩

/-- **Premise (b) of the goal theorem, proved.** -/
theorem nutzerPflicht_bewiesen : NutzerPflichtA gE :=
  nutzerPflichtA_aus gE (fun passes f => pflicht passes f) sperrInvLokal (fun a => nomatch a) startPflicht

/-- **THE GOAL THEOREM FOR THE REFERENCE UNIT, WITHOUT AN OPEN LOGIC PREMISE.** -/
theorem gP_gabbro_bewiesen (O : Orakel gD) (hH : HardwareAnnahmen O gE.Q) (passes : Nat)
    (sp : Speicher gD.mitRuhe)
    (init : Faden → Σ f : gD.mitRuhe.Fn, Env gD.mitRuhe (gD.mitRuhe.params f))
    (hL : Laufzeit gE sp init) (lebt0 : Faden → Bool)
    (K : FadenMaschine gD.mitRuhe)
    (hK : FadenErreichbarX gE.P.mitRuhe O.mitRuhe passes (GeteiltV (D := gD) gE.P gE.ws)
      (FadenStart gE.P.mitRuhe sp init lebt0) K) :
    ZielFX gE.P.mitRuhe gE.S.mitRuhe O.mitRuhe passes (GeteiltV (D := gD) gE.P gE.ws)
      (RufStartG gE.P.mitRuhe sp init) [] K :=
  gP_gabbro_f nutzerPflicht_bewiesen O hH passes sp init hL lebt0 K hK

#print axioms gP_gabbro_bewiesen

end G104_referenz_oblig

end Gabbro.Grammatik
