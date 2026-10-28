/- Part 2 of 3 of `Verbund` (split by instrumente/teile/lean-teilen.py; the umbrella `Verbund.lean` imports all parts). -/
import Grammatik.Zielsatz.Faeden.Verbund.T1

namespace Gabbro.Grammatik.Zielsatz

open Gabbro.Grammatik
variable {D : Deklaration}
open Gabbro.Grammatik
variable {D : Deklaration}

section Verbund

variable [DecidableEq D.Fn] {E₁ E₂ : Einheit D} {e : D.Fn → Bool}

omit [DecidableEq D.Fn] in
/-- Under a shared link declaration the second unit's program is the first one's contracts
    with the second one's bodies. -/
theorem p2_eq (hV : Verbindbar E₁ E₂) : E₂.P = mitRumpf E₁.P E₂.P.rumpf := by
  unfold mitRumpf
  rw [hV.invariante, hV.requires, hV.ensures, hV.unterbricht]

omit [DecidableEq D.Fn] in
theorem verbindeP_rumpf (f : D.Fn) :
    (verbindeP e E₁ E₂).rumpf f = (teilP e E₁ E₂ f).rumpf f := by
  show (if e f then E₁.P.rumpf f else E₂.P.rumpf f) = (if e f then E₁.P else E₂.P).rumpf f
  cases e f <;> rfl

omit [DecidableEq D.Fn] in
theorem teilP_gleich {f g : D.Fn} (h : e f = e g) : teilP e E₁ E₂ f = teilP e E₁ E₂ g := by
  unfold teilP
  rw [h]

theorem teilP_teil (hV : Verbindbar E₁ E₂) (f : D.Fn) :
    teilP e E₁ E₂ f = mitRumpf E₁.P (teilP e E₁ E₂ f).rumpf := by
  unfold teilP
  cases e f
  · exact p2_eq hV
  · rfl

theorem fussOrteG_teil (hV : Verbindbar E₁ E₂) (f : D.Fn) :
    fussOrteG (verbindeP e E₁ E₂) f = fussOrteG (teilP e E₁ E₂ f) f := by
  conv => rhs; rw [teilP_teil hV f]
  exact fussOrteG_mitRumpf2 E₁.P _ _ f (verbindeP_rumpf f)

theorem fussOrte_teil (hV : Verbindbar E₁ E₂) (f : D.Fn) :
    fussOrte (verbindeP e E₁ E₂) f = fussOrte (teilP e E₁ E₂ f) f := by
  conv => rhs; rw [teilP_teil hV f]
  exact fussOrte_mitRumpf2 E₁.P _ _ f (verbindeP_rumpf f)

theorem kandB_teil (hV : Verbindbar E₁ E₂) (fs : List D.Fn) (f : D.Fn) :
    kandB (verbindeP e E₁ E₂) fs = kandB (teilP e E₁ E₂ f) fs := by
  rw [teilP_teil hV f]
  rfl

theorem ruftB_teil (h g : D.Fn) :
    ruftB (verbindeP e E₁ E₂) h g = ruftB (teilP e E₁ E₂ h) h g := by
  unfold ruftB
  rw [verbindeP_rumpf]

/-- **The linked call graph of a root lies in its composed hull** (`HuelleV`): no callback. -/
theorem huelle_of_reach {fs : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hNC : KeinRueckruf fs e E₁ E₂) (w : D.Fn) :
    ∀ h, reachB (verbindeP e E₁ E₂) fs w h = true → HuelleV fs e E₁ E₂ w h := by
  refine reachB_in _ fs (Or.inl ⟨rfl, reachB_wurzel _ fs w⟩) ?_
  intro h g hh hr
  rw [ruftB_teil] at hr
  rcases hh with ⟨heh, hwh⟩ | ⟨f, hne, heh, hwf, hfh⟩
  · rw [teilP_gleich heh] at hr
    have hwg := reachB_ruft _ hvoll hwh hr
    by_cases hg : e g = e w
    · exact Or.inl ⟨hg, hwg⟩
    · exact Or.inr ⟨g, hg, rfl, hwg, reachB_wurzel _ fs g⟩
  · rw [teilP_gleich heh] at hr
    have hfg := reachB_ruft _ hvoll hfh hr
    exact Or.inr ⟨f, hne, hNC w f g hne hwf hfg, hwf, hfg⟩

theorem teil_abg {fs : List D.Fn}
    (hA₁ : ∀ w, AbgK E₁.P fs (reachB E₁.P fs w)) (hA₂ : ∀ w, AbgK E₂.P fs (reachB E₂.P fs w))
    (f : D.Fn) : ∀ w, AbgK (teilP e E₁ E₂ f) fs (reachB (teilP e E₁ E₂ f) fs w) := by
  unfold teilP
  cases e f
  · exact hA₂
  · exact hA₁

/-- Every edge of the owner's view of `f` is an edge of the linked program (placeholders are
    leaves). -/
theorem kante_teil (hB₁ : Platzhalter e E₁.P) (hB₂ : Platzhalter (fun f => !e f) E₂.P)
    (f h g : D.Fn) (hr : ruftB (teilP e E₁ E₂ f) h g = true) :
    ruftB (verbindeP e E₁ E₂) h g = true := by
  rw [ruftB_teil]
  by_cases heh : e h = e f
  · rw [teilP_gleich heh]
    exact hr
  · exfalso
    unfold teilP at hr
    cases hf : e f
    · rw [hf] at heh hr
      have : e h = true := by cases h' : e h; exact absurd h' heh; rfl
      have := hB₂ h g (by simp only [this, Bool.not_true])
      simp only [Bool.false_eq_true, ↓reduceIte] at hr
      rw [this] at hr
      cases hr
    · rw [hf] at heh hr
      have : e h = false := by cases h' : e h; rfl; exact absurd h' heh
      have := hB₁ h g this
      simp only [↓reduceIte] at hr
      rw [this] at hr
      cases hr

omit [DecidableEq D.Fn] in
theorem mle_rufM {fs : List D.Fn} {Z Z' : D.Fn → Bool} (h : ∀ g, Z g = true → Z' g = true) :
    MLe (rufM fs Z) (rufM fs Z') := by
  refine ⟨fun g hg => h g hg, fun n hn => ?_, fun _ _ => rfl⟩
  refine List.all_eq_true.mpr fun g hg => ?_
  have h1 := List.all_eq_true.mp hn g hg
  simp only [Bool.or_eq_true] at h1 ⊢
  rcases h1 with h1 | h1
  · exact Or.inl h1
  · exact Or.inr (h g h1)

/-- **The linked call graphs are closed.** -/
theorem abg_verbinde {fs : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hA₁ : ∀ w, AbgK E₁.P fs (reachB E₁.P fs w)) (hA₂ : ∀ w, AbgK E₂.P fs (reachB E₂.P fs w))
    (hB₁ : Platzhalter e E₁.P) (hB₂ : Platzhalter (fun f => !e f) E₂.P) :
    ∀ w, AbgK (verbindeP e E₁ E₂) fs (reachB (verbindeP e E₁ E₂) fs w) := by
  intro w f hf
  have hu := teil_abg (e := e) hA₁ hA₂ f f f (reachB_wurzel _ fs f)
  have hsub : ∀ g, reachB (teilP e E₁ E₂ f) fs f g = true →
      reachB (verbindeP e E₁ E₂) fs w g = true :=
    reachB_teil hvoll (kante_teil hB₁ hB₂ f) hf
  rw [verbindeP_rumpf]
  exact mE_mono (mle_rufM hsub) _ hu

omit [DecidableEq D.Fn] in
theorem mem_ws_verbinde {w : D.Fn} (h : w ∈ (verbinde e E₁ E₂).ws) : w ∈ E₁.ws ∨ w ∈ E₂.ws := by
  simp only [Einheit.ws, verbinde, List.map_append, List.mem_append] at h ⊢
  rcases h with ((h | h) | (h | h)) | (h | h)
  · exact Or.inl (Or.inl (Or.inl h))
  · exact Or.inr (Or.inl (Or.inl h))
  · exact Or.inl (Or.inl (Or.inr h))
  · exact Or.inr (Or.inl (Or.inr h))
  · exact Or.inl (Or.inl (Or.inr h))
  · exact Or.inr (Or.inl (Or.inr h))

/-- **The linked unit is accepted**: the per-unit verdicts carry every per-body component,
    the link check carries the three whole-program components over the composed hulls. -/
theorem akzeptiertSpec_verbinde {fs : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hA₁ : AkzeptiertSpec E₁.P E₁.S fs E₁.ws) (hA₂ : AkzeptiertSpec E₂.P E₂.S fs E₂.ws)
    (hV : Verbindbar E₁ E₂) (hS : SchnittstelleSpec fs e E₁ E₂) :
    AkzeptiertSpec (verbinde e E₁ E₂).P (verbinde e E₁ E₂).S fs (verbinde e E₁ E₂).ws := by
  have hH := huelle_of_reach (e := e) (E₁ := E₁) (E₂ := E₂) hvoll hS.keinRueckruf
  have hfrag : ∀ f, ((teilP e E₁ E₂ f).rumpf f).gOk
      (kandB (teilP e E₁ E₂ f) fs (fussOrteG (teilP e E₁ E₂ f) f)) (fun _ => true) = true := by
    intro f
    unfold teilP
    cases e f
    · exact List.all_eq_true.mp hA₂.frag f (hvoll f)
    · exact List.all_eq_true.mp hA₁.frag f (hvoll f)
  have hGetrennt : ∀ c, LokBedarf e E₁ E₂ c →
      Getrennt (verbinde e E₁ E₂).P fs (verbinde e E₁ E₂).ws c := by
    intro c hc w₁ hw₁ w₂ hw₂ hne f g hf hcf hg
    refine hS.lok c hc w₁ hw₁ w₂ hw₂ hne f g (hH w₁ f hf) ?_ (hH w₂ g hg)
    rw [← fussOrteG_teil hV]
    exact hcf
  refine ⟨?_, abg_verbinde hvoll hA₁.abg hA₂.abg hS.blatt₁ hS.blatt₂, ?_, ?_, hA₁.sperrOrte,
    ?_, ?_, ?_, ?_, ?_⟩
  · -- frag
    refine List.all_eq_true.mpr fun f _ => ?_
    show ((verbindeP e E₁ E₂).rumpf f).gOk
      (kandB (verbindeP e E₁ E₂) fs (fussOrteG (verbindeP e E₁ E₂) f)) (fun _ => true) = true
    rw [verbindeP_rumpf, kandB_teil hV fs f, fussOrteG_teil hV]
    exact hfrag f
  · -- fuss
    intro f
    have hlok : ∀ c, LokBedarf e E₁ E₂ c → lokW (verbinde e E₁ E₂).P fs (verbinde e E₁ E₂).ws c = true :=
      fun c hc => @decide_eq_true _ (Classical.propDecidable _) (hGetrennt c hc)
    refine ⟨fun c hc => ?_, fun c hc => ?_⟩
    · have hc' : c ∈ fussOrte (teilP e E₁ E₂ f) f := by
        rw [← fussOrte_teil hV]
        exact hc
      by_cases hs : sigB f c = true
      · exact Or.inl (by rw [hs, Bool.true_or])
      · by_cases hg : ∃ L, Bewacht c L ∧ c ∈ E₁.S.orte L
        · exact Or.inr hg
        · refine Or.inl ?_
          rw [hlok c ⟨f, Or.inl ⟨hc', by simpa using hs, hg⟩⟩, Bool.or_true]
    · have hc' : c ∈ ((teilP e E₁ E₂ f).rumpf f).regs.flatMap D.rtraeger := by
        rw [← verbindeP_rumpf]
        exact hc
      by_cases hs : sigB f c = true
      · rw [hs, Bool.true_or]
      · rw [hlok c ⟨f, Or.inr ⟨hc', by simpa using hs⟩⟩, Bool.or_true]
  · -- stufen
    intro f
    show Grammatik.mE (bodenM f) ((verbindeP e E₁ E₂).rumpf f) = true
    rw [verbindeP_rumpf]
    unfold teilP
    cases e f
    · exact hA₂.stufen f
    · exact hA₁.stufen f
  · -- wurzeln
    intro w hw
    rcases mem_ws_verbinde hw with h | h
    · exact hA₁.wurzeln w h
    · exact hA₂.wurzeln w h
  · -- einzeln
    intro w hw
    obtain ⟨h1, h2, h3⟩ := hS.einzeln w hw
    exact ⟨h1, h2, fun f hf c hc => h3 f (hH w f hf) c hc⟩
  · -- renn
    intro c hB hAt w₁ hw₁ w₂ hw₂ hne g hg hgc h hh
    have := hS.renn c hB hAt w₁ hw₁ w₂ hw₂ hne g (hH w₁ g hg) hgc h (hH w₂ h hh)
    have e' : fussOrteG (verbinde e E₁ E₂).P h = fussOrteG (teilP e E₁ E₂ h) h := fussOrteG_teil hV h
    rw [e']
    exact this
  · -- antworten
    intro f x hx
    change x ∈ ((verbindeP e E₁ E₂).rumpf f).ants at hx
    rw [verbindeP_rumpf] at hx
    unfold teilP at hx
    cases hf : e f
    · rw [hf] at hx
      exact hA₂.antworten f x hx
    · rw [hf] at hx
      exact hA₁.antworten f x hx
  · -- masken: the link check over the composed hull (Opus agent H, 2026-09-26)
    intro w hw h hh
    show mE (NurMaskiert D) ((verbindeP e E₁ E₂).rumpf h) = true
    rw [verbindeP_rumpf]
    exact hS.masken w hw h (hH w h hh)

/-- **The user's duty of the linked unit is the two units' duties.** -/
theorem nutzerPflicht_verbinde (hV : Verbindbar E₁ E₂) (hQ : E₂.Q = E₁.Q)
    (hN₁ : NutzerTeil e E₁) (hN₂ : NutzerTeil (fun f => !e f) E₂) :
    NutzerPflicht (verbinde e E₁ E₂) := by
  have hS : E₂.S = E₁.S := hV.sperren.symm
  refine ⟨⟨fun passes f => ?_, hN₁.logik.2.1, hN₁.logik.2.2⟩, ⟨hN₁.start.sperren, ?_⟩⟩
  · show KoerperGutS (verbindeP e E₁ E₂) passes E₁.Q E₁.S f ∧
      InvGutS (verbindeP e E₁ E₂) passes E₁.Q E₁.S f ∧
      InvGutGrund (verbindeP e E₁ E₂) passes E₁.Q E₁.S f
    cases hf : e f
    · obtain ⟨k, i, g⟩ := hN₂.logik.1 passes f (by simp only [hf, Bool.not_false])
      rw [p2_eq hV, hQ, hS] at k i g
      have hr : (fun f => if e f then E₁.P.rumpf f else E₂.P.rumpf f) f = E₂.P.rumpf f := by
        simp only [hf, Bool.false_eq_true, ↓reduceIte]
      exact ⟨(koerper_mitRumpf2 E₁.P _ _ passes _ _ f hr).mpr k,
        (invGutS_mitRumpf2 E₁.P _ _ passes _ _ f hr).mpr i,
        (invGutGrund_mitRumpf2 E₁.P _ _ passes _ _ f hr).mpr g⟩
    · obtain ⟨k, i, g⟩ := hN₁.logik.1 passes f hf
      have hr : (fun f => if e f then E₁.P.rumpf f else E₂.P.rumpf f) f = E₁.P.rumpf f := by
        simp only [hf, ↓reduceIte]
      exact ⟨(koerper_mitRumpf2 E₁.P _ E₁.P.rumpf passes _ _ f hr).mpr k,
        (invGutS_mitRumpf2 E₁.P _ E₁.P.rumpf passes _ _ f hr).mpr i,
        (invGutGrund_mitRumpf2 E₁.P _ E₁.P.rumpf passes _ _ f hr).mpr g⟩
  · intro a ha
    show ReqAmEintritt E₁.P a.1 (E₁.sp0.welt []) a.2
    simp only [verbinde, List.mem_append] at ha
    rcases ha with (h | h) | (h | h)
    · exact hN₁.start.req a (List.mem_append_left _ h)
    · have := hN₂.start.req a (List.mem_append_left _ h)
      unfold ReqAmEintritt at this ⊢
      rw [hV.requires, hV.speicher]
      exact this
    · exact hN₁.start.req a (List.mem_append_right _ h)
    · have := hN₂.start.req a (List.mem_append_right _ h)
      unfold ReqAmEintritt at this ⊢
      rw [hV.requires, hV.speicher]
      exact this

end Verbund
/-- **LINKING, PROVED.** -/
theorem gabbro_ziel_verbund_sc : GabbroZielVerbundSC := by
  intro C D _ E₁ E₂ e fs ls cs h₁ h₂ hV hS hN₁ hN₂ hQ O hH passes sp init hL lebt0 K hK
  have hA := akzeptiertSpec_verbinde fs.2 (C.korrekt E₁ fs ls cs h₁) (C.korrekt E₂ fs ls cs h₂)
    hV hS
  have hB : akzeptiert_pruefer.akzeptiert (verbinde e E₁ E₂) fs.1 ls.1 cs.1 = true :=
    (akzeptiert_iff fs.2 ls.2 cs.2).mpr hA
  exact gabbro_ziel_sc akzeptiert_pruefer D (verbinde e E₁ E₂) fs ls cs hB
    (nutzerPflicht_verbinde hV hQ hN₁ hN₂) O hH passes sp init hL lebt0 K hK


end Gabbro.Grammatik.Zielsatz


namespace Gabbro.Grammatik.Zielsatz
open Gabbro.Grammatik
variable {D : Deklaration}

/-! ## The link check as ONE Bool -/


end Gabbro.Grammatik.Zielsatz
