/- Part 3 of 3 of `Verbund` (split by instrumente/teile/lean-teilen.py; the umbrella `Verbund.lean` imports all parts). -/
module
public import Grammatik.Zielsatz.Faeden.Verbund.T2
public import Grammatik.Zielsatz.Kern.Akzeptiert.Teil3
@[expose] public section


namespace Gabbro.Grammatik.Zielsatz

open Gabbro.Grammatik
variable {D : Deklaration}
open Gabbro.Grammatik
variable {D : Deklaration}
open Gabbro.Grammatik
variable {D : Deklaration}

section Bool

variable [DecidableEq D.Fn]

/-- `Platzhalter`, decided: every function the unit does not own calls nothing. -/
def platzhalterB (fs : List D.Fn) (eigen : D.Fn → Bool) (P : Programm D) : Bool :=
  fs.all fun f => eigen f || fs.all fun g => !ruftB P f g

/-- `HuelleV`, decided. -/
def huelleB (fs : List D.Fn) (e : D.Fn → Bool) (E₁ E₂ : Einheit D) (w h : D.Fn) : Bool :=
  (decide (e h = e w) && reachB (teilP e E₁ E₂ w) fs w h) ||
  fs.any fun f => !decide (e f = e w) && decide (e h = e f) &&
    reachB (teilP e E₁ E₂ w) fs w f && reachB (teilP e E₁ E₂ f) fs f h

/-- `KeinRueckruf`, decided. -/
def keinRueckrufB (fs : List D.Fn) (e : D.Fn → Bool) (E₁ E₂ : Einheit D) : Bool :=
  fs.all fun w => fs.all fun f => fs.all fun h =>
    !(!decide (e f = e w) && reachB (teilP e E₁ E₂ w) fs w f &&
      reachB (teilP e E₁ E₂ f) fs f h) || decide (e h = e f)

/-- `LokBedarf`, decided. -/
def lokBedarfB (fs : List D.Fn) (e : D.Fn → Bool) (E₁ E₂ : Einheit D) (c : D.Tab ⊕ D.Glob) :
    Bool :=
  fs.any fun f =>
    (istIn (fussOrte (teilP e E₁ E₂ f) f) c && !sigB f c &&
      !((waechterVon c).any fun L => istIn (E₁.S.orte L) c)) ||
    (istIn (((teilP e E₁ E₂ f).rumpf f).regs.flatMap D.rtraeger) c && !sigB f c)

/-- `GetrenntV`, decided. -/
def getrenntVB (fs : List D.Fn) (e : D.Fn → Bool) (E₁ E₂ : Einheit D) (ws : List D.Fn)
    (c : D.Tab ⊕ D.Glob) : Bool :=
  ws.all fun w₁ => ws.all fun w₂ => (decide (w₁ = w₂) && !(mehrfachB ws w₁)) ||
    (fs.all fun f => !(huelleB fs e E₁ E₂ w₁ f) || !(istIn (fussOrteG (teilP e E₁ E₂ f) f) c)) ||
    (fs.all fun g => !(huelleB fs e E₁ E₂ w₂ g) || !(TraegerSchreibt g c))

/-- `SchreibGetrenntV`, decided. -/
def schreibGetrenntVB (fs : List D.Fn) (e : D.Fn → Bool) (E₁ E₂ : Einheit D) (ws : List D.Fn)
    (c : D.Tab ⊕ D.Glob) : Bool :=
  ws.all fun w₁ => ws.all fun w₂ => decide (w₁ = w₂) ||
    (fs.all fun g => !(huelleB fs e E₁ E₂ w₁ g) || !(TraegerSchreibt g c)) ||
    (fs.all fun h => !(huelleB fs e E₁ E₂ w₂ h) ||
      (!(TraegerSchreibt h c) && !(istIn (fussOrteG (teilP e E₁ E₂ h) h) c)))

/-- `PoolSicherV`, decided over the carrier list `cs`. -/
def poolSicherVB (fs : List D.Fn) (cs : List (D.Tab ⊕ D.Glob)) (e : D.Fn → Bool)
    (E₁ E₂ : Einheit D) (w : D.Fn) : Bool :=
  (D.haelt w).isEmpty && decide (D.gruende w = 0) && fs.all fun f =>
    !(huelleB fs e E₁ E₂ w f) ||
      (cs.all fun c => !(TraegerSchreibt f c) || (!(waechterVon c).isEmpty || atomarB c))

/-- **THE LINK CHECK** (`SchnittstelleSpec`, decided): placeholders are leaves, no callback
    through an imported function, thread-locality, write separation and pool safety over
    the COMPOSED hulls, and both units' declared checks admitted over the linked program. -/
def schnittstelleB (fs : List D.Fn) (cs : List (D.Tab ⊕ D.Glob)) (e : D.Fn → Bool)
    (E₁ E₂ : Einheit D) : Bool :=
  platzhalterB fs e E₁.P && platzhalterB fs (fun f => !e f) E₂.P && keinRueckrufB fs e E₁ E₂ &&
    (cs.all fun c => !(lokBedarfB fs e E₁ E₂ c) || getrenntVB fs e E₁ E₂ (verbinde e E₁ E₂).ws c) &&
    (cs.all fun c => ausgenommenB c || schreibGetrenntVB fs e E₁ E₂ (verbinde e E₁ E₂).ws c) &&
    ((verbinde e E₁ E₂).ws.all fun w =>
      !(mehrfachB (verbinde e E₁ E₂).ws w) || poolSicherVB fs cs e E₁ E₂ w) &&
    (fs.all fun w => !(E₁.P.unterbricht w) || fs.all fun h =>
      !(huelleB fs e E₁ E₂ w h) || mE (NurMaskiert D) ((teilP e E₁ E₂ h).rumpf h)) &&
    Kernzelle.accumulatorB (verbinde e E₁ E₂).P fs cs (verbinde e E₁ E₂).akku && checkB (verbindeP e E₁ E₂) (tabsOf cs) (globsOf cs) fs (E₁.pruefungen ++ E₂.pruefungen)

variable {fs : List D.Fn} {cs : List (D.Tab ⊕ D.Glob)} {e : D.Fn → Bool} {E₁ E₂ : Einheit D}

theorem platzhalterB_iff (hvoll : ∀ g : D.Fn, g ∈ fs) {eigen : D.Fn → Bool} {P : Programm D} :
    platzhalterB fs eigen P = true ↔ Platzhalter eigen P := by
  unfold platzhalterB Platzhalter
  constructor
  · intro h f g hf
    have h1 := List.all_eq_true.mp h f (hvoll f)
    rw [hf, Bool.false_or] at h1
    have h2 := List.all_eq_true.mp h1 g (hvoll g)
    simpa using h2
  · intro h
    refine List.all_eq_true.mpr fun f _ => ?_
    cases hf : eigen f
    · rw [Bool.false_or]
      exact List.all_eq_true.mpr fun g _ => by simp only [h f g hf, Bool.not_false]
    · rfl

theorem huelleB_iff (hvoll : ∀ g : D.Fn, g ∈ fs) {w h : D.Fn} :
    huelleB fs e E₁ E₂ w h = true ↔ HuelleV fs e E₁ E₂ w h := by
  unfold huelleB HuelleV
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true,
    Bool.not_eq_true', decide_eq_false_iff_not]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨f, _, ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩⟩)
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨f, h1, h2, h3, h4⟩
  · rintro (⟨h1, h2⟩ | ⟨f, h1, h2, h3, h4⟩)
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨f, hvoll f, ⟨⟨h1, h2⟩, h3⟩, h4⟩

theorem keinRueckrufB_iff (hvoll : ∀ g : D.Fn, g ∈ fs) :
    keinRueckrufB fs e E₁ E₂ = true ↔ KeinRueckruf fs e E₁ E₂ := by
  unfold keinRueckrufB KeinRueckruf
  constructor
  · intro h w f g hne hwf hfg
    have h1 := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp h w (hvoll w)) f
      (hvoll f)) g (hvoll g)
    simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_true_eq,
      Bool.not_eq_false'] at h1
    rcases h1 with ((h1 | h1) | h1) | h1
    · exact absurd h1 hne
    · rw [hwf] at h1; cases h1
    · rw [hfg] at h1; cases h1
    · exact h1
  · intro h
    refine List.all_eq_true.mpr fun w _ => List.all_eq_true.mpr fun f _ =>
      List.all_eq_true.mpr fun g _ => ?_
    by_cases hne : e f = e w
    · simp only [hne, decide_true, Bool.not_true, Bool.false_and, Bool.not_false, Bool.true_or]
    · cases hwf : reachB (teilP e E₁ E₂ w) fs w f
      · simp only [Bool.and_false, Bool.false_and, Bool.not_false, Bool.true_or]
      · cases hfg : reachB (teilP e E₁ E₂ f) fs f g
        · simp only [Bool.and_true, Bool.and_false, Bool.not_false, Bool.true_or]
        · simp only [Bool.and_true, Bool.not_not, h w f g hne hwf hfg, decide_true, Bool.or_true]

theorem lokBedarfB_iff (hvoll : ∀ g : D.Fn, g ∈ fs) {c : D.Tab ⊕ D.Glob} :
    lokBedarfB fs e E₁ E₂ c = true ↔ LokBedarf e E₁ E₂ c := by
  unfold lokBedarfB LokBedarf
  have hW : ((waechterVon c).any fun L => istIn (E₁.S.orte L) c) = true ↔
      ∃ L, Bewacht c L ∧ c ∈ E₁.S.orte L := by
    rw [List.any_eq_true]
    constructor
    · rintro ⟨L, hL, hi⟩
      exact ⟨L, waechterVon_mem.mp hL, istIn_iff.mp hi⟩
    · rintro ⟨L, hL, hi⟩
      exact ⟨L, waechterVon_mem.mpr hL, istIn_iff.mpr hi⟩
  rw [List.any_eq_true]
  constructor
  · rintro ⟨f, _, hf⟩
    refine ⟨f, ?_⟩
    simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hf
    rcases hf with ⟨⟨h1, h2⟩, h3⟩ | ⟨h1, h2⟩
    · refine Or.inl ⟨istIn_iff.mp h1, h2, fun hx => ?_⟩
      rw [hW.mpr hx] at h3
      cases h3
    · exact Or.inr ⟨istIn_iff.mp h1, h2⟩
  · rintro ⟨f, hf⟩
    refine ⟨f, hvoll f, ?_⟩
    simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true']
    rcases hf with ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
    · refine Or.inl ⟨⟨istIn_iff.mpr h1, h2⟩, ?_⟩
      cases hx : ((waechterVon c).any fun L => istIn (E₁.S.orte L) c)
      · rfl
      · exact absurd (hW.mp hx) h3
    · exact Or.inr ⟨istIn_iff.mpr h1, h2⟩

theorem getrenntVB_iff (hvoll : ∀ g : D.Fn, g ∈ fs) {ws : List D.Fn} {c : D.Tab ⊕ D.Glob} :
    getrenntVB fs e E₁ E₂ ws c = true ↔ GetrenntV fs e E₁ E₂ ws c := by
  constructor
  · intro h w1 hw1 w2 hw2 hne f g hf hc hg
    have h1 := (List.all_eq_true.mp ((List.all_eq_true.mp h) w1 hw1)) w2 hw2
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h1
    rcases h1 with (h1 | h1) | h1
    · rcases hne with hne | hne
      · exact absurd h1.1 hne
      · rw [mehrfachB_iff.mpr hne] at h1
        cases h1.2
    · have h2 := (List.all_eq_true.mp h1) f (hvoll f)
      rw [(huelleB_iff hvoll).mpr hf, istIn_iff.mpr hc] at h2
      simp only [Bool.not_true, Bool.or_self, Bool.false_eq_true] at h2
    · have h2 := (List.all_eq_true.mp h1) g (hvoll g)
      rw [(huelleB_iff hvoll).mpr hg] at h2
      simpa using h2
  · intro h
    refine List.all_eq_true.mpr fun w1 hw1 => List.all_eq_true.mpr fun w2 hw2 => ?_
    by_cases hne : w1 = w2 ∧ mehrfachB ws w1 = false
    · obtain ⟨rfl, hm⟩ := hne
      simp only [decide_true, hm, Bool.not_false, Bool.and_self, Bool.true_or]
    have hne' : w1 ≠ w2 ∨ Mehrfach ws w1 := by
      by_cases he : w1 = w2
      · refine Or.inr (mehrfachB_iff.mp ?_)
        cases hm : mehrfachB ws w1
        · exact absurd ⟨he, hm⟩ hne
        · rfl
      · exact Or.inl he
    by_cases hfr : (fs.all fun f => !(huelleB fs e E₁ E₂ w1 f) ||
        !(istIn (fussOrteG (teilP e E₁ E₂ f) f) c)) = true
    · simp only [hfr, Bool.or_true, Bool.true_or]
    · have hex : ∃ f, HuelleV fs e E₁ E₂ w1 f ∧ c ∈ fussOrteG (teilP e E₁ E₂ f) f := by
        refine Classical.byContradiction fun hn => hfr (List.all_eq_true.mpr fun f _ => ?_)
        cases hr : huelleB fs e E₁ E₂ w1 f
        · rfl
        · cases hi : istIn (fussOrteG (teilP e E₁ E₂ f) f) c
          · rfl
          · exact absurd ⟨f, (huelleB_iff hvoll).mp hr, istIn_iff.mp hi⟩ hn
      obtain ⟨f, hf, hc⟩ := hex
      have hw : (fs.all fun g => !(huelleB fs e E₁ E₂ w2 g) || !(TraegerSchreibt g c)) = true :=
        List.all_eq_true.mpr fun g _ => by
          cases hg : huelleB fs e E₁ E₂ w2 g
          · rfl
          · simp only [Bool.not_true, h w1 hw1 w2 hw2 hne' f g hf hc ((huelleB_iff hvoll).mp hg), Bool.not_false,
  Bool.or_true]
      simp only [hw, Bool.or_true]

end Bool
end Gabbro.Grammatik.Zielsatz
