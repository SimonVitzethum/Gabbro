/- Part 3 of 3 of `Verbund` (split by instrumente/teile/lean-teilen.py; the umbrella `Verbund.lean` imports all parts). -/
import Grammatik.Zielsatz.Faeden.Verbund.T2

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
    through an imported function, and thread-locality, write separation and pool safety over
    the COMPOSED hulls. -/
def schnittstelleB (fs : List D.Fn) (cs : List (D.Tab ⊕ D.Glob)) (e : D.Fn → Bool)
    (E₁ E₂ : Einheit D) : Bool :=
  platzhalterB fs e E₁.P && platzhalterB fs (fun f => !e f) E₂.P && keinRueckrufB fs e E₁ E₂ &&
    (cs.all fun c => !(lokBedarfB fs e E₁ E₂ c) || getrenntVB fs e E₁ E₂ (verbinde e E₁ E₂).ws c) &&
    (cs.all fun c => ausgenommenB c || schreibGetrenntVB fs e E₁ E₂ (verbinde e E₁ E₂).ws c) &&
    ((verbinde e E₁ E₂).ws.all fun w =>
      !(mehrfachB (verbinde e E₁ E₂).ws w) || poolSicherVB fs cs e E₁ E₂ w) &&
    (fs.all fun w => !(E₁.P.unterbricht w) || fs.all fun h =>
      !(huelleB fs e E₁ E₂ w h) || mE (NurMaskiert D) ((teilP e E₁ E₂ h).rumpf h))

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

theorem schreibGetrenntVB_iff (hvoll : ∀ g : D.Fn, g ∈ fs) {ws : List D.Fn}
    {c : D.Tab ⊕ D.Glob} :
    schreibGetrenntVB fs e E₁ E₂ ws c = true ↔ SchreibGetrenntV fs e E₁ E₂ ws c := by
  constructor
  · intro h w1 hw1 w2 hw2 hne g hg hgc k hk
    have h1 := (List.all_eq_true.mp ((List.all_eq_true.mp h) w1 hw1)) w2 hw2
    simp only [Bool.or_eq_true, decide_eq_true_eq] at h1
    rcases h1 with (h1 | h1) | h1
    · exact absurd h1 hne
    · have h2 := (List.all_eq_true.mp h1) g (hvoll g)
      rw [(huelleB_iff hvoll).mpr hg, hgc] at h2
      simp only [Bool.not_true, Bool.or_self, Bool.false_eq_true] at h2
    · have h2 := (List.all_eq_true.mp h1) k (hvoll k)
      rw [(huelleB_iff hvoll).mpr hk] at h2
      simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, Bool.not_eq_true'] at h2
      refine ⟨h2.1, fun hc => ?_⟩
      rw [istIn_iff.mpr hc] at h2
      cases h2.2
  · intro h
    refine List.all_eq_true.mpr fun w1 hw1 => List.all_eq_true.mpr fun w2 hw2 => ?_
    by_cases hne : w1 = w2
    · simp only [hne, decide_true, Bool.true_or]
    by_cases hfr : (fs.all fun g => !(huelleB fs e E₁ E₂ w1 g) || !(TraegerSchreibt g c)) = true
    · simp only [hfr, Bool.or_true, Bool.true_or]
    · have hex : ∃ g, HuelleV fs e E₁ E₂ w1 g ∧ TraegerSchreibt g c = true := by
        refine Classical.byContradiction fun hn => hfr (List.all_eq_true.mpr fun g _ => ?_)
        cases hr : huelleB fs e E₁ E₂ w1 g
        · rfl
        · cases hi : TraegerSchreibt g c
          · rfl
          · exact absurd ⟨g, (huelleB_iff hvoll).mp hr, hi⟩ hn
      obtain ⟨g, hg, hgc⟩ := hex
      have hw : (fs.all fun k => !(huelleB fs e E₁ E₂ w2 k) ||
          (!(TraegerSchreibt k c) && !(istIn (fussOrteG (teilP e E₁ E₂ k) k) c))) = true :=
        List.all_eq_true.mpr fun k _ => by
          cases hk : huelleB fs e E₁ E₂ w2 k
          · rfl
          · obtain ⟨h1, h2⟩ := h w1 hw1 w2 hw2 hne g hg hgc k ((huelleB_iff hvoll).mp hk)
            cases hi : istIn (fussOrteG (teilP e E₁ E₂ k) k) c
            · simp only [Bool.not_true, h1, Bool.not_false, Bool.and_self, Bool.or_true]
            · exact absurd (istIn_iff.mp hi) h2
      simp only [hw, Bool.or_true]

theorem poolSicherVB_iff (hvoll : ∀ g : D.Fn, g ∈ fs) (hcs : ∀ c : D.Tab ⊕ D.Glob, c ∈ cs)
    {w : D.Fn} : poolSicherVB fs cs e E₁ E₂ w = true ↔ PoolSicherV fs e E₁ E₂ w := by
  unfold poolSicherVB PoolSicherV
  have hex : ∀ c : D.Tab ⊕ D.Glob, (!(waechterVon c).isEmpty || atomarB c) = true ↔
      (∃ L, Bewacht c L) ∨ AtomarAusgenommen c := by
    intro c
    constructor
    · intro hc
      have hc' : ausgenommenB c = true := hc
      by_cases hB : ∃ L, Bewacht c L
      · exact Or.inl hB
      · refine Or.inr (Classical.byContradiction fun hA => ?_)
        have := ausgenommenB_false.mpr ⟨fun L hL => hB ⟨L, hL⟩, hA⟩
        rw [hc'] at this
        cases this
    · intro hc
      show ausgenommenB c = true
      cases hx : ausgenommenB c
      · obtain ⟨hB, hA⟩ := ausgenommenB_false.mp hx
        rcases hc with ⟨L, hL⟩ | hc
        · exact absurd hL (hB L)
        · exact absurd hc hA
      · rfl
  simp only [Bool.and_eq_true, List.isEmpty_iff, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨h1, h2, fun f hf c hc => ?_⟩
    have h4 := List.all_eq_true.mp h3 f (hvoll f)
    rw [(huelleB_iff hvoll).mpr hf, Bool.not_true, Bool.false_or] at h4
    have h5 := List.all_eq_true.mp h4 c (hcs c)
    rw [hc, Bool.not_true, Bool.false_or] at h5
    exact (hex c).mp h5
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨h1, h2⟩, List.all_eq_true.mpr fun f _ => ?_⟩
    cases hf : huelleB fs e E₁ E₂ w f
    · rfl
    · rw [Bool.not_true, Bool.false_or]
      refine List.all_eq_true.mpr fun c _ => ?_
      cases hc : TraegerSchreibt f c
      · rfl
      · rw [Bool.not_true, Bool.false_or]
        exact (hex c).mpr (h3 f ((huelleB_iff hvoll).mp hf) c hc)

/-- **The link Bool decides exactly `SchnittstelleSpec`** (given complete member lists). -/
theorem schnittstelleB_iff (hvoll : ∀ g : D.Fn, g ∈ fs) (hcs : ∀ c : D.Tab ⊕ D.Glob, c ∈ cs) :
    schnittstelleB fs cs e E₁ E₂ = true ↔ SchnittstelleSpec fs e E₁ E₂ := by
  unfold schnittstelleB
  simp only [Bool.and_eq_true]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩
    refine ⟨(platzhalterB_iff hvoll).mp h1, (platzhalterB_iff hvoll).mp h2,
      (keinRueckrufB_iff hvoll).mp h3, fun c hc => ?_, fun c hB hA => ?_, fun w hw => ?_,
      fun w hw h hh => ?_⟩
    · have h := List.all_eq_true.mp h4 c (hcs c)
      rw [(lokBedarfB_iff hvoll).mpr hc, Bool.not_true, Bool.false_or] at h
      exact (getrenntVB_iff hvoll).mp h
    · have h := List.all_eq_true.mp h5 c (hcs c)
      rw [ausgenommenB_false.mpr ⟨hB, hA⟩, Bool.false_or] at h
      exact (schreibGetrenntVB_iff hvoll).mp h
    · have hw' : w ∈ (verbinde e E₁ E₂).ws := hw.subset (List.mem_cons_self)
      have h := List.all_eq_true.mp h6 w hw'
      rw [mehrfachB_iff.mpr hw, Bool.not_true, Bool.false_or] at h
      exact (poolSicherVB_iff hvoll hcs).mp h
    · have h1 := List.all_eq_true.mp h7 w (hvoll w)
      rw [hw, Bool.not_true, Bool.false_or] at h1
      have h2 := List.all_eq_true.mp h1 h (hvoll h)
      rw [(huelleB_iff hvoll).mpr hh, Bool.not_true, Bool.false_or] at h2
      exact h2
  · intro h
    refine ⟨⟨⟨⟨⟨⟨(platzhalterB_iff hvoll).mpr h.blatt₁, (platzhalterB_iff hvoll).mpr h.blatt₂⟩,
      (keinRueckrufB_iff hvoll).mpr h.keinRueckruf⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · refine List.all_eq_true.mpr fun c _ => ?_
      cases hc : lokBedarfB fs e E₁ E₂ c
      · rfl
      · rw [Bool.not_true, Bool.false_or]
        exact (getrenntVB_iff hvoll).mpr (h.lok c ((lokBedarfB_iff hvoll).mp hc))
    · refine List.all_eq_true.mpr fun c _ => ?_
      cases ha : ausgenommenB c
      · obtain ⟨hB, hA⟩ := ausgenommenB_false.mp ha
        rw [Bool.false_or]
        exact (schreibGetrenntVB_iff hvoll).mpr (h.renn c hB hA)
      · rfl
    · refine List.all_eq_true.mpr fun w _ => ?_
      cases hm : mehrfachB (verbinde e E₁ E₂).ws w
      · rfl
      · rw [Bool.not_true, Bool.false_or]
        exact (poolSicherVB_iff hvoll hcs).mpr (h.einzeln w (mehrfachB_iff.mp hm))
    · refine List.all_eq_true.mpr fun w _ => ?_
      cases hw : E₁.P.unterbricht w
      · rfl
      · refine List.all_eq_true.mpr fun k _ => ?_
        cases hk : huelleB fs e E₁ E₂ w k
        · rfl
        · rw [Bool.not_true, Bool.false_or]
          exact h.masken w hw k ((huelleB_iff hvoll).mp hk)

end Bool

end Gabbro.Grammatik.Zielsatz

namespace Gabbro.Grammatik.Zielsatz
open Gabbro.Grammatik
variable {D : Deklaration}

/-! ## Embedding and iteration -/

section Einbettung

variable [DecidableEq D.Fn]

/-- **Linking is conservative**: a unit linked with a partner that owns nothing and starts
    nothing IS the unit. The statement `GabbroZiel` is unchanged by this diff; this lemma says
    the new operation does not move a single unit either. -/
theorem verbinde_leer (E E' : Einheit D) (h1 : E'.starts = []) (h2 : E'.gestartet = [])
    (h3 : E'.arenen = []) : verbinde (fun _ => true) E E' = E := by
  cases E
  unfold verbinde verbindeP mitRumpf
  rw [h1, h2, h3, List.append_nil, List.append_nil, List.append_nil]
  rfl

/-- **The linked unit is accepted by the concrete checker** -- so it can be linked again: a
    chain of units, by iteration. -/
theorem verbinde_akzeptiert {E₁ E₂ : Einheit D} {e : D.Fn → Bool} {fs : List D.Fn}
    {ls : List D.Lock} {cs : List (D.Tab ⊕ D.Glob)} (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hls : ∀ L : D.Lock, L ∈ ls) (hcs : ∀ c : D.Tab ⊕ D.Glob, c ∈ cs)
    (h₁ : Akzeptiert E₁.P E₁.S fs ls cs E₁.ws = true)
    (h₂ : Akzeptiert E₂.P E₂.S fs ls cs E₂.ws = true) (hV : Verbindbar E₁ E₂)
    (hS : schnittstelleB fs cs e E₁ E₂ = true) :
    Akzeptiert (verbinde e E₁ E₂).P (verbinde e E₁ E₂).S fs ls cs (verbinde e E₁ E₂).ws = true :=
  (akzeptiert_iff hvoll hls hcs).mpr (akzeptiertSpec_verbinde hvoll
    ((akzeptiert_iff hvoll hls hcs).mp h₁) ((akzeptiert_iff hvoll hls hcs).mp h₂) hV
    ((schnittstelleB_iff hvoll hcs).mp hS))

/-- **The user duty of the linked unit, restricted to what the two users own** (`a₁` inside
    unit 1's share, `a₂` inside unit 2's): the premise (b) of a further link. -/
theorem nutzerTeil_verbinde {E₁ E₂ : Einheit D} {e a₁ a₂ : D.Fn → Bool}
    (hV : Verbindbar E₁ E₂) (hQ : E₂.Q = E₁.Q)
    (h₁ : ∀ f, a₁ f = true → e f = true) (h₂ : ∀ f, a₂ f = true → e f = false)
    (hN₁ : NutzerTeil a₁ E₁) (hN₂ : NutzerTeil a₂ E₂) :
    NutzerTeil (fun f => a₁ f || a₂ f) (verbinde e E₁ E₂) := by
  have hS : E₂.S = E₁.S := hV.sperren.symm
  refine ⟨⟨fun passes f hf => ?_, hN₁.logik.2.1, hN₁.logik.2.2⟩, ⟨hN₁.start.sperren, ?_⟩⟩
  · show KoerperGutS (verbindeP e E₁ E₂) passes E₁.Q E₁.S f ∧
      InvGutS (verbindeP e E₁ E₂) passes E₁.Q E₁.S f ∧
      InvGutGrund (verbindeP e E₁ E₂) passes E₁.Q E₁.S f
    cases ha : a₁ f
    · have ha2 : a₂ f = true := by simpa [ha] using hf
      have hef := h₂ f ha2
      obtain ⟨k, i, g⟩ := hN₂.logik.1 passes f ha2
      rw [p2_eq hV, hQ, hS] at k i g
      have hr : (fun f => if e f then E₁.P.rumpf f else E₂.P.rumpf f) f = E₂.P.rumpf f := by
        simp only [hef, Bool.false_eq_true, ↓reduceIte]
      exact ⟨(koerper_mitRumpf2 E₁.P _ _ passes _ _ f hr).mpr k,
        (invGutS_mitRumpf2 E₁.P _ _ passes _ _ f hr).mpr i,
        (invGutGrund_mitRumpf2 E₁.P _ _ passes _ _ f hr).mpr g⟩
    · have hef := h₁ f ha
      obtain ⟨k, i, g⟩ := hN₁.logik.1 passes f ha
      have hr : (fun f => if e f then E₁.P.rumpf f else E₂.P.rumpf f) f = E₁.P.rumpf f := by
        simp only [hef, ↓reduceIte]
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

end Einbettung

#print axioms gabbro_ziel_verbund_sc
#print axioms akzeptiertSpec_verbinde
#print axioms nutzerPflicht_verbinde
#print axioms schnittstelleB_iff
#print axioms reachB_ruft
#print axioms verbinde_leer
#print axioms verbinde_akzeptiert
#print axioms nutzerTeil_verbinde


end Gabbro.Grammatik.Zielsatz
