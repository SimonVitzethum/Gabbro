/-
  File:      Grammatik/Gen/Text/Satz.lean
  Subject:   THEOREM 5 AT THE TEXT LEVEL: a checker or a compiler that reads SOURCE TEXT and depends only on the cells of
             the program the text is (`NeutralText`, `NeutralKorrektText`, over `ausText`) and answers right on the 7 + 13
             witness texts answers right on every text that is a program of the source.

  `M99_824` waits at a static that is no atomic, which the language does not say; its text is a premise (`Text99`)
  until the witness is regenerated over the narrowed model. The witness texts are the printed delaborations of the witnesses of `Gen/Zeugen` (`textVon`); each reads back as a
  program with the witness's cells and verdict (`Zeugen/<w>.lean`). Only cells and verdicts need to agree: a
  cell-neutral checker cannot tell two programs with the same cells apart, so no equality of declarations is needed.
-/
import Grammatik.Gen.Text.Zeugen.M103_131
import Grammatik.Gen.Text.Zeugen.M103_803
import Grammatik.Gen.Text.Zeugen.M16_13
import Grammatik.Gen.Text.Zeugen.M169_350
import Grammatik.Gen.Text.Zeugen.M47_549
import Grammatik.Gen.Text.Zeugen.M49_50
import Grammatik.Gen.Text.Zeugen.N16_5
import Grammatik.Gen.Text.Zeugen.N18_0
import Grammatik.Gen.Text.Zeugen.N18_4
import Grammatik.Gen.Text.Zeugen.N19_0
import Grammatik.Gen.Text.Zeugen.N19_2
import Grammatik.Gen.Text.Zeugen.N19_5
import Grammatik.Gen.Text.Zeugen.N19_7
import Grammatik.Gen.Text.Zeugen.N20_1
import Grammatik.Gen.Text.Zeugen.N23_4
import Grammatik.Gen.Text.Zeugen.N24_0
import Grammatik.Gen.Text.Zeugen.N3_0
import Grammatik.Gen.Text.Zeugen.N47_20
import Grammatik.Gen.Text.Zeugen.N47_45

namespace Gabbro.Grammatik.Gen.Text

open Gabbro.Grammatik Gabbro.Grammatik.Gen Gabbro.Grammatik.Adaequanz

/-- A checker on source text that depends only on the cells of the program the text is. -/
def NeutralText (R : String → Bool) : Prop :=
  ∃ φ : Zelle → Bool, ∀ s e, ausText s = .ok e → (R s = true ↔ akzeptiert Einsatz.Hat φ e)

/-- A compiler correctness on source text that depends only on the cells of the program the text is. -/
def NeutralKorrektText (K : String → Prop) : Prop :=
  ∃ ψ : Zelle → Prop, ∀ s e, ausText s = .ok e → (K s ↔ ∀ z, e.Hat z → ψ z)

/-- The texts of the valid witnesses (the order of `Mw`), the text `t99` of `M99_824` given: that witness waits at a
    static that is no atomic, which the language does not say (the model is being narrowed so the generator no
    longer emits it; the witness is regenerated after that change). -/
def mText (t99 : String) : List String :=
  [t99,
   textVon Zeugen.M47_549.z Zeugen.M47_549.P Zeugen.M47_549.ws,
   textVon Zeugen.M169_350.z Zeugen.M169_350.P Zeugen.M169_350.ws,
   textVon Zeugen.M16_13.z Zeugen.M16_13.P Zeugen.M16_13.ws,
   textVon Zeugen.M49_50.z Zeugen.M49_50.P Zeugen.M49_50.ws,
   textVon Zeugen.M103_803.z Zeugen.M103_803.P Zeugen.M103_803.ws,
   textVon Zeugen.M103_131.z Zeugen.M103_131.P Zeugen.M103_131.ws]

/-- The texts of the refused witnesses (the order of `Nw`). -/
def nText : List String :=
  [textVon Zeugen.N16_5.z Zeugen.N16_5.P Zeugen.N16_5.ws,
   textVon Zeugen.N18_0.z Zeugen.N18_0.P Zeugen.N18_0.ws,
   textVon Zeugen.N18_4.z Zeugen.N18_4.P Zeugen.N18_4.ws,
   textVon Zeugen.N19_0.z Zeugen.N19_0.P Zeugen.N19_0.ws,
   textVon Zeugen.N19_2.z Zeugen.N19_2.P Zeugen.N19_2.ws,
   textVon Zeugen.N19_5.z Zeugen.N19_5.P Zeugen.N19_5.ws,
   textVon Zeugen.N19_7.z Zeugen.N19_7.P Zeugen.N19_7.ws,
   textVon Zeugen.N20_1.z Zeugen.N20_1.P Zeugen.N20_1.ws,
   textVon Zeugen.N23_4.z Zeugen.N23_4.P Zeugen.N23_4.ws,
   textVon Zeugen.N24_0.z Zeugen.N24_0.P Zeugen.N24_0.ws,
   textVon Zeugen.N3_0.z Zeugen.N3_0.P Zeugen.N3_0.ws,
   textVon Zeugen.N47_20.z Zeugen.N47_20.P Zeugen.N47_20.ws,
   textVon Zeugen.N47_45.z Zeugen.N47_45.P Zeugen.N47_45.ws]

/-- The text of `M99_824` reads back with its cells and verdict (a premise until the witness is regenerated). -/
def Text99 (t99 : String) : Prop :=
  ∃ e', ausText t99 = .ok e' ∧ e'.zellen = Gen.Zeugen.M99_824.e.zellen ∧ e'.gueltig = Gen.Zeugen.M99_824.e.gueltig

/-- **Every witness has its text**: a text in the list that reads back with the witness's cells and verdict. -/
theorem m_texte (t99 : String) (h99 : Text99 t99) :
    ∀ m ∈ Zeugen.Mw, ∃ t ∈ mText t99, ∃ e', ausText t = .ok e' ∧ e'.zellen = m.zellen ∧ e'.gueltig = m.gueltig := by
  intro m hm
  simp only [Zeugen.Mw, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, by simp [mText], h99⟩
  · exact ⟨_, by simp [mText], Zeugen.M47_549.text⟩
  · exact ⟨_, by simp [mText], Zeugen.M169_350.text⟩
  · exact ⟨_, by simp [mText], Zeugen.M16_13.text⟩
  · exact ⟨_, by simp [mText], Zeugen.M49_50.text⟩
  · exact ⟨_, by simp [mText], Zeugen.M103_803.text⟩
  · exact ⟨_, by simp [mText], Zeugen.M103_131.text⟩

theorem n_texte : ∀ n ∈ Zeugen.Nw, ∃ t ∈ nText, ∃ e', ausText t = .ok e' ∧ e'.zellen = n.zellen ∧ e'.gueltig = n.gueltig := by
  intro n hn
  simp only [Zeugen.Nw, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, by simp [nText], Zeugen.N16_5.text⟩
  · exact ⟨_, by simp [nText], Zeugen.N18_0.text⟩
  · exact ⟨_, by simp [nText], Zeugen.N18_4.text⟩
  · exact ⟨_, by simp [nText], Zeugen.N19_0.text⟩
  · exact ⟨_, by simp [nText], Zeugen.N19_2.text⟩
  · exact ⟨_, by simp [nText], Zeugen.N19_5.text⟩
  · exact ⟨_, by simp [nText], Zeugen.N19_7.text⟩
  · exact ⟨_, by simp [nText], Zeugen.N20_1.text⟩
  · exact ⟨_, by simp [nText], Zeugen.N23_4.text⟩
  · exact ⟨_, by simp [nText], Zeugen.N24_0.text⟩
  · exact ⟨_, by simp [nText], Zeugen.N3_0.text⟩
  · exact ⟨_, by simp [nText], Zeugen.N47_20.text⟩
  · exact ⟨_, by simp [nText], Zeugen.N47_45.text⟩

/-- Acceptance by a cell table depends on the cells only. -/
theorem akzeptiert_zellen (φ : Zelle → Bool) (e e' : Einsatz) (h : e.zellen = e'.zellen) :
    akzeptiert Einsatz.Hat φ e ↔ akzeptiert Einsatz.Hat φ e' := by
  unfold akzeptiert Einsatz.Hat
  rw [h]

/-- **A cell-neutral checker on source text that answers like the model on the 7 + 13 witness texts answers like
    the model on every text that is a program of the source.** -/
theorem pruefer_text_korrekt (t99 : String) (h99 : Text99 t99) (R : String → Bool) (hR : NeutralText R)
    (hM : ∀ t ∈ mText t99, R t = true) (hN : ∀ t ∈ nText, R t = false) :
    ∀ s e, ausText s = .ok e → R s = e.gueltig := by
  obtain ⟨φ, hφ⟩ := hR
  classical
  let C : Einsatz → Bool := fun e => decide (akzeptiert Einsatz.Hat φ e)
  have hC : Neutral C := ⟨φ, fun e => by simp [C]⟩
  have hCw : ∀ w t e', t ∈ mText t99 ∨ t ∈ nText → ausText t = .ok e' → e'.zellen = w.zellen →
      C w = R t := by
    intro w t e' _ ht hz
    have h1 := hφ t e' ht
    cases hr : R t
    · simp only [C, decide_eq_false_iff_not]
      intro ha
      rw [← akzeptiert_zellen φ e' w hz] at ha
      have := h1.2 ha
      rw [hr] at this; cases this
    · simp only [C, decide_eq_true_eq]
      rw [← akzeptiert_zellen φ e' w hz]
      exact h1.1 hr
  have hMC : ∀ m ∈ Zeugen.Mw, C m = m.gueltig := by
    intro m hm
    obtain ⟨t, htm, e', ht, hz, hg⟩ := m_texte t99 h99 m hm
    rw [hCw m t e' (Or.inl htm) ht hz, hM t htm]
    have : m.gueltig = true := Zeugen.zeugen_tafel.gut_m m hm
    rw [this]
  have hNC : ∀ n ∈ Zeugen.Nw, C n = n.gueltig := by
    intro n hn
    obtain ⟨t, htn, e', ht, hz, hg⟩ := n_texte n hn
    rw [hCw n t e' (Or.inr htn) ht hz, hN t htn]
    rw [Zeugen.zeugen_tafel.n_schlecht n hn]
  intro s e hs
  have hce := Zeugen.pruefer_zeugen_korrekt C hC hMC hNC e
  rw [← hce]
  cases hr : R s
  · symm; simp only [C, decide_eq_false_iff_not]
    intro ha; have := (hφ s e hs).2 ha; rw [hr] at this; cases this
  · symm; simp only [C, decide_eq_true_eq]; exact (hφ s e hs).1 hr

/-- **A cell-neutral compiler on source text correct on the 7 valid witness texts is correct on every text that is a
    valid program of the source.** -/
theorem compiler_text_korrekt (t99 : String) (h99 : Text99 t99) (K : String → Prop) (hK : NeutralKorrektText K)
    (hM : ∀ t ∈ mText t99, K t) :
    ∀ s e, ausText s = .ok e → e.gueltig = true → K s := by
  obtain ⟨ψ, hψ⟩ := hK
  let K' : Einsatz → Prop := fun e => ∀ z, e.Hat z → ψ z
  have hK' : NeutralKorrekt K' := ⟨ψ, fun _ => Iff.rfl⟩
  have hMK : ∀ m ∈ Zeugen.Mw, K' m := by
    intro m hm
    obtain ⟨t, htm, e', ht, hz, _⟩ := m_texte t99 h99 m hm
    have := (hψ t e' ht).1 (hM t htm)
    intro z hzm
    exact this z (by unfold Einsatz.Hat; rw [hz]; exact hzm)
  intro s e hs hv
  exact (hψ s e hs).2 (Zeugen.compiler_zeugen_korrekt K' hK' hMK e hv)

end Gabbro.Grammatik.Gen.Text

#print axioms Gabbro.Grammatik.Gen.Text.pruefer_text_korrekt
#print axioms Gabbro.Grammatik.Gen.Text.compiler_text_korrekt
#print axioms Gabbro.Grammatik.Gen.Text.m_texte
#print axioms Gabbro.Grammatik.Gen.Text.n_texte
