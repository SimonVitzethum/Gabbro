/-
  List-level lemmas for the run invariant linking a memory graph to its low observation. A graph records
  every materialised write since boot, while a low trace also survives a crash; the observation-side
  predicate therefore counts writes only after the last crash boundary, which is exactly when the graph
  is rebuilt from the restart entry.
-/
module

public import Core.Beobachtung.Fluss.Beweise.Zugriff.Hilfen

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine

variable {Ort Wert Grund Form : Type}

/-- A low memory event that writes cell `x`. -/
def SchreibBeob (x : Ort) : NiedrigesEreignis Ort Wert Grund Form → Prop
  | .speicher _ .schreiben ort _ _ _ => ort = x
  | .speicher _ .rmw ort _ _ _ => ort = x
  | _ => False

/-- The crash boundary that resets the materialised memory graph. -/
def AbsturzBeob : NiedrigesEreignis Ort Wert Grund Form → Bool
  | .katalog (.persistenz .crash) => true
  | _ => false

/-- Whether the observed list contains a crash boundary. -/
def HatAbsturz : List (NiedrigesEreignis Ort Wert Grund Form) → Bool
  | [] => false
  | e :: es => AbsturzBeob e || HatAbsturz es

/-- A write of `x` observed after the last crash boundary. -/
def SchreibSeitAbsturz (x : Ort) : List (NiedrigesEreignis Ort Wert Grund Form) → Prop
  | [] => False
  | e :: es =>
      if AbsturzBeob e then SchreibSeitAbsturz x es
      else if HatAbsturz es then SchreibSeitAbsturz x es
      else SchreibBeob x e ∨ SchreibSeitAbsturz x es

theorem hatAbsturz_append (a b : List (NiedrigesEreignis Ort Wert Grund Form)) :
    HatAbsturz (a ++ b) = (HatAbsturz a || HatAbsturz b) := by
  induction a with
  | nil => simp only [List.nil_append, HatAbsturz, Bool.false_or]
  | cons e es ih =>
    simp only [List.cons_append, HatAbsturz, ih, Bool.or_assoc]

theorem SchreibSeitAbsturz_append (x : Ort)
    (a b : List (NiedrigesEreignis Ort Wert Grund Form)) :
    SchreibSeitAbsturz x (a ++ b) ↔
      SchreibSeitAbsturz x b ∨ (¬ HatAbsturz b ∧ SchreibSeitAbsturz x a) := by
  induction a with
  | nil =>
    simp only [List.nil_append, SchreibSeitAbsturz, and_false, or_false]
  | cons e es ih =>
    rw [List.cons_append]
    cases hbe : AbsturzBeob e
    · simpa only [SchreibSeitAbsturz, hbe, if_true] using ih
    · simp only [SchreibSeitAbsturz, hbe, if_false]
      have happ : HatAbsturz (es ++ b) = (HatAbsturz es || HatAbsturz b) := hatAbsturz_append es b
      cases hEs : HatAbsturz es <;> cases hBs : HatAbsturz b <;>
        simp only [happ, hEs, hBs, Bool.true_or, Bool.false_or, Bool.or_true, Bool.or_false,
          Bool.false_eq_true, Bool.true_eq_false, not_false_eq_true, not_true_eq_false,
          false_and, true_and, or_false, true_or] at ih ⊢
      all_goals
        rw [ih]
        tauto

theorem SchreibSeitAbsturz_ohne_absturz (x : Ort)
    {l : List (NiedrigesEreignis Ort Wert Grund Form)} (h : ¬ HatAbsturz l) :
    SchreibSeitAbsturz x l ↔ ∃ e ∈ l, SchreibBeob x e := by
  induction l with
  | nil =>
    constructor
    · intro hh; cases hh
    · rintro ⟨e, he, hs⟩; cases he
  | cons e es ih =>
    have hbe : ¬ AbsturzBeob e := by
      intro hb
      exact h (by simp only [HatAbsturz, hb, Bool.true_or])
    have hes : ¬ HatAbsturz es := by
      intro hs
      exact h (by simp only [HatAbsturz, hs, Bool.or_true])
    constructor
    · intro hh
      have hodd : SchreibBeob x e ∨ SchreibSeitAbsturz x es := by
        simpa only [SchreibSeitAbsturz, hbe, if_false, hes, if_false] using hh
      rcases hodd with hhead | htail
      · refine ⟨e, ?_, hhead⟩
        simp only [List.mem_cons, eq_self_iff_true, true_or]
      · obtain ⟨e', he', hs'⟩ := (ih hes).1 htail
        refine ⟨e', ?_, hs'⟩
        simp only [List.mem_cons, he', or_true]
    · rintro ⟨e', he', hs'⟩
      simp only [List.mem_cons] at he'
      rcases he' with rfl | he'
      · simpa only [SchreibSeitAbsturz, hbe, if_false, hes, if_false, hs', or_true]
      · have htail : SchreibSeitAbsturz x es := (ih hes).2 ⟨e', he', hs'⟩
        simpa only [SchreibSeitAbsturz, hbe, if_false, hes, if_false, htail, or_true]

theorem SchreibSeitAbsturz_nach_absturz (x : Ort)
    {e : NiedrigesEreignis Ort Wert Grund Form}
    {es : List (NiedrigesEreignis Ort Wert Grund Form)} (hc : AbsturzBeob e = true) :
    SchreibSeitAbsturz x (e :: es) ↔ SchreibSeitAbsturz x es := by
  simp only [SchreibSeitAbsturz, hc, if_true]

theorem hatQuelle_nach_viele {Ort Wert : Type}
    {g g' : SpeicherGraph Ort Wert}
    {es : List (SpeicherAkteur Ort × Speicher.Etikett Ort Wert)}
    (hv : g.Viele es g') (x : Ort) :
    HatQuelle g' x ↔ HatQuelle g x ∨ ∃ e ∈ es, e.2.art.schreibt ∧ e.2.ort = x := by
  rw [HatQuelle, HatQuelle, hv.ev, hatQuelle_iff_mem, hatQuelle_iff_mem]
  constructor
  · rintro ⟨e, he, hs, ho⟩
    rw [List.mem_append] at he
    rcases he with he | he
    · exact Or.inl ⟨e, he, hs, ho⟩
    · rw [List.mem_map] at he
      rcases he with ⟨p, hp, rfl⟩
      exact Or.inr ⟨p, hp, by simpa using hs, by simpa using ho⟩
  · rintro (⟨e, he, hs, ho⟩ | ⟨p, hp, hs, ho⟩)
    · exact ⟨e, by rw [List.mem_append]; exact Or.inl he, hs, ho⟩
    · refine ⟨⟨p.1, p.2⟩, ?_, hs, ho⟩
      rw [List.mem_append]
      exact Or.inr (by rw [List.mem_map]; exact ⟨p, hp, rfl⟩)

theorem SchreibBeob_filterMap_speicherBeob
    {label : Etiketten Ort} (hpub : ∀ y : Ort, oeffentlich (label.ort y) = true)
    {es : List (SpeicherAkteur Ort × Speicher.Etikett Ort Wert)} :
    (∃ ev ∈ es.filterMap (speicherBeob (Grund := Grund) (Form := Form) label), SchreibBeob x ev) ↔
      ∃ e ∈ es, e.2.art.schreibt ∧ e.2.ort = x := by
  constructor
  · rintro ⟨ev, hev, hs⟩
    rw [List.mem_filterMap] at hev
    rcases hev with ⟨⟨akteur, lab⟩, he, heq⟩
    cases ev with
    | speicher a art ort m gel schr =>
      cases art <;> simp only [SchreibBeob] at hs
      · cases hs
      · cases hArt : lab.art <;>
          simp only [speicherBeob, hArt, sichtbar, hpub, if_true] at heq
        · cases (Option.some.inj heq)
        · cases (Option.some.inj heq)
          exact ⟨(akteur, lab), he, trivial, hs⟩
        · cases (Option.some.inj heq)
        · cases heq
        · cases heq
      · cases hArt : lab.art <;>
          simp only [speicherBeob, hArt, sichtbar, hpub, if_true] at heq
        · cases (Option.some.inj heq)
        · cases (Option.some.inj heq)
        · cases (Option.some.inj heq)
          exact ⟨(akteur, lab), he, trivial, hs⟩
        · cases heq
        · cases heq
      · cases hs
      · cases hs
    | _ => cases hs
  · rintro ⟨⟨akteur, lab⟩, he, hs, ho⟩
    cases hArt : lab.art <;> simp only [Speicher.Art.schreibt] at hs
    · cases hs
    · subst ho
      refine ⟨.speicher akteur .schreiben lab.ort lab.modus none (some lab.geschrieben), ?_, ?_⟩
      · rw [List.mem_filterMap]
        exact ⟨(akteur, lab), he, by simp only [speicherBeob, hArt, sichtbar, hpub, if_true]⟩
      · simp only [SchreibBeob]
    · subst ho
      refine ⟨.speicher akteur .rmw lab.ort lab.modus (some lab.gelesen) (some lab.geschrieben), ?_, ?_⟩
      · rw [List.mem_filterMap]
        exact ⟨(akteur, lab), he, by simp only [speicherBeob, hArt, sichtbar, hpub, if_true]⟩
      · simp only [SchreibBeob]
    · cases hs
    · cases hs

end Gabbro.Core.Beobachtung
