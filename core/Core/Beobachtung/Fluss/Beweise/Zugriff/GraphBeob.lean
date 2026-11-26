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
  | .speicher _ art ort _ _ _ => art.schreibt ∧ ort = x
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
    simp only [List.nil_append, SchreibSeitAbsturz, false_and, or_false]
  | cons e es ih =>
    rw [List.cons_append, hatAbsturz_append]
    cases hbe : AbsturzBeob e <;>
      cases hHa : HatAbsturz es <;> cases hHb : HatAbsturz b <;>
        simp only [SchreibSeitAbsturz, hbe, hHa, hHb, if_true, if_false,
          Bool.true_or, Bool.false_or, Bool.or_true, Bool.or_false,
          Bool.false_eq_true, Bool.true_eq_false, true_and, false_and, or_false,
          true_or] at ih ⊢
    all_goals
      rw [ih]
      tauto

theorem SchreibSeitAbsturz_ohne_absturz (x : Ort)
    {l : List (NiedrigesEreignis Ort Wert Grund Form)} (h : ¬ HatAbsturz l) :
    SchreibSeitAbsturz x l ↔ ∃ e ∈ l, SchreibBeob x e := by
  induction l with
  | nil => simp only [HatAbsturz, Bool.false_eq_true, not_false_eq_true,
      SchreibSeitAbsturz, List.not_mem_nil, false_exists]
  | cons e es ih =>
    have hbe : ¬ AbsturzBeob e := by
      intro hb
      exact h (by simp only [HatAbsturz, hb, Bool.true_or])
    have hes : ¬ HatAbsturz es := by
      intro hs
      exact h (by simp only [HatAbsturz, hs, Bool.or_true])
    rw [List.mem_cons]
    simp only [SchreibSeitAbsturz, hbe, if_false, hes, if_false, ih hes,
      forall_exists_index, or_and_right]

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
  rw [HatQuelle, HatQuelle, hv.ev, hatQuelle_iff_mem, hatQuelle_iff_mem, List.mem_map]
  constructor
  · rintro ⟨e, he, hs, ho⟩
    rw [List.mem_append] at he
    rcases he with he | he
    · exact Or.inl ⟨e, he, hs, ho⟩
    · rcases he with ⟨p, hp, rfl⟩
      exact Or.inr ⟨p, hp, by simpa using hs, by simpa using ho⟩
  · rintro (⟨e, he, hs, ho⟩ | ⟨p, hp, hs, ho⟩)
    · exact ⟨e, by rw [List.mem_append]; exact Or.inl he, hs, ho⟩
    · exact ⟨⟨p.1, p.2⟩, by rw [List.mem_append]; exact Or.inr ⟨p, hp, rfl⟩, hs, ho⟩

theorem SchreibBeob_filterMap_speicherBeob
    {label : Etiketten Ort} {x : Ort} (hpub : oeffentlich (label.ort x) = true)
    {es : List (SpeicherAkteur Ort × Speicher.Etikett Ort Wert)} :
    (∃ ev ∈ es.filterMap (speicherBeob (Grund := Grund) (Form := Form) label), SchreibBeob x ev) ↔
      ∃ e ∈ es, e.2.art.schreibt ∧ e.2.ort = x := by
  constructor
  · rintro ⟨ev, hev, hs⟩
    rw [List.mem_filterMap] at hev
    rcases hev with ⟨e, he, heq⟩
    rcases e with ⟨akteur, lab⟩
    cases ev with
    | speicher a art ort m gel schr =>
      rcases hs with ⟨hsArt, hsOrt⟩
      subst hsOrt
      cases hArt : lab.art <;>
        simp only [speicherBeob, hArt, sichtbar, hpub] at heq
      · cases hsArt
      · cases heq
        exact ⟨(akteur, lab), he, trivial, rfl⟩
      · cases heq
        exact ⟨(akteur, lab), he, trivial, rfl⟩
      · cases heq
      · cases heq
    | _ => cases hs
  · rintro ⟨e, he, hs, ho⟩
    rcases e with ⟨akteur, lab⟩
    cases hArt : lab.art <;> simp only [Art.schreibt] at hs
    all_goals
      subst ho
      simp only [speicherBeob, hArt, sichtbar, hpub]
      rw [List.mem_filterMap]
      refine ⟨(akteur, lab), he, rfl⟩

end Gabbro.Core.Beobachtung
