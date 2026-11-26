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
    match AbsturzBeob e with
    | true => SchreibSeitAbsturz x es
    | false =>
      match HatAbsturz es with
      | true => SchreibSeitAbsturz x es
      | false => SchreibBeob x e ∨ SchreibSeitAbsturz x es

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
    · simp only [SchreibSeitAbsturz, hbe]
      have happ : HatAbsturz (es ++ b) = (HatAbsturz es || HatAbsturz b) := hatAbsturz_append es b
      cases hesa : HatAbsturz es <;> cases hbsa : HatAbsturz b <;>
        simp only [happ, hesa, hbsa, Bool.true_or, Bool.false_or, Bool.or_true, Bool.or_false,
          Bool.false_eq_true, Bool.true_eq_false, not_false_eq_true, not_true_eq_false,
          false_and, true_and, or_false, true_or] at ih ⊢
      all_goals
        rw [ih]
        tauto
    · simpa only [SchreibSeitAbsturz, hbe] using ih

theorem SchreibSeitAbsturz_ohne_absturz (x : Ort)
    {l : List (NiedrigesEreignis Ort Wert Grund Form)} (h : ¬ HatAbsturz l) :
    SchreibSeitAbsturz x l ↔ ∃ e ∈ l, SchreibBeob x e := by
  induction l with
  | nil =>
    constructor
    · intro hh; cases hh
    · rintro ⟨e, he, hs⟩; cases he
  | cons e es ih =>
    have hbe : AbsturzBeob e = false := by
      cases hb : AbsturzBeob e
      · rfl
      · exact False.elim (h (by simp only [HatAbsturz, hb, Bool.true_or]))
    have hes : ¬ HatAbsturz es := by
      intro hs
      exact h (by simp only [HatAbsturz, hs, Bool.or_true])
    have hesF : HatAbsturz es = false := by
      cases hx : HatAbsturz es <;> simp_all
    constructor
    · intro hh
      have hodd : SchreibBeob x e ∨ SchreibSeitAbsturz x es := by
        simpa only [SchreibSeitAbsturz, hbe, hesF] using hh
      rcases hodd with hhead | htail
      · refine ⟨e, ?_, hhead⟩
        simp only [List.mem_cons, eq_self_iff_true, true_or]
      · obtain ⟨e', he', hs'⟩ := (ih hes).1 htail
        refine ⟨e', ?_, hs'⟩
        simp only [List.mem_cons, he', or_true]
    · rintro ⟨e', he', hs'⟩
      simp only [List.mem_cons] at he'
      rcases he' with rfl | he'
      · simpa only [SchreibSeitAbsturz, hbe, hesF, hs', true_or]
      · have htail : SchreibSeitAbsturz x es := (ih hes).2 ⟨e', he', hs'⟩
        simpa only [SchreibSeitAbsturz, hbe, hesF, htail, or_true]

theorem SchreibSeitAbsturz_nach_absturz (x : Ort)
    {e : NiedrigesEreignis Ort Wert Grund Form}
    {es : List (NiedrigesEreignis Ort Wert Grund Form)} (hc : AbsturzBeob e = true) :
    SchreibSeitAbsturz x (e :: es) ↔ SchreibSeitAbsturz x es := by
  simp only [SchreibSeitAbsturz, hc]

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

/-- The observed write content of one optional low memory event. -/
def SchreibBeobOpt (x : Ort) : Option (NiedrigesEreignis Ort Wert Grund Form) → Prop
  | some ev => SchreibBeob x ev
  | none => False

theorem speicherBeob_schreibt_iff
    {label : Etiketten Ort} (hpub : ∀ y : Ort, oeffentlich (label.ort y) = true)
    (e : SpeicherAkteur Ort × Speicher.Etikett Ort Wert) :
    SchreibBeobOpt x (speicherBeob (Grund := Grund) (Form := Form) label e) ↔
      e.2.art.schreibt ∧ e.2.ort = x := by
  rcases e with ⟨akteur, lab⟩
  cases hArt : lab.art <;>
    simp only [speicherBeob, hArt, sichtbar, hpub, if_true, SchreibBeobOpt, SchreibBeob,
      Speicher.Art.schreibt, false_and, true_and]

theorem SchreibBeob_filterMap_speicherBeob
    {label : Etiketten Ort} (hpub : ∀ y : Ort, oeffentlich (label.ort y) = true)
    {es : List (SpeicherAkteur Ort × Speicher.Etikett Ort Wert)} :
    (∃ ev ∈ es.filterMap (speicherBeob (Grund := Grund) (Form := Form) label), SchreibBeob x ev) ↔
      ∃ e ∈ es, e.2.art.schreibt ∧ e.2.ort = x := by
  constructor
  · rintro ⟨ev, hev, hs⟩
    rw [List.mem_filterMap] at hev
    rcases hev with ⟨e, he, heq⟩
    have ho : SchreibBeobOpt x (speicherBeob (Grund := Grund) (Form := Form) label e) := by
      rw [heq]
      exact hs
    exact ⟨e, he, (speicherBeob_schreibt_iff (x := x) hpub e).1 ho⟩
  · rintro ⟨e, he, hs⟩
    have ho : SchreibBeobOpt x (speicherBeob (Grund := Grund) (Form := Form) label e) :=
      (speicherBeob_schreibt_iff (x := x) hpub e).2 hs
    cases hsome : speicherBeob (Grund := Grund) (Form := Form) label e with
    | none =>
      simp only [SchreibBeobOpt] at ho
      cases ho
    | some ev =>
      refine ⟨ev, ?_, ?_⟩
      · rw [List.mem_filterMap]
        exact ⟨e, he, hsome⟩
      · simpa only [SchreibBeobOpt] using ho

end Gabbro.Core.Beobachtung
