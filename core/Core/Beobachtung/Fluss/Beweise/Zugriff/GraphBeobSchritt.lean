/-
  Step-level lemmas for the single-run memory-graph invariant. A step's low observation is
  `speicher.filterMap speicherBeob ++ aussen.flatMap aussenBeob ++ form ++ abschluesse`. The last three
  parts never write a cell and never carry a crash boundary: a crash boundary is exactly the low event
  `.katalog (.persistenz .crash)`, which only a crash step contributes. Hence for a non-crash step the
  write observations of a step are exactly those of `spur.speicher`.
-/
module

public import Core.Beobachtung.Fluss.Beweise.Zugriff.GraphBeobMehr

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine

variable {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L] [DecidableEq Ort]
variable {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form}

/-- `HatAbsturz` is false when every element is not a crash boundary. -/
theorem hatAbsturz_of_all_false {l : List (NiedrigesEreignis Ort Wert Grund Form)}
    (h : ∀ e ∈ l, AbsturzBeob e = false) : HatAbsturz l = false := by
  induction l with
  | nil => rfl
  | cons e es ih =>
    have he : AbsturzBeob e = false := h e (by simp only [List.mem_cons, eq_self_iff_true, true_or])
    have hes : ∀ e' ∈ es, AbsturzBeob e' = false := by
      intro e' he'
      exact h e' (by simp only [List.mem_cons, he', or_true])
    simp only [HatAbsturz, he, Bool.false_or, ih hes]

theorem hatAbsturz_singleton (e : NiedrigesEreignis Ort Wert Grund Form)
    (he : AbsturzBeob e = false) : HatAbsturz [e] = false := by
  simp only [HatAbsturz, he, Bool.false_or]

/-- A filtered list is empty when every element fails the predicate. -/
theorem filter_SB_nil_of_all {l : List (NiedrigesEreignis Ort Wert Grund Form)} (x : Ort)
    (h : ∀ e ∈ l, SB x e = false) : l.filter (SB x) = [] := by
  induction l with
  | nil => rfl
  | cons e es ih =>
    have he : SB x e = false := h e (by simp only [List.mem_cons, eq_self_iff_true, true_or])
    have hes : ∀ e' ∈ es, SB x e' = false := by
      intro e' he'
      exact h e' (by simp only [List.mem_cons, he', or_true])
    simp only [List.filter_cons, he, Bool.false_eq_true, if_false, ih hes]

/-- A list with no observed write at `x` has no `SchreibBeob x`. -/
theorem keinSchreib_aus_filter_nil {l : List (NiedrigesEreignis Ort Wert Grund Form)} (x : Ort)
    (h : l.filter (SB x) = []) : ∀ e ∈ l, ¬ SchreibBeob x e := by
  intro e he hs
  have hm : e ∈ l.filter (SB x) := by
    rw [List.mem_filter]
    exact ⟨he, (SB_iff x e).2 hs⟩
  rw [h] at hm
  cases hm

/-- Appending a write-free tail preserves existence of an observed write. -/
theorem exists_schreib_append_nil {l₁ l₂ : List (NiedrigesEreignis Ort Wert Grund Form)}
    (x : Ort) (h : ∀ e ∈ l₂, ¬ SchreibBeob x e) :
    (∃ e ∈ l₁ ++ l₂, SchreibBeob x e) ↔ ∃ e ∈ l₁, SchreibBeob x e := by
  constructor
  · rintro ⟨e, he, hs⟩
    rw [List.mem_append] at he
    rcases he with he | he
    · exact ⟨e, he, hs⟩
    · exact False.elim (h e he hs)
  · rintro ⟨e, he, hs⟩
    exact ⟨e, by rw [List.mem_append]; exact Or.inl he, hs⟩

/-- Filter lemmas without a DecidableEq requirement on the source type. -/
private theorem filterMap_filter_nil' {α β : Type} (f : β → Bool) (g : α → Option β) (l : List α)
    (h : ∀ a b, g a = some b → f b = false) : (l.filterMap g).filter f = [] := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    cases hg : g a with
    | none => simp only [List.filterMap_cons, hg, ih]
    | some b =>
      have hb : f b = false := h a b hg
      simp only [List.filterMap_cons, hg, List.filter_cons, hb, Bool.false_eq_true, if_false, ih]

private theorem map_filter_nil' {α β : Type} (f : β → Bool) (g : α → β) (l : List α)
    (h : ∀ a, f (g a) = false) : (l.map g).filter f = [] := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [List.map_cons, List.filter_cons, h a, Bool.false_eq_true, if_false, ih]

/-- Generic `HatAbsturz` helpers with the event type fixed. -/
theorem map_absturz_false {α : Type} (l : List α)
    (g : α → NiedrigesEreignis Ort Wert Grund Form)
    (h : ∀ a, AbsturzBeob (g a) = false) : HatAbsturz (l.map g) = false := by
  induction l with
  | nil => rfl
  | cons a as ih => simp only [List.map_cons, HatAbsturz, h a, Bool.false_or, ih]

theorem filterMap_absturz_false {α : Type} (l : List α)
    (g : α → Option (NiedrigesEreignis Ort Wert Grund Form))
    (h : ∀ a b, g a = some b → AbsturzBeob b = false) :
    HatAbsturz (l.filterMap g) = false := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    cases hg : g a with
    | none => simpa only [List.filterMap_cons, hg] using ih
    | some b => rw [List.filterMap_cons, hg, HatAbsturz, h a b hg, Bool.false_or, ih]

theorem option_map_absturz_false {α : Type} (o : Option α)
    (g : α → NiedrigesEreignis Ort Wert Grund Form)
    (h : ∀ a, AbsturzBeob (g a) = false) : HatAbsturz (o.map g).toList = false := by
  cases o with
  | none => rfl
  | some a => simp only [Option.map, Option.toList, HatAbsturz, h a, Bool.false_or]

theorem sichtbar_absturz_false (label : Etikett) (d : NiedrigesEreignis Ort Wert Grund Form)
    (hd : AbsturzBeob d = false) : HatAbsturz (sichtbar label d).toList = false := by
  unfold sichtbar
  split
  · simp only [Option.toList, HatAbsturz, hd, Bool.false_or]
  · rfl

/-- No memory observation is a crash boundary. -/
theorem speicherBeob_absturz_false (label : Etiketten Ort)
    (a : SpeicherAkteur Ort × Speicher.Etikett Ort Wert)
    {ev : NiedrigesEreignis Ort Wert Grund Form}
    (h : speicherBeob (Grund := Grund) (Form := Form) label a = some ev) :
    AbsturzBeob ev = false := by
  rcases a with ⟨akteur, lab⟩
  cases hArt : lab.art <;> simp only [speicherBeob, hArt, sichtbar] at h ⊢
  · cases ho : oeffentlich (label.ort lab.ort) <;>
      simp only [ho, if_false, if_true, Option.some.injEq] at h ⊢
    · cases h
    · subst ev; rfl
  · cases ho : oeffentlich (label.ort lab.ort) <;>
      simp only [ho, if_false, if_true, Option.some.injEq] at h ⊢
    · cases h
    · subst ev; rfl
  · cases ho : oeffentlich (label.ort lab.ort) <;>
      simp only [ho, if_false, if_true, Option.some.injEq] at h ⊢
    · cases h
    · subst ev; rfl
  · cases h
  · cases h

theorem hatAbsturz_filterMap_speicherBeob (label : Etiketten Ort)
    (l : List (SpeicherAkteur Ort × Speicher.Etikett Ort Wert)) :
    HatAbsturz (l.filterMap (speicherBeob (Grund := Grund) (Form := Form) label)) = false := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    cases hbe : speicherBeob (Grund := Grund) (Form := Form) label a with
    | none => simpa only [List.filterMap_cons, hbe] using ih
    | some ev =>
      have hev := speicherBeob_absturz_false (label := label) (a := a) (ev := ev) hbe
      rw [List.filterMap_cons, hbe, HatAbsturz, hev, Bool.false_or, ih]

/-- A catalogue event is not a crash boundary unless it is the crash event itself. -/
theorem aussenBeob_keinCrash (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    {event : Ereignis} (hne : event ≠ .persistenz .crash) :
    HatAbsturz (aussenBeob E event) = false := by
  cases event with
  | frage q =>
    rw [aussenBeob]
    exact sichtbar_absturz_false _ _ (by rfl)
  | antwort q =>
    rw [aussenBeob]
    dsimp only
    rw [hatAbsturz_append]
    have hr1 : HatAbsturz (sichtbar (E.etiketten.frage q.question)
        (NiedrigesEreignis.antwort (Ort := Ort) (Wert := Wert) (Grund := Grund) (Form := Form)
          q.context q.questionInstance q.question q.reply)).toList = false :=
      sichtbar_absturz_false _ _ (by rfl)
    have hr2 : HatAbsturz ((if q.reply.result.isOk then
        (registerAdresse E.katalog.plattform q.question).map fun (bus, adresse) =>
          NiedrigesEreignis.register (Ort := Ort) (Wert := Wert) (Grund := Grund) (Form := Form)
            q.question.endpoint bus adresse
        else none).toList) = false := by
      by_cases hok : q.reply.result.isOk = true
      · rw [if_pos hok]
        apply option_map_absturz_false
        intro pair
        rfl
      · rw [if_neg hok]
        rfl
    rw [hr1, hr2]
    rfl
  | dma q a =>
    simp only [aussenBeob]
    cases a with
    | read token offset count =>
      simp only [HatAbsturz, AbsturzBeob, Bool.false_or]
      exact sichtbar_absturz_false _ _ (by rfl)
    | write token offset bytes =>
      simp only [HatAbsturz, AbsturzBeob, Bool.false_or]
      exact sichtbar_absturz_false _ _ (by rfl)
  | geraet q a =>
    rw [aussenBeob]
    exact hatAbsturz_singleton _ (by rfl)
  | interrupt c irq entry =>
    rw [aussenBeob]
    exact hatAbsturz_singleton _ (by rfl)
  | seite q =>
    rw [aussenBeob]
    exact hatAbsturz_singleton _ (by rfl)
  | persistenz pe =>
    cases pe with
    | write addr value =>
      rw [aussenBeob]
      exact sichtbar_absturz_false _ _ (by rfl)
    | durable w =>
      rw [aussenBeob]
      exact sichtbar_absturz_false _ _ (by rfl)
    | discard w =>
      rw [aussenBeob]
      exact sichtbar_absturz_false _ _ (by rfl)
    | flush range =>
      rw [aussenBeob]
      exact hatAbsturz_singleton _ (by rfl)
    | fence =>
      rw [aussenBeob]
      exact hatAbsturz_singleton _ (by rfl)
    | crash =>
      exact False.elim (hne rfl)

theorem hatAbsturz_flatMap_aussenBeob (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (l : List Ereignis) (h : ∀ e ∈ l, e ≠ .persistenz .crash) :
    HatAbsturz (l.flatMap (aussenBeob E)) = false := by
  induction l with
  | nil => rfl
  | cons e es ih =>
    have he : e ≠ .persistenz .crash := h e (by simp only [List.mem_cons, eq_self_iff_true, true_or])
    have hes : ∀ e' ∈ es, e' ≠ .persistenz .crash := by
      intro e' he'
      exact h e' (by simp only [List.mem_cons, he', or_true])
    rw [List.flatMap_cons, hatAbsturz_append, aussenBeob_keinCrash E he, ih hes, Bool.false_or]

theorem flatMap_aussenBeob_filter_nil (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (l : List Ereignis) (x : Ort) :
    (l.flatMap (aussenBeob E)).filter (SB x) = [] := by
  induction l with
  | nil => rfl
  | cons e es ih =>
    rw [List.flatMap_cons, List.filter_append, aussenBeob_filter_nil E e x, ih, List.nil_append]

/-- The machine-owned commit ledger contributes only register observations. -/
theorem commitBeob_filter_nil (p : Plattform) (v n : Zustand L Ort Wert Raum Lok Grund) (x : Ort) :
    (commitBeob p v n : List (NiedrigesEreignis Ort Wert Grund Form)).filter (SB x) = [] := by
  rw [commitBeob]
  apply filterMap_filter_nil'
  intro a b hg
  cases a with
  | freigabe => cases hg
  | aussen effect =>
    dsimp at hg
    cases hreg : registerAdresse p effect.frage with
    | none =>
      rw [hreg] at hg
      cases hg
    | some pair =>
      rcases pair with ⟨bus, adresse⟩
      rw [hreg] at hg
      dsimp at hg
      have hb := Option.some.inj hg
      subst b
      simp only [SB]

theorem commitBeob_keinCrash (p : Plattform) (v n : Zustand L Ort Wert Raum Lok Grund) :
    HatAbsturz (commitBeob p v n : List (NiedrigesEreignis Ort Wert Grund Form)) = false := by
  rw [commitBeob]
  apply filterMap_absturz_false
  intro a b hg
  cases a with
  | freigabe => cases hg
  | aussen effect =>
    dsimp at hg
    cases hreg : registerAdresse p effect.frage with
    | none =>
      rw [hreg] at hg
      cases hg
    | some pair =>
      rcases pair with ⟨bus, adresse⟩
      rw [hreg] at hg
      dsimp at hg
      have hb := Option.some.inj hg
      subst b
      rfl

theorem ausgabeBeob_filter_nil (c : Kontext) (v n : Lok) (x : Ort) :
    (ausgabeBeob E c v n : List (NiedrigesEreignis Ort Wert Grund Form)).filter (SB x) = [] := by
  rw [ausgabeBeob]
  apply map_filter_nil'
  intro a
  cases a <;> simp only [SB]

theorem ausgabeBeob_keinCrash (c : Kontext) (v n : Lok) :
    HatAbsturz (ausgabeBeob E c v n : List (NiedrigesEreignis Ort Wert Grund Form)) = false := by
  rw [ausgabeBeob]
  apply map_absturz_false
  intro a
  cases a <;> rfl

theorem zeitBeob_filter_nil (ρ : Lauf E) (c : Kontext) (v n : Lok) (x : Ort) :
    (zeitBeob ρ c v n : List (NiedrigesEreignis Ort Wert Grund Form)).filter (SB x) = [] := by
  rw [zeitBeob]
  dsimp only
  apply filterMap_filter_nil'
  intro a b hg
  cases ha : a.phase <;> simp only [ha] at hg ⊢
  · cases hg
  · have hb := Option.some.inj hg
    subst b
    simp only [SB]
  · have hb := Option.some.inj hg
    subst b
    simp only [SB]

theorem zeitBeob_keinCrash (ρ : Lauf E) (c : Kontext) (v n : Lok) :
    HatAbsturz (zeitBeob ρ c v n : List (NiedrigesEreignis Ort Wert Grund Form)) = false := by
  rw [zeitBeob]
  dsimp only
  apply filterMap_absturz_false
  intro a b hg
  cases ha : a.phase <;> simp only [ha] at hg ⊢
  · cases hg
  · have hb := Option.some.inj hg
    subst b
    rfl
  · have hb := Option.some.inj hg
    subst b
    rfl

theorem konstantBeob_filter_nil (form : Form) (c : Kontext) (l : List Ort) (k : Nat) (x : Ort)
    (b : Bool) :
    ((if b then [NiedrigesEreignis.konstanteZeit c form l k] else []) :
      List (NiedrigesEreignis Ort Wert Grund Form)).filter (SB x) = [] := by
  split
  · simp only [List.filter_cons, SB, Bool.false_eq_true, if_false, List.filter_nil]
  · rfl

theorem konstantBeob_keinCrash (form : Form) (c : Kontext) (l : List Ort) (k : Nat) (b : Bool) :
    HatAbsturz ((if b then [NiedrigesEreignis.konstanteZeit c form l k] else []) :
      List (NiedrigesEreignis Ort Wert Grund Form)) = false := by
  split
  · simp only [HatAbsturz, AbsturzBeob, Bool.false_or]
  · rfl

theorem spekulationBeob_filter_nil (c : Kontext) (l : List Ort) (x : Ort) :
    (l.map (fun adresse => (NiedrigesEreignis.spekulation (Ort := Ort) (Wert := Wert)
      (Grund := Grund) (Form := Form) c adresse))).filter (SB x) = [] := by
  apply map_filter_nil'
  intro a
  simp only [SB]

theorem spekulationBeob_keinCrash (c : Kontext) (l : List Ort) :
    HatAbsturz (l.map (fun adresse => (NiedrigesEreignis.spekulation (Ort := Ort) (Wert := Wert)
      (Grund := Grund) (Form := Form) c adresse))) = false := by
  apply map_absturz_false
  intro a
  rfl

/-- The context part of a step observation never writes a cell and never carries a crash. -/
theorem kontextBeob_filter_nil (ρ : Lauf E) (predictor : Praediktor) (t : Nat) (c : Kontext)
    (s n : Zustand L Ort Wert Raum Lok Grund) (spur : SchrittSpur Ort Wert) (x : Ort) :
    (kontextBeob ρ predictor t c s n spur : List (NiedrigesEreignis Ort Wert Grund Form)).filter (SB x) = [] := by
  rw [kontextBeob]
  dsimp only
  cases hkopf : E.system.kopf s c with
  | none =>
    simp only [List.filter_append, commitBeob_filter_nil, ausgabeBeob_filter_nil,
      zeitBeob_filter_nil, List.nil_append]
  | some form =>
    simp only [List.filter_append, spekulationBeob_filter_nil, konstantBeob_filter_nil,
      commitBeob_filter_nil, ausgabeBeob_filter_nil, zeitBeob_filter_nil, List.nil_append]

theorem kontextBeob_keinCrash (ρ : Lauf E) (predictor : Praediktor) (t : Nat) (c : Kontext)
    (s n : Zustand L Ort Wert Raum Lok Grund) (spur : SchrittSpur Ort Wert) :
    HatAbsturz (kontextBeob ρ predictor t c s n spur : List (NiedrigesEreignis Ort Wert Grund Form)) = false := by
  rw [kontextBeob]
  dsimp only
  cases hkopf : E.system.kopf s c with
  | none =>
    simp only [hatAbsturz_append, commitBeob_keinCrash, ausgabeBeob_keinCrash,
      zeitBeob_keinCrash, Bool.false_or]
  | some form =>
    simp only [hatAbsturz_append, spekulationBeob_keinCrash, konstantBeob_keinCrash,
      commitBeob_keinCrash, ausgabeBeob_keinCrash, zeitBeob_keinCrash, Bool.false_or]

/-- A termination closure is neither a write nor a crash boundary. -/
theorem abschlussBeob_filter_nil (ende : Kontext → Option (Ende Wert Grund)) (x : Ort)
    [Decidable (∃ c, (ende c).isSome = true)] :
    ((if ∃ c, (ende c).isSome = true then [NiedrigesEreignis.ende (Ort := Ort) (Wert := Wert)
      (Grund := Grund) (Form := Form) ende] else []) :
      List (NiedrigesEreignis Ort Wert Grund Form)).filter (SB x) = [] := by
  split
  · simp only [List.filter_cons, SB, Bool.false_eq_true, if_false, List.filter_nil]
  · rfl

theorem abschlussBeob_keinCrash (ende : Kontext → Option (Ende Wert Grund))
    [Decidable (∃ c, (ende c).isSome = true)] :
    HatAbsturz ((if ∃ c, (ende c).isSome = true then [NiedrigesEreignis.ende (Ort := Ort)
      (Wert := Wert) (Grund := Grund) (Form := Form) ende] else []) :
      List (NiedrigesEreignis Ort Wert Grund Form)) = false := by
  split
  · simp only [HatAbsturz, AbsturzBeob, Bool.false_or]
  · rfl

end Gabbro.Core.Beobachtung
