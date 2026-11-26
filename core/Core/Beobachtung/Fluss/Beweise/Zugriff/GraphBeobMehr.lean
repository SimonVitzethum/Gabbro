/-
  The low trace writes only at memory events. These lemmas let the single-run graph invariant read the
  write events of one step off `spur.speicher` instead of inspecting every observation stream.
-/
module

public import Core.Beobachtung.Fluss.Beweise.Zugriff.GraphBeob

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine

variable {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L] [DecidableEq Ort]
variable {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form}

abbrev SB [DecidableEq Ort] (x : Ort) : NiedrigesEreignis Ort Wert Grund Form → Bool :=
  SchreibBeobBool (Wert := Wert) (Grund := Grund) (Form := Form) x

theorem filter_map_nil [DecidableEq α] (f : β → Bool) (g : α → β) (l : List α)
    (h : ∀ a, f (g a) = false) : (l.map g).filter f = [] := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [List.map_cons, List.filter_cons, h a, Bool.false_eq_true, if_false, ih]

theorem filter_filterMap_nil [DecidableEq α] (f : β → Bool) (g : α → Option β) (l : List α)
    (h : ∀ a b, g a = some b → f b = false) : (l.filterMap g).filter f = [] := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    cases hg : g a with
    | none => simp only [List.filterMap_cons, hg, List.filter_cons, ih]
    | some b =>
      cases hg
      simp only [List.filterMap_cons, List.filter_cons, h a b rfl,
        Bool.false_eq_true, if_false, ih]

theorem filter_sichtbar_nil (label : Etikett)
    (d : NiedrigesEreignis Ort Wert Grund Form) (hd : SB x d = false) :
    (sichtbar label d).toList.filter (SB x) = [] := by
  unfold sichtbar
  split
  · simp only [Option.toList, List.filter_cons, hd, Bool.false_eq_true, if_false,
      List.filter_nil, List.nil_append]
  · rfl

theorem filter_option_map_nil [DecidableEq α] (f : β → Bool) (o : Option α) (g : α → β)
    (h : ∀ a, f (g a) = false) : (o.map g).toList.filter f = [] := by
  cases o with
  | none => rfl
  | some a =>
    simp only [Option.map, Option.toList, List.filter_cons, h a, Bool.false_eq_true,
      if_false, List.filter_nil, List.nil_append]

/-- No outside event produces a low memory write observation. -/
theorem aussenBeob_filter_nil
    (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form) (event : Ereignis) (x : Ort) :
    (aussenBeob E event).filter (SB x) = [] := by
  cases event with
  | frage q =>
    rw [aussenBeob]
    exact filter_sichtbar_nil _ _ (by rfl)
  | antwort q =>
    rw [aussenBeob, List.filter_append, filter_sichtbar_nil _ _ (by rfl), List.nil_append]
    cases hok : q.reply.result.isOk
    · rfl
    · apply filter_option_map_nil
      intro p
      rfl
  | dma q a =>
    rw [aussenBeob, List.filter_cons]
    cases a with
    | read t o c => simp only [SB, SchreibBeobBool, Bool.false_eq_true, if_false]
    | write t o b => simp only [SB, SchreibBeobBool, Bool.false_eq_true, if_false]
    rw [filter_sichtbar_nil _ _ (by rfl), List.nil_append]
  | geraet q a | interrupt c irq e | seite q =>
    rw [aussenBeob]
    rfl
  | persistenz pe =>
    rw [aussenBeob]
    cases pe <;> simp only
    · exact filter_sichtbar_nil _ _ (by rfl)
    · exact filter_sichtbar_nil _ _ (by rfl)
    · exact filter_sichtbar_nil _ _ (by rfl)
    · rfl
    · rfl
    · rfl

end Gabbro.Core.Beobachtung
