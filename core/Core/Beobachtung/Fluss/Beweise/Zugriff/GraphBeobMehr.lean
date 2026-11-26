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

/-- The boolean form of an observed write. -/
def SB [DecidableEq Ort] (x : Ort) : NiedrigesEreignis Ort Wert Grund Form → Bool
  | .speicher _ .schreiben ort _ _ _ => decide (ort = x)
  | .speicher _ .rmw ort _ _ _ => decide (ort = x)
  | _ => false

theorem SB_iff (x : Ort) (ev : NiedrigesEreignis Ort Wert Grund Form) :
    SB x ev = true ↔ SchreibBeob x ev := by
  cases ev with
  | speicher a art ort m g1 g2 =>
    cases art <;> simp only [SB, SchreibBeob, Bool.false_eq_true, decide_eq_true_eq]
  | _ => simp only [SB, SchreibBeob, Bool.false_eq_true]

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
      have hb : f b = false := h a b hg
      simp only [List.filterMap_cons, hg, List.filter_cons, hb,
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
    simp only [aussenBeob, List.filter_cons]
    cases a with
    | read t o c =>
      simp only [SB, Bool.false_eq_true, if_false]
      exact filter_sichtbar_nil _ _ (by rfl)
    | write t o b =>
      simp only [SB, Bool.false_eq_true, if_false]
      exact filter_sichtbar_nil _ _ (by rfl)
  | geraet q a | interrupt c irq e | seite q =>
    rw [aussenBeob]
    rfl
  | persistenz pe =>
    cases pe with
    | write addr value =>
      rw [aussenBeob]
      exact filter_sichtbar_nil _ _ (by rfl)
    | durable w =>
      rw [aussenBeob]
      exact filter_sichtbar_nil _ _ (by rfl)
    | discard w =>
      rw [aussenBeob]
      exact filter_sichtbar_nil _ _ (by rfl)
    | flush range | fence | crash =>
      rw [aussenBeob]
      rfl

end Gabbro.Core.Beobachtung
