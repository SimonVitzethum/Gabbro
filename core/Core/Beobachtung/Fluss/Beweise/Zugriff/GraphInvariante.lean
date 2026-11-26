/-
  The single-run invariant behind `SpeicherGraphKopplungAussage`: a materialised write source at a cell
  exists exactly when a public write of that cell was observed after the last crash boundary. A restart
  rebuilds the graph while the low trace keeps the whole history, so a plain prefix reading is false.
-/
module

public import Core.Beobachtung.Fluss.Beweise.Zugriff.GraphBeob
public import Core.Beobachtung.Fluss.Fragment

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine
open Ast.Semantik (Fragment Befehl Plan)

variable {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]
variable {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form}

/-- Every observed memory event that writes is a `speicher` constructor. -/
theorem SchreibBeob_ist_speicher {x : Ort} {ev : NiedrigesEreignis Ort Wert Grund Form}
    (h : SchreibBeob x ev) :
    ∃ a art ort m g1 g2, ev = .speicher a art ort m g1 g2 := by
  cases ev with
  | speicher a art ort m g1 g2 => exact ⟨a, art, ort, m, g1, g2, rfl⟩
  | _ => cases h

/-- The boolean form of the observed-write predicate. -/
def SchreibBeobBool [DecidableEq Ort] (x : Ort) :
    NiedrigesEreignis Ort Wert Grund Form → Bool
  | .speicher _ .schreiben ort _ _ _ => decide (ort = x)
  | .speicher _ .rmw ort _ _ _ => decide (ort = x)
  | _ => false

theorem SchreibBeobBool_iff [DecidableEq Ort] (x : Ort)
    (ev : NiedrigesEreignis Ort Wert Grund Form) :
    SchreibBeobBool x ev = true ↔ SchreibBeob x ev := by
  cases ev with
  | speicher a art ort m g1 g2 =>
    cases art <;> simp only [SchreibBeobBool, SchreibBeob, Bool.decide_eq_true]
  | _ => simp only [SchreibBeobBool, SchreibBeob, Bool.false_eq_true]

theorem filter_nil_iff_forall [DecidableEq α] (f : α → Bool) (l : List α) :
    l.filter f = [] ↔ ∀ a ∈ l, f a = false := by
  induction l with
  | nil => simp only [List.filter_nil, List.not_mem_nil, forall_false_eq_true]
  | cons a as ih =>
    cases h : f a <;> simp only [List.filter_cons, h, Bool.false_eq_true, Bool.true_eq_false,
      if_false, if_true, Bool.false_and, List.cons_ne_nil, Bool.false_eq_true, ih,
      List.mem_cons, forall_exists_index, or_and_right]

/-- No outside event produces a low memory write observation. -/
theorem aussenBeob_filter_nil [DecidableEq Ort]
    (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form) (event : Ereignis) (x : Ort) :
    (aussenBeob E event).filter (SchreibBeobBool (Wert := Wert) (Grund := Grund) (Form := Form) x) = [] := by
  cases event <;> simp only [aussenBeob, sichtbar, Option.toList, List.filter_append,
    List.filter_cons, List.filter_nil, SchreibBeobBool, Bool.false_eq_true, if_false,
    List.nil_append]

/-- No protocol or output event produces a low memory write observation. -/
theorem kontextBeob_filter_nil [DecidableEq Ort]
    (ρ : Lauf E) (predictor : Praediktor) (t : Nat) (c : Kontext)
    (s n : Zustand L Ort Wert Raum Lok Grund) (spur : SchrittSpur Ort Wert) (x : Ort) :
    (kontextBeob ρ predictor t c s n spur).filter
      (SchreibBeobBool (Wert := Wert) (Grund := Grund) (Form := Form) x) = [] := by
  unfold kontextBeob
  dsimp only
  split
  · simp only [commitBeob, ausgabeBeob, zeitBeob, List.filter_append, List.filter_nil,
      List.filter_filterMap, SchreibBeobBool, Bool.false_eq_true]
  · simp only [commitBeob, ausgabeBeob, zeitBeob, List.filter_append, List.filter_nil,
      List.filter_filterMap, SchreibBeobBool, Bool.false_eq_true]

end Gabbro.Core.Beobachtung
