/-
  File:      core/Core/Maschine/Sperre.lean
  Subject:   LOCKS WITH OWNER, TICKET QUEUE AND HAND-OFF (PERFECT-MODEL §3.4, step M4): the language's
             lock. A context that wants the lock draws a ticket (`anstellen`: it joins the end of the queue);
             it takes a free lock only from the head of the queue (`Nimmt`); a release by the owner hands the
             lock directly to the head of the queue (`Gibt`, `abgeben`). Strong fairness is structural: the
             context at position `i` owns the lock after `i + 1` releases, whatever is queued meanwhile
             (`uebergabe_nach`, `anstellen_erhaelt`). Memory events of a lock follow the CHANGE of the owner
             (`Wechsel`), never a release of a lock not held -- such a release is no step (`Gibt` needs the
             owner).
-/
module

public import Core.Maschine.Kontext

@[expose] public section

namespace Gabbro.Core.Maschine

/-- **The state of a lock**: its owner and its ticket queue (oldest first). -/
structure SperrZustand where
  besitzer : Option Kontext
  schlange : List Kontext

namespace SperrZustand

/-- A free lock with an empty queue. -/
def frei : SperrZustand := ⟨none, []⟩

/-- Drawing a ticket: the context joins the end of the queue. -/
def anstellen (s : SperrZustand) (c : Kontext) : SperrZustand := ⟨s.besitzer, s.schlange ++ [c]⟩

/-- The release: the lock goes directly to the head of the queue, or becomes free. -/
def abgeben (s : SperrZustand) : SperrZustand :=
  match s.schlange with
  | [] => ⟨none, []⟩
  | c :: r => ⟨some c, r⟩

/-- **Taking a free lock**: only the head of the queue takes it. -/
inductive Nimmt : SperrZustand → Kontext → SperrZustand → Prop
  | frei (c : Kontext) (r : List Kontext) : Nimmt ⟨none, c :: r⟩ c ⟨some c, r⟩

/-- **Releasing**: only the owner releases; the lock is handed off. -/
inductive Gibt : SperrZustand → Kontext → SperrZustand → Prop
  | besitzer (c : Kontext) (r : List Kontext) : Gibt ⟨some c, r⟩ c (abgeben ⟨some c, r⟩)

/-- The owner changed: the only lock transitions that become memory events. -/
def Wechsel (s s' : SperrZustand) : Prop := s.besitzer ≠ s'.besitzer

/-- Only the owner releases. -/
theorem Gibt.besitzt {s s' : SperrZustand} {c : Kontext} (h : Gibt s c s') :
    s.besitzer = some c := by
  cases h
  rfl

/-- Taking makes the taker the owner. -/
theorem Nimmt.besitzt {s s' : SperrZustand} {c : Kontext} (h : Nimmt s c s') :
    s'.besitzer = some c ∧ s.besitzer = none := by
  cases h
  exact ⟨rfl, rfl⟩

/-- A take changes the owner, so it is a lock event. -/
theorem Nimmt.wechsel {s s' : SperrZustand} {c : Kontext} (h : Nimmt s c s') : Wechsel s s' := by
  cases h
  intro e
  cases e

/-- Drawing a ticket keeps every earlier position. -/
theorem anstellen_erhaelt (s : SperrZustand) (c : Kontext) {i : Nat} (h : i < s.schlange.length)
    (h' : i < (s.anstellen c).schlange.length) :
    (s.anstellen c).schlange[i]'h' = s.schlange[i]'h :=
  List.getElem_append_left h

/-- The state after `n` releases. -/
def abgebenN : Nat → SperrZustand → SperrZustand
  | 0, s => s
  | n + 1, s => abgebenN n (abgeben s)

/-- **Strong fairness of the ticket lock**: the context at position `i` of the queue owns the lock
    after `i + 1` releases. -/
theorem uebergabe_nach : ∀ (i : Nat) (o : Option Kontext) (q : List Kontext) (h : i < q.length),
    (abgebenN (i + 1) ⟨o, q⟩).besitzer = some (q[i]'h)
  | 0, _, [], h => absurd h (Nat.not_lt_zero 0)
  | i + 1, _, [], h => absurd h (Nat.not_lt_zero (i + 1))
  | 0, _, _ :: _, _ => rfl
  | i + 1, _, c :: r, h => uebergabe_nach i (some c) r (Nat.lt_of_succ_lt_succ h)

/-- Satisfiability: a lock is taken by a waiting context and handed to the next one. -/
theorem sperre_erfuellbar (c d : Kontext) :
    Nimmt ⟨none, [c, d]⟩ c ⟨some c, [d]⟩ ∧ Gibt ⟨some c, [d]⟩ c ⟨some d, []⟩ :=
  ⟨.frei c [d], .besitzer c [d]⟩

end SperrZustand

end Gabbro.Core.Maschine
