/-
  File:      Core/Fortschritt/SperrHilfen.lean
  Subject:   SMALL LOCKS AND COUNTING LEMMAS FOR THE WAITING BOUND (PERFECT-MODEL §3.7, step M8):
             taking from the head, queue positions, ticket hand-off as releases, owner-step
             budgets and M9 holds bound on the owners own steps.
-/
module

public import Core.Fortschritt.Klasse

@[expose] public section

namespace Gabbro.Core.Fortschritt

open Gabbro.Core.Maschine
open Gabbro.Core.Katalog
open Gabbro.Core.Beobachtung

variable {L Ort Wert Raum Lok Grund Bedingung Wahl F : Type} [DecidableEq L]
variable {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl F}

/-- A free lock with the waiter at the head can be taken. -/
theorem nimmt_am_kopf {o : Option Kontext} {qq : List Kontext} {h : Kontext} {q : List Kontext}
    (hfree : o = none) (hhead : qq = h :: q) :
    ∃ s', (⟨o, qq⟩ : SperrZustand).Nimmt h s' := by
  subst hfree
  subst hhead
  exact ⟨_, .frei h q⟩

/-- Head shape of a queue known by its zeroth entry. -/
theorem schlange_kopfform {q : List Kontext} {c : Kontext} (h : q[(0 : Nat)]? = some c) :
    ∃ r, q = c :: r := by
  cases q with
  | nil =>
    have hnone : (([] : List Kontext)[(0 : Nat)]? = none) := rfl
    rw [hnone] at h
    cases h
  | cons x xs =>
    have hx : x = c := Option.some.inj (List.getElem?_cons_zero.symm.trans h)
    subst hx
    exact ⟨xs, rfl⟩

/-- Membership gives a queue position. -/
theorem mem_getElem? {q : List Kontext} {c : Kontext} (h : c ∈ q) : ∃ i : Nat, q[i]? = some c := by
  induction q with
  | nil => exact (List.not_mem_nil h).elim
  | cons x xs ih =>
    rcases List.mem_cons.mp h with heq | h'
    · subst heq
      exact ⟨0, rfl⟩
    · obtain ⟨i, hi⟩ := ih h'
      exact ⟨i + 1, by simpa only [List.getElem?_cons_succ] using hi⟩

/-- A bound on a singleton list. -/
theorem forall_mem_singleton_le {x H : Nat} (h : x ≤ H + 1) : ∀ y ∈ [x], y ≤ H + 1 := by
  intro y hy
  have heq : y = x := List.mem_singleton.mp hy
  subst heq
  exact h

/-- A release hands the lock off as a queue step. -/
theorem gibt_abgeben {s s' : SperrZustand} {h : Kontext} (hg : s.Gibt h s') :
    ∃ q, s = ⟨some h, q⟩ ∧ s' = SperrZustand.abgeben ⟨some h, q⟩ := by
  cases hg with
  | besitzer _ q => exact ⟨q, rfl, rfl⟩

/-- The owner-step budgets of a hand-off chain fit in positions times bound. -/
theorem halter_summe_schranke (e : List Nat) (H : Nat) (hall : ∀ x ∈ e, x ≤ H + 1) :
    e.sum ≤ e.length * (H + 1) := by
  induction e with
  | nil =>
    have h0 : ([] : List Nat).sum = 0 := rfl
    have h1 : ([] : List Nat).length * (H + 1) = 0 := by
      simp only [List.length_nil, Nat.zero_mul]
    omega
  | cons x e ih =>
    have hx : x ≤ H + 1 := hall x (List.mem_cons.mpr (Or.inl rfl))
    have htail : e.sum ≤ e.length * (H + 1) :=
      ih (fun y hy => hall y (List.mem_cons.mpr (Or.inr hy)))
    have hsum : (x :: e).sum = x + e.sum := rfl
    have hlen : (x :: e).length = e.length + 1 := rfl
    have hdist : (e.length + 1) * (H + 1) = (H + 1) + e.length * (H + 1) := by
      rw [Nat.add_mul, Nat.one_mul]
      exact Nat.add_comm _ _
    rw [hsum, hlen, hdist]
    exact Nat.add_le_add hx htail

/-- A hold bound on the owner's own steps, from `HalteSchranken` and the unit data. -/
theorem halte_kosten_schranke {ρ : Maschine.Lauf E} {l : L} {h : Kontext} {H a n : Nat}
    (halte : E.schranken.halten l = some H)
    (hhalte : HalteSchranken E ρ)
    (hown : ∀ t, a ≤ t → t < a + n → ∃ s, ρ.zeit.zustand t = some s ∧
      (s.sperren l).besitzer = some h) :
    Kontextkosten ρ h a n ≤ H :=
  (hhalte l h a n hown) H halte

end Gabbro.Core.Fortschritt
