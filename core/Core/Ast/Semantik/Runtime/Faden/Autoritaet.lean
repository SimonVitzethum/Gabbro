/-
  File:      core/Core/Ast/Semantik/Runtime/Faden/Autoritaet.lean
  Subject:   AUTHORITY MOVES, IT IS NEVER COPIED (MK-07). A thread start hands handles over to the new thread
             (`Buchung.uebergeben`), a join takes back what the ended thread still held (`Buchung.zurueckgegeben`). Both
             are functions on the holdings of the ledger. The lemmas say what they do exactly:
             * what `von` held on a handed-over handle passes to `an`, and `von` holds none of it afterwards
               (`uebergeben_an`, `uebergeben_von`);
             * the holdings of every other context and of every other handle are unchanged
               (`uebergeben_andere`, `uebergeben_ausser`);
             * exclusive authority keeps one holder (`uebergeben_eindeutig`, `zurueckgegeben_eindeutig`): no handle is
               ever held with the right to write or to release by two contexts after a hand-over or a take-back,
               if it was not before. Authority is therefore present EXACTLY ONCE after a start.
-/
module

public import Core.Maschine.Buchung

@[expose] public section

namespace Gabbro.Core.Sicherheit

open Maschine

variable {Ort : Type}

/-- **Authority copied instead of moved**: the starter keeps what it handed over. The model REPRESENTS this error
    (`fadenAutoritaet_nichtTrivial`); it is not what a start does. -/
def Buchung.kopiert (b : Buchung Ort) (von an : Kontext) (gs : List Griff) :
    Kontext → Griff → Speicherrecht → Prop :=
  fun d g r => b.haelt d g r ∨ (d = an ∧ g ∈ gs ∧ b.haelt von g r)

/-- **The holdings after a hand-over, spelled out.** -/
theorem Buchung.uebergeben_iff (b : Buchung Ort) (von an : Kontext) (gs : List Griff) (d : Kontext) (g : Griff)
    (r : Speicherrecht) :
    b.uebergeben von an gs d g r ↔
      (g ∈ gs ∧ ((d = an ∧ (b.haelt von g r ∨ b.haelt an g r)) ∨ (d ≠ an ∧ d ≠ von ∧ b.haelt d g r))) ∨
        (g ∉ gs ∧ b.haelt d g r) := by
  unfold Buchung.uebergeben
  by_cases hg : g ∈ gs
  · rw [if_pos hg]
    by_cases h1 : d = an
    · rw [if_pos h1]
      constructor
      · intro h
        exact Or.inl ⟨hg, Or.inl ⟨h1, h⟩⟩
      · rintro (⟨_, ⟨_, h⟩ | ⟨h, _⟩⟩ | ⟨h, _⟩)
        · exact h
        · exact absurd h1 h
        · exact absurd hg h
    · rw [if_neg h1]
      by_cases h2 : d = von
      · rw [if_pos h2]
        constructor
        · intro h
          exact h.elim
        · rintro (⟨_, ⟨h, _⟩ | ⟨_, h, _⟩⟩ | ⟨h, _⟩)
          · exact absurd h h1
          · exact absurd h2 h
          · exact absurd hg h
      · rw [if_neg h2]
        constructor
        · intro h
          exact Or.inl ⟨hg, Or.inr ⟨h1, h2, h⟩⟩
        · rintro (⟨_, ⟨h, _⟩ | ⟨_, _, h⟩⟩ | ⟨h, _⟩)
          · exact absurd h h1
          · exact h
          · exact absurd hg h
  · rw [if_neg hg]
    constructor
    · intro h
      exact Or.inr ⟨hg, h⟩
    · rintro (⟨h, _⟩ | ⟨_, h⟩)
      · exact absurd h hg
      · exact h

/-- **What `von` held on a handed-over handle, `an` holds afterwards.** -/
theorem Buchung.uebergeben_an (b : Buchung Ort) (von an : Kontext) (gs : List Griff) {g : Griff} (hg : g ∈ gs)
    (r : Speicherrecht) (h : b.haelt von g r) : b.uebergeben von an gs an g r := by
  rw [Buchung.uebergeben_iff]
  exact Or.inl ⟨hg, Or.inl ⟨rfl, Or.inl h⟩⟩

/-- **`von` holds nothing of what it handed over.** -/
theorem Buchung.uebergeben_von (b : Buchung Ort) {von an : Kontext} (gs : List Griff) (hne : von ≠ an)
    {g : Griff} (hg : g ∈ gs) (r : Speicherrecht) : ¬ b.uebergeben von an gs von g r := by
  rw [Buchung.uebergeben_iff]
  rintro (⟨_, ⟨h, _⟩ | ⟨_, h, _⟩⟩ | ⟨h, _⟩)
  · exact hne h
  · exact h rfl
  · exact h hg

/-- **Nobody else's holdings change.** -/
theorem Buchung.uebergeben_andere (b : Buchung Ort) {von an : Kontext} (gs : List Griff) {d : Kontext}
    (hvon : d ≠ von) (han : d ≠ an) (g : Griff) (r : Speicherrecht) :
    b.uebergeben von an gs d g r ↔ b.haelt d g r := by
  rw [Buchung.uebergeben_iff]
  constructor
  · rintro (⟨_, ⟨h, _⟩ | ⟨_, _, h⟩⟩ | ⟨_, h⟩)
    · exact absurd h han
    · exact h
    · exact h
  · intro h
    by_cases hg : g ∈ gs
    · exact Or.inl ⟨hg, Or.inr ⟨han, hvon, h⟩⟩
    · exact Or.inr ⟨hg, h⟩

/-- **No other handle changes.** -/
theorem Buchung.uebergeben_ausser (b : Buchung Ort) (von an : Kontext) {gs : List Griff} {g : Griff}
    (hg : g ∉ gs) (d : Kontext) (r : Speicherrecht) : b.uebergeben von an gs d g r ↔ b.haelt d g r := by
  rw [Buchung.uebergeben_iff]
  constructor
  · rintro (⟨h, _⟩ | ⟨_, h⟩)
    · exact absurd h hg
    · exact h
  · intro h
    exact Or.inr ⟨hg, h⟩

/-- **A hand-over keeps exclusive authority with one holder.** -/
theorem Buchung.uebergeben_eindeutig (b : Buchung Ort) (von an : Kontext) (gs : List Griff)
    (h : b.Eindeutig) (d d' : Kontext) (g : Griff) (r : Speicherrecht)
    (hr : r = Speicherrecht.schreiben ∨ r = Speicherrecht.freigeben)
    (hd : b.uebergeben von an gs d g r) (hd' : b.uebergeben von an gs d' g r) : d = d' := by
  rw [Buchung.uebergeben_iff] at hd hd'
  rcases hd with ⟨hg, ⟨h1, a1⟩ | ⟨h1, v1, b1⟩⟩ | ⟨hg, b1⟩ <;>
    rcases hd' with ⟨hg', ⟨h2, a2⟩ | ⟨h2, v2, b2⟩⟩ | ⟨hg', b2⟩
  · exact h1.trans h2.symm
  · rcases a1 with hv | ha
    · exact absurd (h von d' g r hr hv b2).symm v2
    · exact absurd (h an d' g r hr ha b2).symm h2
  · exact absurd hg hg'
  · rcases a2 with hv | ha
    · exact absurd (h d von g r hr b1 hv) v1
    · exact absurd (h d an g r hr b1 ha) h1
  · exact h d d' g r hr b1 b2
  · exact absurd hg hg'
  · exact absurd hg' hg
  · exact absurd hg' hg
  · exact h d d' g r hr b1 b2

/-- **The holdings after a take-back, spelled out.** -/
theorem Buchung.zurueckgegeben_iff (b : Buchung Ort) (kind an : Kontext) (d : Kontext) (g : Griff)
    (r : Speicherrecht) :
    b.zurueckgegeben kind an d g r ↔
      (d = an ∧ (b.haelt an g r ∨ b.haelt kind g r)) ∨ (d ≠ an ∧ d ≠ kind ∧ b.haelt d g r) := by
  unfold Buchung.zurueckgegeben
  by_cases h1 : d = an
  · rw [if_pos h1]
    constructor
    · intro h
      exact Or.inl ⟨h1, h⟩
    · rintro (⟨_, h⟩ | ⟨h, _⟩)
      · exact h
      · exact absurd h1 h
  · rw [if_neg h1]
    by_cases h2 : d = kind
    · rw [if_pos h2]
      constructor
      · intro h
        exact h.elim
      · rintro (⟨h, _⟩ | ⟨_, h, _⟩)
        · exact absurd h h1
        · exact absurd h2 h
    · rw [if_neg h2]
      constructor
      · intro h
        exact Or.inr ⟨h1, h2, h⟩
      · rintro (⟨h, _⟩ | ⟨_, _, h⟩)
        · exact absurd h h1
        · exact h

/-- **What the ended thread still held, the joiner holds afterwards; the ended thread holds nothing.** -/
theorem Buchung.zurueckgegeben_zurueck (b : Buchung Ort) {kind an : Kontext} (hne : kind ≠ an)
    (g : Griff) (r : Speicherrecht) (h : b.haelt kind g r) :
    b.zurueckgegeben kind an an g r ∧ ¬ b.zurueckgegeben kind an kind g r := by
  constructor
  · rw [Buchung.zurueckgegeben_iff]
    exact Or.inl ⟨rfl, Or.inr h⟩
  · rw [Buchung.zurueckgegeben_iff]
    rintro (⟨e, _⟩ | ⟨_, e, _⟩)
    · exact hne e
    · exact e rfl

/-- **A take-back keeps exclusive authority with one holder.** -/
theorem Buchung.zurueckgegeben_eindeutig (b : Buchung Ort) (kind an : Kontext)
    (h : b.Eindeutig) (d d' : Kontext) (g : Griff) (r : Speicherrecht)
    (hr : r = Speicherrecht.schreiben ∨ r = Speicherrecht.freigeben)
    (hd : b.zurueckgegeben kind an d g r) (hd' : b.zurueckgegeben kind an d' g r) : d = d' := by
  rw [Buchung.zurueckgegeben_iff] at hd hd'
  rcases hd with ⟨h1, a1⟩ | ⟨h1, k1, b1⟩ <;> rcases hd' with ⟨h2, a2⟩ | ⟨h2, k2, b2⟩
  · exact h1.trans h2.symm
  · rcases a1 with ha | hk
    · exact absurd (h an d' g r hr ha b2).symm h2
    · exact absurd (h kind d' g r hr hk b2).symm k2
  · rcases a2 with ha | hk
    · exact absurd (h d an g r hr b1 ha) h1
    · exact absurd (h d kind g r hr b1 hk) k1
  · exact h d d' g r hr b1 b2

end Gabbro.Core.Sicherheit
