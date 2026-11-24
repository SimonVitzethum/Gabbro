module

public import Core.Ideal.Replay
public import Core.Maschine.Start

@[expose] public section

namespace Gabbro.Core.Maschine.I

open Gabbro.Core.Katalog

variable {L Ort Wert Raum Lok Grund Bedingung Wahl ι : Type}
variable {s i s' i' : Zustand L Ort Wert Raum Lok Grund}

/-- Both machines expose the same outside accounting after discarding pre-crash pending work. -/
theorem aussen_absturz (h : AussenBezug s i) (w : Wiederanlauf Ort Wert Raum Lok Grund)
    (t : Nat) (p q : PersistZustand) :
    AussenBezug (s.wiederanlauf w t p) (i.wiederanlauf w t q) :=
  ⟨h.fragen, h.antworten, h.verbraucht, h.verlauf, rfl, by
    simp only [Zustand.wiederanlauf, Zustand.angekommen, h.antworten, h.verbraucht]⟩

/-- The volatile parts may differ at a crash. Equality of the surviving medium and of the
    observation ledger suffices to restart at exactly the same state. -/
theorem absturz_rahmen {region w k hw t spur spur'}
    (bezug : AussenBezug s i) (medium : nachAbsturz s.persistenz = nachAbsturz i.persistenz)
    (konkret : AbsturzSchritt region w k hw t s spur s')
    (ideal : AbsturzSchritt region w k hw t i spur' i') :
    spur = spur' ∧ s' = i' := by
  refine ⟨konkret.genau.1.trans ideal.genau.1.symm, ?_⟩
  rw [konkret.genau.2, ideal.genau.2, medium]
  simp only [Zustand.wiederanlauf, Zustand.angekommen, bezug.fragen, bezug.antworten,
    bezug.verlauf, bezug.verbraucht]

variable [DecidableEq L] {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι}

/-- The crash case of simulation at an arbitrary matched hardware cut. Both runs must
    take the crash offer, and their continuations start from the same state. -/
theorem absturz_im_lauf {ρ : Maschine.Lauf E} {η : Lauf E} {t : Nat}
    (hw : ρ.hw = η.hw) (offer : AbsturzAngeboten E.katalog ρ.hw t)
    (atCut : ρ.zeit.zustand t = some s) (bezug : AussenBezug s (η.zeit.zustand t))
    (medium : nachAbsturz s.persistenz = nachAbsturz (η.zeit.zustand t).persistenz) :
    ρ.zeit.spur t = some absturzSpur ∧ η.zeit.spur t = some absturzSpur ∧
      ρ.zeit.zustand (t + 1) = some (η.zeit.zustand (t + 1)) := by
  obtain ⟨spur, next, label, state, konkret⟩ := Maschine.absturz_am_schnitt atCut offer
  obtain ⟨spur', label', ideal⟩ := absturz_am_schnitt E η (hw ▸ offer)
  rw [hw] at konkret
  obtain ⟨_, eq⟩ := absturz_rahmen bezug medium konkret ideal
  exact ⟨label.trans (congrArg some konkret.genau.1), label'.trans (congrArg some ideal.genau.1),
    state.trans (congrArg some eq)⟩

end Gabbro.Core.Maschine.I
