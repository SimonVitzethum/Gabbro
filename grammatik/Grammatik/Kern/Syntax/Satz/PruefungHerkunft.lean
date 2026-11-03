/- C16 inventory item 13: report/token provenance at the evidence level.

    The report a gate receives is the one the probe produced -- never a
    guessed value, never a second usable owner. `BerichtHerkunft` pins the
    verdict threading: the discharged evidence entry carries the completed
    report unchanged, so its verdict is the probe's answer. `HerkunftSchritt`
    pins the travel order: a live entry (pushed, then completed at the
    producer's normal pop) becomes the consumed entry at the admitted gate
    push, for the same probe and the same report. The machine-event half
    (call push and normal pop over `RufEreignisF`) lives in
    `Parser/Elab/Uebersetze/Pruefung/Herkunft.lean`, which may import the
    call machine; this file stays on the evidence level so `Satz.lean` keeps
    its import order. -/
module

public import Grammatik.Kern.Syntax.Satz.Pruefung
public import Grammatik.Kern.Syntax.Satz.PruefungAbschluss

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration}

section Herkunft

variable [DecidableEq D.Fn]

/-- The verdict a gate receives is the one the probe produced: the discharged
    evidence entry carries the completed report unchanged. -/
def BerichtHerkunft (P : Programm D) (c : CheckDecl D) (r : CheckReport)
    (g : D.Fn) : Prop :=
  CheckEntladung P c r g ∧
    (⟨c.probe, r, false, some g⟩ : CheckEvidenz D).bericht = r

/-- The verdict threading follows from the discharge. -/
theorem bericht_herkunft_aus_entladung {P : Programm D} {c : CheckDecl D}
    {r : CheckReport} {g : D.Fn} (h : CheckEntladung P c r g) :
    BerichtHerkunft P c r g :=
  ⟨h, rfl⟩

/-- Every sample of a completed report was actually observed at its push: the
    completion carries no guessed value. -/
theorem herkunft_proben_vollstaendig {P : Programm D} {c : CheckDecl D}
    {r : CheckReport} (h : CheckAbschluss P c r) : r.vollstaendig :=
  h.2.1

/-- One step of the token's travel: a live entry (pushed, then completed at
    the producer's normal pop) becomes the consumed entry at the admitted
    gate push, for the same probe and the same report. -/
def HerkunftSchritt (e₁ e₂ : CheckEvidenz D) : Prop :=
  e₁.erzeuger = e₂.erzeuger ∧ e₁.bericht = e₂.bericht ∧
    e₁.lebt = true ∧ e₁.tor = none ∧ e₂.lebt = false ∧ ∃ g, e₂.tor = some g

/-- The travel step follows from the discharge: the live completed entry of
    the probe becomes the consumed entry of the discharging gate. -/
theorem herkunft_schritt_aus_entladung {P : Programm D} {c : CheckDecl D}
    {r : CheckReport} {g : D.Fn} (h : CheckEntladung P c r g) :
    HerkunftSchritt (D := D) ⟨c.probe, r, true, none⟩ ⟨c.probe, r, false, some g⟩ := by
  obtain ⟨_, _, _⟩ := h
  exact ⟨rfl, rfl, rfl, rfl, rfl, g, rfl⟩

/-! ## Witnesses: the travel step on the fixture, for both verdicts -/

/-- The travel step of the completed positive report through its gate. -/
theorem herkunft_schritt_wahr_zeuge :
    HerkunftSchritt (D := pruefD)
      ⟨pruefC1.probe, messBerichtWahr, true, none⟩
      ⟨pruefC1.probe, messBerichtWahr, false, some false⟩ :=
  herkunft_schritt_aus_entladung entladung_wahr_zeuge

/-- The travel step of the completed negative report through the same gate:
    the failure stays report data on the travel. -/
theorem herkunft_schritt_falsch_zeuge :
    HerkunftSchritt (D := pruefD)
      ⟨pruefC1.probe, messBerichtFalsch, true, none⟩
      ⟨pruefC1.probe, messBerichtFalsch, false, some false⟩ :=
  herkunft_schritt_aus_entladung entladung_falsch_zeuge

/-- The consumed false entry carries the negative verdict: the gate receives
    what the probe produced. -/
theorem herkunft_urteil_zeuge :
    (⟨pruefC1.probe, messBerichtFalsch, false, some false⟩ :
      CheckEvidenz pruefD).bericht.urteil = false := rfl

/-- The completed true report threads its verdict into the discharge. -/
theorem herkunft_bericht_wahr_zeuge :
    BerichtHerkunft pruefP pruefC1 messBerichtWahr false :=
  bericht_herkunft_aus_entladung entladung_wahr_zeuge

end Herkunft

end Gabbro.Grammatik
