module

public import Core.Beobachtung.SchrankenB8

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine

/-- Empty intervals cost nothing, for the run and for every context.
    Difficulty: leicht. Sketch: unfold `Laufkosten`/`Kontextkosten`; both are `I.zaehle`
    at length `0`, which is `0` by its basis equation. -/
def kostenNullAussage : Prop :=
  ∀ (L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type) [DecidableEq L]
    (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (ρ : Lauf E) (c : Kontext) (anfang : Nat),
    Laufkosten ρ anfang 0 = 0 ∧ Kontextkosten ρ c anfang 0 = 0

/-- One cut extends the run cost by exactly the occupancy of its tick: an idle tick adds
    nothing, an occupied tick adds one.
    Difficulty: leicht. Sketch: unfold `Laufkosten`; rewrite with the step equation of
    `I.zaehle`; the two cases are the two values of `Option.isSome`. -/
def kostenSchrittAussage : Prop :=
  ∀ (L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type) [DecidableEq L]
    (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (ρ : Lauf E) (t : Nat),
    (ρ.zeit.spur t = none → Laufkosten ρ 0 (t + 1) = Laufkosten ρ 0 t) ∧
      (∀ w spur, ρ.zeit.spur t = some (w, spur) →
        Laufkosten ρ 0 (t + 1) = Laufkosten ρ 0 t + 1)

/-- Both cost counters split over adjacent intervals, for the run and per context. This is the
    workhorse for the per-pass bound of `forever` and for every interval-chopping argument.
    Difficulty: mittel. Sketch: induction over the second length with the step equation of
    `I.zaehle`; the index shift needs `Nat.add_assoc`. -/
def kostenTeilungAussage : Prop :=
  ∀ (L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type) [DecidableEq L]
    (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (ρ : Lauf E) (c : Kontext) (anfang m n : Nat),
    Laufkosten ρ anfang (m + n) = Laufkosten ρ anfang m + Laufkosten ρ (anfang + m) n ∧
      Kontextkosten ρ c anfang (m + n)
        = Kontextkosten ρ c anfang m + Kontextkosten ρ c (anfang + m) n

/-- Run costs grow monotonically with the interval length.
    Difficulty: leicht-mittel. Sketch: write `n = m + (n - m)` and apply the run half of
    `kostenTeilungAussage` with `Nat.le_add_right`. -/
def kostenMonotonAussage : Prop :=
  ∀ (L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type) [DecidableEq L]
    (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (ρ : Lauf E) (anfang m n : Nat),
    m ≤ n → Laufkosten ρ anfang m ≤ Laufkosten ρ anfang n

/-- The cost leg holds at the initial cut: an empty prefix costs nothing.
    Difficulty: leicht. Sketch: `kostenNullAussage` gives cost `0`; `UnterGrenze` with
    need `0` follows from `Nat.zero_le`. -/
def kostenAnfangAussage : Prop :=
  ∀ (L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type) [DecidableEq L]
    (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (ρ : Lauf E),
    KostenPrefix E ρ 0

/-- The hold leg holds at the initial cut: the only interval inside cut `0` is empty.
    Difficulty: leicht-mittel. Sketch: `a + n ≤ 0` forces `a = n = 0`; the context cost is
    `0` by `kostenNullAussage`; `UnterGrenze` follows from `Nat.zero_le`. -/
def halteAnfangAussage : Prop :=
  ∀ (L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type) [DecidableEq L]
    (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (ρ : Lauf E),
    HaltePrefix E ρ 0

/-- A tick that carries no context step of `c` preserves the hold prefix for `c`: every
    interval ending at the new cut either already ended before, or its last tick contributes
    nothing, so the counted cost is unchanged and ownership restricts to the shorter interval.
    This covers idle ticks, answers, interrupts, crashes and steps of other contexts in one
    lemma; the same-context hold step is the checker-dependent remainder.
    Difficulty: mittel. Sketch: case split on `a + n ≤ t` (induction hypothesis) versus
    `a + n = t + 1` (last tick contributes nothing: `I.zaehle` step equation; `n = 0` is
    trivial); ownership restricts to the subinterval. -/
def halteFremdAussage : Prop :=
  ∀ (L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type) [DecidableEq L]
    (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (ρ : Lauf E) (c : Kontext) (t : Nat),
    (∀ d w spur, ρ.zeit.spur t = some (.kontext d w, spur) → d ≠ c) →
      HaltePrefix E ρ t → HaltePrefix E ρ (t + 1)

/-- A freshly opened `rumpf` mark always meets its bound: no clock has advanced yet.
    Difficulty: leicht-mittel. Sketch: substitute the equality of start and cut; the clock
    difference is `0`, which satisfies every bound via `Nat.zero_le`. -/
def zeitRumpfNeuAussage : Prop :=
  ∀ (max : Option Nat) (d : Zeitdeklaration) (anfang cut : Nat)
    (clock kosten : Nat → Nat),
    anfang = cut →
      ZeitInSchranken max d .rumpf anfang cut clock kosten

/-- A decided in-time check stays valid when the cut moves out: the checked instant is fixed,
    so only the order hypotheses need extending by transitivity.
    Difficulty: mittel. Sketch: unfold `ZeitInSchranken`; extend `t ≤ cut` and the clock
    order by `le_trans`; all other components are unchanged. -/
def zeitRechtzeitigErweiternAussage : Prop :=
  ∀ (max : Option Nat) (d : Zeitdeklaration) (geprueft anfang cut cut' : Nat)
    (clock kosten : Nat → Nat),
    ZeitInSchranken max d (.rechtzeitig geprueft) anfang cut clock kosten →
      cut ≤ cut' → clock cut ≤ clock cut' →
      ZeitInSchranken max d (.rechtzeitig geprueft) anfang cut' clock kosten

/-- A decided late check stays valid when the cut moves out: same shape as the in-time case,
    the fallback cost refers to the fixed check instant.
    Difficulty: mittel. Sketch: as for `zeitRechtzeitigErweiternAussage`; the `lateKosten`
    premise is untouched because the check instant does not move. -/
def zeitSpaetErweiternAussage : Prop :=
  ∀ (max : Option Nat) (d : Zeitdeklaration) (geprueft anfang cut cut' : Nat)
    (clock kosten : Nat → Nat),
    ZeitInSchranken max d (.late geprueft) anfang cut clock kosten →
      cut ≤ cut' → clock cut ≤ clock cut' →
      ZeitInSchranken max d (.late geprueft) anfang cut' clock kosten

/-- An idle tick preserves the cost and hold prefix: the state is unchanged and neither
    cost counter moves. The time prefix is excluded on purpose: the hardware clock may advance
    on an idle tick, so running `rumpf` marks need the B19 clock bounds. This is the stuttering
    case of every future per-form induction.
    Difficulty: mittel. Sketch: cost legs via `kostenSchrittAussage` (idle case) and
    `halteFremdAussage` (an idle tick is foreign to every context). -/
def khLeerlaufAussage : Prop :=
  ∀ (L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type) [DecidableEq L]
    (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (ρ : Lauf E) (t : Nat),
    ρ.zeit.spur t = none →
      KostenPrefix E ρ t → HaltePrefix E ρ t →
      KostenPrefix E ρ (t + 1) ∧ HaltePrefix E ρ (t + 1)

end Gabbro.Core.Beobachtung
