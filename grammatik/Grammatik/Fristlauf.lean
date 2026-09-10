/-
  File:       Grammatik/Fristlauf.lean
  Subject:    Time-TOCTOU shapes as definitions: check-at-t, run-at-t', and
              expiry-between as an explicit named outcome.

  A time-of-check / time-of-use pair is `PruefPaar`: the check at moment `t`,
  the use at moment `t'`, with `t < t'` carried as a field. A moment is a
  `Nat` step index -- logical time, never wall-clock: there is no `Time`
  type below, and that absence is the statement (same boundary as
  `Budget.lean`, which counts steps, not seconds).

  The outcome is `FristOut`: either `ok`, or `abgelaufen` -- expiry-between
  as an EXPLICIT named shape. A deadline is the named environment assumption
  (`Frist.annahme`, answered as `Hardware.fortschritt` by `fristErgebnis`,
  the same assumption that carries `forever` in `Semantik.lean`) plus the
  probe that measures it (`Frist.sonde`, e.g. `"sonde_tick"`). The probe is
  NAMED, not modelled: measured by the probe, never proved here -- the same
  split as `fristAlsAnnahme` in `Ziel.lean`.

  Proven below: nothing -- this file holds shapes as `def`s, with the probe
  (`Sprechprobe`: `fristProbe` over the empty declaration `leer`, evaluated
  by `rfl`) showing each shape computes. What the shapes MEAN over a run --
  which step counts as the check, which as the use, what sets the deadline
  moment -- is cut, not faked (C1 below).

  Premises (trusted, not proved):
    P1  Moments are step indices: `t < t'` is the run order, not the clock.
    P2  The probe measures the deadline: `Frist.sonde` names it, nothing here
        reads it.

  Cuts (booked, not hidden):
    C1  No wiring into a run: `PruefPaar` and the deadline moment `d` are
        bare indices, not positions in a `GLauf` (`Geraet.lean`) or outcomes
        of `exec` (`Semantik.lean`). Tying check/use/expiry to device steps
        or to `foreverLauf` fuel is cut.
    C2  No duration arithmetic: a deadline is a moment, not a span; nothing
        adds, compares, or converts spans.
    C3  Not wired into `Grammatik.lean`: lane scope forbids the index edit;
        check this file directly with `lake env lean Grammatik/Fristlauf.lean`.

  No `mathlib`, no `sorry`, no `axiom`.
-/
import Grammatik.Satz

namespace Gabbro.Grammatik

/-- A logical moment: a step index into a run, never wall-clock. There is no
    `Time` type in this file, and that absence is the statement. -/
abbrev Moment := Nat

/-- Check-at-t / run-at-t': the check at `pruef`, the use at `lauf`, with the
    order carried as a field. A pair with `lauf ≤ pruef` is not writable --
    there is no term for a use before its check. -/
structure PruefPaar where
  pruef : Moment
  lauf : Moment
  reihenfolge : pruef < lauf

/-- A deadline: the named environment assumption plus the probe that measures
    it. The assumption is what expiry ANSWERS (`fristErgebnis`); the probe
    name (`sonde`) is what MEASURES it -- named here, read nowhere. -/
structure Frist (D : Deklaration) where
  annahme : D.Annahme
  sonde : String

/-- Expiry-between: the deadline moment lies strictly between check and use.
    Either endpoint coincidence (`d = pruef`, `d = lauf`) is `ok`, not
    expiry -- the shape names the open interval, nothing wider. -/
def laeuftAb (p : PruefPaar) (d : Moment) : Prop :=
  p.pruef < d ∧ d < p.lauf

/-- The outcome of a deadline run. Two constructors, like the two errors of
    `Ausgang` in `Semantik.lean`: `ok` is the quiet case, and expiry is
    `abgelaufen` -- named, carrying the deadline whose assumption answers.
    There is no third. -/
inductive FristOut (D : Deklaration) where
  | ok : FristOut D
  | abgelaufen (f : Frist D) : FristOut D

/-- The TOCTOU decision: a deadline moment strictly between check and use
    expires the run under the deadline's name; no deadline, or one outside
    the open interval, is `ok`. -/
def fristlauf {D : Deklaration} (p : PruefPaar) (f : Frist D)
    (d : Option Moment) : FristOut D :=
  match d with
  | none => .ok
  | some m => if decide (p.pruef < m ∧ m < p.lauf) then .abgelaufen f else .ok

/-- Expiry answers the hardware assumption `fortschritt` -- the same
    assumption that carries `forever` (`Semantik.lean`), reached through the
    deadline's name. `ok` answers nothing. -/
def fristErgebnis {D : Deklaration} : FristOut D → Option (Hardware D)
  | .ok => none
  | .abgelaufen f => some (.fortschritt f.annahme)

/-! ## Speech probe: the shapes compute (values, not sentences) -/

/-- The probe deadline over the empty declaration: the assumption is `unit`,
    the probe is the tick probe by name. -/
def fristProbe : Frist leer := ⟨(), "sonde_tick"⟩

/-- The probe pair: check at 3, use at 7. -/
def paarProbe : PruefPaar := ⟨3, 7, by decide⟩

/-- Deadline at 5, strictly between: the run expires under the probe's name. -/
example : fristlauf paarProbe fristProbe (some 5) = .abgelaufen fristProbe := by rfl

/-- Deadline AT the use: endpoint coincidence is `ok`, not expiry. -/
example : fristlauf paarProbe fristProbe (some 7) = .ok := by rfl

/-- Deadline AT the check: endpoint coincidence is `ok`, not expiry. -/
example : fristlauf paarProbe fristProbe (some 3) = .ok := by rfl

/-- No deadline moment: the run is `ok`. -/
example : fristlauf paarProbe fristProbe none = .ok := by rfl

/-- Expiry answers `fortschritt` with the deadline's assumption. -/
example : fristErgebnis (FristOut.abgelaufen fristProbe) = some (.fortschritt ()) := by rfl

/-- `ok` answers nothing. -/
example : fristErgebnis (FristOut.ok : FristOut leer) = none := by rfl

#print axioms Gabbro.Grammatik.laeuftAb
#print axioms Gabbro.Grammatik.fristlauf
#print axioms Gabbro.Grammatik.fristErgebnis
#print axioms Gabbro.Grammatik.fristProbe
#print axioms Gabbro.Grammatik.paarProbe

end Gabbro.Grammatik
