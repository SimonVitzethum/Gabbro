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

   Proven below (`#print axioms` at the end shows each rests on no axioms):
     `fristErgebnis_abgelaufen` / `fristErgebnis_ok` -- the outcome answers
       `Hardware.fortschritt` with the deadline's assumption on expiry, nothing
       off it. This is the `fristAlsAnnahme` mapping of `Ziel.lean`
       (`def fristAlsAnnahme (a : D.Annahme) : Hardware D := .fortschritt a`),
       mirrored by shape, not imported (same boundary as `Budget.lean`, which
       cites the mapping without reading it; the lane forbids the index edit
       that would wire the import).
     `fristErgebnis_eq_some_iff` / `fristErgebnis_eq_none_iff` -- exact on the
       outcome: `some` iff expiry under some deadline, `none` iff `ok`.
     `fristlauf_some_abgelaufen` / `fristlauf_some_ok` -- the decision answers
       expiry exactly when the deadline lies strictly between check and use.
     `fristErgebnis_fristlauf_some` / `fristErgebnis_fristlauf_ok` -- composed:
       `fristErgebnis` over `fristlauf` answers `fortschritt` exactly on
       expiry, `none` exactly off it.
     `fristErgebnis_fristlauf_none` / `fristlauf_erschöpfend` -- no deadline
       moment is `ok`; every run is `ok` or expiry. No third outcome.
   What the shapes MEAN over a run -- which step counts as the check, which as
   the use, what sets the deadline moment -- is cut, not faked (C1 below).

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
    C3  The `Ziel.lean` mapping is mirrored, not imported: the lane scope
        forbids the index edit that would wire the import, so `fristAlsAnnahme`
        is cited by shape (`.fortschritt f.annahme`). Check per-file with
        `lake env lean Grammatik/Fristlauf.lean` and with the full `lake build`.

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
    deadline's name. This is the `fristAlsAnnahme` mapping of `Ziel.lean`,
    mirrored by shape (`.fortschritt f.annahme`), not imported.
    `ok` answers nothing. -/
def fristErgebnis {D : Deklaration} : FristOut D → Option (Hardware D)
  | .ok => none
  | .abgelaufen f => some (.fortschritt f.annahme)

/-! ## Expiry answers the hardware outcome -- exactly `fortschritt` on expiry -/

/-- On expiry the outcome answers `fortschritt` with the deadline's
    assumption -- the `fristAlsAnnahme` mapping of `Ziel.lean`. -/
theorem fristErgebnis_abgelaufen {D : Deklaration} (f : Frist D) :
    fristErgebnis (.abgelaufen f) = some (.fortschritt f.annahme) := rfl

/-- Off expiry the outcome answers nothing. -/
theorem fristErgebnis_ok {D : Deklaration} :
    fristErgebnis (.ok : FristOut D) = none := rfl

/-- Exact on the outcome: `some` iff expiry under some deadline, naming exactly
    that deadline's assumption. -/
theorem fristErgebnis_eq_some_iff {D : Deklaration} (o : FristOut D) (h : Hardware D) :
    fristErgebnis o = some h ↔ ∃ f : Frist D, o = .abgelaufen f ∧ .fortschritt f.annahme = h := by
  cases o with
  | ok =>
    constructor
    · intro hh
      simp [fristErgebnis] at hh
    · rintro ⟨_, hg, _⟩
      cases hg
  | abgelaufen f =>
    simp only [fristErgebnis]
    constructor
    · intro hh
      exact ⟨f, rfl, Option.some_inj.mp hh⟩
    · rintro ⟨_, hg, heq⟩
      cases hg
      exact congrArg some heq

/-- Exact on the quiet case: `none` iff `ok`. -/
theorem fristErgebnis_eq_none_iff {D : Deklaration} (o : FristOut D) :
    fristErgebnis o = none ↔ o = .ok := by
  cases o with
  | ok => simp [fristErgebnis]
  | abgelaufen _ => simp [fristErgebnis]

/-- The decision, unfolded: a deadline moment expires the run iff it lies
    strictly between check and use. -/
theorem fristlauf_some {D : Deklaration} (p : PruefPaar) (f : Frist D) (m : Moment) :
    fristlauf p f (some m) =
      (if decide (p.pruef < m ∧ m < p.lauf) then .abgelaufen f else .ok) := rfl

/-- The run expires under the deadline's name exactly when the deadline lies
    strictly between check and use. -/
theorem fristlauf_some_abgelaufen {D : Deklaration} (p : PruefPaar) (f : Frist D) (m : Moment) :
    fristlauf p f (some m) = .abgelaufen f ↔ laeuftAb p m := by
  rw [fristlauf_some]
  unfold laeuftAb
  by_cases h : p.pruef < m ∧ m < p.lauf
  · rw [if_pos (decide_eq_true h)]
    exact iff_of_true rfl h
  · rw [if_neg (fun he => h (of_decide_eq_true he))]
    exact iff_of_false (by simp) h

/-- The run is `ok` exactly when the deadline does not lie strictly between
    check and use -- endpoint coincidence included. -/
theorem fristlauf_some_ok {D : Deklaration} (p : PruefPaar) (f : Frist D) (m : Moment) :
    fristlauf p f (some m) = .ok ↔ ¬ laeuftAb p m := by
  rw [fristlauf_some]
  unfold laeuftAb
  by_cases h : p.pruef < m ∧ m < p.lauf
  · rw [if_pos (decide_eq_true h)]
    exact iff_of_false (by simp) (fun hn => hn h)
  · rw [if_neg (fun he => h (of_decide_eq_true he))]
    exact iff_of_true rfl h

/-- Composed, on expiry: `fristErgebnis` over `fristlauf` answers
    `Hardware.fortschritt` with the deadline's assumption exactly when the
    deadline lies strictly between check and use. -/
theorem fristErgebnis_fristlauf_some {D : Deklaration} (p : PruefPaar) (f : Frist D) (m : Moment) :
    fristErgebnis (fristlauf p f (some m)) = some (.fortschritt f.annahme) ↔ laeuftAb p m := by
  constructor
  · intro hh
    by_cases h : laeuftAb p m
    · exact h
    · have hok : fristlauf p f (some m) = .ok := (fristlauf_some_ok p f m).mpr h
      rw [hok, fristErgebnis_ok] at hh
      cases hh
  · intro h
    rw [(fristlauf_some_abgelaufen p f m).mpr h, fristErgebnis_abgelaufen]

/-- Composed, off expiry: `fristErgebnis` over `fristlauf` answers nothing
    exactly when the deadline does not lie strictly between check and use. -/
theorem fristErgebnis_fristlauf_ok {D : Deklaration} (p : PruefPaar) (f : Frist D) (m : Moment) :
    fristErgebnis (fristlauf p f (some m)) = none ↔ ¬ laeuftAb p m := by
  constructor
  · intro hh h
    have hs := (fristErgebnis_fristlauf_some p f m).mpr h
    rw [hh] at hs
    cases hs
  · intro h
    rw [(fristlauf_some_ok p f m).mpr h, fristErgebnis_ok]

/-- No deadline moment: the run answers nothing. -/
theorem fristErgebnis_fristlauf_none {D : Deklaration} (p : PruefPaar) (f : Frist D) :
    fristErgebnis (fristlauf p f none) = none := rfl

/-- No third outcome: every run is `ok` or expiry under some deadline. -/
theorem fristlauf_erschöpfend {D : Deklaration} (p : PruefPaar) (f : Frist D) (d : Option Moment) :
    fristlauf p f d = .ok ∨ ∃ g : Frist D, fristlauf p f d = .abgelaufen g := by
  cases d with
  | none => exact Or.inl rfl
  | some m =>
    by_cases h : laeuftAb p m
    · exact Or.inr ⟨f, (fristlauf_some_abgelaufen p f m).mpr h⟩
    · exact Or.inl ((fristlauf_some_ok p f m).mpr h)

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
#print axioms Gabbro.Grammatik.fristErgebnis_abgelaufen
#print axioms Gabbro.Grammatik.fristErgebnis_ok
#print axioms Gabbro.Grammatik.fristErgebnis_eq_some_iff
#print axioms Gabbro.Grammatik.fristErgebnis_eq_none_iff
#print axioms Gabbro.Grammatik.fristlauf_some
#print axioms Gabbro.Grammatik.fristlauf_some_abgelaufen
#print axioms Gabbro.Grammatik.fristlauf_some_ok
#print axioms Gabbro.Grammatik.fristErgebnis_fristlauf_some
#print axioms Gabbro.Grammatik.fristErgebnis_fristlauf_ok
#print axioms Gabbro.Grammatik.fristErgebnis_fristlauf_none
#print axioms Gabbro.Grammatik.fristlauf_erschöpfend

end Gabbro.Grammatik
