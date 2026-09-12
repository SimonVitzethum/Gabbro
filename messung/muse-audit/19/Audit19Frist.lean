-- Audit demo G: `sampling_closes_frist` conclusion restates the miss-arm
-- exclusion. Pattern (a)/(e): `hspace : d + S ≤ p.lauf` is exactly the
-- negation of the `p.lauf < d + S` miss arm, so the proof closes the
-- second disjunct by contradiction with the premise -- the premise IS the
-- conclusion's missing case. Slice anchor: Ziel.lean:366-369 premises and
-- line 387 use inside `ziel_nutzer_last`.
-- Also pattern (d): the §5 docstring books this leg as the "probe leg"
-- discharging the deadline, while the file itself (Fristlauf.lean:388)
-- says sampling alone never discharges `hspace`.
import Grammatik.Ziel
import Grammatik.Fristlauf

namespace GabbroAudit19

open Gabbro.Grammatik

-- The miss arm `p.lauf < d + S` and the premise `d + S ≤ p.lauf` are
-- direct negations: the premise rules out exactly the case the window
-- leaves open, by `Nat.not_lt`.
example (S d l : Nat) (h : d + S ≤ l) : ¬ l < d + S :=
  Nat.not_lt.mpr h

-- The positive arm needs no clock either: given a tick in range, the
-- existential is the tick itself plus the `fristErgebnis` rewrite --
-- the clock premises (`hstart`, TickClock laws) are used only to GET the
-- tick via `c.window`, i.e. the detection content is the window
-- disjunction, and `hspace` deletes its second arm.
example {D : Deklaration} {S : Nat} (c : TickClock S)
    (hstart : c.tick 0 ≤ S) (p : PruefPaar) (f : Frist D) (d : Moment)
    (hpd : p.pruef < d) (hdl : d < p.lauf)
    (hspace : deadlineSpacing S p d) :
    ∃ n, d ≤ c.tick n ∧ c.tick n ≤ p.lauf ∧
      fristErgebnis (fristlauf p f (some d)) = some (.fortschritt f.annahme) :=
  sampling_closes_frist c hstart p f d hpd hdl hspace

#print axioms Gabbro.Grammatik.sampling_closes_frist

/-
CUTS:
- Not a soundness bug: `sampling_closes_frist` is valid. The audit point
  is pattern (a): with `hspace` as premise, the theorem's content over
  `TickClock.window` is exactly deleting the miss arm the premise negates.
  The per-use hardware duty (`hspace`, NAMED-HW) stays open, as the file
  itself books it.
-/
