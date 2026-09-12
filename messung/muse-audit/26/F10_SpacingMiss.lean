/-
  Audit 26, finding F10 -- Fristlauf.lean: `sampling_closes_frist`
  (line 395) adds premise `hspace : deadlineSpacing S p d`, i.e.
  `d + S ≤ p.lauf`, to `sampling_upholds_frist`. But `deadlineSpacing`
  says the use waits out the FULL sampling window -- which is nearly the
  conclusion (a tick in `[d, l]` exists because the window is wide
  enough). Pattern (a/e): the spacing premise plus `TickClock.window`
  (whose miss arm is `l < d + S`) closes the miss arm by `omega`-shaped
  contradiction -- the detection is carried by the ARITHMETIC of the
  premise, not by sampling. This demo shows the shape: spacing directly
  contradicts the miss arm.
-/
import Grammatik.Fristlauf

open Gabbro.Grammatik

/-- F10: spacing contradicts the miss arm on its own (no clock needed). -/
theorem audit26_spacing_kills_miss (S : Nat) (p : PruefPaar) (d : Moment)
    (hspace : deadlineSpacing S p d) : ¬ p.lauf < d + S := by
  unfold deadlineSpacing at hspace
  exact Nat.not_lt.mpr hspace

/-- F10: the filed composition, for reference. -/
theorem audit26_closes_frist_shape {D : Deklaration} {S : Nat}
    (c : TickClock S) (hstart : c.tick 0 ≤ S) (p : PruefPaar)
    (f : Frist D) (d : Moment) (hpd : p.pruef < d) (hdl : d < p.lauf)
    (hspace : deadlineSpacing S p d) :
    ∃ n, d ≤ c.tick n ∧ c.tick n ≤ p.lauf ∧
      fristErgebnis (fristlauf p f (some d)) = some (.fortschritt f.annahme) :=
  sampling_closes_frist c hstart p f d hpd hdl hspace

#print axioms audit26_spacing_kills_miss
#print axioms audit26_closes_frist_shape

/-
CUTS:
  (C1) Whether per-run spacing is dischargeable (watchdog/granularity) is
       booked in the file; this demo only shows the proof burden sits in
       the premise arithmetic.
-/
