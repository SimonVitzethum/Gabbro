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
      `fristErgebnis_fristlauf_erschöpfend` -- exhaustive over the HARDWARE
        answer: every run answers `none` or a named `fortschritt`
        assumption. The expiry side is decided (`laeuftAb`); the hardware
        side stays an existential over the deadline's name (goal-conform,
        the `dma_inhalt` shape: a named hypothesis, never modelled).
      `TickClock` -- the sampler's hardware premises, named (`advance`,
        `maxGap`, per-use `start`): the same class as `dma_inhalt`.
      `TickClock.mono` -- timer monotonicity, proved from `advance`, never
        assumed beside it.
      `TickClock.covers` / `TickClock.window` -- the exact bound sampling
        gives: every deadline is met by a tick within one period; an expiry
        strictly between check and use is SEEN (a tick in `[d, l]`) or MISSED
        INSIDE A BOUND (`l < d + S`).
      `gridTick` / `gridClock` / `grid_window` -- the probe's discipline
        (start at `0`, step by `S`) keeps the clock premises (proved); the
        window for that grid. Addition-recursive, so no distribution lemma
        (which would cost `propext`) is ever needed.
      `sampling_upholds_frist` / `sampling_closes_frist` -- on the seen arm
        `fristErgebnis` answers the named `fortschritt` assumption (the
        `fristAlsAnnahme` mapping); with the residual premise
        (`deadlineSpacing`: the use waits out the window) detection is total.
   What the shapes MEAN over a run -- which step counts as the check, which as
   the use, what sets the deadline moment -- is cut, not faked (C1 below).

  Premises (trusted, not proved):
    P1  Moments are step indices: `t < t'` is the run order, not the clock.
    P2  The probe measures the deadline: `Frist.sonde` names it, nothing here
        reads it.
     P3  Sampling keeps a named clock (`TickClock`): ticks advance every step
         (hence monotone, proved as `TickClock.mono`), no gap exceeds `S`,
         the first tick lands within `S` (`start`). The grid instance
         (`gridClock`) is proved; that the hardware keeps the grid is assumed
         per use (C4).

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
     C4  No probe link: nothing here says the hardware keeps the grid.
         `sonde_tick.c` samples counter cycles (R15/W10: a sample, not a
         verdict); it is not a periodic deadline sampler. The clock is the
         sampling argument's shape, not the probe -- discharging `hProbe`
         (`Ziel.lean`) cites these names, it does not import them (same lane
         as C3).

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

/-- Exhaustive over the HARDWARE answer: every run answers nothing or a named
    hardware `fortschritt` assumption -- no third hardware outcome. The expiry
    side is decided by `laeuftAb` (proved above); the hardware side stays an
    existential over the deadline's named assumption -- goal-conform, the same
    shape as `dma_inhalt` in `Geraet.lean`, where the content invariant is a
    named hypothesis, never modelled. -/
theorem fristErgebnis_fristlauf_erschöpfend {D : Deklaration} (p : PruefPaar)
    (f : Frist D) (d : Option Moment) :
    fristErgebnis (fristlauf p f d) = none ∨
      ∃ a : D.Annahme, fristErgebnis (fristlauf p f d) = some (.fortschritt a) := by
  cases d with
  | none => exact Or.inl rfl
  | some m =>
    by_cases h : laeuftAb p m
    · exact Or.inr ⟨f.annahme, (fristErgebnis_fristlauf_some p f m).mpr h⟩
    · exact Or.inl ((fristErgebnis_fristlauf_ok p f m).mpr h)

/-! ## Sampling upholds the deadline assumption -- the bounded missed-expiry window -/

/-- The sampler's hardware premises, NAMED (same class as `dma_inhalt` in
    `Geraet.lean`): a tick counter that moves every step (`advance` -- hence
    monotone, proved as `TickClock.mono` below, never assumed beside it) and
    whose worst-case gap is the period (`maxGap`). Whether the hardware keeps
    them is a per-use premise (C4), never proved here. -/
structure TickClock (S : Nat) where
  tick : Nat → Moment
  advance : ∀ n, tick n < tick (n + 1)
  maxGap : ∀ n, tick (n + 1) ≤ tick n + S

/-- Timer monotonicity, PROVED from `advance`: a clock that moves every step
    never runs backward. Named so consumers cite monotonicity without
    re-proving it. -/
theorem TickClock.mono (c : TickClock S) {n m : Nat} (h : n ≤ m) :
    c.tick n ≤ c.tick m := by
  induction h with
  | refl => exact Nat.le_refl _
  | step h ih => exact Nat.le_trans ih (Nat.le_of_lt (c.advance _))

/-- Every deadline is met by a tick within one period: the sampling bound.
    Induction on the deadline: the step keeps the old tick while it still
    lies ahead, and moves one tick forward when the deadline reaches it --
    the forward tick lands within one gap (`maxGap`) past a moved (`advance`)
    tick. Needs `start` (the first tick is within `S`, so the induction
    starts) and nothing else. -/
theorem TickClock.covers (c : TickClock S) (hstart : c.tick 0 ≤ S) (d : Moment) :
    ∃ n, d < c.tick n ∧ c.tick n ≤ d + S := by
  induction d with
  | zero =>
    show ∃ n, 0 < c.tick n ∧ c.tick n ≤ 0 + S
    by_cases h : 0 < c.tick 0
    · exact ⟨0, h, Nat.le_trans hstart (Nat.le_add_left S 0)⟩
    · have hz : c.tick 0 = 0 := Nat.eq_zero_of_not_pos h
      have h1lt : 0 < c.tick 1 :=
        Nat.lt_of_le_of_lt (Nat.zero_le _) (c.advance 0)
      have h1le : c.tick 1 ≤ 0 + S :=
        Nat.le_trans (c.maxGap 0)
          (Nat.add_le_add (Nat.le_of_eq hz) (Nat.le_refl S))
      exact ⟨1, h1lt, h1le⟩
  | succ d ih =>
    show ∃ n, d + 1 < c.tick n ∧ c.tick n ≤ (d + 1) + S
    obtain ⟨n, hlt, hle⟩ := ih
    by_cases h : d + 1 < c.tick n
    · exact ⟨n, h, Nat.le_trans hle (Nat.add_le_add (Nat.le_succ d) (Nat.le_refl S))⟩
    · have h1 : d + 1 ≤ c.tick n := hlt
      have h2 : c.tick n ≤ d + 1 := Nat.not_lt.mp h
      exact ⟨n + 1, Nat.lt_of_le_of_lt h1 (c.advance n),
        Nat.le_trans (c.maxGap n) (Nat.add_le_add h2 (Nat.le_refl S))⟩

/-- Worst-case sampling: an expiry strictly between check and use is either
    SEEN -- some tick lands in `[d, l]` -- or MISSED INSIDE A BOUND -- the use
    sits within `S` of the deadline. This dichotomy is the EXACT bound
    sampling gives; closing the second arm is the residual premise
    (`deadlineSpacing`), never proved here. -/
theorem TickClock.window (c : TickClock S) (hstart : c.tick 0 ≤ S)
    (d l : Moment) :
    (∃ n, d ≤ c.tick n ∧ c.tick n ≤ l) ∨ l < d + S := by
  obtain ⟨n, hlt, hle⟩ := c.covers hstart d
  by_cases hseen : c.tick n ≤ l
  · exact Or.inl ⟨n, Nat.le_of_lt hlt, hseen⟩
  · exact Or.inr (Nat.lt_of_lt_of_le (Nat.not_le.mp hseen) hle)

/-- The probe's grid as the clock counts it: start at `0`, step by `S`.
    Addition-recursive, so both clock laws below hold by unfolding --
    no distribution lemma (which would cost `propext`) is ever needed. -/
def gridTick (S : Nat) : Nat → Moment
  | Nat.zero => 0
  | Nat.succ n => gridTick S n + S

/-- The probe's discipline keeps the clock premises: the grid advances every
    step and no gap exceeds `S` (both proved, from `0 < S`). What stays a
    premise is only that the hardware KEEPS this grid (C4). -/
def gridClock (S : Nat) (hS : 0 < S) : TickClock S where
  tick := gridTick S
  advance := by
    intro n
    show gridTick S n < gridTick S n + S
    exact Nat.lt_add_of_pos_right hS
  maxGap := by
    intro n
    show gridTick S n + S ≤ gridTick S n + S
    exact Nat.le_refl _

/-- The sampling bound for the probe's grid: every deadline strictly between
    two moments is met by a grid tick before the later one, or the later
    moment sits within `S` of the deadline. -/
theorem grid_window {S : Nat} (hS : 0 < S) (d l : Moment) :
    (∃ n, d ≤ (gridClock S hS).tick n ∧ (gridClock S hS).tick n ≤ l) ∨
      l < d + S := by
  have hstart : (gridClock S hS).tick 0 ≤ S := by
    show (0 : Nat) ≤ S
    exact Nat.zero_le S
  exact (gridClock S hS).window hstart d l

/-- Sampling upholds the deadline assumption up to the bounded window: every
    expiry strictly between check and use is either caught by a tick that
    still lands before the use -- and then `fristErgebnis` answers the named
    `fortschritt` assumption (the `fristAlsAnnahme` mapping of `Ziel.lean`) --
    or the use sits within `S` of the deadline. -/
theorem sampling_upholds_frist {D : Deklaration} {S : Nat} (c : TickClock S)
    (hstart : c.tick 0 ≤ S) (p : PruefPaar) (f : Frist D) (d : Moment)
    (hpd : p.pruef < d) (hdl : d < p.lauf) :
    (∃ n, d ≤ c.tick n ∧ c.tick n ≤ p.lauf ∧
      fristErgebnis (fristlauf p f (some d)) = some (.fortschritt f.annahme)) ∨
      p.lauf < d + S := by
  obtain h | h := c.window hstart d p.lauf
  · obtain ⟨n, hdn, hnl⟩ := h
    exact Or.inl ⟨n, hdn, hnl, (fristErgebnis_fristlauf_some p f d).mpr ⟨hpd, hdl⟩⟩
  · exact Or.inr h

/-- Residual HW premise (named, never modelled -- `dma_inhalt`-class): the use
    waits out the sampling window -- the deadline is at least `S` before the
    use. A watchdog at the use, or deadline granularity above `S`, discharges
    it per run; sampling alone never does. -/
def deadlineSpacing (S : Nat) (p : PruefPaar) (d : Moment) : Prop :=
  d + S ≤ p.lauf

/-- With the residual premise, detection is total: every expiry strictly
    between check and use is caught by a tick before the use, and
    `fristErgebnis` answers the named `fortschritt` assumption. The miss arm
    of the window contradicts the spacing, so it closes by `False`. -/
theorem sampling_closes_frist {D : Deklaration} {S : Nat} (c : TickClock S)
    (hstart : c.tick 0 ≤ S) (p : PruefPaar) (f : Frist D) (d : Moment)
    (hpd : p.pruef < d) (hdl : d < p.lauf)
    (hspace : deadlineSpacing S p d) :
    ∃ n, d ≤ c.tick n ∧ c.tick n ≤ p.lauf ∧
      fristErgebnis (fristlauf p f (some d)) = some (.fortschritt f.annahme) := by
  have hspace' : d + S ≤ p.lauf := hspace
  obtain h | h := c.window hstart d p.lauf
  · obtain ⟨n, hdn, hnl⟩ := h
    exact ⟨n, hdn, hnl, (fristErgebnis_fristlauf_some p f d).mpr ⟨hpd, hdl⟩⟩
  · exact absurd h (Nat.not_lt.mpr hspace')

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

-- Executable witness: the expiry decision RUNS at check time. `Hardware`
-- carries no `Repr`, so the witness projects the `fristlauf` decision to
-- strings: expiry inside the open interval, `ok` at either endpoint
-- coincidence. The `example` pins the printed triple, so a silent change in
-- the decision breaks the build instead of the log.
#eval (match fristlauf paarProbe fristProbe (some 5) with | .abgelaufen _ => "expired" | .ok => "ok",
  match fristlauf paarProbe fristProbe (some 7) with | .abgelaufen _ => "expired" | .ok => "ok",
  match fristlauf paarProbe fristProbe (some 3) with | .abgelaufen _ => "expired" | .ok => "ok")

example : (match fristlauf paarProbe fristProbe (some 5) with | .abgelaufen _ => "expired" | .ok => "ok",
    match fristlauf paarProbe fristProbe (some 7) with | .abgelaufen _ => "expired" | .ok => "ok",
    match fristlauf paarProbe fristProbe (some 3) with | .abgelaufen _ => "expired" | .ok => "ok") =
    ("expired", "ok", "ok") := by rfl

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
#print axioms Gabbro.Grammatik.fristErgebnis_fristlauf_erschöpfend
#print axioms Gabbro.Grammatik.TickClock.mono
#print axioms Gabbro.Grammatik.TickClock.covers
#print axioms Gabbro.Grammatik.TickClock.window
#print axioms Gabbro.Grammatik.gridTick
#print axioms Gabbro.Grammatik.gridClock
#print axioms Gabbro.Grammatik.grid_window
#print axioms Gabbro.Grammatik.deadlineSpacing
#print axioms Gabbro.Grammatik.sampling_upholds_frist
#print axioms Gabbro.Grammatik.sampling_closes_frist

end Gabbro.Grammatik
