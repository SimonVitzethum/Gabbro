/-
  File:    Grammatik/Zielsatz/SpecProben.lean -- the anti-vacuity obligations of
           PLAN-ZIELSATZ.md §4, STATED (as `def … : Prop`), not proved.
  Purpose: the reviewer sees next to `GabbroZiel` (Spec.lean) what must be false and what
           must be true of its premises. `Proben.lean` proves them.

  Refutations -- each must FAIL a premise group:
  * probe A (`paP`, `ensures false`, `traverse … invariant false`)  -> (b) `NutzerPflicht`;
  * probe D (`fvP false`, `forever … invariant false { leave }`)   -> (b), at some budget;
  * a table-invariant breaker (`ivPschlecht`)                      -> (b);
  * an unguarded carrier one start reads and another writes        -> (a) `AkzeptiertSpec`
    (stated for EVERY program, so for every sound `Pruefer` the Bool is `false`).
  The refutations of (b) are stated for every lock-invariant family whose protected carriers
  are guarded and which SOME memory satisfies: a family no memory satisfies empties the class
  `HavocOk` and hence `NutzerPflicht` -- but then no start is admissible (`sperren`), so the
  whole statement is empty for it; that is review question 3, not a refutation.

  Positives -- all premises jointly, with an admissible start:
  * the two-thread program `mP` (two ACTIVE threads, private unguarded tables, a shared
    table under a lock with invariant `konto[0] == konto[1]`, idle `mRuhe` elsewhere);
  * probes B/C (`zPB`, `zPC`, family `zS`). EXPECTED FALSE ON `zD` AS IT STANDS: `zD` has
    four functions and no idle one; `Faden = Nat` runs infinitely many threads, so some
    function runs on two threads and must be `Ruhig` (`StartZulaessig.einmal`), and none of
    `ein`/`lies`/`wrap`/`haupt` has an empty footprint. The Proben lane must give `zD` an
    idle function (as `mD` has `mRuhe`) before B/C can be positives of THIS statement.
-/
import Grammatik.Zielsatz.Spec
import Grammatik.ProbeD
import Grammatik.InvZeuge
import Grammatik.MehrfadenZeuge

namespace Gabbro.Grammatik.Zielsatz

open Gabbro.Grammatik

instance zD_fn_deq' : DecidableEq zD.Fn := inferInstanceAs (DecidableEq ZFn)

/-- **All premise groups at once**: the checker's facts, the user's logic, SOME oracle meeting
    the hardware assumptions, and SOME admissible start. -/
def Erfuellbar {D : Deklaration} [DecidableEq D.Fn] (P : Programm D) (S : SperrInv D)
    (Q : AxEns D) (fs : Aufzaehlung D.Fn) (ws : List D.Fn) : Prop :=
  AkzeptiertSpec P S fs.1 ws ∧ NutzerPflicht P S Q ∧ (∃ O : Orakel D, HardwareAnnahmen O Q) ∧
    ∃ (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f)),
      StartZulaessig P S fs.1 ws sp init

/-- **Group (b) refutes `P`**: for every declared axiom ensures and every lock-invariant family
    with guarded carriers that some memory satisfies, the user obligation fails. -/
def NutzerWiderlegt {D : Deklaration} (P : Programm D) : Prop :=
  ∀ (S : SperrInv D) (Q : AxEns D), (∀ L c, c ∈ S.orte L → Bewacht c L) →
    (∃ s : Speicher D, ∀ L, S.inv L s = true) → ¬ NutzerPflicht P S Q

/-- Probe A fails (b). -/
def probeA_widerlegt : Prop := NutzerWiderlegt paP

/-- Probe D fails (b): at budget `1` the body ends in `logik schleife` (at budget `0` alone it
    would not -- the reason `NutzerPflicht` quantifies every budget). -/
def probeD_widerlegt : Prop := NutzerWiderlegt (fvP false)

/-- The `forever` variant with invariant `true` (the shape of `manifest_pruefen`,
    `beispiele/04-schleifen.gab`) fails (b) too: at budget `1` it returns under `ensures false`. -/
def probeD_wahr_widerlegt : Prop := NutzerWiderlegt (fvP true)

/-- A body that breaks a declared table invariant fails (b). -/
def tabelle_widerlegt : Prop := NutzerWiderlegt ivPschlecht

/-- **An unguarded shared write fails (a)**, for every program: a carrier with no guard lock
    that one declared start reaches in its footprint and ANOTHER declared start writes. -/
def ungeschuetzt_abgelehnt : Prop :=
  ∀ (D : Deklaration) [DecidableEq D.Fn] (P : Programm D) (S : SperrInv D) (fs ws : List D.Fn)
    (w₁ w₂ : D.Fn) (c : D.Tab ⊕ D.Glob),
    w₁ ∈ ws → w₂ ∈ ws → w₁ ≠ w₂ → c ∈ fussOrte P w₁ → TraegerSchreibt w₂ c = true →
    (∀ L, ¬ Bewacht c L) → ¬ AkzeptiertSpec P S fs ws

/-- **The two-thread program satisfies every premise group**, with its declared starts
    `hauptA`, `hauptB`, the family `mSI` and the trivial axiom ensures. -/
def zweiFaeden_erfuellbar : Prop :=
  ∃ fs : Aufzaehlung mD.Fn, Erfuellbar mP mSI (axWahr mD) fs [mHauptA, mHauptB]

/-- Probe B satisfies every premise group (EXPECTED FALSE on `zD`, see the header). -/
def probeB_erfuellbar : Prop :=
  ∃ (fs : Aufzaehlung zD.Fn) (ws : List zD.Fn), Erfuellbar zPB zS (axWahr zD) fs ws

/-- Probe C satisfies every premise group (EXPECTED FALSE on `zD`, see the header). -/
def probeC_erfuellbar : Prop :=
  ∃ (fs : Aufzaehlung zD.Fn) (ws : List zD.Fn), Erfuellbar zPC zS (axWahr zD) fs ws

/-- **Non-degeneracy of the positive witness** (PLAN §4 `gabbro_ziel_zeuge`, stated): on some
    admissible start of `mP` a reached machine has CHANGED memory, so the conclusion is not
    only about the start machine. -/
def zweiFaeden_bewegt : Prop :=
  ∃ (sp : Speicher mD) (init : Faden → Σ f : mD.Fn, Env mD (mD.params f))
    (fs : Aufzaehlung mD.Fn) (passes : Nat) (M : RufMaschineG mD),
    StartZulaessig mP mSI fs.1 [mHauptA, mHauptB] sp init ∧
    RufErreichbarG mP mO passes (RufStartG mP sp init) M ∧ M.speicher ≠ sp

end Gabbro.Grammatik.Zielsatz
