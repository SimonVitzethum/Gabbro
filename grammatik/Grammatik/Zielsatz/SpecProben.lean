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
    (stated for EVERY program, so for every sound `Pruefer` the Bool is `false`);
  * NEW (race fix, 2026-09-14): an unguarded carrier, neither `atomic` nor a payload, that two
    declared starts WRITE -- even if nothing reads it                -> (a) `AkzeptiertSpec`
    (`zwei_schreiber_abgelehnt`, proved below; the decided instance with no read anywhere is
    `ak3_zwei_schreiber_ohne_lesen`, AkzeptiertZeuge.lean, which the old Bool accepted).
  The refutations of (b) are stated for every lock-invariant family whose protected carriers
  are guarded and which SOME memory satisfies: a family no memory satisfies empties the class
  `HavocOk` and hence `NutzerPflicht` -- but then no start is admissible (`sperren`), so the
  whole statement is empty for it; that is review question 3, not a refutation.

  Positives -- all premises jointly, with an admissible start OF `P.mitRuhe` (A4, the machine
  `GabbroZiel` runs) on which every declared start runs on some thread:
  * the two-thread program `mP` (two ACTIVE threads, private unguarded tables, a shared
    table under a lock with invariant `konto[0] == konto[1]`, the runtime's root elsewhere);
  * probes B/C (`zPB`, `zPC`, family `zS`). Before the idle root they were EXPECTED FALSE:
    `zD` has no idle function, and `Faden = Nat` runs infinitely many threads. With the
    runtime's root the start component holds; the statements fix `haupt` as the DECLARED
    start (`ws = [haupt]`, running on some thread), so the admissible start is not the root on
    every thread, where the probe bodies would never run.
-/
import Grammatik.Zielsatz.Spec
import Grammatik.ProbeD
import Grammatik.InvZeuge
import Grammatik.MehrfadenZeuge

namespace Gabbro.Grammatik.Zielsatz

open Gabbro.Grammatik

instance zD_fn_deq' : DecidableEq zD.Fn := inferInstanceAs (DecidableEq ZFn)

/-- **All premise groups at once**: the checker's facts, the user's logic, SOME oracle meeting
    the hardware assumptions, and SOME admissible start on which EVERY declared start of `ws`
    runs on some thread (without that clause the runtime's root on every thread would be
    admissible for any `ws`, and the declared bodies would never run). -/
def Erfuellbar {D : Deklaration} [DecidableEq D.Fn] (P : Programm D) (S : SperrInv D)
    (Q : AxEns D) (fs : Aufzaehlung D.Fn) (ws : List D.Fn) : Prop :=
  AkzeptiertSpec P S fs.1 ws ∧ NutzerPflicht P S Q ∧ (∃ O : Orakel D, HardwareAnnahmen O Q) ∧
    ∃ (sp : Speicher D.mitRuhe)
      (init : Faden → Σ f : D.mitRuhe.Fn, Env D.mitRuhe (D.mitRuhe.params f)),
      StartZulaessig P.mitRuhe S.mitRuhe (fsRuhe fs.1) (wsRuhe ws) sp init ∧
        ∀ w ∈ wsRuhe ws, ∃ t : Faden, (init t).1 = w

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

/-- **Two declared starts writing one unguarded carrier fail (a)**, for every program --
    whether or not anything reads the carrier (the race fix of 2026-09-14). -/
def zwei_schreiber_abgelehnt : Prop :=
  ∀ (D : Deklaration) [DecidableEq D.Fn] (P : Programm D) (S : SperrInv D) (fs ws : List D.Fn)
    (w₁ w₂ : D.Fn) (c : D.Tab ⊕ D.Glob),
    w₁ ∈ ws → w₂ ∈ ws → w₁ ≠ w₂ → TraegerSchreibt w₁ c = true → TraegerSchreibt w₂ c = true →
    (∀ L, ¬ Bewacht c L) → ¬ AtomarAusgenommen c → ¬ PaarungAusgenommen c →
    ¬ AkzeptiertSpec P S fs ws

theorem zwei_schreiber_abgelehnt_gilt : zwei_schreiber_abgelehnt := by
  intro D _ P S fs ws w₁ w₂ c h₁ h₂ hne hw₁ hw₂ hB hA hP hS
  have := (hS.renn c hB hA hP w₁ h₁ w₂ h₂ hne w₁ (reachB_wurzel P fs w₁) hw₁ w₂
    (reachB_wurzel P fs w₂)).1
  rw [hw₂] at this
  cases this

/-- **The two-thread program satisfies every premise group**, with its declared starts
    `hauptA`, `hauptB`, the family `mSI` and the trivial axiom ensures. -/
def zweiFaeden_erfuellbar : Prop :=
  ∃ fs : Aufzaehlung mD.Fn, Erfuellbar mP mSI (axWahr mD) fs [mHauptA, mHauptB]

/-- Probe B satisfies every premise group with `haupt` as its DECLARED start, running on some
    thread (the runtime's root on the others). -/
def probeB_erfuellbar : Prop :=
  ∃ fs : Aufzaehlung zD.Fn, Erfuellbar zPB zS (axWahr zD) fs [zHaupt]

/-- Probe C satisfies every premise group with `haupt` as its DECLARED start, running on some
    thread (the runtime's root on the others). -/
def probeC_erfuellbar : Prop :=
  ∃ fs : Aufzaehlung zD.Fn, Erfuellbar zPC zS (axWahr zD) fs [zHaupt]

/-- **Non-degeneracy of the positive witness** (PLAN §4 `gabbro_ziel_zeuge`, stated): on some
    admissible start of `mP` a reached machine has CHANGED memory, so the conclusion is not
    only about the start machine. -/
def zweiFaeden_bewegt : Prop :=
  ∃ (sp : Speicher mD.mitRuhe)
    (init : Faden → Σ f : mD.mitRuhe.Fn, Env mD.mitRuhe (mD.mitRuhe.params f))
    (fs : Aufzaehlung mD.Fn) (passes : Nat) (M : RufMaschineG mD.mitRuhe),
    StartZulaessig mP.mitRuhe mSI.mitRuhe (fsRuhe fs.1) (wsRuhe [mHauptA, mHauptB]) sp init ∧
    RufErreichbarG mP.mitRuhe mO.mitRuhe passes (RufStartG mP.mitRuhe sp init) M ∧
    M.speicher ≠ sp

end Gabbro.Grammatik.Zielsatz
