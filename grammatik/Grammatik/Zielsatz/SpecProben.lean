/-
  File:    Grammatik/Zielsatz/SpecProben.lean -- the anti-vacuity obligations of
           PLAN-ZIELSATZ.md §4, STATED (as `def … : Prop`), not proved.
  Purpose: the reviewer sees next to `GabbroZiel` (Spec.lean) what must be false and what
           must be true of its premises. `Proben.lean` proves them.

  Since 2026-09-15 the premises speak about ONE program `E : Einheit D` (code, lock
  invariants, axiom ensures, declared starts, declared initial memory), so every probe is a
  statement about programs `E`, not about a code `P` with freely chosen `S`, `Q`, `ws`.

  Refutations -- each must FAIL a premise group:
  * probe A (`paP`, `ensures false`, `traverse … invariant false`)  -> (b) `NutzerPflicht`,
    for EVERY program with that code: no side condition on the lock invariants any more;
  * probe A with an unsatisfiable lock invariant (`sFalsch`, `invariant false`; verdict P1)
                                                                   -> (b), by the start
    obligation `StartPflicht.sperren` (the checker's Bool ACCEPTS it, `p1_akzeptiert`);
  * probe D (`fvP false`, `forever … invariant false { leave }`)   -> (b), at some budget;
  * probe F1 (`f1P`: probe A's contracts, a float literal outside its range in front of every
    body; verdict F1 of URTEIL-OPUS-2026-09-15b)                   -> (b), since the
    out-of-range float is `logik bereich` (it was `hardware ieee`; the checker ACCEPTS the
    program, `f1_akzeptiert`, so the refusal is (b)'s);
  * a table-invariant breaker (`ivPschlecht`)                      -> (b);
  * an unguarded carrier one start reads and another writes        -> (a) `AkzeptiertSpec`
    (stated for EVERY program, so for every sound `Pruefer` the Bool is `false`);
  * two declared starts WRITING one unguarded, non-atomic carrier -- a publish payload
    included since 2026-09-15 (verdict P3) -- even if nothing reads it -> (a).
  The refutations of (b) hold for EVERY program with the given code: `NutzerPflicht` itself
  carries a memory meeting every lock invariant (`StartPflicht.sperren` at `E.sp0`) and
  their locality (`SperrInvLokal`), so the class `HavocOk` is inhabited
  (`havocOk_misch_lokal`). Before 2026-09-15 the refutations needed "some memory satisfies
  the family" as a side condition, and a family no memory satisfies emptied both (b) and
  the conclusion (verdict P1).

  Positives -- all premise groups jointly, with a runtime start (d) of the program on which
  every declared start runs on some thread:
  * the two-thread program `mE` (two ACTIVE threads, private unguarded tables, a shared
    table under a lock with invariant `konto[0] == konto[1]`, the runtime's root elsewhere);
  * probes B/C (`zEB`, `zEC`, family `zS`, declared start `haupt`).
-/
import Grammatik.Zielsatz.Spec
import Grammatik.ProbeD
import Grammatik.InvZeuge
import Grammatik.MehrfadenZeuge

namespace Gabbro.Grammatik.Zielsatz

open Gabbro.Grammatik

instance zD_fn_deq' : DecidableEq zD.Fn := inferInstanceAs (DecidableEq ZFn)

/-- **All premise groups at once**: the checker's facts, the user's logic, SOME oracle meeting
    the hardware assumptions, and SOME runtime start (A4) on which EVERY declared start runs
    on some thread (without that clause a start running only the root would do, and the
    declared bodies would never run). -/
def Erfuellbar {D : Deklaration} [DecidableEq D.Fn] (E : Einheit D) (fs : Aufzaehlung D.Fn) :
    Prop :=
  AkzeptiertSpec E.P E.S fs.1 E.ws ∧ NutzerPflicht E ∧ (∃ O : Orakel D, HardwareAnnahmen O E.Q) ∧
    ∃ (sp : Speicher D.mitRuhe)
      (init : Faden → Σ f : D.mitRuhe.Fn, Env D.mitRuhe (D.mitRuhe.params f)),
      Laufzeit E sp init ∧ ∀ w ∈ E.ws, ∃ t : Faden, (init t).1 = some w

/-- **Group (b) refutes the code `P`**: no program with this code meets the user obligation
    -- whatever its lock invariants, axiom ensures, starts and initial memory. -/
def NutzerWiderlegt {D : Deklaration} (P : Programm D) : Prop :=
  ∀ E : Einheit D, E.P = P → ¬ NutzerPflicht E

/-- Probe A fails (b). -/
def probeA_widerlegt : Prop := NutzerWiderlegt paP

/-- The unsatisfiable lock-invariant family of verdict P1 (`invariant false` on the one lock
    of `zD`, protecting nothing). -/
def sFalsch : SperrInv zD := ⟨fun _ => [], fun _ _ => false⟩

/-- **Probe A with `invariant false` fails (b)** (verdict P1): before 2026-09-15 this program
    met every premise group and every start was inadmissible, so the statement was empty. -/
def probeA_falsch_inv : Prop :=
  ∀ (Q : AxEns zD) (starts : List (Σ w : zD.Fn, Env zD (zD.params w))) (sp0 : Speicher zD),
    ¬ NutzerPflicht ⟨paP, sFalsch, Q, starts, sp0⟩

/-- Verdict F1's crash (URTEIL-OPUS-2026-09-15b): `if true { let x = 2.0 in 0 .. 1; }` -- a
    float literal outside its declared range. The kernel IEEE model decides it, for every
    oracle. -/
def f1Crash {V : Vertrag zD} {Γ : Ctx} {Λ : List (Res zD)} : Stmt zD V false Γ Λ Λ :=
  .ite .wahr (.gleitLit (2, 1) (0, 1) (1, 1) .nil) .nil

/-- **Probe F1**: probe A's contracts (`ensures false` everywhere) with the crash in front of
    every body. Until 2026-09-15 the crash ended the body in `hardware ieee` -- a "hardware"
    stop no clause of (b) constrained -- so this program met (b), passed the checker with
    `haupt` declared and running, and `gabbro_ziel` certified it. -/
def f1P : Programm zD where
  invariante := fun i => nomatch i
  requires := fun _ => .wahr
  ensures := fun _ => .falsch
  rumpf f := .cons f1Crash (paP.rumpf f)

/-- **Probe F1 fails (b)** (verdict F1, 2026-09-15): an out-of-range float is `logik bereich`,
    which the body obligation excludes -- for every program with this code. -/
def probeF1_widerlegt : Prop := NutzerWiderlegt f1P

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
    whether or not anything reads the carrier (the race fix of 2026-09-14), and whether or
    not it is a publish payload (verdict P3, 2026-09-15). Only `atomic` globals are exempt. -/
def zwei_schreiber_abgelehnt : Prop :=
  ∀ (D : Deklaration) [DecidableEq D.Fn] (P : Programm D) (S : SperrInv D) (fs ws : List D.Fn)
    (w₁ w₂ : D.Fn) (c : D.Tab ⊕ D.Glob),
    w₁ ∈ ws → w₂ ∈ ws → w₁ ≠ w₂ → TraegerSchreibt w₁ c = true → TraegerSchreibt w₂ c = true →
    (∀ L, ¬ Bewacht c L) → ¬ AtomarAusgenommen c → ¬ AkzeptiertSpec P S fs ws

theorem zwei_schreiber_abgelehnt_gilt : zwei_schreiber_abgelehnt := by
  intro D _ P S fs ws w₁ w₂ c h₁ h₂ hne hw₁ hw₂ hB hA hS
  have := (hS.renn c hB hA w₁ h₁ w₂ h₂ hne w₁ (reachB_wurzel P fs w₁) hw₁ w₂
    (reachB_wurzel P fs w₂)).1
  rw [hw₂] at this
  cases this

/-- The two-thread program as ONE declaration: code `mP`, family `mSI`, trivial axiom
    ensures, declared starts `hauptA`, `hauptB` (no parameters), initial memory `mSp`. -/
def mE : Einheit mD := ⟨mP, mSI, axWahr mD, [⟨mHauptA, .nil⟩, ⟨mHauptB, .nil⟩], mSp⟩

/-- Probe B as ONE declaration: declared start `haupt`, initial memory `zSp`. -/
def zEB : Einheit zD := ⟨zPB, zS, axWahr zD, [⟨zHaupt, .nil⟩], zSp⟩

/-- Probe C as ONE declaration. -/
def zEC : Einheit zD := ⟨zPC, zS, axWahr zD, [⟨zHaupt, .nil⟩], zSp⟩

/-- **The two-thread program satisfies every premise group.** -/
def zweiFaeden_erfuellbar : Prop := ∃ fs : Aufzaehlung mD.Fn, Erfuellbar mE fs

/-- Probe B satisfies every premise group with `haupt` running on some thread. -/
def probeB_erfuellbar : Prop := ∃ fs : Aufzaehlung zD.Fn, Erfuellbar zEB fs

/-- Probe C satisfies every premise group with `haupt` running on some thread. -/
def probeC_erfuellbar : Prop := ∃ fs : Aufzaehlung zD.Fn, Erfuellbar zEC fs

/-- **Non-degeneracy of the positive witness** (PLAN §4 `gabbro_ziel_zeuge`, stated): on some
    runtime start of `mE` a reached machine has CHANGED memory, so the conclusion is not only
    about the start machine. -/
def zweiFaeden_bewegt : Prop :=
  ∃ (sp : Speicher mD.mitRuhe)
    (init : Faden → Σ f : mD.mitRuhe.Fn, Env mD.mitRuhe (mD.mitRuhe.params f))
    (passes : Nat) (M : RufMaschineG mD.mitRuhe),
    Laufzeit mE sp init ∧
    RufErreichbarG mE.P.mitRuhe mO.mitRuhe passes (RufStartG mE.P.mitRuhe sp init) M ∧
    M.speicher ≠ sp

end Gabbro.Grammatik.Zielsatz
