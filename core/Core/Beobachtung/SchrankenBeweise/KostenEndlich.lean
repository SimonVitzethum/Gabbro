/-
  File:      core/Core/Beobachtung/SchrankenBeweise/KostenEndlich.lean
  Subject:   THE FINITE-BOUND CORE STATEMENTS (M9, MK-12). The estimator of
              `KostenSchaetzer` bounds one invocation window: a call window runs from an
              entry cut (depth `d + 1` with the function name) to its matching exit cut
              (depth `d`), never below `d + 1` inside, and contains no crash; an entry
              segment runs from the loader start or from a restart cut to the next crash
              (or any later cut), crash-free. Restarts begin a new segment instead of
              extending the old count, so the k-restart accumulation that falsified the
              old prefix-from-zero claim (see `ohneFensterung_akkumuliert` in
              `KostenEndlichBeweise`) is out of scope by construction. Every statement
              quantifies over admitted runs (`Laeufe`: loader start, maximality), never
              over arbitrary `Lauf`.

              Three statements carry the finite bound, pinned for Hy4 under one
              collective root:

              * `KostenSchrittKorrespondenzAussage`: the source-to-machine link. Every
                context step of an admitted run executes the Befehl at its head, and
                that Befehl is one the estimator charged (`f ∈ (programm u.baum).code`,
                whose class rows the estimator sums in `fragmentKosten`); loop counters
                (`zaehler`/`obergrenzen`) stay within their source bounds; installed
                measures stay inside their static `decreases` interval. Proof sketch:
                heads come from the elaborated fragment (`Fragment.einheit` rules are
                exactly the code); the counter bounds follow the loop-entry commands
                (`setzePasszahl`, `forAnfang`) with the static trip bounds
                (`boundSchranke`, `forSchranke`) recorded on the test instruction;
                the measure bound follows the
                runtime descent check (`Rahmen.setzeMass`: a new measure is installed
                only strictly below the previous same-function mass, else the frame
                halts) with the `decreases` clause (`KlauselnWahr` over `I`, carried by
                acceptance). Difficulty: schwer.

              * `KostenSchaetzerKorrektAussage`: every invocation window and every entry
                segment of an accepted unit costs at most the estimator. Proof sketch:
                induction over the window from its start cut, using the correspondence:
                each step costs its context exactly one tick
                (`kontextkosten_schritt_gleich`); straight-line code is counted once;
                `whileBounded`/`forRange` bodies run at most their static trip bound by
                (ii); recursive re-entries descend strictly by (iv), so the interval width
                bounds the cycle activations; calls cost their verified table entry or
                their structural estimate. Protocol ticks are foreign to every context,
                so they add nothing to the window. Difficulty: mittel (given the
                correspondence).

              * `GebundenKHEndlichAussage`: the cost and hold duties of every accepted
                unit with a finite bound, stated window-relative: every cut of every
                invocation window and every cut of every entry segment meets the
                declared ceilings. Proved in `KostenEndlichBeweise` from the correctness
                statement with the checker's `E ≤ K` (case split on the declaration;
                the open leg is vacuous as in `bindungKHOffen`).

              The window predicates are inlined as `…Aussage` definitions covered by the
              root pin. The satisfiability witnesses below are run-free (checker outcomes
              and estimator values on tiny trees); the run-side joint premises are the
              prover's first step.
-/
module

public import Core.Beobachtung.SchrankenBeweise.KostenSchaetzer
public import Core.Beobachtung.Schranken

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine Annahme
open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik

/-- A crash cuts every window: no crash tick strictly inside `[a, b)`. After a crash
    the recovery entry starts a new window instead of extending the old count. -/
def FensterOhneAbsturzAussage (P : Katalog.Plattform) (u : UnitMitSchranken)
    (ρ : Lauf (einheitMitSchranken P u)) (a b : Nat) : Prop :=
  ∀ t, a ≤ t → t < b →
    ∀ spurv : SchrittSpur Zelle Int, ρ.zeit.spur t ≠ some (.absturz, spurv)

/-- One invocation window: from an entry cut (depth `d + 1` with the function name) to
    its matching exit cut (depth `d`), never below `d + 1` inside, with no crash in
    between. A crash ends the window; the recovery entry opens a new one. -/
def AufrufFensterAussage (P : Katalog.Plattform) (u : UnitMitSchranken)
    (ρ : Lauf (einheitMitSchranken P u)) (c : Kontext) (f : Identifier)
    (a b : Nat) : Prop :=
  ∃ d ta tb, ρ.zeit.zustand a = some ta ∧ ρ.zeit.zustand b = some tb ∧
    (ta.lokal c).funktion = some f ∧
    (ta.lokal c).fortsetzungen.length = d + 1 ∧
    (tb.lokal c).fortsetzungen.length = d ∧ a < b ∧
    (∀ t s, a < t → t < b → ρ.zeit.zustand t = some s →
      d + 1 ≤ (s.lokal c).fortsetzungen.length) ∧
    FensterOhneAbsturzAussage P u ρ a b

/-- One entry segment: from the loader start or from a restart cut, crash-free up to
    `b`. Every prefix of a crash-delimited segment is covered, so restarts never
    accumulate into the old count. -/
def EintrittSegmentAussage (P : Katalog.Plattform) (u : UnitMitSchranken)
    (ρ : Lauf (einheitMitSchranken P u)) (a b : Nat) : Prop :=
  a < b ∧ FensterOhneAbsturzAussage P u ρ a b ∧
    (a = 0 ∨ ∃ spurv : SchrittSpur Zelle Int,
      a > 0 ∧ ρ.zeit.spur (a - 1) = some (.absturz, spurv))

/-- **The source-to-machine correspondence** (`KostenSchrittKorrespondenzAussage`):
    for every accepted unit whose estimator is defined, every context step of every
    admitted run executes the Befehl at its head, and that Befehl is one the
    estimator charged; counters and range endpoints stay within the test site's
    static bounds; installed
    measures stay inside their static `decreases` interval. Open for Hy4; the sketch is
    in the file header. Difficulty: schwer. -/
def KostenSchrittKorrespondenzAussage : Prop :=
  ∀ (P : Katalog.Plattform) (u : UnitMitSchranken) (tab : KostenTabelle)
    (z : Wirkungsklasse → KlassenKostenzeile) (E : Nat),
    EndlichAkzeptiertAussage P u tab z →
    schaetzeEinheit z tab u.baum = some E →
    ∀ {h : Umgebung} {ρ : Lauf (einheitMitSchranken P u)},
      Laeufe (einheitMitSchranken P u) h ρ →
      (∀ t (c : Kontext) (w : PUnit) (spurv : SchrittSpur Zelle Int) vor
        (f : Befehl),
        ρ.zeit.spur t = some (.kontext c w, spurv) →
        ρ.zeit.zustand t = some vor →
        (einheitMitSchranken P u).system.kopf vor c = some f →
        f ∈ (programm u.baum).code) ∧
      (∀ t s (c : Kontext) (pc n : Nat),
        ρ.zeit.zustand t = some s →
        (s.lokal c).zaehler pc = some n →
        ∃ grenze, (pc, grenze) ∈ (programm u.baum).schleifen ∧ n ≤ grenze.paesse) ∧
      (∀ t s (c : Kontext) (pc : Nat) (b : Ganzzahl),
        ρ.zeit.zustand t = some s →
        (s.lokal c).obergrenzen pc = some b →
        ∃ grenze hi, (pc, grenze) ∈ (programm u.baum).schleifen ∧
          grenze.oben = some hi ∧ b.zahl.wert ≤ hi) ∧
      ∀ t s (c : Kontext) (name : Identifier) (n : Nat) (lo hi : Int)
        (kern : FunktionsKern),
        ρ.zeit.zustand t = some s →
        (s.lokal c).funktion = some name → (s.lokal c).mass = some n →
        findeKern u.baum.2 name = some kern → kern.massIntervall = some (lo, hi) →
        lo ≤ (n : Int) ∧ (n : Int) ≤ hi

/-- **Correctness of the structural estimator** (`KostenSchaetzerKorrektAussage`):
    for every accepted unit whose estimator is defined, each invocation window of
    every admitted run costs at most the estimator in the acting context's own
    ticks, and so does every entry segment. Open for Hy4; the sketch is in the file
    header. Difficulty: mittel (given the correspondence). -/
def KostenSchaetzerKorrektAussage : Prop :=
  ∀ (P : Katalog.Plattform) (u : UnitMitSchranken) (tab : KostenTabelle)
    (z : Wirkungsklasse → KlassenKostenzeile) (E : Nat),
    EndlichAkzeptiertAussage P u tab z →
    schaetzeEinheit z tab u.baum = some E →
    ∀ {h : Umgebung} {ρ : Lauf (einheitMitSchranken P u)},
      Laeufe (einheitMitSchranken P u) h ρ →
      (∀ (c : Kontext) (f : Identifier) (a b : Nat),
        AufrufFensterAussage P u ρ c f a b →
        Kontextkosten ρ c a (b - a) ≤ E) ∧
      ∀ (a b : Nat),
        EintrittSegmentAussage P u ρ a b →
        Kontextkosten ρ eintritt a (b - a) ≤ E

/-- **The cost and hold duties of every accepted bound unit with a finite
    bound** (`GebundenKHEndlichAussage`): window-relative, over every cut of every
    invocation window and every cut of every entry segment of every admitted run.
    Proved in `KostenEndlichBeweise` from the correctness statement with the
    checker's `E ≤ K` (case split on the declaration, vacuous hold legs). -/
def GebundenKHEndlichAussage : Prop :=
  ∀ (P : Katalog.Plattform) (u : UnitMitSchranken) (tab : KostenTabelle)
    (z : Wirkungsklasse → KlassenKostenzeile),
    EndlichAkzeptiertAussage P u tab z →
    ∀ {h : Umgebung} {ρ : Lauf (einheitMitSchranken P u)},
      Laeufe (einheitMitSchranken P u) h ρ →
      (∀ (c : Kontext) (f : Identifier) (a b : Nat),
        AufrufFensterAussage P u ρ c f a b →
        ∀ t, a ≤ t → t ≤ b →
          UnterGrenze (einheitMitSchranken P u).schranken.kosten
            (Kontextkosten ρ c a (t - a)) ∧
          ∀ (l : Nat) (a' n : Nat), a ≤ a' → a' + n ≤ t →
            (∀ t', a' ≤ t' → t' < a' + n →
              ∃ s, ρ.zeit.zustand t' = some s ∧
                (s.sperren l).besitzer = some c) →
            UnterGrenze ((einheitMitSchranken P u).schranken.halten l)
              (Kontextkosten ρ c a' n)) ∧
      ∀ (a b : Nat),
        EintrittSegmentAussage P u ρ a b →
        ∀ t, a ≤ t → t ≤ b →
          UnterGrenze (einheitMitSchranken P u).schranken.kosten
            (Kontextkosten ρ eintritt a (t - a)) ∧
          ∀ (l : Nat) (a' n : Nat), a ≤ a' → a' + n ≤ t →
            (∀ t', a' ≤ t' → t' < a' + n →
              ∃ s, ρ.zeit.zustand t' = some s ∧
                (s.sperren l).besitzer = some eintritt) →
            UnterGrenze ((einheitMitSchranken P u).schranken.halten l)
              (Kontextkosten ρ eintritt a' n)

/-- The collective root of the finite-bound core: step correspondence, estimator
    correctness and the finite KH duties close together. -/
def KostenEndlichWurzelAussage : Prop :=
  KostenSchrittKorrespondenzAussage ∧ KostenSchaetzerKorrektAussage ∧
    GebundenKHEndlichAussage

/-- Joint satisfiability for the estimator correctness: the open declaration passes
    the endliche line and the estimator is defined on a unit with a `main`. No run
    is constructed. -/
theorem kostenSchaetzer_erfuellbar :
    ∃ (P : Katalog.Plattform) (u : UnitMitSchranken) (tab : KostenTabelle)
      (z : Wirkungsklasse → KlassenKostenzeile) (E : Nat),
      pruefeSchrankenEndlich u tab z = true ∧
        schaetzeEinheit z tab u.baum = some E := by
  refine ⟨Katalog.Plattform.x86_64, ⟨engerBaum, Schrankendeklaration.leer⟩, [],
    Wirkungsklasse.kostenZeile, _, rfl, rfl⟩

/-- Joint satisfiability for the step correspondence: the same static bundle (open
    declaration, defined estimator) carries the correspondence premises. No run is
    constructed. -/
theorem kostenKorrespondenz_erfuellbar :
    ∃ (P : Katalog.Plattform) (u : UnitMitSchranken) (tab : KostenTabelle)
      (z : Wirkungsklasse → KlassenKostenzeile) (E : Nat),
      pruefeSchrankenEndlich u tab z = true ∧
        schaetzeEinheit z tab u.baum = some E := by
  refine ⟨Katalog.Plattform.x86_64, ⟨engerBaum, Schrankendeklaration.leer⟩, [],
    Wirkungsklasse.kostenZeile, _, rfl, rfl⟩

/-- Sharpness for the estimator correctness: some unit has no estimator value, some
    declaration is refused by the endliche line, and without windowing the bound is
    false in general — two full windows already break any positive bound (the
    k-restart accumulation; see `ohneFensterung_akkumuliert`). The bound is claimed
    only where it is defined, and only per window. -/
theorem kostenSchaetzer_nichtTrivial :
    (∃ (u : Ast.Unit) (tab : KostenTabelle)
      (z : Wirkungsklasse → KlassenKostenzeile),
      schaetzeEinheit z tab u = none) ∧
    (∃ (P : Katalog.Plattform) (u : UnitMitSchranken) (tab : KostenTabelle)
      (z : Wirkungsklasse → KlassenKostenzeile),
      pruefeSchrankenEndlich u tab z = false) ∧
    ∀ Ebound : Nat, 0 < Ebound → ¬ 2 * Ebound ≤ Ebound := by
  refine ⟨⟨endlosBaum, [], Wirkungsklasse.kostenZeile, rfl⟩,
    ⟨Katalog.Plattform.x86_64, ⟨engerBaum, engeDeklaration⟩, [],
      Wirkungsklasse.kostenZeile, rfl⟩, ?_⟩
  intro Ebound hE h
  have h2 : Ebound + Ebound ≤ Ebound + 0 := by
    simpa only [two_mul, Nat.add_zero] using h
  have hle : Ebound ≤ 0 := Nat.le_of_add_le_add_left h2
  have h0 : Ebound = 0 := Nat.le_zero.mp hle
  rw [h0] at hE
  exact Nat.lt_irrefl 0 hE

/-- Sharpness for the step correspondence: some unit has no estimator value, and
    some declaration is refused by the endliche line. The correspondence is claimed
    only where the estimator is defined. -/
theorem kostenKorrespondenz_nichtTrivial :
    (∃ (u : Ast.Unit) (tab : KostenTabelle)
      (z : Wirkungsklasse → KlassenKostenzeile),
      schaetzeEinheit z tab u = none) ∧
    ∃ (P : Katalog.Plattform) (u : UnitMitSchranken) (tab : KostenTabelle)
      (z : Wirkungsklasse → KlassenKostenzeile),
      pruefeSchrankenEndlich u tab z = false := by
  refine ⟨⟨endlosBaum, [], Wirkungsklasse.kostenZeile, rfl⟩,
    ⟨Katalog.Plattform.x86_64, ⟨engerBaum, engeDeklaration⟩, [],
      Wirkungsklasse.kostenZeile, rfl⟩⟩

/-- Joint satisfiability for the finite KH duties: the open declaration passes
    the endliche line. -/
theorem gebundenKHEndlich_erfuellbar :
    ∃ (P : Katalog.Plattform) (u : UnitMitSchranken) (tab : KostenTabelle)
      (z : Wirkungsklasse → KlassenKostenzeile),
      pruefeSchrankenEndlich u tab z = true := by
  refine ⟨Katalog.Plattform.x86_64, ⟨engerBaum, Schrankendeklaration.leer⟩, [],
    Wirkungsklasse.kostenZeile, rfl⟩

/-- Sharpness for the finite KH duties: the endliche line refuses a too-tight
    finite ceiling. -/
theorem gebundenKHEndlich_nichtTrivial :
    ∃ (P : Katalog.Plattform) (u : UnitMitSchranken) (tab : KostenTabelle)
      (z : Wirkungsklasse → KlassenKostenzeile),
      pruefeSchrankenEndlich u tab z = false := by
  refine ⟨Katalog.Plattform.x86_64, ⟨engerBaum, engeDeklaration⟩, [],
    Wirkungsklasse.kostenZeile, rfl⟩

end Gabbro.Core.Beobachtung
