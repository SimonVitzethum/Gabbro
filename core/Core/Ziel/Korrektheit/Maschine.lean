/-
  File:      core/Core/Ziel/Korrektheit/Maschine.lean
  Subject:   CORRECTNESS OF THE IMPLEMENTATION MACHINE AND OF THE IDEAL MACHINE `I` (M4): one shared preservation
             theorem for the invariants of the protocol state, determinacy up to the declared choice points, and
             `I` for every elaborated unit, as pinned propositions.

  A form updates only the fields `Zustandsrahmen` leaves to it (local data, statuses, authority, leases, the
  booking); the machine owns every other field, and both machines run the SAME protocol steps (`FuehrtSchrittAus`,
  `AntwortSchritt`, `UnterbrechungsSchritt`, `AbsturzSchritt`). The invariants of the machine are therefore the
  invariants of the protocol-owned fields, and they are preserved once, at the level of the protocol steps, for
  both machines:
  * `speicher`  the memory graph is consistent and complete (`impl_speicher_gut`, `ideal_speicher_gut`);
  * `verbrauch` a context consumes only answers that arrived (`ImplSchritt.verbrauch`);
  * `sperren`   every lock queue is duplicate free and its owner is not queued (the ticket rule guards both,
                `nehmen` and `geben` keep them, a crash frees every lock).
  Invariants of the form-owned fields (a status discipline, authority) are NOT machine invariants — a form may
  change them — and are the checker's obligations (`Lokal`); the statement below does not claim them.

  A statement that a run preserves "all invariants" that names no list would hold for any list; the list is the
  structure `ProtokollGut`, so a missing or a false conjunct makes the statement unprovable instead of vacuous.
-/
module

public import Core.Ziel.Korrektheit.Pruefer
public import Core.Ast.Semantik.Pflichten
public import Core.Ast.Semantik.Runtime.Atom.Rein
public import Core.Verfeinerung.Formen.Familie
public import Core.Maschine.Schritte
public import Core.Ideal.Komposition
public import Core.Verfeinerung.Sicherheit

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit

open Gabbro.Core Maschine

/-- The invariants of the protocol-owned part of a state (see the file header). -/
structure ProtokollGut {L Ort Wert Raum Lok Grund : Type}
    (z : Maschine.Zustand L Ort Wert Raum Lok Grund) : Prop where
  speicher : z.SpeicherGut
  verbrauch : z.Verbrauch
  sperren : ∀ l, (z.sperren l).schlange.Nodup ∧
    ∀ c, (z.sperren l).besitzer = some c → c ∉ (z.sperren l).schlange

/-- THE PROTOCOL INVARIANTS ARE PRESERVED BY EVERY STEP OF BOTH MACHINES, for every unit: an implementation step
and an ideal step each keep `ProtokollGut`. Feeds: `impl_speicher_gut`, `ideal_speicher_gut`,
`ImplSchritt.verbrauch`, `kontextSchritt_sperren`, `antwortSchritt_sperren`, `interruptSchritt_sperren`,
`nimmt_inv`, `abgeben_nodup`, `absturz_leert_schlange`. Proof sketch: split the step into its four protocol cases
(context step, arrival, interrupt delivery, crash), which both machines share; in the context case use
`Zustandsrahmen` (the form keeps lock, graph and answer fields) and the three lock rules. Open: the lock
invariant over `SperrSchritt` and the lift to `I.Schritt` (Prover). Non-trivial: `sperr_schritt_erfuellbar`
shows each lock rule fires; a rule without the ticket guard (`keinTicket`) would break the invariant, so a
weaker ticket rule makes this statement unprovable. -/
def ProtokollSchrittErhaeltAussage : Prop :=
  ∀ (L Ort Wert Raum Lok Grund Bedingung Wahl ι : Type) [DecidableEq L]
    (e : Einrichtung L Ort Wert Raum Lok Grund Bedingung)
    (Sy : MaschinenSystem L Ort Wert Raum Lok Grund Bedingung Wahl ι)
    (k : Katalog.Katalog) (hw : Katalog.HwLauf) (t : Nat)
    (s s' : Maschine.Zustand L Ort Wert Raum Lok Grund) (spur : SchrittWahl Wahl × SchrittSpur Ort Wert),
    ProtokollGut s →
      (ImplSchritt e Sy k hw t s spur s' → ProtokollGut s') ∧
      (I.Schritt e Sy k hw t s spur s' → ProtokollGut s')

/-- THE LOADED START SATISFIES THE INVARIANTS for every elaborated unit, at every admissible start. Feeds:
`Zustand.start_gut`, the elaborated loader `Ast.Semantik.laden` (it builds the state with `Zustand.start`).
Proof sketch: unfold the loader; the start state has free locks and an empty graph. -/
def ProtokollStartGutAussage : Prop :=
  ∀ (P : Katalog.Plattform) (t : Ast.Unit) (H : Katalog.Umgebung) (s : Katalog.AussenStart)
    (z : Maschine.Zustand Nat Ast.Semantik.Zelle Int Nat Ast.Semantik.Rahmen PUnit),
    (einheitVon P t).laden s (H.lade (einheitVon P t).bild) = some z → ProtokollGut z

/-- THE INVARIANTS HOLD AT EVERY CUT OF EVERY RUN of an elaborated unit, in both machines: implementation runs
and ideal runs. This is the single preservation theorem of the machine layer; every other state-level guarantee
(`SpeicherGut`, consumption, lock discipline) is a conjunct of `ProtokollGut`. Feeds:
`ProtokollSchrittErhaeltAussage`, `ProtokollStartGutAussage`, `speicher_gut_im_lauf`. Proof sketch: induction over
the hardware ticks of `Zeitlauf`, as in `speicher_gut_im_lauf`; a pause keeps the state. -/
def ProtokollGutImLaufAussage : Prop :=
  ∀ (P : Katalog.Plattform) (t : Ast.Unit) (H : Katalog.Umgebung)
    (ρ : Maschine.Lauf (einheitVon P t)),
      Maschine.Laeufe (einheitVon P t) H ρ →
      ∀ n z, ρ.zeit.zustand n = some z → ProtokollGut z

/-- THE IDEAL RUNS KEEP THE INVARIANTS TOO (the same list, the same protocol steps). -/
def IdealProtokollGutImLaufAussage : Prop :=
  ∀ (P : Katalog.Plattform) (t : Ast.Unit) (η : Maschine.I.Lauf (einheitVon P t)),
    Maschine.I.Laeufe (einheitVon P t) η → ∀ n, ProtokollGut (η.zeit.zustand n)

/-- THE IMPLEMENTATION MACHINE IS DETERMINATE UP TO ITS DECLARED CHOICE POINTS: given the source choice, the
recorded outside answers and the resolution of the memory order, an implementation step has one effect and one
successor, provided the instruction rules themselves are determinate (the premise is the implementation twin of
`RegelBestimmt`, one line per rule, discharged by the form). It is the twin of `I.Bestimmt`; a rule that adds
hidden nondeterminism makes the premise false, not the conclusion trivial. Feeds: `FuehrtSchrittAus.bestimmt`,
`AntwortSchritt.bestimmt`, `UnterbrechungsSchritt.bestimmt`, `Speicherfolge.bestimmt`, `bestimmt_aus_regeln`. -/
def ImplBestimmtAussage : Prop :=
  ∀ (L Ort Wert Raum Lok Grund Bedingung Wahl ι : Type) [DecidableEq L]
    (e : Einrichtung L Ort Wert Raum Lok Grund Bedingung)
    (Sy : MaschinenSystem L Ort Wert Raum Lok Grund Bedingung Wahl ι),
    (∀ i c s w plans plans' u u', (Sy.regel i).impl c s w plans u → (Sy.regel i).impl c s w plans' u' →
      plans = plans' ∧ u = u') →
    ∀ (k : Katalog.Katalog) (hw : Katalog.HwLauf) (t : Nat)
      (s : Maschine.Zustand L Ort Wert Raum Lok Grund) (w : SchrittWahl Wahl)
      (es es' : SchrittSpur Ort Wert) (s' s'' : Maschine.Zustand L Ort Wert Raum Lok Grund),
      ImplSchritt e Sy k hw t s (w, es) s' → ImplSchritt e Sy k hw t s (w, es') s'' →
      SpeicherWahlGleich s'.graph s''.graph → es = es' ∧ s' = s''

/-- `I` IS DETERMINATE AND MAKES PROGRESS FOR EVERY ELABORATED UNIT — the eighth conjunct of `NichtLeer`, and the
statement that `I` is defined for every unit of the current instruction set: every instruction has one plan and
one successor, every non-final state has a step. This holds for every source tree, accepted or not, because it is
a property of the instruction rules. Proved from the per-instruction lemmas. -/
def IdealAkzeptierteEinheitAussage : Prop :=
  ∀ (P : Katalog.Plattform) (t : Ast.Unit),
    Maschine.I.Bestimmt (einheitVon P t).einrichtung (einheitVon P t).system ∧
    Maschine.I.Fortschritt (einheitVon P t).einrichtung (einheitVon P t).system

theorem ideal_akzeptierte_einheit : IdealAkzeptierteEinheitAussage := by
  intro P t
  have rein := Ast.Semantik.fragment_rein Ast.Category.unit t
  exact ⟨Maschine.I.bestimmt_aus_kopfregeln _ _ (fun i s c hk =>
      Ast.Semantik.Befehl.bestimmt i
        (rein i (Ast.Semantik.kopf_mem (code := (Ast.Semantik.fragment Ast.Category.unit t).code) hk))),
    Maschine.I.fortschritt_aus_regeln _ _
      (Ast.Semantik.Fragment.fertig (Ast.Semantik.fragment Ast.Category.unit t) P)
      (fun b => Ast.Semantik.Befehl.regelFortschritt (Ast.Semantik.fragment Ast.Category.unit t) P b)
      (fun i => by
        by_cases h : i.Privat
        · exact Ast.Semantik.Befehl.komponierbar (Ast.Semantik.fragment Ast.Category.unit t) P i h
        · intro t' s c w plans u hk _ _
          exact absurd (rein i (Ast.Semantik.kopf_mem
            (code := (Ast.Semantik.fragment Ast.Category.unit t).code) hk)) h)⟩

end Gabbro.Core.Ziel.Korrektheit
