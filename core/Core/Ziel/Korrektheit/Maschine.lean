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
public import Core.Ziel.Korrektheit.Zugriff
public import Core.Ast.Semantik.Runtime.Mehrkontext.System
public import Core.Verfeinerung.Formen.Familie
public import Core.Maschine.Schritte
public import Core.Katalog.Erfuellbar
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

/-- The statement for a unit whose fragment is frame-only. -/
theorem ideal_akzeptierte_einheit_rein (P : Katalog.Plattform) (t : Ast.Unit)
    (rein : (Ast.Semantik.fragment Ast.Category.unit t).Rein) :
    Maschine.I.Bestimmt (einheitVon P t).einrichtung (einheitVon P t).system ∧
    Maschine.I.Fortschritt (einheitVon P t).einrichtung (einheitVon P t).system := by
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


/-- The frame-only case of the fragment-level theorem, lifted from the form-level obligations. Determinacy is
    `system_bestimmt` and progress is `system_fortschritt` of the fragment's code (both discharged by `p.Rein`),
    composed with the machine frame; `Fragment.fertig` is the no-head-is-finished obligation that both use. -/
theorem ideal_fragment_einheit_rein (p : Ast.Semantik.Fragment) (platform : Katalog.Plattform)
    (rein : p.Rein) :
    Maschine.I.Bestimmt (p.einheit platform).einrichtung (p.einheit platform).system ∧
    Maschine.I.Fortschritt (p.einheit platform).einrichtung (p.einheit platform).system := by
  refine ⟨Maschine.I.bestimmt_aus_formen (p.einheit platform).einrichtung (p.einheit platform).system
    (Ast.Semantik.system_bestimmt p.code rein), ?_⟩
  exact Maschine.I.fortschritt_aus_formen (p.einheit platform).einrichtung (p.einheit platform).system
    (Ast.Semantik.system_fortschritt p.code rein)
    (fun i => by
      by_cases h : i.Privat
      · exact Ast.Semantik.Befehl.komponierbar p platform i h
      · intro t' s c w plans u hk _ _
        exact absurd (rein i (Ast.Semantik.kopf_mem (code := p.code) hk)) h)

/-- `I` IS DETERMINATE AND MAKES PROGRESS FOR THE UNIT OF ANY FRAGMENT IN THE TWO CLASSES. The class obligation
    `klassenrein` is the only premise: a frame-only fragment uses the template rules (`ideal_fragment_einheit_rein`),
    one with an access uses the pinned determinacy and liveness of `ZugriffZielAussage`. No source origin is assumed,
    so an ordinary source unit, a unit carrying declared invariants and a linked whole are all covered once their
    class obligation is proved. This is the fragment-level form of the eighth conjunct of `NichtLeer`; it does not
    close the gap to arbitrary accepted units (see the counterexample below), and says nothing about `R₀`. -/
theorem ideal_fragment_einheit (zugriff : ZugriffZielAussage)
    (p : Ast.Semantik.Fragment) (platform : Katalog.Plattform) (klassenrein : p.KlassenRein) :
    Maschine.I.Bestimmt (p.einheit platform).einrichtung (p.einheit platform).system ∧
    Maschine.I.Fortschritt (p.einheit platform).einrichtung (p.einheit platform).system := by
  by_cases rein : p.Rein
  · exact ideal_fragment_einheit_rein p platform rein
  · exact ⟨zugriff.2.1 p platform ⟨klassenrein, rein⟩,
      fortschritt_klassenrein zugriff.2.2.1 p platform klassenrein⟩

/-- The old, source-indexed statement is the fragment theorem restricted to the fragment of a source tree:
    `fragment_klassenrein` supplies the class obligation. Its type is unchanged. -/
theorem ideal_akzeptierte_einheit (zugriff : ZugriffZielAussage) : IdealAkzeptierteEinheitAussage := by
  intro P t
  exact ideal_fragment_einheit zugriff (Ast.Semantik.fragment Ast.Category.unit t) P
    (Ast.Semantik.fragment_klassenrein Ast.Category.unit t)

/-- A source fragment — an ordinary unit or one carrying declared invariants — proves the class obligation: only
    the clause table differs between `programm` and `programmMitInvarianten`, so the code and its classes are the
    same. This is the exact existing inclusion for the first two fragment origins. -/
theorem fragmentQuelleinheit_klassenrein {p : Ast.Semantik.Fragment} (h : p.Quelleinheit) : p.KlassenRein := by
  rcases h with ⟨u, rfl⟩ | ⟨t, rfl⟩
  · change (Ast.Semantik.programm u.baum).KlassenRein
    exact Ast.Semantik.programm_klassenrein u.baum
  · exact Ast.Semantik.programm_klassenrein t

/-- The ideal guarantee for a source fragment: ordinary source and declared invariants are included, the class
    obligation being discharged by `fragmentQuelleinheit_klassenrein`. -/
theorem ideal_quelleinheit (zugriff : ZugriffZielAussage) (p : Ast.Semantik.Fragment)
    (platform : Katalog.Plattform) (quelle : p.Quelleinheit) :
    Maschine.I.Bestimmt (p.einheit platform).einrichtung (p.einheit platform).system ∧
    Maschine.I.Fortschritt (p.einheit platform).einrichtung (p.einheit platform).system :=
  ideal_fragment_einheit zugriff p platform (fragmentQuelleinheit_klassenrein quelle)

/- **Exact scope of the generalization.** The premise of `ideal_fragment_einheit` is a property of the fragment's
   code, not of its origin, so the three fragment origins are handled as follows.

   * Ordinary source. `fragment Category.unit t = programmMitInvarianten ⟨t, []⟩`; `fragment_klassenrein` gives the
     class obligation. `ideal_akzeptierte_einheit` above is this case.
   * Declared invariants. `programmMitInvarianten u` differs from `programm u.baum` only in its clause table, so
     `programm_klassenrein u.baum` gives the class obligation (`fragmentQuelleinheit_klassenrein`). `Quelleinheit`
     covers both source origins exactly; no checker verdict is needed for determinacy or progress.
   * Linked fragments. `Linken.verknuepfteFragmente plan` is a `Fragment`, so `ideal_fragment_einheit` applies as soon
     as `(verknuepfteFragmente plan).KlassenRein` is supplied. `Linken.verknuepfte_klassenrein` derives it from one
     `KlassenRein` premise per module (concatenation preserves the predicate). There is NO closed proof of that
     obligation from `bauplanOk plan = true` alone: `Linken.linker_akzeptiert_aus_guard_transfer` likewise takes
     `hpriv : ∀ b ∈ (verknuepfteFragmente plan).code, b.Privat` as a premise, and no module of the plan constrains
     the classes of its instructions. That premise is the missing proof, not a theorem of the model.

   The generalization does NOT close `idealLuecke`: the eighth conjunct of `NichtLeer` ranges over every accepted
   `Einheit`, while the theorem above ranges over `Fragment.einheit` units with a proved class obligation. The
   counterexample below (`lueckenEinheit`) is accepted but is not the elaboration of any fragment, so `R₀`, the goal
   statements and the proof requirements stay exactly as they are and M12 is not claimed closed. -/

/-- A system with no forms at any state: no rule steps, no head, nothing finished, never blocked. -/
def keinFormenSystem : MaschinenSystem Nat Zelle Int Nat Rahmen PUnit PUnit PUnit Befehl :=
  ⟨fun _ => ⟨fun _ _ _ _ _ => False, fun _ _ _ _ _ => False⟩,
   fun _ _ => none, fun _ _ => False, fun _ _ _ => False⟩

/-- An accepted unit whose forms are absent everywhere. Its start binds one running, dispatched context,
    its source tables and bounds are empty, and only the system is changed against an elaborated empty unit. -/
def lueckenEinheit : Ast.Semantik.Einheit :=
  { einheitVon Katalog.Plattform.x86_64 (⟨[], Ast.UnitBody.done⟩ : Ast.Unit) with
    system := keinFormenSystem
    startdaten := fun _ => ⟨fun _ => Gabbro.Core.Ast.Semantik.Rahmen.start ([] : Ast.Scope),
      fun _ => .laeuft,
      fun _ => ⟨some (Kontext.faden 0), .nutzer, 0, fun _ => false, 0, false, []⟩,
      ⟨fun _ => true, fun _ => 0⟩⟩
    quelltabellen := .leer
    schranken := .leer
    etiketten := .leer
    fluss := .leer
    domaenen := eineTabelle }

/-- The unit is accepted: no form steps, no generated guard use, no written clause, no bound, no lock section. -/
theorem lueckenEinheit_akzeptiert : Annahme.Akzeptiert lueckenEinheit := by
  refine ⟨⟨Katalog.Plattform.katalog_wohlgeformt .x86_64, ?_,
    ⟨Aussen.zulassung_m2 _, ?_⟩, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro i c s u w plan h
    exact False.elim h
  · apply Annahme.aussen_gueltig_aus_kontext
    intro _ _ _ _ _ _ _ step
    cases step with
    | kontext _ _ regel _ =>
        obtain ⟨i, hi, _⟩ := regel
        exact nomatch hi
  · refine ⟨fun _ _ _ => ⟨fun _ _ _ => rfl, fun _ => rfl, fun _ => rfl, rfl, rfl, fun _ => rfl⟩, fun _ => ?_⟩
    constructor
    · intro _ _ _ _ _ h
      cases h.1
    · intro _ _ _ _ _ _ _ _ _ _ _ h
      cases h.1
  · exact Annahme.schrankenLokal_leer rfl rfl rfl
  · exact Annahme.abschnittWartefrei_ohne_blockade _ fun _ _ _ hb => hb
  · exact Annahme.domaenenLokal_ohne_kopf _ eineTabelle_akzeptiert fun _ _ => rfl
  · intro ρ _
    exact ⟨fun _ h => (List.not_mem_nil h).elim, fun _ _ h => (List.not_mem_nil h).elim,
      fun _ _ _ h => (List.not_mem_nil h).elim⟩
  · refine ⟨fun ρ _ t op args need => False.elim need, fun ρ _ t => ?_,
      fun _ _ _ _ _ _ hne => (hne rfl).elim⟩
    intro h
    obtain ⟨C, hC⟩ := h
    obtain ⟨hex, hall⟩ := hC
    obtain ⟨c, hc⟩ := hex
    obtain ⟨b, hb, _⟩ := hall c hc
    exact False.elim hb

def lueckenStart : Katalog.AussenStart := ⟨0, fun _ => none, [], fun _ => none, Katalog.AussenSicht.leer⟩

/-- `I` does not progress for the accepted unit: at its running, dispatched start state there is no crash offer,
    no finished or blocked form, no context rule and no ideal rule, so `FortschrittAm` has no alternative. -/
theorem lueckenEinheit_nicht_fortschritt :
    ¬ I.Fortschritt lueckenEinheit.einrichtung lueckenEinheit.system := by
  intro hf
  let k := lueckenEinheit.katalog
  let sicht : Nat → Katalog.AussenVerlauf → Katalog.AussenSicht := fun _ _ => Katalog.AussenSicht.leer
  let h : Katalog.Umgebung := Katalog.Umgebung.referenz k 1 sicht
  let hw : Katalog.HwLauf := Katalog.Umgebung.referenzLauf k 1 sicht
  let s := (I.start lueckenEinheit lueckenStart).2
  let c := Kontext.faden 0
  have konf : hw.konform k h := by
    refine ⟨rfl, ?_⟩
    exact (Katalog.Umgebung.referenz_fair k 1 sicht
      (Katalog.Plattform.katalog_wohlgeformt .x86_64) (by omega)).gueltig
  have gut : s.SpeicherGut := by
    dsimp [s, I.start, Zustand.start]
    exact ⟨Speicher.Zustand.leer_konsistent, Speicher.Zustand.leer_vollstaendig⟩
  have am := hf k h hw 0 s c konf gut rfl ⟨0, rfl⟩
  rcases am with crash | done | blocked | step | wait
  · rcases crash with ⟨spur, s', hstep⟩
    cases hstep with
    | absturz hab =>
        have hc : (hw.angebot 0).crash = true := hab.1.2
        change false = true at hc
        cases hc
  · exact done
  · rcases blocked with ⟨b, hb⟩
    exact hb
  · rcases step with ⟨w, spur, s', hstep⟩
    cases hstep with
    | kontext _ _ regel _ =>
        obtain ⟨i, hi, _⟩ := regel
        exact nomatch hi
  · rcases wait with ⟨wartet, _⟩
    obtain ⟨w, plans, u, ischritt⟩ := wartet
    obtain ⟨i, hi, _⟩ := ischritt
    exact nomatch hi

/-- The universal accepted-unit determinacy and progress requirement is false: acceptance constrains the unit's
    authority, clauses and guards, but not whether its forms step or progress. -/
theorem idealLuecke_widerlegt :
    ¬ (∀ E : Ast.Semantik.Einheit, Annahme.Akzeptiert E →
      I.Bestimmt E.einrichtung E.system ∧ I.Fortschritt E.einrichtung E.system) := by
  intro h
  have good := h lueckenEinheit lueckenEinheit_akzeptiert
  exact lueckenEinheit_nicht_fortschritt good.2

end Gabbro.Core.Ziel.Korrektheit
