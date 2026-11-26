/-
  File:      core/Core/Ast/Semantik/Runtime/Faden/Offen.lean
  Subject:   THE OPEN DUTIES OF THE LIFECYCLE INSTRUCTIONS (MK-07), pinned under `FadenBefehlAussage` for the registry
             entry of `Befehl.faden` (the kernel statements that are proved are `FadenAussagen`,
             `Faden/Aussagen.lean`):
             * composability of a step the machine accepts, one independent unit per action
               (`FadenVerweigertKomponierbarAussage`, `StarteKomponierbarAussage`, `VerbindeKomponierbarAussage`,
               `BeendeKomponierbarAussage`, `WechsleKomponierbarAussage`) and the common statement
               `FadenKomponierbarAussage`;
             * the progress of a join under hardware fairness (`VerbindeFortschrittAussage`).
-/
module

public import Core.Ast.Semantik.Runtime.Faden.Aussagen

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog

/-- **Composability of a lifecycle step the protocol accepts** (open). If the machine can run the action of the step
    (`Aktion.Ausfuehrbar`: the thread to start rests, the thread to join has ended and the joiner is its recorded
    creator, the form has set the outcome of the ending thread, the core and the context of a switch are free), the
    protocol executes the step. Difficulty: leicht.
    Sketch: `FuehrtSchrittAus` needs `Zustandsrahmen s u` (`Zustand.NurFaden.rahmen` of `Schrittform.lebenszyklus_ideal`),
    the read-label condition (the plan has no read), the action (`FuehrtAus.starte`, `.verbinde`, `.beende` or `.wechsle`
    from the premise, `FuehrtAus.intern` after a refusal) and the empty memory trace (`Speicherfolge.nil`), with the state
    `{ v with graph := s.graph }`; the premise of `.beende` is the status the form sets. -/
def FadenKomponierbarAussage : Prop :=
  ∀ (p : Fragment) (platform : Plattform) (z : Fadenform) (t : Nat) (s : Zustand) (c : Kontext) (w : PUnit.{1})
    (plan : Plan) (u : Zustand),
    (p.einheit platform).system.kopf s c = some (Befehl.faden z) → (Befehl.faden z).ideal c s w [plan] u →
      plan.aktion.Ausfuehrbar s u c →
      ∃ spur s', FuehrtSchrittAus (p.einheit platform).einrichtung t c s u plan spur s'

/-- **Composability of the refusal of a lifecycle step** (open, independent unit of `FadenKomponierbarAussage`). A
    lifecycle instruction whose operands name nothing is refused (the private plan, the internal action) and the protocol
    executes the refusal. Difficulty: leicht. Sketch: `FuehrtAus.intern`, `Speicherfolge.nil`, `Zustandsrahmen` from
    `Schrittform.verweigert_nurFaden`. -/
def FadenVerweigertKomponierbarAussage : Prop :=
  ∀ (p : Fragment) (platform : Plattform) (z : Fadenform) (t : Nat) (s : Zustand) (c : Kontext) (w : PUnit.{1})
    (plan : Plan) (u : Zustand),
    (p.einheit platform).system.kopf s c = some (Befehl.faden z) → (Befehl.faden z).ideal c s w [plan] u →
      plan.aktion = .intern →
      ∃ spur s', FuehrtSchrittAus (p.einheit platform).einrichtung t c s u plan spur s'

/-- **Composability of a start the machine accepts** (open, independent unit of `FadenKomponierbarAussage`): when the thread
    with the next number rests, the protocol executes the start. Difficulty: leicht. Sketch: `FuehrtAus.starte`, the
    state `{ v with graph := s.graph }`, `Speicherfolge.nil`, `Zustandsrahmen` from `Schrittform.faedenNach_nurFaden`. -/
def StarteKomponierbarAussage : Prop :=
  ∀ (p : Fragment) (platform : Plattform) (z : Fadenform) (t : Nat) (s : Zustand) (c : Kontext) (w : PUnit.{1})
    (plan : Plan) (u : Zustand),
    (p.einheit platform).system.kopf s c = some (Befehl.faden z) → (Befehl.faden z).ideal c s w [plan] u →
      plan.aktion = .starte → s.status (.faden s.naechsterFaden) = .ruht →
      ∃ spur s', FuehrtSchrittAus (p.einheit platform).einrichtung t c s u plan spur s'

/-- **Composability of a join the machine accepts** (open, independent unit of `FadenKomponierbarAussage`): when the joined
    context has ended and the joiner is its recorded creator, the protocol executes the join. Difficulty: leicht. Sketch: as for the start with `FuehrtAus.verbinde`. -/
def VerbindeKomponierbarAussage : Prop :=
  ∀ (p : Fragment) (platform : Plattform) (z : Fadenform) (t : Nat) (s : Zustand) (c : Kontext) (w : PUnit.{1})
    (plan : Plan) (u : Zustand) (kind : Kontext),
    (p.einheit platform).system.kopf s c = some (Befehl.faden z) → (Befehl.faden z).ideal c s w [plan] u →
      plan.aktion = .verbinde kind → (∃ ausgang, s.status kind = .beendet ausgang) →
      s.erzeuger kind = some c →
      ∃ spur s', FuehrtSchrittAus (p.einheit platform).einrichtung t c s u plan spur s'

/-- **Composability of a thread end** (open, independent unit of `FadenKomponierbarAussage`): the step of the end sets the
    outcome of the acting thread, and the protocol executes it. Difficulty: leicht. Sketch: `FuehrtAus.beende` with the status
    the form sets (`Schrittform.faedenNach`, the `beende` arm: `Function.update_self`). -/
def BeendeKomponierbarAussage : Prop :=
  ∀ (p : Fragment) (platform : Plattform) (z : Fadenform) (t : Nat) (s : Zustand) (c : Kontext) (w : PUnit.{1})
    (plan : Plan) (u : Zustand),
    (p.einheit platform).system.kopf s c = some (Befehl.faden z) → (Befehl.faden z).ideal c s w [plan] u →
      plan.aktion = .beende → (∃ ausgang, u.status c = .beendet ausgang) →
      ∃ spur s', FuehrtSchrittAus (p.einheit platform).einrichtung t c s u plan spur s'

/-- **Composability of a switch or a core start the machine accepts** (open, independent unit of
    `FadenKomponierbarAussage`): when the core is the acting context's or idle and the context switched to runs on no core,
    the protocol executes the switch. Difficulty: leicht. Sketch: as for the start with `FuehrtAus.wechsle`. -/
def WechsleKomponierbarAussage : Prop :=
  ∀ (p : Fragment) (platform : Plattform) (z : Fadenform) (t : Nat) (s : Zustand) (c : Kontext) (w : PUnit.{1})
    (plan : Plan) (u : Zustand) (kern : Kern) (kind : Kontext),
    (p.einheit platform).system.kopf s c = some (Befehl.faden z) → (Befehl.faden z).ideal c s w [plan] u →
      plan.aktion = .wechsle kern kind →
      (((s.kerne kern).laeuft = some c ∨ (s.kerne kern).laeuft = none) ∧ s.status kind = .laeuft ∧
        (∀ k, (s.kerne k).laeuft ≠ some kind) ∧ kind ≠ c) →
      ∃ spur s', FuehrtSchrittAus (p.einheit platform).einrichtung t c s u plan spur s'

/-- **A join makes progress under hardware fairness** (open, pinned). A context whose open instruction is a join of a
    context that ends, by its recorded creator, does not hang on a hardware-fair, scheduler-fair run whose preemption
    returns, once the ideal run is matched to that run over the one environment `hU`. The premises are bound to that
    single environment (a `∀ h'` over admissible environments is unsatisfiable with `Laeufe`, see
    `faire_umgebung_nicht_eindeutig`). Without them the promise is false: `verbindeFortschritt_ohneFairness_falsch`.
    Difficulty: mittel.
    Sketch: from the end cut on, `FuehrtAus.verbinde` is available at every cut (the status of an ended context is
    final, and the creator entry persists until this join: only a join of that thread clears it), the form step of the class is total (`klassenFortschritt`), and the hardware fairness of the run gives the
    core an opportunity infinitely often, so the instance cannot stay open on the whole suffix (`BleibtOffen`);
    the memory part of the step is empty. The statement is the join case of the progress classes of
    `Fortschritt/Klasse` (`starvationFree`), whose per-thread promise is `¬ Haengt`. -/
def VerbindeFortschrittAussage : Prop :=
  ∀ {L Ort Wert Raum Lok Grund Bedingung Wahl F : Type} [DecidableEq L]
    (E : Maschine.Einheit L Ort Wert Raum Lok Grund Bedingung Wahl F) (ρ : Maschine.Lauf E) (η : I.Lauf E)
    (hU : Katalog.Umgebung) (c kind : Kontext),
    Laeufe E hU ρ →
    FairLaeufe E.katalog hU ρ.hw →
    SchedulerFair E ρ →
    VerdraengungKehrtZurueck E ρ →
    I.Laufabgleich ρ η →
    η.umgebung = hU →
    (∃ t ausgang, (η.zeit.zustand t).status kind = .beendet ausgang ∧
      ∀ t', t ≤ t' → (η.zeit.zustand t').erzeuger kind = some c) →
      (∃ a, ∀ t, a ≤ t → ∃ plan w u, E.system.ISchritt c (η.zeit.zustand t) w [plan] u ∧
        plan.aktion = .verbinde kind) →
        ¬ I.Haengt E ρ η c

/-- **The registry packet of `Befehl.faden`**: the two duties the classes do not carry. The other duties of the
    lifecycle classes are in `KlassenAussagen` (simulation, locality, progress, the four safety legs, bounds, information
    flow), the stack effect is `klassenStapel`, the information flow of the family is `ZugriffNIAussage`, and the kernel
    statements are `FadenAussagen`. -/
def FadenBefehlAussage : Prop :=
  FadenKomponierbarAussage ∧ VerbindeFortschrittAussage ∧ FadenVerweigertKomponierbarAussage ∧
    StarteKomponierbarAussage ∧ VerbindeKomponierbarAussage ∧ BeendeKomponierbarAussage ∧
    WechsleKomponierbarAussage

end Gabbro.Core.Ast.Semantik
