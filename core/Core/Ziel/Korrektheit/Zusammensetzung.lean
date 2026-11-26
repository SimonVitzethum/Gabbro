/-
  File:      core/Core/Ziel/Korrektheit/Zusammensetzung.lean
  Subject:   THE GOAL THEOREM OVER THE CONCRETE FRAME, COMPOSED FROM ITS LEGS (PERFECT-MODEL §2, §2.2), the legs
             that are still open, the statements that give the frame content, and the linker interface.

  `GabbroZielForm (R₀ P B)` decomposes into legs, each a statement about elaborated units of the concrete types:
  * proved here or in `core/`: text well-formedness and functional denotation (`Frontend.lean`), acceptance gives a
    well-formed catalogue (`akzeptiert_katalog`), the catalogue is satisfiable (`katalog_nichtLeer`), every admissible
    fair history lifts to a run (`fairer_lauf`), a run exists from every admissible start (`lauf_ab_start`), `I` is
    determinate and makes progress (`ideal_akzeptierte_einheit`), refinement and today's guarantee
    (`verfeinerung_akzeptiert`, `zielFX_akzeptiert`);
  * open, one pinned statement each (below): `BildGueltigAussage`, `FormenGedecktAussage`,
    `FortschrittAkzeptiertAussage`, `SchrankenAkzeptiertAussage`, `NIAkzeptiertAussage`.
  `ZielAusTeilenAussage` is the composition: the open legs imply the goal over `R₀`. It is a statement about the
  frame, so it is where a wrong field of `R₀` shows (a field bound to the wrong constant makes it unprovable).

  `ZielInhaltAussage` is the answer to the documented vacuity of `GabbroZielForm` for a free frame: over `R₀` some
  accepted unit has a run, some unit is refused, and the refinement and noninterference can each fail for a refused
  unit. `SicherheitAusTeilenAussage` is the same for `gabbro_sicherheit`.
-/
module

public import Core.Ziel.Korrektheit.Instanz
public import Core.Ziel.Korrektheit.Verfeinerung
public import Core.Katalog.Erfuellbar
public import Core.Linken.Modul
public import Core.Linken.Offen

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit

open Gabbro.Core

/-- LEG `NichtLeer 6`: the image of an admitted unit is valid on the selected platform, so a catalogue-conformant
start exists (`zulStart_erfuellbar`). Open: the elaborated image and its validity (M6 loader, Designer then
Prover). -/
def BildGueltigAussage (P : Katalog.Plattform) : Prop :=
  ∀ t : Ast.Unit, Ast.Semantik.zugelassen P Ast.Category.unit t →
    (einheitVon P t).bild.gueltig (einheitVon P t).katalog.plattform.ziel

/-- LEG `NichtLeer 3`: every language form of the registry occurs in some accepted program and its occurrence is
realised (`Rahmen.realisiert`). Open: the registry evidence `B` for every inventory form (M6 registry; the
guard of §6.5 asks for it per constructor). -/
def FormenGedecktAussage (P : Katalog.Plattform) (B : FormBeleg) : Prop :=
  ∀ f : B.Form, ∃ (a : Text.RawText) (E : Ast.Semantik.Einheit),
    B.enthaelt a f ∧ Ast.Semantik.Bezeichnet P Ast.Category.unit a E ∧ Annahme.Akzeptiert E ∧ B.realisiert f a E

/-- LEG `Verfeinert 4`: every run of an accepted elaborated unit stays within the unit's declared bounds on hold
time, cost, memory, stack and time (`ImSchranken`). Feeds: `SchrankenLokal`, `RegelSchranken`, the fifteen
`SchrankenB9B21Pflichten`, `SchrankenB8Beweise`. Open: M9 (Prover; the duties are pinned). -/
def SchrankenAkzeptiertAussage (P : Katalog.Plattform) : Prop :=
  ∀ t : Ast.Unit, Annahme.Akzeptiert (einheitVon P t) →
    ∀ (H : Katalog.Umgebung) (ρ : Maschine.Lauf (einheitVon P t)),
      Maschine.Laeufe (einheitVon P t) H ρ → Beobachtung.ImSchranken (einheitVon P t) ρ

/-- LEG `NI`: an accepted elaborated unit is noninterferent. Feeds: `ni_akzeptierter_einheit`,
`akzeptiertes_fragment_ni`, `FragmentNIBeweise` (open: interrupt, crash, pause, call and loop duties). -/
def NIAkzeptiertAussage (P : Katalog.Plattform) : Prop :=
  ∀ t : Ast.Unit, Annahme.Akzeptiert (einheitVon P t) → Beobachtung.Nichtinterferent (einheitVon P t)

/-- THE GOAL THEOREM OVER THE CONCRETE FRAME FOLLOWS FROM ITS OPEN LEGS: with the five legs, `GabbroZielForm` holds
for `R₀ P B` (the proved legs are not hypotheses). Proof sketch: instantiate each conjunct of `NichtLeer`,
`Verfeinert` and `NI` at the tagged runs of `R₀` (`ρ.1 = E` is the first conjunct of every run field), using
`text_wohlgeformt`, `bezeichnet_funktional`, `akzeptiert_katalog`, `katalog_nichtLeer`, `fairer_lauf`,
`lauf_ab_start`, `ideal_akzeptierte_einheit`, `verfeinerung_akzeptiert`, `zielFX_akzeptiert`,
`deadlockfrei_aus_waechter` for the class `deadlockFree`. The casts are the tag equalities of `R₀`. -/
def ZielAusTeilenAussage (P : Katalog.Plattform) (B : FormBeleg) : Prop :=
  BildGueltigAussage P → FormenGedecktAussage P B → FortschrittAkzeptiertAussage →
    SchrankenAkzeptiertAussage P → NIAkzeptiertAussage P → Ziel.GabbroZielForm (R₀ P B)

/-- THE FOUR SAFETY PROPERTIES FOR EVERY ACCEPTED ELABORATED UNIT: memory safety, preservation of the declared
invariants, race freedom and TOCTOU freedom hold on every run. Feeds: `sicherheit_aus_regeln`,
`Befehl.sicherheitsPflichten`, `ProgramKernSicherheitsAussage`. Open: the current proof covers units with no
declared invariant (`p.klauseln.invariant = []`) and needs `GrenzenSicher` for the elaborated loader; units WITH
invariants are the real content (`InvariantenErhalten` reads the clause table through `sicherheitVon`). -/
def SicherheitAkzeptiertAussage (P : Katalog.Plattform) : Prop :=
  ∀ t : Ast.Unit, Annahme.Akzeptiert (einheitVon P t) →
    ∀ (H : Katalog.Umgebung) (ρ : Maschine.Lauf (einheitVon P t)),
      Maschine.Laeufe (einheitVon P t) H ρ →
      Gabbro.Core.Sicherheit.Speichersicher (sicherheitVon (einheitVon P t)) H ρ ∧
      Gabbro.Core.Sicherheit.InvariantenErhalten (sicherheitVon (einheitVon P t)) H ρ ∧
      Gabbro.Core.Sicherheit.Rennfrei (sicherheitVon (einheitVon P t)) H ρ ∧
      Gabbro.Core.Sicherheit.ToctouFrei (sicherheitVon (einheitVon P t)) H ρ

/-- EACH SAFETY PROPERTY CAN FAIL over the concrete frame: for each, some run of some elaborated-type unit
violates it (the refutations of `sicherheit_nichtLeer` at the concrete unit type). Open: the four witnesses at
`Ast.Semantik.Einheit` (Prover; the proofs exist at `Sicherheit.Laufkonstruktion.Modell`). -/
def SicherheitNichtLeerInstanzAussage (P : Katalog.Plattform) (B : FormBeleg) : Prop :=
  Ziel.SicherheitNichtLeer (R₀ P B) (S₀ P B)

/-- THE SAFETY THEOREM OVER THE CONCRETE FRAME FOLLOWS FROM ITS LEGS. -/
def SicherheitAusTeilenAussage (P : Katalog.Plattform) (B : FormBeleg) : Prop :=
  SicherheitAkzeptiertAussage P → SicherheitNichtLeerInstanzAussage P B →
    Ziel.GabbroSicherheitForm (R₀ P B) (S₀ P B)

/-- THE FRAME HAS CONTENT: (1) an accepted unit has a run, (2) some unit is refused, (3) the acceptance premise
matters for refinement (`SimRefutierbarAussage`) and (4) for noninterference: some unit has two low-equal runs
whose low traces differ. This is the answer to the vacuity of `GabbroZielForm` over a free frame: over `R₀` the
premises are satisfiable and each conclusion can fail for a refused unit. Feeds: `akzeptiert_erfuellbar`,
`stale_nicht_akzeptiert`, `lauf_erfuellbar`, `ni_erfuellbar`, `Beschriftung/Leck`. Open: the witnesses at the
concrete unit type (Prover). -/
def ZielInhaltAussage (P : Katalog.Plattform) : Prop :=
    (∃ t : Ast.Unit, Annahme.Akzeptiert (einheitVon P t) ∧
      ∃ (H : Katalog.Umgebung) (ρ : Maschine.Lauf (einheitVon P t)), Maschine.Laeufe (einheitVon P t) H ρ)
  ∧ (∃ t : Ast.Unit, ¬ Annahme.Akzeptiert (einheitVon P t))
  ∧ SimRefutierbarAussage
  ∧ (∃ E : Maschine.Einheit Unit Unit Unit Unit Unit Unit Unit Unit Unit, ¬ Beobachtung.Nichtinterferent E)

/-- LINKER CORRECTNESS over the real linker (`Core/Linken`): a plan that links, whose
    control flow is sealed and all of whose modules are openly accepted on the plan's platform,
    links to an accepted unit, so every theorem about accepted units applies to the linked
    program. Open acceptance quantifies over runs starting at an entry state, which covers module
    entries through calls and starts with foreign arguments — no run from a canonical start. The
    seal (`kontrollflussAbgeschottet`) is listed although `linke` already implies it: it is the
    premise that carries the content. Without it the statement is false (MK-22: fall-through and
    jumps carry temporary state across module boundaries into a guard instruction). Finding:
    `Linken.LinkAkzeptanzAussage` is `Iff.rfl` — acceptance of a plan is DEFINED as acceptance of
    its linked unit, which says nothing about the parts; this statement is the one that says
    something. Open (Designer: the compatibility check; Prover: the open run surgery
    `Linken.OffeneLaufChirurgieAussage`, which projects whole runs onto entry-starting part runs). -/
def LinkerAkzeptiertAussage : Prop :=
  ∀ (plan : Linken.Bauplan) (frag : Ast.Semantik.Fragment), Linken.linke plan = some frag →
    Linken.kontrollflussAbgeschottet plan = true →
    (∀ m ∈ plan.module, Linken.OffenAkzeptiertAussage m plan.plattform) →
    Annahme.Akzeptiert (frag.einheit plan.plattform)

/-- THE LINKER IS NOT TRIVIAL IN EITHER DIRECTION: it links some plan of at least two modules, and it refuses some
plan whose modules are each accepted (a refuse-everything linker satisfies `LinkerAkzeptiertAussage`; an
accept-everything linker is refuted by the second conjunct). -/
def LinkerNichtTrivialAussage : Prop :=
    (∃ (plan : Linken.Bauplan) (frag : Ast.Semantik.Fragment),
      Linken.linke plan = some frag ∧ 2 ≤ plan.module.length)
  ∧ (∃ plan : Linken.Bauplan, Linken.linke plan = none ∧
      ∀ m ∈ plan.module, Annahme.Akzeptiert (m.fragment.einheit plan.plattform))

end Gabbro.Core.Ziel.Korrektheit

namespace Gabbro.Core.Ziel.Korrektheit

/-- THE CHECKER'S FRAGMENT REACHES EVERY LANGUAGE FORM: for every form of the registry there is a source unit of
the fragment that contains it (the registry's evidence `B.enthaelt` for some text that parses to the unit) and that
the checker accepts. A checker that accepts only the empty program fails this, so the soundness of `pruefe` cannot
be met by refusing everything that matters. Open: the registry evidence and a checker (M5, M6). -/
def PrueferDecktFormenAussage (C : Pruefer) (B : FormBeleg) : Prop :=
  ∀ f : B.Form, ∃ (P : Katalog.Plattform) (t : Ast.Unit) (a : Text.RawText),
    C.fragment P t = true ∧ C.pruefe P t = true ∧
    Ast.Parse (category := Ast.Category.unit) a t ∧ B.enthaelt a f

end Gabbro.Core.Ziel.Korrektheit
