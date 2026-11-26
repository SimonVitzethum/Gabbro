/-
  File:      core/Core/Ziel/Korrektheit/Beweise/BegleitZusammensetzung.lean
  Subject:   COMPANION LEMMAS for the pinned statements of `Core/Ziel/Korrektheit/Zusammensetzung.lean`
              (the goal theorem over the concrete frame, composed from its legs): for every `…Aussage`
              an `X.erfuellbar` (premises hold jointly) and an `X.nichtTrivial` (the statement is sharp:
              a weaker form fails, or a refused object violates it). No statement is changed.

  No witness is local to a program: the empty source unit on x86-64 is accepted and has an admitted run
  (`Fragment.akzeptiert_ohne_bedarf`, `lauf_erfuellbar`), the two-module example plan links and is accepted
  (`Linken.link_erfuellbar`), and the safety falsification witnesses are reused at their generic unit type.
  Where a leg of a composition is still open (scheduler progress, bounds, the refutations at
  `Ast.Semantik.Einheit`), the companion takes exactly that leg as a hypothesis and names it; the proved
  legs are discharged.
-/
module

public import Core.Ziel.Korrektheit.Zusammensetzung
public import Core.Ziel.Korrektheit.Beweise.BegleitMaschine
public import Core.Ziel.Korrektheit.Beweise.BildGueltig
public import Core.Ziel.Korrektheit.Beweise.NIAkzeptiert
public import Core.Ziel.Korrektheit.Beweise.SicherheitAkzeptiert
public import Core.Ast.LowLevel.Proofs.EnvironmentSatisfiability
public import Core.Maschine.Start
public import Core.Annahme.Annahme
public import Core.Sicherheit.Erfuellbar
public import Core.Beobachtung.NichtinterferenzErfuellbar
public import Core.Linken.Aussage
public import Core.Linken.OffenSchluss

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit

open Gabbro.Core
open Gabbro.Core.Katalog
open Gabbro.Core.Maschine
open Gabbro.Core.Linken

/-- The empty source unit has no clauses and no guarded instruction, so its elaboration is accepted on every
    platform. -/
theorem trivialUnit_akzeptiert (P : Plattform) :
    Annahme.Akzeptiert (einheitVon P trivialUnit) := by
  let p := Ast.Semantik.fragment Ast.Category.unit trivialUnit
  change Annahme.Akzeptiert (p.einheit P)
  refine Ast.Semantik.Fragment.akzeptiert_ohne_bedarf p P ?_
    (Ast.Semantik.fragment_rein Ast.Category.unit trivialUnit) ?_
  · rfl
  · intro b present frame
    have code : p.code = [Ast.Semantik.Befehl.starte Ast.Semantik.mainName, Ast.Semantik.Befehl.ende] := rfl
    rw [code] at present
    simp only [List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with same | same <;> cases same <;> rfl

/-- The empty source unit is admitted: its only instructions are `starte` and `ende`. -/
theorem trivialUnit_zugelassen (P : Plattform) :
    Ast.Semantik.zugelassen P Ast.Category.unit trivialUnit := by
  let p := Ast.Semantik.fragment Ast.Category.unit trivialUnit
  change p.environmentAllowed P.katalog ∧ p.code.all (Ast.Semantik.Befehl.platformAllowed P) = true
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · exact List.nodup_nil
    · intro e present
      cases present
  · have code : p.code = [Ast.Semantik.Befehl.starte Ast.Semantik.mainName, Ast.Semantik.Befehl.ende] := rfl
    rw [code]
    simp only [List.all_cons, List.all_nil, Ast.Semantik.Befehl.platformAllowed, Bool.true_and]

/-- An admitted run of the empty unit: the image is valid by `bildGueltig`, and the catalogue supplies a
    conforming environment and a fair history. -/
theorem trivialUnit_lauf (P : Plattform) :
    ∃ (H : Umgebung) (s : AussenStart) (hw : HwLauf) (ρ : Lauf (einheitVon P trivialUnit)),
      Laeufe (einheitVon P trivialUnit) H ρ := by
  let E := einheitVon P trivialUnit
  have image : E.bild.gueltig E.katalog.plattform.ziel :=
    bildGueltig P trivialUnit (trivialUnit_zugelassen P)
  obtain ⟨H, s, hw, ρ, _, _, run, _, _⟩ :=
    lauf_erfuellbar E (Plattform.katalog_wohlgeformt P) image
  exact ⟨H, s, hw, ρ, run⟩

/-- A registry evidence with one form: the form occurs in a printed empty unit and is realised by that unit's
    elaboration. -/
def beleg : FormBeleg :=
  ⟨Unit, fun a _ => Ast.Parse (category := Ast.Category.unit) a trivialUnit,
    fun _ a E => E = einheitVon Plattform.x86_64 trivialUnit⟩

theorem beleg_gedeckt : FormenGedecktAussage Plattform.x86_64 beleg := by
  intro f
  refine ⟨Ast.print (category := Ast.Category.unit) trivialUnit,
    einheitVon Plattform.x86_64 trivialUnit, ?_, ?_, ?_, ?_⟩
  · exact Ast.parse_print (category := Ast.Category.unit) trivialUnit
  · exact ⟨trivialUnit, Ast.parse_print (category := Ast.Category.unit) trivialUnit,
      ⟨rfl, trivialUnit_zugelassen Plattform.x86_64⟩⟩
  · exact trivialUnit_akzeptiert Plattform.x86_64
  · rfl

/-- The two defining modules of the example plan are accepted on their own. -/
theorem modulDef_akzeptiert :
    Annahme.Akzeptiert (Linken.modulDef.fragment.einheit Plattform.x86_64) := by
  refine Ast.Semantik.Fragment.akzeptiert_ohne_bedarf Linken.modulDef.fragment Plattform.x86_64 rfl
    Linken.modulDef_rein ?_
  intro b present frame
  change b ∈ ([Ast.Semantik.Befehl.definiere Ast.Semantik.mainName [] none 0 2 false [] none,
    Ast.Semantik.Befehl.rueckVoid, Ast.Semantik.Befehl.ende] : List Ast.Semantik.Befehl) at present
  simp only [List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl | rfl <;> rfl

theorem modulCall_akzeptiert :
    Annahme.Akzeptiert (Linken.modulCall.fragment.einheit Plattform.x86_64) := by
  refine Ast.Semantik.Fragment.akzeptiert_ohne_bedarf Linken.modulCall.fragment Plattform.x86_64 rfl ?_ ?_
  · intro b present
    change b ∈ ([Ast.Semantik.Befehl.rufe Ast.Semantik.mainName [] none] : List Ast.Semantik.Befehl) at present
    obtain rfl := List.mem_singleton.mp present
    exact Or.inr (Or.inl rfl)
  · intro b present frame
    change b ∈ ([Ast.Semantik.Befehl.rufe Ast.Semantik.mainName [] none] : List Ast.Semantik.Befehl) at present
    obtain rfl := List.mem_singleton.mp present
    rfl

/-- The premises of image validity hold jointly: the empty unit is admitted and its image is valid. -/
theorem BildGueltigAussage.erfuellbar :
    ∃ (P : Plattform) (t : Ast.Unit), Ast.Semantik.zugelassen P Ast.Category.unit t ∧
      (einheitVon P t).bild.gueltig (einheitVon P t).katalog.plattform.ziel :=
  ⟨Plattform.x86_64, trivialUnit, trivialUnit_zugelassen _,
    bildGueltig _ _ (trivialUnit_zugelassen _)⟩

/-- Image validity is a real condition: the elf image whose only entry has no byte is refused on x86-64,
    whose target admits elf. -/
theorem BildGueltigAussage.nichtTrivial :
    ∃ (P : Plattform) (b : Bild), ¬ b.gueltig P.ziel := by
  refine ⟨Plattform.x86_64, ⟨Bildformat.elf, fun _ => none, [0]⟩, ?_⟩
  intro h
  obtain ⟨byte, present⟩ := h.2.2 0 (List.mem_singleton.mpr rfl)
  cases present

/-- The premises of form coverage hold jointly: the one-form registry evidence above is covered. -/
theorem FormenGedecktAussage.erfuellbar :
    ∃ (P : Plattform) (B : FormBeleg), FormenGedecktAussage P B :=
  ⟨Plattform.x86_64, beleg, beleg_gedeckt⟩

/-- Coverage is sharp: a registry whose form never occurs in a text is not covered. -/
theorem FormenGedecktAussage.nichtTrivial :
    ∃ (P : Plattform) (B : FormBeleg), ¬ FormenGedecktAussage P B := by
  refine ⟨Plattform.x86_64, ⟨Unit, fun _ _ => False, fun _ _ _ => True⟩, ?_⟩
  intro h
  obtain ⟨a, E, present, _, _, _⟩ := h ()
  exact present

/-- The premises of the bounds leg hold jointly: the accepted empty unit has an admitted run. -/
theorem SchrankenAkzeptiertAussage.erfuellbar :
    ∃ (P : Plattform) (t : Ast.Unit), Annahme.Akzeptiert (einheitVon P t) ∧
      ∃ (H : Umgebung) (ρ : Lauf (einheitVon P t)), Laeufe (einheitVon P t) H ρ := by
  obtain ⟨H, s, hw, ρ, run⟩ := trivialUnit_lauf Plattform.x86_64
  exact ⟨Plattform.x86_64, trivialUnit, trivialUnit_akzeptiert _, H, ρ, run⟩

/-- Acceptance is a real restriction on the bounds leg: the stale unit of `Core.Annahme` is refused. -/
theorem SchrankenAkzeptiertAussage.nichtTrivial :
    ∃ (E : Maschine.Einheit Unit Unit Unit Unit Unit Unit Unit Unit Unit), ¬ Annahme.Akzeptiert E :=
  ⟨Annahme.staleEinheit, Annahme.stale_nicht_akzeptiert⟩

/-- The premises of the noninterference leg hold jointly: the accepted empty unit is noninterferent. -/
theorem NIAkzeptiertAussage.erfuellbar :
    ∃ (P : Plattform) (t : Ast.Unit), Annahme.Akzeptiert (einheitVon P t) ∧
      Beobachtung.Nichtinterferent (einheitVon P t) :=
  ⟨Plattform.x86_64, trivialUnit, trivialUnit_akzeptiert _,
    niAkzeptiert _ _ (trivialUnit_akzeptiert _)⟩

/-- Noninterference has content: the comparison premise of two low-equal runs with different high answers is
    satisfiable (`ni_erfuellbar` at the generic unit type). -/
def NIAkzeptiertAussage.nichtTrivial := Beobachtung.ni_erfuellbar

/-- The five legs of the goal hold jointly as soon as the two open ones are supplied: image validity, form
    coverage and noninterference are proved here; `FortschrittAkzeptiertAussage` and
    `SchrankenAkzeptiertAussage` are the legs still open (`SchedulerFortschrittVoraussetzung`, M9). -/
theorem ZielAusTeilenAussage.erfuellbar
    (fortschritt : FortschrittAkzeptiertAussage)
    (schranken : SchrankenAkzeptiertAussage Plattform.x86_64) :
    ∃ (P : Plattform) (B : FormBeleg), BildGueltigAussage P ∧ FormenGedecktAussage P B ∧
      FortschrittAkzeptiertAussage ∧ SchrankenAkzeptiertAussage P ∧ NIAkzeptiertAussage P :=
  ⟨Plattform.x86_64, beleg, bildGueltig _, beleg_gedeckt, fortschritt, schranken, niAkzeptiert _⟩

/-- A leg of the composition is a real restriction: a registry whose form never occurs breaks coverage. -/
theorem ZielAusTeilenAussage.nichtTrivial :
    ∃ (P : Plattform) (B : FormBeleg), ¬ FormenGedecktAussage P B :=
  FormenGedecktAussage.nichtTrivial

/-- The premises of the safety leg hold jointly: the accepted empty unit has an admitted run. -/
theorem SicherheitAkzeptiertAussage.erfuellbar :
    ∃ (P : Plattform) (t : Ast.Unit), Annahme.Akzeptiert (einheitVon P t) ∧
      ∃ (H : Umgebung) (ρ : Lauf (einheitVon P t)), Laeufe (einheitVon P t) H ρ := by
  obtain ⟨H, s, hw, ρ, run⟩ := trivialUnit_lauf Plattform.x86_64
  exact ⟨Plattform.x86_64, trivialUnit, trivialUnit_akzeptiert _, H, ρ, run⟩

/-- Safety is not trivially true: at the generic unit type a run of a loaded unit violates memory safety. -/
theorem SicherheitAkzeptiertAussage.nichtTrivial :
    ∃ (E : Gabbro.Core.Sicherheit.Laufkonstruktion.Modell) (H : Umgebung)
      (ρ : Gabbro.Core.Sicherheit.Lauf E), Maschine.Laeufe E.maschine H ρ ∧ ¬ Gabbro.Core.Sicherheit.Speichersicher E H ρ :=
  Gabbro.Core.Sicherheit.sicherheit_nichtLeer.1

/-- The concrete non-triviality leg is satisfiable at the generic unit type: the four falsification witnesses
    of `Core.Sicherheit` (the missing step is to lift them to `Ast.Semantik.Einheit`). -/
theorem SicherheitNichtLeerInstanzAussage.erfuellbar :
    ∃ (E : Gabbro.Core.Sicherheit.Laufkonstruktion.Modell) (H : Umgebung)
      (ρ : Gabbro.Core.Sicherheit.Lauf E), Maschine.Laeufe E.maschine H ρ ∧ ¬ Gabbro.Core.Sicherheit.Speichersicher E H ρ :=
  Gabbro.Core.Sicherheit.sicherheit_nichtLeer.1

/-- The refutations are not forced: a loaded unit with a true declaration satisfies all four properties. -/
def SicherheitNichtLeerInstanzAussage.nichtTrivial := Gabbro.Core.Sicherheit.sicherheit_erfuellbar

/-- The two legs of safety hold jointly once the concrete refutations are supplied (open: the four witnesses
    at `Ast.Semantik.Einheit`); acceptance of the elaborated empty unit is proved here. -/
theorem SicherheitAusTeilenAussage.erfuellbar
    (nichtLeer : SicherheitNichtLeerInstanzAussage Plattform.x86_64 beleg) :
    ∃ (P : Plattform) (B : FormBeleg), SicherheitAkzeptiertAussage P ∧
      SicherheitNichtLeerInstanzAussage P B :=
  ⟨Plattform.x86_64, beleg, sicherheitAkzeptiert _, nichtLeer⟩

/-- The safety conclusion is not trivially true: memory safety can fail on an admitted run at the generic
    unit type. -/
theorem SicherheitAusTeilenAussage.nichtTrivial :
    ∃ (E : Gabbro.Core.Sicherheit.Laufkonstruktion.Modell) (H : Umgebung)
      (ρ : Gabbro.Core.Sicherheit.Lauf E), Maschine.Laeufe E.maschine H ρ ∧ ¬ Gabbro.Core.Sicherheit.Speichersicher E H ρ :=
  Gabbro.Core.Sicherheit.sicherheit_nichtLeer.1

/-- Part of `ZielInhaltAussage` holds at the concrete frame: an accepted unit has an admitted run. Open: a
    refused elaborated unit, `SimRefutierbarAussage` and the noninterference refutation at the concrete type. -/
theorem ZielInhaltAussage.erfuellbar :
    ∃ (P : Plattform) (t : Ast.Unit), Annahme.Akzeptiert (einheitVon P t) ∧
      ∃ (H : Umgebung) (ρ : Lauf (einheitVon P t)), Laeufe (einheitVon P t) H ρ := by
  obtain ⟨H, s, hw, ρ, run⟩ := trivialUnit_lauf Plattform.x86_64
  exact ⟨Plattform.x86_64, trivialUnit, trivialUnit_akzeptiert _, H, ρ, run⟩

/-- The frame has a refused object at the generic unit type: acceptance is not vacuous. -/
theorem ZielInhaltAussage.nichtTrivial :
    ∃ (E : Maschine.Einheit Unit Unit Unit Unit Unit Unit Unit Unit Unit), ¬ Annahme.Akzeptiert E :=
  ⟨Annahme.staleEinheit, Annahme.stale_nicht_akzeptiert⟩

/-- The premise of linker acceptance holds jointly: the two-module example plan links, is sealed,
    and both of its modules are openly accepted on their own. -/
theorem LinkerAkzeptiertAussage.erfuellbar :
    ∃ (plan : Bauplan) (frag : Ast.Semantik.Fragment), linke plan = some frag ∧
      kontrollflussAbgeschottet plan = true ∧
      ∀ m ∈ plan.module, Linken.OffenAkzeptiertAussage m plan.plattform :=
  ⟨Linken.beispielPlan, Linken.beispielFragment, Linken.beispielLinke,
    Linken.beispielAbgeschottet, Linken.beispiel_offen⟩

/-- Linking is not vacuous: the duplicate-name plan is refused although each of its modules is
    openly accepted on its own. -/
theorem LinkerAkzeptiertAussage.nichtTrivial :
    ∃ (plan : Bauplan), linke plan = none ∧
      ∀ m ∈ plan.module, Linken.OffenAkzeptiertAussage m plan.plattform := by
  refine ⟨Linken.doppelPlan, Linken.doppelLinke, ?_⟩
  intro m present
  simp only [Linken.doppelPlan, List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl <;>
    exact Linken.modulOffenOk_korrekt _ _ (by rfl)

/-- The linker is non-trivial in both directions: it links the two-module example and refuses the
    duplicate-name plan whose parts are each accepted (`Linken.link_erfuellbar`, `Linken.doppelTeile`). -/
theorem LinkerNichtTrivialAussage.erfuellbar : LinkerNichtTrivialAussage := by
  refine ⟨?_, ?_⟩
  · obtain ⟨plan, frag, fn, linked, length, defs, call, accepted⟩ := Linken.link_erfuellbar
    refine ⟨plan, frag, linked, ?_⟩
    omega
  · exact ⟨Linken.doppelPlan, Linken.doppelLinke, Linken.doppelTeile⟩

/-- The definition-level acceptance statement is empty (`Iff.rfl`), so the non-triviality of `linke` is the
    content of its own statement, not of the old one. -/
theorem LinkerNichtTrivialAussage.nichtTrivial : Linken.LinkAkzeptanzAussage :=
  Linken.linkAkzeptanz

/-- The premises of checker coverage hold jointly: a checker that accepts everything and a registry whose
    form occurs in the printed empty unit. -/
theorem PrueferDecktFormenAussage.erfuellbar :
    ∃ (C : Pruefer) (B : FormBeleg), PrueferDecktFormenAussage C B := by
  let C : Pruefer := ⟨fun _ _ => true, fun _ _ => true, fun _ _ => true,
    fun _ _ => true, fun _ _ => true, fun _ _ => true⟩
  let B : FormBeleg :=
    ⟨Unit, fun a _ => Ast.Parse (category := Ast.Category.unit) a trivialUnit, fun _ _ _ => True⟩
  refine ⟨C, B, ?_⟩
  intro f
  refine ⟨Plattform.x86_64, trivialUnit, Ast.print (category := Ast.Category.unit) trivialUnit,
    ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · exact Ast.parse_print (category := Ast.Category.unit) trivialUnit
  · exact Ast.parse_print (category := Ast.Category.unit) trivialUnit

/-- Coverage is sharp: a checker that refuses everything covers no non-empty registry. -/
theorem PrueferDecktFormenAussage.nichtTrivial :
    ∃ (C : Pruefer) (B : FormBeleg), ¬ PrueferDecktFormenAussage C B := by
  let C : Pruefer := ⟨fun _ _ => false, fun _ _ => false, fun _ _ => false,
    fun _ _ => false, fun _ _ => false, fun _ _ => false⟩
  let B : FormBeleg := ⟨Unit, fun _ _ => True, fun _ _ _ => True⟩
  refine ⟨C, B, ?_⟩
  intro h
  obtain ⟨P, t, a, fragment, _, _, _⟩ := h ()
  change (false && false && false) = true at fragment
  cases fragment

end Gabbro.Core.Ziel.Korrektheit
