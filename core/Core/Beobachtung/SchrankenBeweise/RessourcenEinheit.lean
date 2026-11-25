/-
  File:      core/Core/Beobachtung/SchrankenBeweise/RessourcenEinheit.lean
  Subject:   B9/B21 implementation-side duties of units and loaders. The start statement and
             the protocol statement of `SchrankenB9B21` are false without a premise: a tight
             declared ceiling can be broken by the loader at cut zero, and a crash can install
             recovery data outside the declared bounds. The missing premises are named exactly:
             the loader must establish both bounds, and the recovery entry's start data must
             meet them at every durable snapshot. The answer and interrupt legs need no premise.
             The per-form statement is refuted in `SchrankenBeweise/Ressourcen`.
-/
module

public import Core.Beobachtung.SchrankenB9B21
public import Core.Beobachtung.SchrankenBeweise.Leicht
public import Core.Beobachtung.SchrankenBeweise.Mittel
public import Core.Annahme.HostedLauf

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine Annahme
open Annahme.Hosted

variable {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]
variable {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form}

/-- The start duty under its loader premise: if every successful load establishes both bounds,
    the initial cut of every admitted run carries them. This is the premise the bare statement
    omits; the checker row proves it for the ideal side. -/
theorem ressourcenStart_unterLade
    (lade : ∀ (a : AussenStart) (p : Ladung) {s : Zustand L Ort Wert Raum Lok Grund},
      E.laden a p = some s → StapelZustand E s ∧ SpeicherZustand E s) :
    ressourcenStartAussage E := by
  intro h ρ lauf s cut
  exact lade ρ.start (h.lade E.bild) (lauf.2.2.2.symm.trans cut)

/-- The protocol duty under its narrow premise: the recovery entry's start data meets the stack
    bound and admits no live cell on the durable booking. Answers and interrupts leave rights,
    booking and locals untouched, so the two generic preservation facts discharge them. -/
theorem ressourcenProtokoll_unterWiederanlauf
    (daten : ∀ (t : Nat) (s : Zustand L Ort Wert Raum Lok Grund)
        (p : PersistZustand) (c : Kontext),
      UnterGrenze E.schranken.stapel
        (E.schranken.stapelTiefe ((E.einrichtung.wiederanlauf.daten p.dauerhaft).lokal c)) ∧
      ∀ z, z ∈ LebendeZellen { s.wiederanlauf E.einrichtung.wiederanlauf t p with
        rechte := (E.einrichtung.wiederanlauf.daten p.dauerhaft).rechte } → False) :
    ressourcenProtokollAussage E := by
  intro h ρ lauf t w spur vor nach vorEq spurEq wahl nachEq step stapelVor speicherVor
  cases step with
  | kontext => exact wahl.elim
  | antwort _ s => exact antwortErhalten E stapelVor speicherVor s
  | interrupt _ s => exact unterbrechungErhalten E stapelVor speicherVor s
  | absturz s => exact absturzSchranken E (daten t vor) stapelVor speicherVor s

/-- A unit with a finite stack ceiling and a depth measure that ignores the loaded handle. -/
private def startGegenEinheit : Modell :=
  { einheit with
    schranken := { Schrankendaten.leer with
      stapel := some 0,
      stapelTiefe := fun _ => 1 } }

/-- The bare start statement is false: an admitted loader establishes a state whose declared
    depth exceeds the ceiling. The missing premise is the loader obligation
    `ressourcenStart_unterLade` (the checker row's `SchrankenStart`). -/
theorem ressourcenStartAussage_falsch :
    ¬ ∀ (E : Modell), ressourcenStartAussage E := by
  intro all
  obtain ⟨start, zul⟩ :=
    zulStart_erfuellbar (erlaubt []) Sicherheit.Laufkonstruktion.bild_gueltig
  obtain ⟨ρ, lauf, startEq⟩ := lauf_ab_start startGegenEinheit (erlaubt []) zul
  have cut : ρ.zeit.zustand 0 = some (startZustand start) := by
    rw [lauf.2.2.2, startEq]
    rfl
  have bounds := all startGegenEinheit lauf (startZustand start) cut
  have post := bounds.1 kontext 0 rfl
  change 1 ≤ 0 at post
  omega

private def griff2 : Handle := { griff with channel := 1 }

private theorem griff_ungleich : griff ≠ griff2 := by
  intro h
  have hc := congrArg Handle.channel h
  simp only [griff, griff2] at hc
  omega

/-- A recovery entry that installs a distinct handle as its start data. -/
private def einrichtungGegen : Einrichtung Unit Unit Unit Unit (Option Handle) Unit Unit :=
  { einrichtung with
    wiederanlauf := { einrichtung.wiederanlauf with daten := fun _ => daten (some griff2) } }

/-- The declared depth counts the handle installed by the recovery entry. -/
private def gegenEinheit : Modell :=
  { einheit with
    einrichtung := einrichtungGegen
    schranken := { Schrankendaten.leer with
      stapel := some 0,
      stapelTiefe := fun l => if l = some griff2 then 1 else 0 } }

private theorem gegen_persistence : gegenEinheit.katalog.enthaelt .persistence := by
  change .persistence ∈ (ZielZeilen ++ .persistence :: _ : List Zeile)
  exact List.mem_append.mpr (Or.inr (List.Mem.head _))

private def gegenBasis : Gelegenheit := ⟨none, fun _ => false, [], fun _ => false, false, false, 0⟩

/-- One crash opportunity at the first cut, no other offer anywhere. -/
private def gegenHw : HwLauf :=
  { politik := (umgebung []).politik
    angebot := fun t => if t = 0 then { gegenBasis with crash := true } else gegenBasis }

private theorem gegenHw_0 : gegenHw.angebot 0 = { gegenBasis with crash := true } := by
  dsimp only [gegenHw]
  rw [if_pos rfl]

private theorem gegenHw_ander {i : Nat} (h0 : i ≠ 0) : gegenHw.angebot i = gegenBasis := by
  dsimp only [gegenHw]
  rw [if_neg h0]

private theorem gegenHw_konform : gegenHw.konform gegenEinheit.katalog (umgebung []) := by
  constructor
  · rfl
  · intro i
    by_cases h0 : i = 0
    · subst i
      rw [gegenHw_0]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro c hc
        cases hc
      · intro c hc
        cases hc
      · intro sig mem
        cases mem
      · intro e he
        cases he
      · intro hm
        exact gegen_persistence
    · rw [gegenHw_ander h0]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro c hc
        cases hc
      · intro c hc
        cases hc
      · intro sig mem
        cases mem
      · intro e he
        cases he
      · intro hm
        cases hm with
        | inl medium => cases medium
        | inr crash => cases crash

private def zustand2Gegen (s : AussenStart) : Zustand :=
  (startZustand s).wiederanlauf gegenEinheit.einrichtung.wiederanlauf 0
    (nachAbsturz (startZustand s).persistenz)

/-- An admitted run whose first tick is the crash and whose successor ticks are idle. -/
private theorem gegen_konkreter_lauf (s : AussenStart) (zul : einheit.ZulStart (umgebung []) s) :
    ∃ ρ : Lauf gegenEinheit,
      Laeufe gegenEinheit (umgebung []) ρ ∧
      ρ.zeit.zustand 0 = some (startZustand s) ∧
      ρ.zeit.spur 0 = some (.absturz, absturzSpur) ∧
      ρ.zeit.zustand 1 = some (zustand2Gegen s) := by
  let z0 := startZustand s
  let z2 := zustand2Gegen s
  have offer : AbsturzAngeboten gegenEinheit.katalog gegenHw 0 := by
    refine ⟨gegen_persistence, ?_⟩
    rw [gegenHw_0]
  have step0 : Lauffolge gegenEinheit gegenHw 0 (some z0) (.absturz, absturzSpur) (some z2) := by
    apply Lauffolge.schritt
    apply ImplSchritt.absturz
    exact absturz_schritt_erfuellbar _ _ offer z0
  have still : ∀ u, KeinSchritt (Lauffolge gegenEinheit gegenHw) (u + 1) (some z2) := by
    intro u ev next step
    cases step with
    | schritt impl =>
      cases impl with
      | kontext _ ready _ _ =>
        obtain ⟨k, gelegen, _, _⟩ := ready
        change (gegenHw.angebot (u + 1)).core = some k at gelegen
        rw [gegenHw_ander (by omega : u + 1 ≠ 0)] at gelegen
        cases gelegen
      | antwort _ replyStep =>
        have erl := replyStep.1.2.1
        simp only [AntwortEreignis.erlaubt] at erl
        rw [replyStep.1.1] at erl
        rw [gegenHw_ander (by omega : u + 1 ≠ 0)] at erl
        exact Bool.false_ne_true erl.1
      | interrupt _ enters =>
        obtain ⟨k, irq, c, nmi, offerInt, rest⟩ := enters
        rw [gegenHw_ander (by omega : u + 1 ≠ 0)] at offerInt
        cases offerInt
      | absturz crash =>
        have noCrash : (gegenHw.angebot (u + 1)).crash = false := by
          rw [gegenHw_ander (by omega : u + 1 ≠ 0)]
          rfl
        exact Bool.false_ne_true (noCrash.symm.trans crash.1.2)
  let zeit : Zeitlauf (Lauffolge gegenEinheit gegenHw) :=
    { zustand
        | 0 => z0
        | _ + 1 => z2
      spur
        | 0 => some (.absturz, absturzSpur)
        | _ + 1 => none
      takt
        | 0 => .schritt rfl step0
        | u + 1 => .wartet rfl rfl (still u) }
  let ρ : Lauf gegenEinheit := ⟨s, gegenHw, zeit⟩
  refine ⟨ρ, ?_, rfl, rfl, rfl⟩
  exact ⟨erlaubt [], gegenHw_konform, zul, rfl⟩

/-- The bare protocol statement is false: a crash installs recovery data outside the declared
    stack bound even though the pre-state meets it. The missing premise is
    `ressourcenProtokoll_unterWiederanlauf`, the recovery start-data discipline. -/
theorem ressourcenProtokollAussage_falsch :
    ¬ ∀ (E : Modell), ressourcenProtokollAussage E := by
  intro all
  obtain ⟨s, zul⟩ :=
    zulStart_erfuellbar (erlaubt []) Sicherheit.Laufkonstruktion.bild_gueltig
  obtain ⟨ρ, lauf, cut0, spur0, cut1⟩ := gegen_konkreter_lauf s zul
  let z0 := startZustand s
  let z2 := zustand2Gegen s
  have granted : s.outside.channels .hosted 0 = some griff := by
    rw [zul.2.2.2.2.2.2.2]
    rfl
  have stapelVor : StapelZustand gegenEinheit z0 := by
    intro c n bound
    cases Option.some.inj bound
    change (if (startDaten s).lokal c = some griff2 then 1 else 0) ≤ 0
    change (if s.outside.channels .hosted 0 = some griff2 then 1 else 0) ≤ 0
    rw [granted]
    rw [if_neg (by intro eq; exact griff_ungleich (Option.some.inj eq))]
  have speicherVor : SpeicherZustand gegenEinheit z0 := by
    intro n bound
    cases bound
  have step : ImplSchritt gegenEinheit.einrichtung gegenEinheit.system gegenEinheit.katalog
      ρ.hw 0 z0 (.absturz, absturzSpur) z2 := by
    have takt := ρ.zeit.takt 0
    rw [cut0, spur0, cut1] at takt
    cases takt with
    | schritt label folge =>
      cases label
      cases folge with
      | schritt h => exact h
    | wartet label eq hp => cases label
  have grenzen := all gegenEinheit lauf 0 .absturz absturzSpur z0 z2 cut0 spur0
    trivial cut1 step stapelVor speicherVor
  have post := grenzen.1 kontext 0 rfl
  change (if (zustand2Gegen s).lokal kontext = some griff2 then 1 else 0) ≤ 0 at post
  have lokalPost : (zustand2Gegen s).lokal kontext = some griff2 := by
    dsimp only [zustand2Gegen, Zustand.wiederanlauf, Zustand.start, gegenEinheit,
      einrichtungGegen, einrichtung, daten]
  rw [if_pos lokalPost] at post
  omega

end Gabbro.Core.Beobachtung
