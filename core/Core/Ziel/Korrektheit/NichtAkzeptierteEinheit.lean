/-
  File:      core/Core/Ziel/Korrektheit/NichtAkzeptierteEinheit.lean
  Subject:   a concrete SOURCE unit whose elaboration is not accepted, the two
             non-triviality witnesses that were waiting for exactly this object,
             and the content leg of `ZielInhaltAussage` at the concrete frame.

  The witness unit's only declaration is a constant that indexes an empty text at
  offset `0`. The guarded instruction `.textIndex` writes the demand `.index (0, 0)`,
  which the pinned guard row refuses (`0 < 0`). A conforming hardware history that
  offers only the entry core forces an ideal run through the two setup instructions;
  at the third cut the demand is canonical, so `WaechterHalten` fails.

  Nothing here changes a pinned statement. The unit is a source `Ast.Unit`, so its
  elaboration is `einheitVon P t`, the object the checker statements quantify over.
-/
module

public import Core.Ziel.Korrektheit.Pruefer
public import Core.Ziel.Korrektheit.Zusammensetzung
public import Core.Ziel.Korrektheit.Beweise.BegleitPruefer
public import Core.Ziel.Korrektheit.Beweise.BegleitZusammensetzung
public import Core.Linken.GegenbeispielVerknuepft
public import Core.Annahme.Annahme
public import Core.Ast.TextValue.IndexProofs

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit

open Gabbro.Core
open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik
open Gabbro.Core.Katalog
open Gabbro.Core.Maschine
open Gabbro.Core.Annahme
open Classical

/-- The name of the witness constant. -/
def indexName : Identifier :=
  keywordName 'x' [] (by decide) (fun _ member => (List.not_mem_nil member).elim)

theorem indexName_ordinary : ordinaryLocal indexName :=
  (directName_of_singleton (name := indexName) rfl).1

/-- A source unit whose only declaration indexes an empty text at offset `0`. -/
def textIndexUnit : Ast.Unit :=
  let written : WrittenType := .integer false 8 none
  let value : Expr [] (.int 0 255) := Expr.textIndex (Expr.textLiteral []) (Expr.lit 0)
  ⟨[⟨indexName, .int 0 255, false, true⟩],
    .step (.constant indexName indexName_ordinary written
      (by
        change 1 ≤ 8 ∧ 8 ≤ 64 ∧ (0 : Int) ≤ 0 ∧ (0 : Int) ≤ 255 ∧ (255 : Int) ≤ 255
        exact ⟨by decide, by decide, by decide, by decide, by decide⟩) value
      (by dsimp [value, Expr.static]; exact ⟨trivial, trivial⟩)
      (by
        change (0 : Int) ≤ 0 ∧ (255 : Int) ≤ 255
        exact ⟨by decide, by decide⟩)) .done⟩

/-- The code the witness unit elaborates to. -/
abbrev textIndexCode : List Befehl := (fragment Ast.Category.unit textIndexUnit).code

/-- The elaborated code: two setup instructions, the guarded index, the binding, the entry and the end. -/
theorem textIndexUnit_code :
    textIndexCode =
      [.textLiteral 0 [], .literal 1 0, .textIndex 0 (sourceUtf8 []).size,
        .bindeWert 0 (.int 0 255) true, .starte mainName, .ende] := by
  rfl

/-- The elaborated witness unit on the approved x86-64 rows. -/
def textIndexEinheit : Ast.Semantik.Einheit := einheitVon Katalog.Plattform.x86_64 textIndexUnit

/-- The hardware offer for the witness run: core `k` always runs, nothing else happens. -/
def txtAngebot (k : Nat) : Gelegenheit :=
  ⟨some k, fun _ => false, [], fun _ => false, false, false, 0⟩

/-- The hardware history for the witness run. -/
def txtHw (h : Umgebung) (k : Nat) : HwLauf :=
  ⟨fun _ => txtAngebot k, h.politik⟩

/-- The boot status at the entry context. -/
theorem txt_status_entry (s : AussenStart) :
    ((I.start textIndexEinheit s).2).status eintritt = .laeuft :=
  rfl

/-- The boot status away from the entry context. -/
theorem txt_status_other (s : AussenStart) (c : Kontext) (hne : c ≠ eintritt) :
    ((I.start textIndexEinheit s).2).status c = .ruht := by
  show (if c = eintritt then Status.laeuft else Status.ruht) = .ruht
  rw [if_neg hne]

/-- The boot dispatch runs the entry context on its assigned core. -/
theorem txt_dispatch (s : AussenStart) (k : Nat) (assigned : s.assignment 0 = some k) :
    (((I.start textIndexEinheit s).2).kerne k).laeuft = some eintritt := by
  show (if some k = s.assignment 0 then some eintritt else none) = some eintritt
  rw [assigned]
  exact if_pos rfl

/-- A head at rest is absent. -/
theorem txt_kopf_ruht {s : Zustand} {c : Kontext}
    (h : s.status c = .ruht) : kopf textIndexCode s c = none := by
  simp only [kopf, h]

/-- The system head is the code head. -/
theorem txt_system_kopf (s : Zustand) (c : Kontext) :
    textIndexEinheit.system.kopf s c = kopf textIndexCode s c := by
  rfl

/-- Liveness ignores the recorded graph. -/
theorem txt_regionLive_graph_irrelevant (s : Zustand) (g : _) :
    Zustand.regionLive { s with graph := g } = Zustand.regionLive s := by
  rfl

/-- No context steps at a resting head. -/
theorem txt_keinSchritt_ruht {c : Kontext} {s : Zustand} {w : PUnit.{1}} {plans : List Plan}
    {u : Zustand} (h : s.status c = .ruht) (step : textIndexEinheit.system.ISchritt c s w plans u) :
    False := by
  obtain ⟨b, head, _⟩ := step
  rw [txt_system_kopf, txt_kopf_ruht h] at head
  cases head

/-- The witness hardware is conformant. -/
theorem txt_konformHw (h : Umgebung) (s : AussenStart) (zul : textIndexEinheit.ZulStart h s)
    (k : Nat) (assigned : s.assignment 0 = some k) :
    (txtHw h k).konform textIndexEinheit.katalog h := by
  unfold HwLauf.konform
  refine ⟨rfl, fun i => ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro core hc
    cases hc
    exact (zul.2.2.2.1 0 k assigned).2
  · intro core hc
    cases hc
  · intro signal mem
    exact (List.not_mem_nil mem).elim
  · intro e hd
    cases hd
  · intro hmed
    rcases hmed with hmed | hcrash
    · cases hmed
    · cases hcrash

/-- The prefix states of the witness run. -/
def sTxt (s : AussenStart) : Zustand :=
  (I.start textIndexEinheit s).2

def sTxt1 (s : AussenStart) : Zustand :=
  (Befehl.textLiteral 0 []).nach eintritt (sTxt s)

def sTxt2 (s : AussenStart) : Zustand :=
  (Befehl.literal 1 0).nach eintritt (sTxt1 s)

/-- Forcing one ideal step: from local, status and core agreement with a concrete
    pre-state, the run takes the forced step and agrees with the concrete post-state. -/
theorem txtForceStep (ρ : I.Lauf textIndexEinheit) (hρ : I.Laeufe textIndexEinheit ρ)
    (t : Nat) (k : Nat) (b : Befehl) (sPre : Zustand)
    (hNoCrash : (ρ.hw.angebot t).crash = false)
    (hCore : (ρ.hw.angebot t).core = some k)
    (hNoInt : (ρ.hw.angebot t).interrupt = fun _ => false)
    (hNoInts : ∀ i, (ρ.hw.angebot i).interrupts = [])
    (hNoDel : (ρ.hw.angebot t).delivery = fun _ => false)
    (hFrei : ρ.belegt t = none)
    (hEqL : (ρ.zeit.zustand t).lokal = sPre.lokal)
    (hEqS : (ρ.zeit.zustand t).status = sPre.status)
    (hEqK : (ρ.zeit.zustand t).kerne = sPre.kerne)
    (hEqF : (ρ.zeit.zustand t).fragen = sPre.fragen)
    (hEqR : Zustand.regionLive (ρ.zeit.zustand t) = Zustand.regionLive sPre)
    (hHead : kopf textIndexCode sPre eintritt = some b)
    (hPriv : b.Privat)
    (hReady : KannSchreiten ρ.hw t eintritt sPre)
    (hStPre : ∀ c, c ≠ eintritt → sPre.status c = .ruht)
    (hFrPre : sPre.fragen = []) :
    (∃ ev, ρ.zeit.spur t = some ev) ∧
      (ρ.zeit.zustand (t + 1)).lokal = (b.nach eintritt sPre).lokal ∧
      (ρ.zeit.zustand (t + 1)).status = (b.nach eintritt sPre).status ∧
      (ρ.zeit.zustand (t + 1)).kerne = (b.nach eintritt sPre).kerne ∧
      (ρ.zeit.zustand (t + 1)).fragen = [] ∧
      Zustand.regionLive (ρ.zeit.zustand (t + 1)) = Zustand.regionLive (b.nach eintritt sPre) := by
  have hReadyT : KannSchreiten ρ.hw t eintritt (ρ.zeit.zustand t) := by
    obtain ⟨kk, hg, hd, hs⟩ := hReady
    refine ⟨kk, hg, ?_, ?_⟩
    · rw [hEqK]
      exact hd
    · rw [hEqS]
      exact hs
  have headT : kopf textIndexCode (ρ.zeit.zustand t) eintritt = some b := by
    simp only [kopf, hEqS, hEqL]
    exact hHead
  have stepT : I.Schritt textIndexEinheit.einrichtung textIndexEinheit.system
      textIndexEinheit.katalog ρ.hw t
      (ρ.zeit.zustand t) (.kontext eintritt (), ⟨[], []⟩)
      (b.nach eintritt (ρ.zeit.zustand t)) :=
    .kontext hNoCrash hReadyT
      ⟨b, headT, (b.ideal_privat hPriv eintritt (ρ.zeit.zustand t) () [Semantik.plan] _).2 ⟨rfl, rfl⟩⟩
      (b.vollzug _ _ _ _)
  have hsome : ∃ ev, ρ.zeit.spur t = some ev := by
    cases hsp : ρ.zeit.spur t with
    | none =>
      exfalso
      obtain ⟨maxA, _⟩ := (hρ.2.2.2.2).1
      exact (maxA t hsp hFrei _ _ stepT).elim
    | some ev => exact ⟨ev, rfl⟩
  obtain ⟨ev, hev⟩ := hsome
  have htakt := ρ.zeit.takt t
  rw [hev] at htakt
  cases htakt with
  | schritt label step =>
    cases step with
    | kontext _ bereit regel aus =>
      rename_i u0 plan0 spur0 c0 w0 kab0
      by_cases heq : c0 = eintritt
      · subst heq
        obtain ⟨b', head', ideal'⟩ := regel
        have hb' : b' = b := by
          rw [txt_system_kopf, headT] at head'
          cases head'
          rfl
        subst b'
        obtain ⟨same, after⟩ :=
          (b.ideal_privat hPriv eintritt (ρ.zeit.zustand t) w0 [plan0] u0).1 ideal'
        cases same
        cases after
        have hakt : Semantik.plan.aktion = .intern := rfl
        obtain ⟨rahmen, _, sperren, v, fuehrt, _, hstate⟩ := aus
        rw [hakt] at fuehrt
        generalize hau : spur0.2 = au at fuehrt
        cases fuehrt with
        | intern =>
          refine ⟨⟨ev, hev⟩, ?_, ?_, ?_, ?_, ?_⟩
          · rw [hstate]
            simp only [Befehl.nach, hEqL, hEqR]
          · rw [hstate]
            simp only [Befehl.nach, hEqS]
          · rw [hstate]
            simp only [Befehl.nach, hEqK]
          · rw [hstate]
            simp only [Befehl.nach, hEqF, hFrPre]
          · rw [hstate, txt_regionLive_graph_irrelevant, Befehl.nach_regionLive, hEqR,
              ← Befehl.nach_regionLive]
      · exfalso
        obtain ⟨b', head', _⟩ := regel
        have hruht : (ρ.zeit.zustand t).status c0 = .ruht := by
          rw [hEqS]
          exact hStPre c0 heq
        rw [txt_system_kopf, txt_kopf_ruht hruht] at head'
        cases head'
    | antwort _ reply =>
      exfalso
      obtain ⟨offered, _, _, _⟩ := reply
      obtain ⟨q, hmem, _, _⟩ := offered.2.2.2.1
      rw [hEqF, hFrPre] at hmem
      exact (List.not_mem_nil hmem).elim
    | interrupt _ enters =>
      exfalso
      obtain ⟨kk, irq, cc, nmi, _, haus, _, _, _, _, _⟩ := enters
      obtain ⟨_, _, hoffer, _, _⟩ := haus
      rw [hNoInts _] at hoffer
      cases hoffer
    | absturz crash =>
      exfalso
      have hcon := crash.1.2
      rw [hNoCrash] at hcon
      exact Bool.false_ne_true hcon
  | wartet label _ _ =>
    cases label

/-- The text slot at the violation cut holds the empty text; the offset slot holds zero. -/
theorem sTxt2_temp0 (s : AussenStart) :
    ((sTxt2 s).lokal eintritt).temp 0 =
      some ⟨.text (sourceUtf8 []).size, TextValue.literal []⟩ := by
  rfl

theorem sTxt2_zahl1 (s : AussenStart) :
    ((sTxt2 s).lokal eintritt).zahl 1 =
      some (⟨0, 0, Zahl.literal 0⟩ : Ganzzahl) := by
  rfl

/-- The witness source unit is not accepted: its elaboration indexes an empty text at
    offset `0`, and the pinned guard row for `.index` refuses the canonical demand. -/
theorem textIndexUnit_nicht_akzeptiert :
    ¬ Annahme.Akzeptiert (einheitVon Katalog.Plattform.x86_64 textIndexUnit) := by
  obtain ⟨h, hwF, hardwareH, fairH⟩ :=
    katalog_nichtLeer textIndexEinheit.katalog (Plattform.katalog_wohlgeformt .x86_64)
  have imageH : textIndexEinheit.bild.gueltig textIndexEinheit.katalog.plattform.ziel :=
    Sicherheit.Laufkonstruktion.bild_gueltig
  obtain ⟨s, zul⟩ := zulStart_erfuellbar hardwareH imageH
  obtain ⟨k, assigned⟩ := zul.2.2.1 0 (Nat.zero_lt_succ _)
  obtain ⟨zeit, init⟩ := Zeitlauf.existiert
    (I.Schritt textIndexEinheit.einrichtung textIndexEinheit.system textIndexEinheit.katalog
      (txtHw h k))
    (I.start textIndexEinheit s).2
  have pauseOk : ∀ t z,
      KeinSchritt (I.Schritt textIndexEinheit.einrichtung textIndexEinheit.system
        textIndexEinheit.katalog (txtHw h k)) t z →
        ¬ AbsturzAngeboten textIndexEinheit.katalog (txtHw h k) t :=
    fun t z _ offer => Bool.false_ne_true offer.2
  let ρ : I.Lauf textIndexEinheit :=
    ⟨s, h, txtHw h k, zeit.erlaubePausen pauseOk, fun _ => none⟩
  have hρ : I.Laeufe textIndexEinheit ρ :=
    ⟨hardwareH, txt_konformHw h s zul k assigned, zul, init,
      zeit.erlaubePausen_maximal pauseOk _ (fun _ => rfl), fun _ _ h => nomatch h⟩
  have baseL : (ρ.zeit.zustand 0).lokal = (sTxt s).lokal := by
    have e : ρ.zeit.zustand 0 = (I.start textIndexEinheit s).2 := init
    rw [e]
    rfl
  have baseS : (ρ.zeit.zustand 0).status = (sTxt s).status := by
    have e : ρ.zeit.zustand 0 = (I.start textIndexEinheit s).2 := init
    rw [e]
    rfl
  have baseK : (ρ.zeit.zustand 0).kerne = (sTxt s).kerne := by
    have e : ρ.zeit.zustand 0 = (I.start textIndexEinheit s).2 := init
    rw [e]
    rfl
  have baseF : (ρ.zeit.zustand 0).fragen = (sTxt s).fragen := by
    have e : ρ.zeit.zustand 0 = (I.start textIndexEinheit s).2 := init
    rw [e]
    rfl
  have baseR : Zustand.regionLive (ρ.zeit.zustand 0) = Zustand.regionLive (sTxt s) := by
    have e : ρ.zeit.zustand 0 = (I.start textIndexEinheit s).2 := init
    rw [e]
    rfl
  have hwCrash : ∀ t, (ρ.hw.angebot t).crash = false := fun t => rfl
  have hwCore : ∀ t, (ρ.hw.angebot t).core = some k := fun t => rfl
  have hwInt : ∀ t, (ρ.hw.angebot t).interrupt = fun _ => false := fun t => rfl
  have hwInts : ∀ i, (ρ.hw.angebot i).interrupts = [] := fun i => rfl
  have hwDel : ∀ t, (ρ.hw.angebot t).delivery = fun _ => false := fun t => rfl
  have hwFrei : ∀ t, ρ.belegt t = none := fun t => rfl
  have hStPre : ∀ (sPre : Zustand) (c : Kontext), c ≠ eintritt →
      sPre.status = ((I.start textIndexEinheit s).2).status → sPre.status c = .ruht := by
    intro sPre c hne heq
    rw [heq]
    exact txt_status_other s c hne
  have readyAt : ∀ (sPre : Zustand) (t : Nat),
      sPre.kerne = ((I.start textIndexEinheit s).2).kerne →
      sPre.status = ((I.start textIndexEinheit s).2).status →
      KannSchreiten ρ.hw t eintritt sPre := by
    intro sPre t hK hS
    refine ⟨k, hwCore t, ?_, ?_⟩
    · rw [hK]
      exact txt_dispatch s k assigned
    · rw [hS]
      exact txt_status_entry s
  have st0 := txtForceStep ρ hρ 0 k (.textLiteral 0 []) (sTxt s)
    (hwCrash 0) (hwCore 0) (hwInt 0) hwInts (hwDel 0) (hwFrei 0)
    baseL baseS baseK baseF baseR
    (by rw [textIndexUnit_code]; rfl) (by first | exact Or.inl rfl | exact Or.inr rfl)
    (readyAt _ _ rfl rfl) (fun c hne => hStPre _ c hne rfl) (by rfl)
  have st1 := txtForceStep ρ hρ 1 k (.literal 1 0) (sTxt1 s)
    (hwCrash 1) (hwCore 1) (hwInt 1) hwInts (hwDel 1) (hwFrei 1)
    st0.2.1 st0.2.2.1 st0.2.2.2.1 st0.2.2.2.2.1 st0.2.2.2.2.2
    (by rw [textIndexUnit_code]; rfl) (by first | exact Or.inl rfl | exact Or.inr rfl)
    (readyAt _ _ rfl rfl) (fun c hne => hStPre _ c hne rfl) (by rfl)
  obtain ⟨ev1, hspur1⟩ := st1.1
  have hEqL2 : (ρ.zeit.zustand 2).lokal = (sTxt2 s).lokal := st1.2.1
  have hEqS2 : (ρ.zeit.zustand 2).status = (sTxt2 s).status := st1.2.2.1
  have hHead2 : kopf textIndexCode (sTxt2 s) eintritt =
      some (.textIndex 0 (sourceUtf8 []).size) := by
    rw [textIndexUnit_code]
    rfl
  have head2 : kopf textIndexCode (ρ.zeit.zustand 2) eintritt =
      some (.textIndex 0 (sourceUtf8 []).size) := by
    simp only [kopf, hEqS2, hEqL2]
    exact hHead2
  have htemp0 : ((ρ.zeit.zustand 2).lokal eintritt).temp 0 =
      some ⟨.text (sourceUtf8 []).size, TextValue.literal []⟩ := by
    rw [hEqL2]
    exact sTxt2_temp0 s
  have hzahl1 : ((ρ.zeit.zustand 2).lokal eintritt).zahl 1 =
      some (⟨0, 0, Zahl.literal 0⟩ : Ganzzahl) := by
    rw [hEqL2]
    exact sTxt2_zahl1 s
  have guard2 : (Befehl.textIndex 0 (sourceUtf8 []).size).guard
      ((ρ.zeit.zustand 2).lokal eintritt) = some ⟨.index, (0, 0)⟩ := by
    have hg := (textIndexBytes (sourceUtf8 []).size (TextValue.literal [])
      (⟨0, 0, Zahl.literal 0⟩ : Ganzzahl) ((ρ.zeit.zustand 2).lokal eintritt)
      htemp0 hzahl1).1
    simpa [TextValue.literal, sourceUtf8, Zahl.literal] using hg
  let cut : I.Schnitt textIndexEinheit ρ := ⟨2, Or.inr ⟨1, ev1, rfl, hspur1⟩⟩
  have need2 : (kanonischeVerwendung textIndexEinheit).bedarf ρ cut .index (0, 0) :=
    ⟨eintritt, .textIndex 0 (sourceUtf8 []).size, head2, guard2⟩
  intro ha
  have hbad := ha.2.2.1 ρ hρ cut .index (0, 0) need2
  simp only [waechterBedarf] at hbad
  exact (Nat.lt_irrefl 0) hbad

/-- The witness: a source unit whose elaboration is not accepted. -/
theorem nichtAkzeptierteEinheit :
    ∃ P t, ¬ Annahme.Akzeptiert (einheitVon P t) :=
  ⟨Katalog.Plattform.x86_64, textIndexUnit, textIndexUnit_nicht_akzeptiert⟩

/-- The deciding checker accepts the accepted empty unit, so the first half of its
    non-triviality is realised with a real decision. -/
theorem prueferEntscheidet_akzeptiertTrivial :
    ∃ P t, prueferEntscheidet.pruefe P t = true := by
  refine ⟨Katalog.Plattform.x86_64, trivialUnit, ?_⟩
  have hA := trivialUnit_akzeptiert Katalog.Plattform.x86_64
  have hL : (if Annahme.Lokal (einheitVon Katalog.Plattform.x86_64 trivialUnit) then true
      else false) = true := by
    split
    · rfl
    · rename_i h
      exact (h hA.1).elim
  have hK : (if Annahme.KlauselnWahr (einheitVon Katalog.Plattform.x86_64 trivialUnit) then true
      else false) = true := by
    split
    · rfl
    · rename_i h
      exact (h hA.2.1).elim
  have hW : (if Annahme.WaechterHalten (einheitVon Katalog.Plattform.x86_64 trivialUnit) then true
      else false) = true := by
    split
    · rfl
    · rename_i h
      exact (h hA.2.2).elim
  simp only [Pruefer.pruefe, prueferEntscheidet, hL, hK, hW]
  rfl

/-- The deciding checker is non-trivial in both directions: the witness closes the
    second half, which is exactly the premise that was missing. -/
theorem prueferEntscheidet_nichtTrivial : PrueferNichtTrivialAussage prueferEntscheidet := by
  constructor
  · exact prueferEntscheidet_akzeptiertTrivial
  · obtain ⟨P, t, hn⟩ := nichtAkzeptierteEinheit
    refine ⟨P, t, rfl, ?_, hn⟩
    simp only [Pruefer.pruefe, prueferEntscheidet]
    split
    · rename_i hL
      split
      · rename_i hK
        split
        · rename_i hW
          exact False.elim (hn ⟨hL, hK, hW⟩)
        · rfl
      · rfl
    · rfl

/-- The refused-unit leg of `ZielInhaltAussage` at the concrete frame: the text-index
    source unit has an elaboration that is not accepted. The three other legs have
    their own companions, the noninterference refutation remaining open there. -/
theorem ZielInhaltAussage.refutierbareEinheit :
    ∃ t : Ast.Unit, ¬ Annahme.Akzeptiert (einheitVon Katalog.Plattform.x86_64 t) :=
  ⟨textIndexUnit, textIndexUnit_nicht_akzeptiert⟩

end Gabbro.Core.Ziel.Korrektheit
