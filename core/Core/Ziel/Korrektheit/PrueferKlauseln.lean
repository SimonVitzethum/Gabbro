/-
   File:      core/Core/Ziel/Korrektheit/PrueferKlauseln.lean
   Subject:   SOUNDNESS and COMPLETENESS of the clause component of the checker, for the two
              pinned statements `PrueferKlauselnKorrektAussage` and
              `PrueferKlauselnVollstaendigAussage` of `Core/Ziel/Korrektheit/Pruefer.lean`.

   Both statements speak about units WITH the invariants they declare (`UnitMitInvarianten`):
   elaboration stores the declared predicates as denotations in the clause table
   (`programmMitInvarianten_klauseln`), so the statements are not vacuous — a checker that
   accepts a unit whose invariant is violated refutes soundness, and a checker that refuses
   everything refutes completeness.

   The decidable checker is `pruefeEinheit` on the elaborated fragment: the loader premise on
   the memory plan (`pruefeStart_richtig`), the crash-recovery premise (`pruefeNeustart_richtig`)
   and preservation per command. Its fragment (`klauselnFragment`) is the footprint check
   (`pruefeBefehlErhalt` over every command).

   SOUNDNESS (`klauselnWahr_aus_pruefeEinheit`) is proved by induction over `I.Laeufe`: the
   start cut carries the memory plan, pauses keep the state, command steps of frame-only heads
   go through the footprint rule (`pruefeEinheit_befehl` with `Praedikat.gilt_nach`, which
   uses `haelt_stabil` and `fussabdruck_treu`), every other non-crash step keeps the memory
   plan by the machine framing, and a crash resets it to the restart content. The memory
   content (`initial`) is the immutable plan, so the framing carries every step; the footprint
   rule is the command-level preservation the checker decides.

   COMPLETENESS (`prueferKlauselnVollstaendig_fuerDecidierbar`) goes the other way: on its
   footprint-stable fragment, `KlauselnWahr` over ideal runs supplies the loader premise
   (at the start cut of a constructed run) and the crash-recovery premise (at the post-crash
   cut of a constructed crash run); the per-command premise is the fragment. Runs exist on
   every platform (`katalog_nichtLeer`, `zulStart_erfuellbar`, `I.lauf_mit_hw`,
   `fairer_absturz_erfuellbar` with the approved persistence row).

   The witnesses close the statements: `echteInvariante` is a genuine non-trivial invariant
   the decidable checker accepts, `verletzteInvariante` is a violated invariant it refuses,
   and the refuse-everything checker violates completeness.
-/
module

public import Core.Ziel.Korrektheit.Pruefer
public import Core.Maschine.Start
public import Core.Katalog.Start
public import Core.Katalog.Erfuellbar
public import Core.Ast.Semantik.Runtime.Mehrkontext.System

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit

open Gabbro.Core
open Gabbro.Core.Ast.Semantik

/-- The decidable clause fragment with footprint stability: every command of the elaborated
    code preserves every declared predicate. -/
def klauselnFragment (p : Fragment) (ps : List Praedikat) : Bool :=
  p.code.all (pruefeBefehlErhalt ps)

theorem klauselnFragment_richtig (p : Fragment) (ps : List Praedikat) :
    klauselnFragment p ps = true ↔ ∀ b ∈ p.code, pruefeBefehlErhalt ps b = true := by
  simp only [klauselnFragment, List.all_eq_true]

/-- The machine framing keeps the memory plan across a FuehrtAus step: no protocol action
    touches the declared initial content. -/
theorem FuehrtAus_initial {L Ort Wert Raum Lok Grund Bedingung : Type} [DecidableEq L]
    {e : Maschine.Einrichtung L Ort Wert Raum Lok Grund Bedingung} {t : Nat}
    {c : Maschine.Kontext} {s u v : Maschine.Zustand L Ort Wert Raum Lok Grund}
    {akt : Maschine.Aktion L Bedingung} {ls : List (Speicher.Etikett Ort Wert)}
    {sp : List Katalog.Ereignis}
    (rahmen : Maschine.Zustandsrahmen s u) (h : Maschine.FuehrtAus e t c s u akt ls sp v) :
    v.initial = s.initial := by
  cases h with
  | intern => exact rahmen.initial
  | warte _ => exact rahmen.initial
  | sperre _ _ => exact rahmen.initial
  | frage _ => exact rahmen.initial
  | verbrauche _ => exact rahmen.initial
  | rueckkehr _ _ => exact rahmen.initial
  | starte _ => exact rahmen.initial
  | verbinde _ _ => exact rahmen.initial
  | beende _ => exact rahmen.initial
  | wechsle _ _ _ _ => exact rahmen.initial

/-- A command step of the elaborated code carries every declared predicate to the cut state:
    frame-only heads go through the footprint rule the checker decides, every other head
    through the machine framing. -/
theorem kontextSchritt_erhaelt (p : Fragment) (ps : List Praedikat)
    (ok : pruefeEinheit p ps = true)
    {e : Maschine.Einrichtung Nat Zelle Int Nat Rahmen PUnit.{1} PUnit.{1}}
    {c : Maschine.Kontext} {s u s' : Maschine.Zustand Nat Zelle Int Nat Rahmen PUnit.{1}}
    {w : PUnit.{1}} {plan : Maschine.SchrittPlan Nat Zelle Int PUnit.{1}}
    {spur : Maschine.SchrittSpur Zelle Int} {t : Nat} {b : Befehl}
    (hb : kopf p.code s c = some b)
    (hideal : b.ideal c s w [plan] u)
    (haus : Maschine.FuehrtSchrittAus e t c s u plan spur s')
    (q : Praedikat) (hmem : q ∈ ps) (hq : q.gilt s) : q.gilt s' := by
  have hcode : b ∈ p.code := kopf_mem hb
  have hbef : pruefeBefehlErhalt ps b = true := pruefeEinheit_befehl p ps b hcode ok
  obtain ⟨_, _, _, _, hfa, _, heq⟩ := haus
  rw [heq]
  have hvu : _ := FuehrtAus_initial haus.1 hfa
  rcases Classical.em b.Privat with hpriv | hpriv
  · have hu : u = b.nach c s := ((b.ideal_privat hpriv c s w [plan] u).mp hideal).2
    have hfoot : ∀ z ∈ q.beobachtet, z ∉ b.schreibFussabdruck :=
      fun z hz => pruefeBefehlErhalt_richtig ps b q hmem hbef z hz
    have hnach : q.gilt (b.nach c s) := Praedikat.gilt_nach q b c s hfoot hq
    rw [← hu] at hnach
    exact q.gilt_of_initial _ _ (haus.1.initial.trans hvu.symm) hnach
  · exact q.gilt_of_initial _ _ hvu.symm hq

/-- An arriving answer keeps the memory plan, hence every declared predicate. -/
theorem antwortSchritt_erhaelt
    {e : Maschine.Einrichtung Nat Zelle Int Nat Rahmen PUnit.{1} PUnit.{1}}
    {k : Katalog.Katalog} {run : Katalog.HwLauf} {t : Nat}
    {a : Katalog.AntwortEreignis}
    {s s' : Maschine.Zustand Nat Zelle Int Nat Rahmen PUnit.{1}}
    {spur : Maschine.SchrittSpur Zelle Int}
    (h : Maschine.AntwortSchritt e k run t a s spur s')
    (q : Praedikat) (hq : q.gilt s) : q.gilt s' := by
  obtain ⟨_, _, _, heq⟩ := h
  rw [heq]
  exact q.gilt_of_initial s _ rfl hq

/-- An interrupt delivery keeps the memory plan, hence every declared predicate. -/
theorem interruptSchritt_erhaelt
    {e : Maschine.Einrichtung Nat Zelle Int Nat Rahmen PUnit.{1} PUnit.{1}}
    {run : Katalog.HwLauf} {t : Nat} {id : Nat × Nat}
    {s s' : Maschine.Zustand Nat Zelle Int Nat Rahmen PUnit.{1}}
    {spur : Maschine.SchrittSpur Zelle Int}
    (h : Maschine.UnterbrechungsSchritt e run t id s spur s')
    (q : Praedikat) (hq : q.gilt s) : q.gilt s' := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, heq⟩ := h
  rw [heq]
  exact q.gilt_of_initial s _ rfl hq

/-- A crash resets the memory plan to the restart content, which the checker decided. -/
theorem absturzSchritt_startet (p : Fragment) (ps : List Praedikat)
    (ok : pruefeEinheit p ps = true)
    {e : Maschine.Einrichtung Nat Zelle Int Nat Rahmen PUnit.{1} PUnit.{1}}
    {k : Katalog.Katalog} {run : Katalog.HwLauf} {t : Nat}
    {s s' : Maschine.Zustand Nat Zelle Int Nat Rahmen PUnit.{1}}
    {spur : Maschine.SchrittSpur Zelle Int}
    (h : Maschine.AbsturzSchritt e.persistenzRegion e.wiederanlauf k run t s spur s')
    (hw0 : e.wiederanlauf.initial = fun _ _ => 0)
    (q : Praedikat) (hmem : q ∈ ps) : q.gilt s' := by
  have hns := h.neustart
  have hfun : s'.initial = (fun _ => 0) := by
    have h1 := hns.2.2.2.1
    rw [hw0] at h1
    exact h1
  have hq0 := pruefeEinheit_neustart p ps ok q hmem
  rw [← hfun] at hq0
  exact hq0

/-- Every declared predicate holds at every time of every ideal run of a checker-accepted
    elaborated unit. Induction over time: the start cut carries the memory plan, pauses keep
    the state, command steps go through `kontextSchritt_erhaelt`, answers and deliveries
    keep the memory plan, and a crash resets it to the restart content. -/
theorem deklariert_gilt_immer (P : Katalog.Plattform) (u : UnitMitInvarianten)
    (ok : pruefeEinheit (programmMitInvarianten u) u.invarianten = true)
    (ρ : Maschine.I.Lauf (elaborierenMitInvarianten P u))
    (hρ : Maschine.I.Laeufe _ ρ) (t : Nat) (q : Praedikat)
    (hmem : q ∈ u.invarianten) : q.gilt (ρ.zeit.zustand t) := by
  induction t with
  | zero =>
    rw [hρ.2.2.2.1]
    show q.haelt (programmMitInvarianten u).speicher.initial
    exact pruefeEinheit_start _ _ ok q hmem
  | succ t ih =>
    cases ρ.zeit.takt t with
    | wartet label _ _ =>
      rw [(ρ.zeit.wartet label).1]
      exact ih
    | schritt _ step =>
      cases step with
      | kontext _ _ hregel haus =>
        obtain ⟨b, hb_head, hb_ideal⟩ := hregel
        exact kontextSchritt_erhaelt _ _ ok hb_head hb_ideal haus q hmem ih
      | antwort _ h =>
        exact antwortSchritt_erhaelt h q ih
      | interrupt _ h =>
        exact interruptSchritt_erhaelt h q ih
      | absturz h =>
        have hw0 : (elaborierenMitInvarianten P u).einrichtung.wiederanlauf.initial =
            fun _ _ => 0 := rfl
        exact absturzSchritt_startet _ _ ok h hw0 q hmem

/-- SOUNDNESS over units with declared invariants: a checker-accepted elaborated unit
    satisfies `KlauselnWahr` — requires and ensures tables are empty, and every declared
    invariant holds at every `I` cut of every `I` run. -/
theorem klauselnWahr_aus_pruefeEinheit (P : Katalog.Plattform) (u : UnitMitInvarianten)
    (ok : pruefeEinheit (programmMitInvarianten u) u.invarianten = true) :
    Annahme.KlauselnWahr (elaborierenMitInvarianten P u) := by
  intro ρ hρ
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    cases hp
  · intro t p hp
    have hlist : (elaborierenMitInvarianten P u).quelltabellen.klauseln.invariant =
        u.invarianten.map Praedikat.gilt := rfl
    rw [hlist] at hp
    obtain ⟨q, hqmem, rfl⟩ := List.mem_map.mp hp
    exact deklariert_gilt_immer P u ok ρ hρ t.val q hqmem
  · intro t _ p hp
    cases hp

/-- A checker whose clause component is the decidable decision `pruefeEinheit` and whose
    fragment is the footprint check. -/
def prueferKlauselnDecidierbar : Pruefer where
  pruefeLokal := fun _ _ => true
  pruefeKlauseln := fun _ u => pruefeEinheit (programmMitInvarianten u) u.invarianten
  pruefeWaechter := fun _ _ => true
  fragmentLokal := fun _ _ => true
  fragmentKlauseln := fun _ u => klauselnFragment (programmMitInvarianten u) u.invarianten
  fragmentWaechter := fun _ _ => true

/-- SOUNDNESS for the decidable checker. -/
theorem prueferKlauselnKorrekt_fuerDecidierbar :
    PrueferKlauselnKorrektAussage prueferKlauselnDecidierbar := by
  intro P u h
  change pruefeEinheit (programmMitInvarianten u) u.invarianten = true at h
  exact klauselnWahr_aus_pruefeEinheit P u h

/-- Every platform selects the persistence row. Crash runs exist everywhere. -/
theorem plattform_enthaelt_persistence (P : Katalog.Plattform) :
    P.katalog.enthaelt .persistence := by
  cases P <;> decide

/-- The elaborated image is the fixed loader image on the selected target, hence valid. -/
theorem elaboriert_bild_gueltig (P : Katalog.Plattform) (u : UnitMitInvarianten) :
    (elaborierenMitInvarianten P u).bild.gueltig
      (elaborierenMitInvarianten P u).katalog.plattform.ziel := by
  change Ast.Semantik.bild.gueltig P.ziel
  rcases Katalog.ziele_gut P with ⟨_, _, _, _, _, _, _, _, _, helf⟩
  refine ⟨helf, ?_, ?_⟩
  · intro a byte present
    change (if a = 0 then some 0 else none) = some byte at present
    split at present
    · subst a
      exact Nat.pow_pos (Nat.zero_lt_succ _)
    · cases present
  · intro entry mem
    have entryZero : entry = 0 := List.mem_singleton.mp mem
    subst entry
    exact ⟨0, rfl⟩

/-- Every elaborated unit with invariants has an ideal run. -/
theorem elaboriert_idealLauf (P : Katalog.Plattform) (u : UnitMitInvarianten) :
    ∃ ρ : Maschine.I.Lauf (elaborierenMitInvarianten P u), Maschine.I.Laeufe _ ρ := by
  obtain ⟨_, _, _, fair⟩ := Katalog.katalog_nichtLeer _ (Katalog.Plattform.katalog_wohlgeformt P)
  have hbild : (elaborierenMitInvarianten P u).bild.gueltig
      (elaborierenMitInvarianten P u).katalog.plattform.ziel :=
    elaboriert_bild_gueltig P u
  obtain ⟨s, hstart⟩ := Katalog.zulStart_erfuellbar fair.hardware hbild
  obtain ⟨ρ, hρ, _, _⟩ := Maschine.I.lauf_mit_hw (E := elaborierenMitInvarianten P u)
    fair.hardware hstart fair.konform
  exact ⟨ρ, hρ⟩

/-- Every elaborated unit with invariants has an ideal run that crashes at the first cut. -/
theorem elaboriert_absturzLauf (P : Katalog.Plattform) (u : UnitMitInvarianten) :
    ∃ ρ : Maschine.I.Lauf (elaborierenMitInvarianten P u),
      Maschine.I.Laeufe _ ρ ∧ ρ.zeit.spur 0 = some (.absturz, Maschine.absturzSpur) ∧
        Maschine.AbsturzSchritt (elaborierenMitInvarianten P u).einrichtung.persistenzRegion
          (elaborierenMitInvarianten P u).einrichtung.wiederanlauf
          (elaborierenMitInvarianten P u).katalog ρ.hw 0 (ρ.zeit.zustand 0)
          Maschine.absturzSpur (ρ.zeit.zustand 1) := by
  obtain ⟨_, _, _, fair⟩ := Katalog.katalog_nichtLeer _ (Katalog.Plattform.katalog_wohlgeformt P)
  have hbild : (elaborierenMitInvarianten P u).bild.gueltig
      (elaborierenMitInvarianten P u).katalog.plattform.ziel :=
    elaboriert_bild_gueltig P u
  obtain ⟨s, hstart⟩ := Katalog.zulStart_erfuellbar fair.hardware hbild
  obtain ⟨crashHw, fairCrash, offer⟩ :=
    Maschine.fairer_absturz_erfuellbar fair (plattform_enthaelt_persistence P) 0
  obtain ⟨ρ, hρ, _, hwEq⟩ := Maschine.I.lauf_mit_hw (E := elaborierenMitInvarianten P u)
    fairCrash.hardware hstart fairCrash.konform
  have offer' : Maschine.AbsturzAngeboten P.katalog ρ.hw 0 := by
    rw [hwEq]
    exact offer
  obtain ⟨hspur, hstep⟩ := Maschine.I.absturz_am_schnitt _ offer'
  exact ⟨ρ, hρ, hspur, hstep⟩

/-- COMPLETENESS for the decidable checker on its footprint-stable fragment: `KlauselnWahr`
    over ideal runs supplies the loader premise at the start cut and the crash-recovery
    premise at the post-crash cut; the per-command premise is the fragment. -/
theorem prueferKlauselnVollstaendig_fuerDecidierbar :
    PrueferKlauselnVollstaendigAussage prueferKlauselnDecidierbar := by
  intro P u hfrag hWahr
  change pruefeEinheit (programmMitInvarianten u) u.invarianten = true
  simp only [pruefeEinheit, Bool.and_eq_true]
  have hcode := (klauselnFragment_richtig _ _).mp hfrag
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [pruefeStart_richtig]
    intro q hq
    obtain ⟨ρ, hρ⟩ := elaboriert_idealLauf P u
    have hcut : ∀ p ∈ u.invarianten.map Praedikat.gilt, p (ρ.zeit.zustand 0) :=
      (hWahr ρ hρ).2.1 ⟨0, Or.inl rfl⟩
    have hmem : Praedikat.gilt q ∈ u.invarianten.map Praedikat.gilt :=
      List.mem_map.mpr ⟨q, hq, rfl⟩
    have hq0 := hcut _ hmem
    rw [hρ.2.2.2.1] at hq0
    exact hq0
  · rw [pruefeNeustart_richtig]
    intro q hq
    obtain ⟨ρ, hρ, hspur, hstep⟩ := elaboriert_absturzLauf P u
    have hcut : ∀ p ∈ u.invarianten.map Praedikat.gilt, p (ρ.zeit.zustand 1) :=
      (hWahr ρ hρ).2.1 ⟨1, Or.inr ⟨0, (_, _), rfl, hspur⟩⟩
    have hmem : Praedikat.gilt q ∈ u.invarianten.map Praedikat.gilt :=
      List.mem_map.mpr ⟨q, hq, rfl⟩
    have hq1 := hcut _ hmem
    have hw0 : (elaborierenMitInvarianten P u).einrichtung.wiederanlauf.initial =
        fun _ _ => 0 := rfl
    have hzero : (ρ.zeit.zustand 1).initial = (fun _ => 0) := by
      have h1 := hstep.neustart.2.2.2.1
      rw [hw0] at h1
      exact h1
    change q.haelt (ρ.zeit.zustand 1).initial at hq1
    rw [hzero] at hq1
    exact hq1
  · exact List.all_eq_true.mpr hcode

/-- A genuine declared invariant: the region cell starts at `0`. -/
def echteInvariante : UnitMitInvarianten :=
  ⟨⟨[], .done⟩, [Praedikat.vgl .eq (.zelle (.region 0 0)) (.konst 0)]⟩

/-- The decidable checker accepts the genuine invariant. -/
theorem echteInvariante_akzeptiert (P : Katalog.Plattform) :
    prueferKlauselnDecidierbar.pruefeKlauseln P echteInvariante = true := rfl

/-- The checker accepts a unit with a genuine non-trivial invariant. -/
theorem prueferKlauselnDecidierbar_erfuellbar :
    ∃ (P : Katalog.Plattform) (u : UnitMitInvarianten),
      u.invarianten ≠ [] ∧ prueferKlauselnDecidierbar.pruefeKlauseln P u = true := by
  refine ⟨.x86_64, echteInvariante, by decide, echteInvariante_akzeptiert _⟩

/-- A violated invariant: the region cell starts at `0`, not `5`. -/
def verletzteInvariante : UnitMitInvarianten :=
  ⟨⟨[], .done⟩, [Praedikat.vgl .eq (.zelle (.region 0 0)) (.konst 5)]⟩

/-- The decidable checker refuses the violated invariant. -/
theorem verletzteInvariante_abgelehnt (P : Katalog.Plattform) :
    prueferKlauselnDecidierbar.pruefeKlauseln P verletzteInvariante = false := rfl

/-- The violated invariant genuinely fails over the ideal run: the start cut holds `0`. -/
theorem verletzteInvariante_verletzt (P : Katalog.Plattform) :
    ¬ Annahme.KlauselnWahr (elaborierenMitInvarianten P verletzteInvariante) := by
  intro h
  obtain ⟨ρ, hρ⟩ := elaboriert_idealLauf P verletzteInvariante
  have hcut : ∀ p ∈ verletzteInvariante.invarianten.map Praedikat.gilt,
      p (ρ.zeit.zustand 0) :=
    (h ρ hρ).2.1 ⟨0, Or.inl rfl⟩
  have hmem : Praedikat.gilt (Praedikat.vgl .eq (.zelle (.region 0 0)) (.konst 5)) ∈
      verletzteInvariante.invarianten.map Praedikat.gilt :=
    List.mem_map.mpr
      ⟨Praedikat.vgl .eq (.zelle (.region 0 0)) (.konst 5), List.mem_cons.mpr (Or.inl rfl), rfl⟩
  have hq := hcut _ hmem
  rw [hρ.2.2.2.1] at hq
  have hq2 : ((Maschine.I.start _ ρ.start).2).initial (.region 0 0) = 5 := hq
  have hzero : ((Maschine.I.start (elaborierenMitInvarianten P verletzteInvariante)
      ρ.start).2).initial (.region 0 0) = 0 := rfl
  rw [hzero] at hq2
  omega

/-- The checker refuses a unit whose invariant is violated. -/
theorem prueferKlauselnDecidierbar_nichtTrivial :
    ∃ (P : Katalog.Plattform) (u : UnitMitInvarianten),
      prueferKlauselnDecidierbar.pruefeKlauseln P u = false ∧
        ¬ Annahme.KlauselnWahr (elaborierenMitInvarianten P u) := by
  exact ⟨.x86_64, verletzteInvariante, verletzteInvariante_abgelehnt _,
    verletzteInvariante_verletzt _⟩

/-- The checker that refuses every unit and whose fragment is total. -/
def prueferKlauselnVerweigert : Pruefer where
  pruefeLokal := fun _ _ => false
  pruefeKlauseln := fun _ _ => false
  pruefeWaechter := fun _ _ => false
  fragmentLokal := fun _ _ => true
  fragmentKlauseln := fun _ _ => true
  fragmentWaechter := fun _ _ => true

/-- COMPLETENESS is not a property of every checker: the refuse-everything checker violates
    it on the accepted genuine unit. -/
theorem prueferKlauselnVollstaendig_nichtUniversal :
    ∃ C : Pruefer, ¬ PrueferKlauselnVollstaendigAussage C := by
  refine ⟨prueferKlauselnVerweigert, ?_⟩
  intro h
  have hfrag : prueferKlauselnVerweigert.fragmentKlauseln Katalog.Plattform.x86_64
      echteInvariante = true := rfl
  have hwahr : Annahme.KlauselnWahr
      (elaborierenMitInvarianten Katalog.Plattform.x86_64 echteInvariante) :=
    klauselnWahr_aus_pruefeEinheit Katalog.Plattform.x86_64 echteInvariante
      (echteInvariante_akzeptiert Katalog.Plattform.x86_64)
  have hfalse := h Katalog.Plattform.x86_64 echteInvariante hfrag hwahr
  cases hfalse

end Gabbro.Core.Ziel.Korrektheit
