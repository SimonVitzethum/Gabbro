/-
  File:      core/Core/Ast/Semantik/Runtime/Klasse/Beweise/SpeicherPrivat.lean
  Subject:   THE MEMORY LEG OF THE PRIVATE CLASSES (MK-03, MK-20). A step of `lokal`, `ruf`, `frage`
             or one of the four interrupt-control classes records no
             memory access that needs a handle: a private step runs the internal protocol action, and a
             question adds only the outside event of `FuehrtAus.frage`, whose memory label is `.aussen`.
             Both shapes leave the ledger and the rights of the state unchanged, so `ZugriffGebucht` is
             vacuous, `NeueWirkungen` holds with `neu = []` and `FreigabenGueltig` has no release to check.
             The statement is pinned through `KlassenAussagen`; this file only proves it for the classes
             named in the brief (the lock class is excluded in `Klasse/Sicherheit`).
-/
module

public import Core.Ast.Semantik.Runtime.Klasse.Pflichten
public import Core.Sicherheit.KatalogSchritt
public import Core.Ast.Semantik.Runtime.Klasse.Beweise.Faden

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog
open Gabbro.Core.Sicherheit

/-- An internal step of a private form has the empty trace: its protocol action is `.intern`, so it
     appends no events and no memory labels, and the ledger and the rights it leaves are those of the
     pre-state (the form changes only the acting frame, and `FuehrtAus.intern` changes nothing). -/
private theorem intern_spur {ι : Type} (E : Sicherheit.Einheit Nat Zelle Int Nat Rahmen PUnit PUnit PUnit ι)
    {t : Nat} {c : Kontext} {vor zwischen nach : Zustand} {plan : Plan} {spur : SchrittSpur Zelle Int}
    (aus : FuehrtSchrittAus E.maschine.einrichtung t c vor zwischen plan spur nach)
    (buchungZw : zwischen.buchung = vor.buchung) (rechteZw : zwischen.rechte = vor.rechte)
    (planEq : plan = Semantik.plan) :
    spur = ⟨[], []⟩ ∧ nach.buchung = vor.buchung ∧ nach.rechte = vor.rechte := by
  subst plan
  obtain ⟨_, _, _, v, aktion, folge, zustand⟩ := aus
  rcases spur with ⟨events, outside⟩
  cases aktion
  simp only [Semantik.plan, List.nil_append, schreibEreignisse, List.filter_nil, List.map_nil] at folge
  have leer : events = [] := by
    generalize hg : nach.graph = graph at folge
    cases folge
    rfl
  subst events
  refine ⟨rfl, ?_, ?_⟩
  · rw [zustand]
    exact buchungZw
  · rw [zustand]
    exact rechteZw

/-- A still step of a form has the empty trace: its protocol action records no lock and no outside
    event, so the memory labels are empty whatever the plan names, and the ledger and the rights it
    leaves are those of the pre-state. -/
private theorem still_spur {ι : Type} (E : Sicherheit.Einheit Nat Zelle Int Nat Rahmen PUnit PUnit PUnit ι)
    {t : Nat} {c : Kontext} {vor zwischen nach : Zustand} {plan : Plan} {spur : SchrittSpur Zelle Int}
    (aus : FuehrtSchrittAus E.maschine.einrichtung t c vor zwischen plan spur nach)
    (buchungZw : zwischen.buchung = vor.buchung) (rechteZw : zwischen.rechte = vor.rechte)
    (hlesen : plan.lesen = []) (hfuss : plan.fuss = []) (hakt : plan.aktion.Still) :
    spur = ⟨[], []⟩ ∧ nach.buchung = vor.buchung ∧ nach.rechte = vor.rechte := by
  obtain ⟨_, _, _, v, aktion, folge, zustand⟩ := aus
  obtain ⟨hs, he, _, _, hr, _, _, _, _, _, _, _, _, _, _, _, hb⟩ := aktion.still_erhaelt hakt
  rcases spur with ⟨events, outside⟩
  have outsideNil : outside = [] := he
  subst outsideNil
  rw [hs, hlesen, hfuss] at folge
  simp only [List.nil_append, schreibEreignisse, List.filter_nil, List.map_nil, List.append_nil,
    List.map_nil] at folge
  have leer : events = [] := by
    generalize hg : nach.graph = graph at folge
    cases folge
    rfl
  subst events
  refine ⟨rfl, ?_, ?_⟩
  · rw [zustand]
    show v.buchung = vor.buchung
    exact hb.trans buchungZw
  · rw [zustand]
    show v.rechte = vor.rechte
    exact hr.trans rechteZw

/-- Finish the memory leg for the two trace shapes a private step can have: no events, or the one
    outside event of a question (whose memory label is `.aussen`, hence no booking obligation). -/
private theorem privat_fertig {ι : Type} (E : Sicherheit.Einheit Nat Zelle Int Nat Rahmen PUnit PUnit PUnit ι)
    {hw : HwLauf} {t : Nat} {c : Kontext} {vor nach : Zustand} {spur : SchrittSpur Zelle Int}
    (buchung : nach.buchung = vor.buchung) (rechte : nach.rechte = vor.rechte)
    (form : spur = ⟨[], []⟩ ∨ ∃ ev : FrageEreignis,
      spur = ⟨[(.kontext c, aussenEtikett E.maschine.einrichtung (.frage ev))], [.frage ev]⟩) :
    Sicherheit.ZugriffGebucht vor nach spur ∧
      ∃ neu, Sicherheit.NeueWirkungen vor nach spur neu ∧
        Sicherheit.FreigabenGueltig vor nach hw t spur neu := by
  rcases form with leer | ⟨ev, gleich⟩
  · subst spur
    refine ⟨?_, ?_⟩
    · intro i actor l recorded
      simp only [List.getElem?_nil] at recorded
      cases recorded
    · refine ⟨[], wirkungsloser_schritt ?_ buchung rechte⟩
      intro crash
      change Ereignis.persistenz .crash ∈ ([] : List Ereignis) at crash
      cases crash
  · subst spur
    refine ⟨?_, ?_⟩
    · intro i actor l recorded nichtAussen
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at recorded
        rcases recorded with ⟨_, rfl⟩
        exact (nichtAussen rfl).elim
      | succ i =>
        simp only [List.getElem?_cons_succ, List.getElem?_nil] at recorded
        cases recorded
    · refine ⟨[], wirkungsloser_schritt ?_ buchung rechte⟩
      intro crash
      change Ereignis.persistenz .crash ∈ ([.frage ev] : List Ereignis) at crash
      rw [List.mem_singleton] at crash
      cases crash

/-- **The memory leg of the private classes** (`KlassenSpeicherbeinAussage`). The statement is fixed
      in `Klasse/Sicherheit` and pinned through `KlassenAussagen`; the proof only unfolds the class rule
      and reads the trace of `FuehrtSchrittAus`. -/
theorem klassenSpeicherbein_privat (k : Wirkungsklasse)
    (hk : k = .lokal ∨ k = .ruf ∨ k = .frage ∨ k = .verbrauche ∨ (∃ m, k = .zaun m) ∨
      k = .maskiere ∨ k = .prioritaet ∨ k = .sendeUnterbrechung ∨ k = .leiteLeitung) :
    KlassenSpeicherbeinAussage k := by
  intro _ ι E f F hkF emb hw t c w vor zwischen nach plan spur kopf impl aus
  have implIdeal : F.ideal c vor w [plan] zwischen := by
    change (F.regel).impl c vor w [plan] zwischen
    rw [← emb.regel]
    exact impl
  rcases hk with rfl | rfl | rfl | rfl | ⟨m, rfl⟩ | rfl | rfl | rfl | rfl
  · obtain ⟨kF, o, ue⟩ := F
    change kF = .lokal at hkF
    subst kF
    simp only [Schrittform.ideal] at implIdeal
    obtain ⟨same, after⟩ := implIdeal
    subst zwischen
    have planEq : plan = Semantik.plan := (List.cons.inj same).1
    obtain ⟨form, buchung, rechte⟩ :=
      intern_spur E (t := t) (c := c) (vor := vor) aus rfl rfl planEq
    exact privat_fertig E (hw := hw) (t := t) (c := c) buchung rechte (Or.inl form)
  · obtain ⟨kF, o, ue⟩ := F
    change kF = .ruf at hkF
    subst kF
    simp only [Schrittform.ideal] at implIdeal
    obtain ⟨same, after⟩ := implIdeal
    subst zwischen
    have planEq : plan = Semantik.plan := (List.cons.inj same).1
    obtain ⟨form, buchung, rechte⟩ :=
      intern_spur E (t := t) (c := c) (vor := vor) aus rfl rfl planEq
    exact privat_fertig E (hw := hw) (t := t) (c := c) buchung rechte (Or.inl form)
  · obtain ⟨kF, o, ue⟩ := F
    change kF = .frage at hkF
    subst kF
    simp only [Schrittform.ideal, Schrittform.zugriffsschritt] at implIdeal
    rcases implIdeal with ⟨_, same, after⟩ | ⟨_, v, _, same, after⟩
    · subst zwischen
      have planEq : plan = Semantik.plan := (List.cons.inj same).1
      obtain ⟨form, buchung, rechte⟩ :=
        intern_spur E (t := t) (c := c) (vor := vor) aus rfl rfl planEq
      exact privat_fertig E (hw := hw) (t := t) (c := c) buchung rechte (Or.inl form)
    · subst zwischen
      have planEq : plan = (⟨.frage, o, ue⟩ : Schrittform).plan (vor.lokal c) v :=
        (List.cons.inj same).1
      simp only [Schrittform.plan, Wirkungsklasse.plan] at planEq
      cases hfrage : (o (vor.lokal c)).frage with
      | none =>
        simp only [Operand.fragePlan, hfrage] at planEq
        obtain ⟨form, buchung, rechte⟩ :=
          intern_spur E (t := t) (c := c) (vor := vor) aus rfl rfl planEq
        exact privat_fertig E (hw := hw) (t := t) (c := c) buchung rechte (Or.inl form)
      | some q =>
        simp only [Operand.fragePlan, hfrage] at planEq
        subst plan
        obtain ⟨_, _, _, vState, aktion, folge, zustand⟩ := aus
        rcases spur with ⟨events, outside⟩
        cases aktion
        simp only [List.nil_append, schreibEreignisse, List.filter_nil, List.map_cons, List.map_nil] at folge
        have eventsEq : events =
            [(.kontext c, aussenEtikett E.maschine.einrichtung (.frage (vor.stelleFrage t c q)))] := by
          exact (aussen_label_speicher (actor := .kontext c) rfl folge).1
        subst events
        refine privat_fertig E (hw := hw) (t := t) (c := c) ?_ ?_
          (Or.inr ⟨vor.stelleFrage t c q, rfl⟩)
        · rw [zustand]
          rfl
        · rw [zustand]
          rfl
  · obtain ⟨kF, o, ue⟩ := F
    change kF = .verbrauche at hkF
    subst kF
    simp only [Schrittform.ideal] at implIdeal
    obtain ⟨same, after⟩ := implIdeal
    subst zwischen
    have planEq : plan = Semantik.plan := (List.cons.inj same).1
    have hbuchung : (Schrittform.verbraucheNach ⟨.verbrauche, o, ue⟩ c vor).buchung =
        vor.buchung :=
      Schrittform.verbraucheNach_buchung _ _ _
    have hrechte : (Schrittform.verbraucheNach ⟨.verbrauche, o, ue⟩ c vor).rechte =
        vor.rechte :=
      Schrittform.verbraucheNach_rechte _ _ _
    obtain ⟨form, buchung, rechte⟩ :=
      intern_spur E (t := t) (c := c) (vor := vor) aus hbuchung hrechte planEq
    exact privat_fertig E (hw := hw) (t := t) (c := c) buchung rechte (Or.inl form)
  · obtain ⟨kF, o, ue⟩ := F
    change kF = .zaun m at hkF
    subst kF
    simp only [Schrittform.ideal, Schrittform.zugriffsschritt] at implIdeal
    rcases implIdeal with ⟨_, same, after⟩ | ⟨_, v, _, same, after⟩
    · subst zwischen
      have planEq : plan = Semantik.plan := (List.cons.inj same).1
      obtain ⟨form, buchung, rechte⟩ :=
        intern_spur E (t := t) (c := c) (vor := vor) aus rfl rfl planEq
      exact privat_fertig E (hw := hw) (t := t) (c := c) buchung rechte (Or.inl form)
    · subst zwischen
      have planEq : plan = Semantik.plan := by
        have hpe := (List.cons.inj same).1
        rw [hpe]
        rfl
      obtain ⟨form, buchung, rechte⟩ :=
        intern_spur E (t := t) (c := c) (vor := vor) aus rfl rfl planEq
      exact privat_fertig E (hw := hw) (t := t) (c := c) buchung rechte (Or.inl form)
  · obtain ⟨kF, o, ue⟩ := F
    change kF = .maskiere at hkF
    subst kF
    simp only [Schrittform.ideal] at implIdeal
    obtain ⟨same, after⟩ := implIdeal
    subst zwischen
    have hplan : plan = Schrittform.plan ⟨.maskiere, o, ue⟩ (vor.lokal c) 0 :=
      (List.cons.inj same).1
    have hlesen : plan.lesen = [] := by rw [hplan]; rfl
    have hfuss : plan.fuss = [] := by rw [hplan]; rfl
    have hakt : plan.aktion.Still := by rw [hplan]; trivial
    obtain ⟨form, buchung, rechte⟩ :=
      still_spur E (t := t) (c := c) (vor := vor) aus rfl rfl hlesen hfuss hakt
    exact privat_fertig E (hw := hw) (t := t) (c := c) buchung rechte (Or.inl form)
  · obtain ⟨kF, o, ue⟩ := F
    change kF = .prioritaet at hkF
    subst kF
    simp only [Schrittform.ideal] at implIdeal
    obtain ⟨same, after⟩ := implIdeal
    subst zwischen
    have hplan : plan = Schrittform.plan ⟨.prioritaet, o, ue⟩ (vor.lokal c) 0 :=
      (List.cons.inj same).1
    have hlesen : plan.lesen = [] := by rw [hplan]; rfl
    have hfuss : plan.fuss = [] := by rw [hplan]; rfl
    have hakt : plan.aktion.Still := by rw [hplan]; trivial
    obtain ⟨form, buchung, rechte⟩ :=
      still_spur E (t := t) (c := c) (vor := vor) aus rfl rfl hlesen hfuss hakt
    exact privat_fertig E (hw := hw) (t := t) (c := c) buchung rechte (Or.inl form)
  · obtain ⟨kF, o, ue⟩ := F
    change kF = .sendeUnterbrechung at hkF
    subst kF
    simp only [Schrittform.ideal] at implIdeal
    obtain ⟨same, after⟩ := implIdeal
    subst zwischen
    have hplan : plan = Schrittform.plan ⟨.sendeUnterbrechung, o, ue⟩ (vor.lokal c) 0 :=
      (List.cons.inj same).1
    have hlesen : plan.lesen = [] := by rw [hplan]; rfl
    have hfuss : plan.fuss = [] := by rw [hplan]; rfl
    have hakt : plan.aktion.Still := by rw [hplan]; trivial
    obtain ⟨form, buchung, rechte⟩ :=
      still_spur E (t := t) (c := c) (vor := vor) aus rfl rfl hlesen hfuss hakt
    exact privat_fertig E (hw := hw) (t := t) (c := c) buchung rechte (Or.inl form)
  · obtain ⟨kF, o, ue⟩ := F
    change kF = .leiteLeitung at hkF
    subst kF
    simp only [Schrittform.ideal] at implIdeal
    obtain ⟨same, after⟩ := implIdeal
    subst zwischen
    have hplan : plan = Schrittform.plan ⟨.leiteLeitung, o, ue⟩ (vor.lokal c) 0 :=
      (List.cons.inj same).1
    have hlesen : plan.lesen = [] := by rw [hplan]; rfl
    have hfuss : plan.fuss = [] := by rw [hplan]; rfl
    have hakt : plan.aktion.Still := by rw [hplan]; trivial
    obtain ⟨form, buchung, rechte⟩ :=
      still_spur E (t := t) (c := c) (vor := vor) aus rfl rfl hlesen hfuss hakt
    exact privat_fertig E (hw := hw) (t := t) (c := c) buchung rechte (Or.inl form)

/-- A step with the empty trace and no new effect releases nothing and books no access, whatever it does to the
    holdings of the ledger. -/
private theorem faden_fertig {ι : Type}
    (E : Sicherheit.Einheit Nat Zelle Int Nat Rahmen PUnit PUnit PUnit ι)
    {hw : HwLauf} {t : Nat} {vor nach : Zustand} {spur : SchrittSpur Zelle Int}
    (wirkungen : nach.buchung.wirkungen = vor.buchung.wirkungen) (rechte : nach.rechte = vor.rechte)
    (form : spur = ⟨[], []⟩) :
    Sicherheit.ZugriffGebucht vor nach spur ∧
      ∃ neu, Sicherheit.NeueWirkungen vor nach spur neu ∧
        Sicherheit.FreigabenGueltig vor nach hw t spur neu := by
  subst form
  refine ⟨?_, ?_⟩
  · intro i actor l recorded
    simp only [List.getElem?_nil] at recorded
    cases recorded
  · refine ⟨[], wirkungsloser_schritt_wirkungen ?_ wirkungen rechte⟩
    intro crash
    change Ereignis.persistenz .crash ∈ ([] : List Ereignis) at crash
    cases crash

/-- **The memory leg of the lifecycle classes** (`KlassenSpeicherbeinAussage`). A lifecycle step records no memory
    access and no outside event (its plan has no read and no footprint, its protocol action is still), adds no
    effect and leaves the rights alone, so nothing is booked and nothing is released. The hand-over of authority
    moves the holdings of the ledger and nothing else. -/
theorem klassenSpeicherbein_faden (k : Wirkungsklasse)
    (hk : k = .starte ∨ k = .beende ∨ k = .verbinde ∨ k = .wechsle) : KlassenSpeicherbeinAussage k := by
  intro _ ι E f F hkF emb hw t c w vor zwischen nach plan spur kopf impl aus
  have lz : F.Lebenszyklus := by
    rw [Schrittform.Lebenszyklus, hkF]
    exact hk
  have implIdeal : F.ideal c vor w [plan] zwischen := by
    change (F.regel).impl c vor w [plan] zwischen
    rw [← emb.regel]
    exact impl
  obtain ⟨hn, still, lesen, fuss⟩ := Schrittform.lebenszyklus_ideal lz implIdeal
  obtain ⟨_, _, _, v, aktion, folge, zustand⟩ := aus
  obtain ⟨hs, he, _, _, hr, _, _, _, _, _, _, _, _, _, _, _, hb⟩ := aktion.still_erhaelt still
  rcases spur with ⟨events, outside⟩
  have outsideNil : outside = [] := he
  subst outsideNil
  rw [hs, lesen, fuss] at folge
  simp only [List.nil_append, schreibEreignisse, List.filter_nil, List.map_nil, List.append_nil] at folge
  have leer : events = [] := by
    generalize hg : nach.graph = graph at folge
    cases folge
    rfl
  subst leer
  refine faden_fertig E (hw := hw) (t := t) ?_ ?_ rfl
  · rw [zustand]
    change v.buchung.wirkungen = vor.buchung.wirkungen
    rw [hb]
    exact hn.wirkungen
  · rw [zustand]
    change v.rechte = vor.rechte
    rw [hr]
    exact hn.rechte

end Gabbro.Core.Ast.Semantik
