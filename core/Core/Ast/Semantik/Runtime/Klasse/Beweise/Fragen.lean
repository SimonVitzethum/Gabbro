/-
  File:      core/Core/Ast/Semantik/Runtime/Klasse/Beweise/Fragen.lean
  Subject:   THE AUTHORITY OF PENDING QUESTIONS, PROVED ONCE PER EFFECT CLASS (MK-03, PERFECT-MODEL §3.6).
             A step of any class preserves the handles, rights and device authority of every question that
             is still pending. Six of the seven classes touch neither the questions nor the ledger entries
             that authorise them: their protocol action is private (or a lock action) and their frame or
             access update changes no outside authority. The class `frage` appends the question its guard
             authorises: the guard holds the handles of the question and, for a register access, the
             exclusive authority of the device, and the ledger is the same in the successor state.
             The statement is `KlassenFragenbeinAussage`, unchanged and pinned through `KlassenAussagen`.
-/
module

public import Core.Ast.Semantik.Runtime.Klasse.Pflichten
public import Core.Ast.Semantik.Runtime.Klasse.Beweise.Faden

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog
open Gabbro.Core.Sicherheit

/-- Pending authority survives a change that leaves the questions, the answers, the epoch and the outside
    part of the ledger alone. -/
private theorem offen_befugt_gleich {vor nach : Zustand}
    (fragen : nach.fragen = vor.fragen) (antworten : nach.antworten = vor.antworten)
    (epoche : nach.epoche = vor.epoche)
    (aussengriff : nach.buchung.aussengriff = vor.buchung.aussengriff)
    (geraet : nach.buchung.geraet = vor.buchung.geraet)
    (offen : OffeneFragenBefugt vor) : OffeneFragenBefugt nach := by
  intro q mem current unanswered
  rw [fragen] at mem
  rw [antworten] at unanswered
  rcases offen q mem (by rwa [← epoche]) unanswered with ⟨griffe, register⟩
  constructor
  · rcases griffe with ⟨c, nummer, griffe'⟩
    refine ⟨c, nummer, ?_⟩
    intro z hz
    rw [aussengriff]
    exact griffe' z hz
  · intro reg
    rcases register reg with ⟨owner, nummer, geraetEq⟩
    exact ⟨owner, nummer, by rwa [geraet]⟩

/-- A step state that keeps these five fields carries the pending authority of its predecessor. -/
private theorem offen_befugt_nach_erhalten {vor v nach : Zustand}
    (fragen : v.fragen = vor.fragen) (antworten : v.antworten = vor.antworten)
    (epoche : v.epoche = vor.epoche)
    (aussengriff : v.buchung.aussengriff = vor.buchung.aussengriff)
    (geraet : v.buchung.geraet = vor.buchung.geraet)
    (zustand : nach = { v with graph := nach.graph })
    (offen : OffeneFragenBefugt vor) : OffeneFragenBefugt nach := by
  rw [zustand]
  exact offen_befugt_gleich fragen antworten epoche aussengriff geraet offen

/-- The frame transfer changes only the acting frame, so it leaves the outside ledger untouched. -/
private theorem nach_aussen_gleich (F : Schrittform) (c : Kontext) (s : Zustand) (v : Int) :
    (F.nach c s v).buchung.aussengriff = s.buchung.aussengriff ∧
      (F.nach c s v).buchung.geraet = s.buchung.geraet := by
  obtain ⟨k, _, _⟩ := F
  cases k <;> exact ⟨rfl, rfl⟩

/-- A refused access changes only the acting frame, so it leaves the outside ledger untouched. -/
private theorem verweigert_aussen_gleich (F : Schrittform) (c : Kontext) (s : Zustand) :
    (F.verweigert c s).buchung.aussengriff = s.buchung.aussengriff ∧
      (F.verweigert c s).buchung.geraet = s.buchung.geraet := by
  obtain ⟨k, _, _⟩ := F
  cases k <;> exact ⟨rfl, rfl⟩

/-- An access books only the address of its cell, so it leaves the outside ledger untouched. -/
private theorem zugriffNach_aussen_gleich (F : Schrittform) (c : Kontext) (s : Zustand) (v : Int) :
    (F.zugriffNach c s v).buchung.aussengriff = s.buchung.aussengriff ∧
      (F.zugriffNach c s v).buchung.geraet = s.buchung.geraet := by
  obtain ⟨k, _, _⟩ := F
  cases k <;> exact ⟨rfl, rfl⟩

/-- **The authority of pending questions, for a lifecycle form.** A lifecycle step asks no question and answers
    none; it changes the frames, the status of the acting thread and the holdings of the ledger, and neither the
    questions, nor the answers, nor the epoch, nor the outside part of the ledger. -/
private theorem fragenbein_faden {ι : Type}
    (E : Sicherheit.Einheit Nat Zelle Int Nat Rahmen PUnit PUnit PUnit ι) (f : ι) (F : Schrittform)
    (lz : F.Lebenszyklus) (emb : F.Eingebettet E.maschine f) : Sicherheit.RegelAntwortSicher E f := by
  intro t c w vor zwischen nach plan spur kopf impl aus offen
  rw [emb.regel] at impl
  have impl' : F.ideal c vor w [plan] zwischen := impl
  obtain ⟨hn, still, _, _⟩ := Schrittform.lebenszyklus_ideal lz impl'
  obtain ⟨_, _, _, v, aktion, _, zustand⟩ := aus
  obtain ⟨_, _, _, _, _, _, hf, ha, _, _, _, _, _, _, he, _, hb⟩ := aktion.still_erhaelt still
  exact offen_befugt_nach_erhalten (hf.trans hn.fragen) (ha.trans hn.antworten) (he.trans hn.epoche)
    (by rw [hb]; exact hn.aussengriff) (by rw [hb]; exact hn.geraet) zustand offen

/-- **The authority of pending questions, once per class** (`KlassenFragenbeinAussage`). -/
theorem klassenFragenbein (k : Wirkungsklasse) : KlassenFragenbeinAussage k := by
  intro ι E f F _ emb
  by_cases lz : F.Lebenszyklus
  · exact fragenbein_faden E f F lz emb
  intro t c w vor zwischen nach plan spur kopf impl aus offen
  rw [emb.regel] at impl
  obtain ⟨rahmen, _, _, v, aktion, _, zustand⟩ := aus
  generalize hAussen : spur.aussen = aussen at aktion
  obtain ⟨kl, o, tr⟩ := F
  cases kl with
  | lokal =>
      dsimp [Schrittform.regel, Schrittform.impl, Schrittform.ideal] at impl
      have planAkt : plan.aktion = .intern := by
        rw [(List.cons.inj impl.1).1]
        rfl
      have zwischenEq : zwischen = (⟨.lokal, o, tr⟩ : Schrittform).nach c vor 0 := impl.2
      rw [planAkt] at aktion
      cases aktion with
      | intern =>
        have buchung := nach_aussen_gleich (⟨.lokal, o, tr⟩ : Schrittform) c vor 0
        exact offen_befugt_nach_erhalten rahmen.fragen rahmen.antworten rahmen.epoche
          (by rw [zwischenEq]; exact buchung.1) (by rw [zwischenEq]; exact buchung.2) zustand offen
  | ruf =>
      dsimp [Schrittform.regel, Schrittform.impl, Schrittform.ideal] at impl
      have planAkt : plan.aktion = .intern := by
        rw [(List.cons.inj impl.1).1]
        rfl
      have zwischenEq : zwischen = (⟨.ruf, o, tr⟩ : Schrittform).nach c vor 0 := impl.2
      rw [planAkt] at aktion
      cases aktion with
      | intern =>
        have buchung := nach_aussen_gleich (⟨.ruf, o, tr⟩ : Schrittform) c vor 0
        exact offen_befugt_nach_erhalten rahmen.fragen rahmen.antworten rahmen.epoche
          (by rw [zwischenEq]; exact buchung.1) (by rw [zwischenEq]; exact buchung.2) zustand offen
  | verbrauche =>
  | maskiere =>
      dsimp [Schrittform.regel, Schrittform.impl, Schrittform.ideal] at impl
      have planAkt : plan.aktion = .intern := by
        rw [(List.cons.inj impl.1).1]
        rfl
      have zwischenEq : zwischen = (⟨.verbrauche, o, tr⟩ : Schrittform).nach c vor 0 := impl.2
      rw [planAkt] at aktion
      cases aktion with
      | intern =>
        have buchung := nach_aussen_gleich (⟨.verbrauche, o, tr⟩ : Schrittform) c vor 0
      have zwischenEq : zwischen = (⟨.maskiere, o, tr⟩ : Schrittform).nach c vor 0 := impl.2
      rw [planAkt] at aktion
      cases aktion with
      | intern =>
        have buchung := nach_aussen_gleich (⟨.maskiere, o, tr⟩ : Schrittform) c vor 0
        exact offen_befugt_nach_erhalten rahmen.fragen rahmen.antworten rahmen.epoche
          (by rw [zwischenEq]; exact buchung.1) (by rw [zwischenEq]; exact buchung.2) zustand offen
  | prioritaet =>
      dsimp [Schrittform.regel, Schrittform.impl, Schrittform.ideal] at impl
      have planAkt : plan.aktion = .intern := by
        rw [(List.cons.inj impl.1).1]
        rfl
      have zwischenEq : zwischen = (⟨.prioritaet, o, tr⟩ : Schrittform).nach c vor 0 := impl.2
      rw [planAkt] at aktion
      cases aktion with
      | intern =>
        have buchung := nach_aussen_gleich (⟨.prioritaet, o, tr⟩ : Schrittform) c vor 0
        exact offen_befugt_nach_erhalten rahmen.fragen rahmen.antworten rahmen.epoche
          (by rw [zwischenEq]; exact buchung.1) (by rw [zwischenEq]; exact buchung.2) zustand offen
  | sendeUnterbrechung =>
      dsimp [Schrittform.regel, Schrittform.impl, Schrittform.ideal] at impl
      have planAkt : plan.aktion = .intern := by
        rw [(List.cons.inj impl.1).1]
        rfl
      have zwischenEq : zwischen = (⟨.sendeUnterbrechung, o, tr⟩ : Schrittform).nach c vor 0 :=
        impl.2
      rw [planAkt] at aktion
      cases aktion with
      | intern =>
        have buchung := nach_aussen_gleich (⟨.sendeUnterbrechung, o, tr⟩ : Schrittform) c vor 0
        exact offen_befugt_nach_erhalten rahmen.fragen rahmen.antworten rahmen.epoche
          (by rw [zwischenEq]; exact buchung.1) (by rw [zwischenEq]; exact buchung.2) zustand offen
  | leiteLeitung =>
      dsimp [Schrittform.regel, Schrittform.impl, Schrittform.ideal] at impl
      have planAkt : plan.aktion = .intern := by
        rw [(List.cons.inj impl.1).1]
        rfl
      have zwischenEq : zwischen = (⟨.leiteLeitung, o, tr⟩ : Schrittform).nach c vor 0 := impl.2
      rw [planAkt] at aktion
      cases aktion with
      | intern =>
        have buchung := nach_aussen_gleich (⟨.leiteLeitung, o, tr⟩ : Schrittform) c vor 0
        exact offen_befugt_nach_erhalten rahmen.fragen rahmen.antworten rahmen.epoche
          (by rw [zwischenEq]; exact buchung.1) (by rw [zwischenEq]; exact buchung.2) zustand offen
  | lesen mode =>
      dsimp [Schrittform.regel, Schrittform.impl, Schrittform.ideal, Schrittform.zugriffsschritt] at impl
      rcases impl with ⟨_, planEq0, zwischenEq⟩ | ⟨_, val, _, planEq0, zwischenEq⟩
      · have planAkt : plan.aktion = .intern := by
          rw [(List.cons.inj planEq0).1]
          rfl
        rw [planAkt] at aktion
        cases aktion with
        | intern =>
          have buchung := verweigert_aussen_gleich (⟨.lesen mode, o, tr⟩ : Schrittform) c vor
          exact offen_befugt_nach_erhalten rahmen.fragen rahmen.antworten rahmen.epoche
            (by rw [zwischenEq]; exact buchung.1) (by rw [zwischenEq]; exact buchung.2) zustand offen
      · have planAkt : plan.aktion = .intern := by
          rw [(List.cons.inj planEq0).1]
          rfl
        rw [planAkt] at aktion
        cases aktion with
        | intern =>
          have buchung := zugriffNach_aussen_gleich (⟨.lesen mode, o, tr⟩ : Schrittform) c vor val
          exact offen_befugt_nach_erhalten rahmen.fragen rahmen.antworten rahmen.epoche
            (by rw [zwischenEq]; exact buchung.1) (by rw [zwischenEq]; exact buchung.2) zustand offen
  | schreiben mode =>
      dsimp [Schrittform.regel, Schrittform.impl, Schrittform.ideal, Schrittform.zugriffsschritt] at impl
      rcases impl with ⟨_, planEq0, zwischenEq⟩ | ⟨_, val, _, planEq0, zwischenEq⟩
      · have planAkt : plan.aktion = .intern := by
          rw [(List.cons.inj planEq0).1]
          rfl
        rw [planAkt] at aktion
        cases aktion with
        | intern =>
          have buchung := verweigert_aussen_gleich (⟨.schreiben mode, o, tr⟩ : Schrittform) c vor
          exact offen_befugt_nach_erhalten rahmen.fragen rahmen.antworten rahmen.epoche
            (by rw [zwischenEq]; exact buchung.1) (by rw [zwischenEq]; exact buchung.2) zustand offen
      · have planAkt : plan.aktion = .intern := by
          rw [(List.cons.inj planEq0).1]
          rfl
        rw [planAkt] at aktion
        cases aktion with
        | intern =>
          have buchung := zugriffNach_aussen_gleich (⟨.schreiben mode, o, tr⟩ : Schrittform) c vor val
          exact offen_befugt_nach_erhalten rahmen.fragen rahmen.antworten rahmen.epoche
            (by rw [zwischenEq]; exact buchung.1) (by rw [zwischenEq]; exact buchung.2) zustand offen
  | rmw mode =>
      dsimp [Schrittform.regel, Schrittform.impl, Schrittform.ideal, Schrittform.zugriffsschritt] at impl
      rcases impl with ⟨_, planEq0, zwischenEq⟩ | ⟨_, val, _, planEq0, zwischenEq⟩
      · have planAkt : plan.aktion = .intern := by
          rw [(List.cons.inj planEq0).1]
          rfl
        rw [planAkt] at aktion
        cases aktion with
        | intern =>
          have buchung := verweigert_aussen_gleich (⟨.rmw mode, o, tr⟩ : Schrittform) c vor
          exact offen_befugt_nach_erhalten rahmen.fragen rahmen.antworten rahmen.epoche
            (by rw [zwischenEq]; exact buchung.1) (by rw [zwischenEq]; exact buchung.2) zustand offen
      · have planAkt : plan.aktion = .intern := by
          rw [(List.cons.inj planEq0).1]
          rfl
        rw [planAkt] at aktion
        cases aktion with
        | intern =>
          have buchung := zugriffNach_aussen_gleich (⟨.rmw mode, o, tr⟩ : Schrittform) c vor val
          exact offen_befugt_nach_erhalten rahmen.fragen rahmen.antworten rahmen.epoche
            (by rw [zwischenEq]; exact buchung.1) (by rw [zwischenEq]; exact buchung.2) zustand offen
  | zaun mode =>
      dsimp [Schrittform.regel, Schrittform.impl, Schrittform.ideal, Schrittform.zugriffsschritt] at impl
      rcases impl with ⟨_, planEq0, zwischenEq⟩ | ⟨_, val, _, planEq0, zwischenEq⟩
      · have planAkt : plan.aktion = .intern := by
          rw [(List.cons.inj planEq0).1]
          rfl
        rw [planAkt] at aktion
        cases aktion with
        | intern =>
          have buchung := verweigert_aussen_gleich (⟨.zaun mode, o, tr⟩ : Schrittform) c vor
          exact offen_befugt_nach_erhalten rahmen.fragen rahmen.antworten rahmen.epoche
            (by rw [zwischenEq]; exact buchung.1) (by rw [zwischenEq]; exact buchung.2) zustand offen
      · have planAkt : plan.aktion = .intern := by
          rw [(List.cons.inj planEq0).1]
          rfl
        rw [planAkt] at aktion
        cases aktion with
        | intern =>
          have buchung := zugriffNach_aussen_gleich (⟨.zaun mode, o, tr⟩ : Schrittform) c vor val
          exact offen_befugt_nach_erhalten rahmen.fragen rahmen.antworten rahmen.epoche
            (by rw [zwischenEq]; exact buchung.1) (by rw [zwischenEq]; exact buchung.2) zustand offen
  | sperre art =>
      dsimp [Schrittform.regel, Schrittform.impl, Schrittform.ideal, Schrittform.zugriffsschritt] at impl
      rcases impl with ⟨_, planEq0, zwischenEq⟩ | ⟨_, val, _, planEq0, zwischenEq⟩
      · have planAkt : plan.aktion = .intern := by
          rw [(List.cons.inj planEq0).1]
          rfl
        rw [planAkt] at aktion
        cases aktion with
        | intern =>
          have buchung := verweigert_aussen_gleich (⟨.sperre art, o, tr⟩ : Schrittform) c vor
          exact offen_befugt_nach_erhalten rahmen.fragen rahmen.antworten rahmen.epoche
            (by rw [zwischenEq]; exact buchung.1) (by rw [zwischenEq]; exact buchung.2) zustand offen
      · have planAkt : plan.aktion = .sperre (o (vor.lokal c)).sperre art := by
          rw [(List.cons.inj planEq0).1]
          rfl
        rw [planAkt] at aktion
        cases aktion with
        | sperre _ _ =>
          have buchung := zugriffNach_aussen_gleich (⟨.sperre art, o, tr⟩ : Schrittform) c vor val
          rw [zustand]
          exact offen_befugt_gleich
            (by change zwischen.fragen = vor.fragen; exact rahmen.fragen)
            (by change zwischen.antworten = vor.antworten; exact rahmen.antworten)
            (by change zwischen.epoche = vor.epoche; exact rahmen.epoche)
            (by
              change zwischen.buchung.aussengriff = vor.buchung.aussengriff
              rw [zwischenEq]
              exact buchung.1)
            (by
              change zwischen.buchung.geraet = vor.buchung.geraet
              rw [zwischenEq]
              exact buchung.2)
            offen
  | frage =>
      dsimp [Schrittform.regel, Schrittform.impl, Schrittform.ideal, Schrittform.zugriffsschritt] at impl
      rcases impl with ⟨_, planEq0, zwischenEq⟩ | ⟨guard, val, _, planEq0, zwischenEq⟩
      · have planAkt : plan.aktion = .intern := by
          rw [(List.cons.inj planEq0).1]
          rfl
        rw [planAkt] at aktion
        cases aktion with
        | intern =>
          have buchung := verweigert_aussen_gleich (⟨.frage, o, tr⟩ : Schrittform) c vor
          exact offen_befugt_nach_erhalten rahmen.fragen rahmen.antworten rahmen.epoche
            (by rw [zwischenEq]; exact buchung.1) (by rw [zwischenEq]; exact buchung.2) zustand offen
      · have planEq : plan = (o (vor.lokal c)).fragePlan := by
          simpa only [Schrittform.plan, Wirkungsklasse.plan] using (List.cons.inj planEq0).1
        rcases guard with ⟨q, hq, befugtQ⟩
        have planAkt : plan.aktion = .frage q := by
          rw [planEq]
          simp only [Operand.fragePlan, hq]
        rw [planAkt] at aktion
        cases aktion with
        | frage =>
          rw [zustand]
          let ev : FrageEreignis := vor.stelleFrage t c q
          have fragenEq :
              ({zwischen.frage ev with graph := nach.graph} : Zustand).fragen = vor.fragen ++ [ev] := by
            change zwischen.fragen ++ [ev] = vor.fragen ++ [ev]
            rw [rahmen.fragen]
          have antwortenEq :
              ({zwischen.frage ev with graph := nach.graph} : Zustand).antworten = vor.antworten := by
            change zwischen.antworten = vor.antworten
            rw [rahmen.antworten]
          have epocheEq :
              ({zwischen.frage ev with graph := nach.graph} : Zustand).epoche = vor.epoche := by
            change zwischen.epoche = vor.epoche
            rw [rahmen.epoche]
          have buchung := zugriffNach_aussen_gleich (⟨.frage, o, tr⟩ : Schrittform) c vor val
          have bAg :
              ({zwischen.frage ev with graph := nach.graph} : Zustand).buchung.aussengriff =
                vor.buchung.aussengriff := by
            change zwischen.buchung.aussengriff = vor.buchung.aussengriff
            rw [zwischenEq]
            exact buchung.1
          have bGer :
              ({zwischen.frage ev with graph := nach.graph} : Zustand).buchung.geraet =
                vor.buchung.geraet := by
            change zwischen.buchung.geraet = vor.buchung.geraet
            rw [zwischenEq]
            exact buchung.2
          intro q' mem current unanswered
          rw [fragenEq, List.mem_append, List.mem_singleton] at mem
          rw [antwortenEq] at unanswered
          rcases mem with alt | rfl
          · rcases offen q' alt (by rwa [← epocheEq]) unanswered with ⟨griffe, register⟩
            constructor
            · rcases griffe with ⟨c', nummer, griffe'⟩
              refine ⟨c', nummer, ?_⟩
              intro z hz
              rw [bAg]
              exact griffe' z hz
            · intro reg
              rcases register reg with ⟨owner, nummer, geraetEq⟩
              exact ⟨owner, nummer, by rwa [bGer]⟩
          · constructor
            · refine ⟨c, rfl, ?_⟩
              intro z hz
              rw [bAg]
              exact befugtQ.1 z hz
            · intro reg
              rcases befugtQ.2 reg with ⟨owner, nummer, geraetEq⟩
              exact ⟨owner, nummer, by rwa [bGer]⟩
  | starte => exact (lz (Or.inl rfl)).elim
  | beende => exact (lz (Or.inr (Or.inl rfl))).elim
  | verbinde => exact (lz (Or.inr (Or.inr (Or.inl rfl)))).elim
  | wechsle => exact (lz (Or.inr (Or.inr (Or.inr rfl)))).elim

end Gabbro.Core.Ast.Semantik
