/-
  File:      core/Core/Annahme/DomaeneBeweise/Kanal.lean
  Subject:   MK-17d — the accepted unit that asks over a declared channel.

  Under the bound isolation row the vacuity of `Vakuum.lean` (deleted) is replaced by
  its opposite. The hosted unit declares the channel its question uses
  (`Hosted.hostedTabelle`), and `akzeptiert_hosted` proves the full acceptance
  conjuncts for it: authority over empty footprints, outside validity (owned handles
  at issue, commit validity at reply through `aussen_gueltig_aus_kontext`), flow over
  all-high labels, open bounds, no blockade, and the isolation row over its own
  table. `isolation_aus_regel` turns the row into run isolation, and the recorded
  question cut of `HostedLauf.konkreter_lauf` carries a memory event as well, so the
  access leg of `IsolationAussage` is live too (`isolation_zugriff_erfuellbar`).

  `frageStelltKontext` is moved from `Vakuum.lean` unchanged (same name): the machine
  fact both legs use.
-/
module

public import Core.Annahme.DomaeneBeweise.Bruecke
public import Core.Annahme.HostedLauf

@[expose] public section

namespace Gabbro.Core.Annahme

open Gabbro.Core.Maschine
open Gabbro.Core.Katalog
open Gabbro.Core.Annahme.Hosted

/-- Machine fact: a question recorded in the `aussen` trace of a context implementation
    step carries the acting context's number. Only the `frage` protocol action records a
    question event; every other action (including the thread actions `starte`,
    `verbinde`, `beende` and `wechsle`) records the empty event list. -/
theorem frageStelltKontext [DecidableEq L]
    (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι)
    (t : Nat) (c : Kontext) (s u s' : Zustand L Ort Wert Raum Lok Grund)
    (p : SchrittPlan L Ort Wert Bedingung) (spur : SchrittSpur Ort Wert)
    (q : FrageEreignis)
    (haus : FuehrtSchrittAus E.einrichtung t c s u p spur s')
    (hmem : Ereignis.frage q ∈ spur.aussen) :
    q.context = c.nummer := by
  obtain ⟨_, _, _, _, hF, _, _⟩ := haus
  generalize _hA : p.aktion = a at hF
  generalize _hE : spur.aussen = evs at hF hmem
  cases hF with
  | intern => exact (List.not_mem_nil hmem).elim
  | warte _ => exact (List.not_mem_nil hmem).elim
  | sperre _ _ => exact (List.not_mem_nil hmem).elim
  | frage qq =>
    have heq := List.mem_singleton.mp hmem
    cases heq
    rfl
  | verbrauche _ => exact (List.not_mem_nil hmem).elim
  | rueckkehr _ _ => exact (List.not_mem_nil hmem).elim
  | starte _ => exact (List.not_mem_nil hmem).elim
  | verbinde _ _ => exact (List.not_mem_nil hmem).elim
  | beende _ => exact (List.not_mem_nil hmem).elim
  | wechsle _ _ _ _ => exact (List.not_mem_nil hmem).elim

/-- The hosted form meets the authority obligation: both plans have empty footprints,
    so every read and write leg is vacuous. -/
theorem hosted_regel_lokal (i : Unit) : RegelLokal einheit i := by
  intro c s u w plan h
  cases i with
  | unit =>
    have hrule : regel c s w [plan] u := h
    obtain ⟨rfl, h | h⟩ := hrule
    · obtain ⟨planEq, _, _⟩ := h
      obtain rfl := (List.cons.inj planEq).1
      exact ⟨fun x hx => (List.not_mem_nil hx).elim, fun l hl => (List.not_mem_nil hl).elim⟩
    · obtain ⟨planEq, _, _⟩ := h
      obtain rfl := (List.cons.inj planEq).1
      exact ⟨fun x hx => (List.not_mem_nil hx).elim, fun l hl => (List.not_mem_nil hl).elim⟩

/-- The hosted unit meets the outside rule: the bind step records nothing and changes
    no effects, the question step issues the owned question over the selected endpoint,
    and pending ownership is preserved along both transitions. -/
theorem hosted_aussen_gueltig : AussenGueltig einheit := by
  apply aussen_gueltig_aus_kontext
  intro run t s c w spur s' step
  cases step with
  | kontext normal bereit regel aus =>
    obtain ⟨i, _, hideal⟩ := regel
    cases i with
    | unit =>
      obtain ⟨rfl, h | h⟩ := (hideal : regel c s w [_] _)
      · obtain ⟨planEq, _, rfl⟩ := h
        obtain rfl := (List.cons.inj planEq).1
        obtain ⟨_, _, _, _, hF, _, hziel⟩ := aus
        have hAkt : bindePlan.aktion = .intern := rfl
        rw [hAkt] at hF
        generalize hE : spur.aussen = evs at hF
        cases hF with
        | intern =>
          have hWb : ({binde s with graph := s'.graph}).buchung.wirkungen
              = s.buchung.wirkungen := rfl
          refine ⟨⟨fun ev h2 => ?_, ⟨[], ?_, fun _ h2 => (List.not_mem_nil h2).elim⟩⟩,
            fun offen => by rw [hziel]; exact binden_offen offen⟩
          · rw [hE] at h2
            exact (List.not_mem_nil h2).elim
          · rw [hziel]
            exact hWb.trans (List.append_nil _).symm
      · obtain ⟨planEq, hrech, rfl⟩ := h
        obtain rfl := (List.cons.inj planEq).1
        obtain ⟨_, _, _, _, hF, _, hziel⟩ := aus
        have hAkt : fragePlan.aktion = .frage frage := rfl
        rw [hAkt] at hF
        generalize hE : spur.aussen = evs at hF
        cases hF with
        | frage =>
          have hWf : ({(warte s).frage (s.stelleFrage t kontext frage) with graph
              := s'.graph}).buchung.wirkungen = s.buchung.wirkungen := rfl
          refine ⟨⟨fun ev h2 => ?_, ⟨[], ?_, fun _ h2 => (List.not_mem_nil h2).elim⟩⟩,
            fun offen => by rw [hziel]; exact fragen_offen hrech offen⟩
          · rw [hE] at h2
            have heq := List.mem_singleton.mp h2
            cases heq
            exact ⟨ausgewaehlt, hrech⟩
          · rw [hziel]
            exact hWf.trans (List.append_nil _).symm

/-- The hosted unit meets the bound isolation row: its table passes the line, and the
    single head form respects the unit's own table. Context and memory lookups default
    to domain `0`, so recorded memory events are same-domain; the recorded question is
    the acting context's and travels over the declared channel to domain `1`. -/
theorem hosted_domaenen : DomaenenLokal einheit := by
  refine ⟨hostedTabelle_akzeptiert, fun s c i hkopf => ?_⟩
  have hi : i = () := Option.some.inj hkopf
  subst hi
  show RegelIsolation einheit (tabellePlan hostedTabelle) ()
  intro t c s u s' w p spur himpl haus
  have hrule : regel c s w [p] u := himpl
  obtain ⟨rfl, h | h⟩ := hrule
  · obtain ⟨planEq, _, rfl⟩ := h
    obtain rfl := (List.cons.inj planEq).1
    obtain ⟨_, _, _, _, hF, _, _⟩ := haus
    have hAkt : bindePlan.aktion = .intern := rfl
    rw [hAkt] at hF
    generalize hE : spur.aussen = evs at hF
    cases hF with
    | intern =>
      refine ⟨fun a l _ _ hFremd => hFremd (Or.inl rfl),
        fun ev h2 _ _ _ => ?_⟩
      rw [hE] at h2
      exact (List.not_mem_nil h2).elim
  · obtain ⟨planEq, _, rfl⟩ := h
    obtain rfl := (List.cons.inj planEq).1
    obtain ⟨_, _, _, _, hF, _, _⟩ := haus
    have hAkt : fragePlan.aktion = .frage frage := rfl
    rw [hAkt] at hF
    generalize hE : spur.aussen = evs at hF
    cases hF with
    | frage =>
      refine ⟨fun a l _ _ hFremd => hFremd (Or.inl rfl),
        fun ev h2 d _ hFremd => ?_⟩
      rw [hE] at h2
      have heq := List.mem_singleton.mp h2
      cases heq
      exact hFremd (Or.inr (List.mem_singleton.mpr rfl))

/-- The hosted unit is accepted: catalogue, authority, outside validity, flow, open
    bounds, no blockade, and the isolation row over its declared channel table; the
    clause and guard tables are empty. -/
theorem akzeptiert_hosted : Akzeptiert einheit := by
  refine ⟨⟨Plattform.katalog_wohlgeformt .x86_64, ?_,
    ⟨Gabbro.Core.Aussen.zulassung_m2 _, ?_⟩, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro i
    exact hosted_regel_lokal i
  · exact hosted_aussen_gueltig
  · exact fluss_lokal
  · exact schrankenLokal_leer rfl rfl rfl
  · exact abschnittWartefrei_ohne_blockade _ fun _ _ _ hb => hb
  · exact hosted_domaenen
  · intro ρ _
    exact ⟨fun _ h => (List.not_mem_nil h).elim, fun _ _ h => (List.not_mem_nil h).elim,
      fun _ _ _ h => (List.not_mem_nil h).elim⟩
  · refine ⟨fun ρ _ t op args h => ?_, fun ρ _ t hC => ?_, fun ρ _ t l h _ hne => ?_⟩
    · dsimp [kanonischeVerwendung, einheit, Quelltabellen.leer] at h
      exact h.elim
    · obtain ⟨C, hC⟩ := hC
      obtain ⟨c, hc⟩ := hC.1
      obtain ⟨b, hblock, _, _, _⟩ := hC.2 c hc
      exact hblock
    · exact (hne rfl).elim

/-- Run isolation over the hosted unit's own table, from acceptance through the bridge. -/
theorem hosted_isolation : LaufIsolation einheit (tabellePlan einheit.domaenen) :=
  isolation_aus_regel _ akzeptiert_hosted

/-- The access leg is live: the accepted hosted unit has an admitted run whose question
    cut records a memory event, and run isolation holds over its own table. This is the
    memory-access analogue the old universal row ruled out. -/
theorem isolation_zugriff_erfuellbar :
    ∃ (E : Hosted.Modell) (H : Umgebung) (ρ : Lauf E),
      Akzeptiert E ∧ Laeufe E H ρ ∧ LaufIsolation E (tabellePlan E.domaenen) ∧
      ∃ (t : Nat) (w : SchrittWahl Unit) (spur : Hosted.Spur),
        ρ.zeit.spur t = some (w, spur) ∧ spur.speicher ≠ [] := by
  obtain ⟨s, zul⟩ := zulStart_erfuellbar (erlaubt []) Sicherheit.Laufkonstruktion.bild_gueltig
  obtain ⟨ρ, _, _, lauf, _, _, _, _, _, _, _, ea₁, _, _⟩ := konkreter_lauf zul []
  have hmem : (frageSpur s).speicher ≠ [] := by
    intro h
    cases h
  exact ⟨einheit, umgebung [], ρ, akzeptiert_hosted, lauf, hosted_isolation,
    ⟨1, .kontext kontext (), frageSpur s, ea₁, hmem⟩⟩

end Gabbro.Core.Annahme
