/-
  File:      core/Core/Annahme/DomaeneBeweise/Tabellen.lean
  Subject:   MK-17c item 2 — FINITE DOMAIN TABLES: domain assignments as declared finite
              tables instead of functions, with a checker that is correct AND complete
              with no extra premise.

  Design. `Maschine.DomaenenTabelle` (in `Core/Maschine/Quelltabellen.lean`) declares
  the domain count, the finite assignment tables
  for contexts, memory objects and device objects, and the declared channels. The
  tables are pure data (no `Prop` fields). Lookup is total with default domain `0`.
  Coherence (`tabKohaerent`: every table entry lands inside the declared domains) is
  a finite check, so the checker line `pruefeDomaenenTab` decides exactly coherence:
  `tabellenKorrekt` and `tabellenVollstaendig` prove both directions with no
  `Akzeptiert` and no well-formedness premise. This repairs the MK-17 finding of
  `Pruefer.lean` (functions are never inspected by the line) without touching the
  function-based plan: `tabellePlan` embeds every table, preserves the line's verdict
  (`tabellePlan_wohlgeformt`) and turns table coherence into the old coherence
  (`tabellePlan_kohaerent`).

  The collection root `DomaenenTabellenAussage` is new and pinned independently; no
  statement of `Domaene.lean` is changed.
-/
module

public import Core.Annahme.Domaene

@[expose] public section

namespace Gabbro.Core.Annahme

open Gabbro.Core.Maschine
open Gabbro.Core.Katalog

variable {L Ort Wert Raum Lok Grund Bedingung Wahl ι : Type}

/-- The table data lives in `Core/Maschine/Quelltabellen.lean` (MK-17d): the unit carries
    its table in `Einheit.domaenen`, so the checker row can decide exactly the unit's own
    declaration. This file keeps the checker analysis over `Maschine.DomaenenTabelle`. -/

/-- CORRECTNESS of the table checker: every accepted table is coherent. No
    `Akzeptiert`, no well-formedness premise. -/
def DomaenenTabellenKorrektAussage : Prop :=
  ∀ tab : DomaenenTabelle, pruefeDomaenenTab tab = true → tabKohaerent tab

/-- COMPLETENESS of the table checker: every coherent table passes. No
    `Akzeptiert`, no well-formedness premise. -/
def DomaenenTabellenVollstaendigAussage : Prop :=
  ∀ tab : DomaenenTabelle, tabKohaerent tab → pruefeDomaenenTab tab = true

/-- The claimed equivalence: the line accepts exactly the coherent tables. -/
def DomaenenTabellenAequivalenzAussage : Prop :=
  ∀ tab : DomaenenTabelle, (pruefeDomaenenTab tab = true ↔ tabKohaerent tab)

/-- The new pinned collection root of the table analysis. It is NOT a conjunct of
    `DomaenenAussage`: the two roots are pinned independently. -/
def DomaenenTabellenAussage : Prop :=
  DomaenenTabellenKorrektAussage ∧
    DomaenenTabellenVollstaendigAussage ∧ DomaenenTabellenAequivalenzAussage

/-- Correctness: unfold the line; both sides are the same finite conjunction. -/
theorem tabellenKorrekt : DomaenenTabellenKorrektAussage := by
  intro tab h
  simp only [pruefeDomaenenTab, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true] at h
  obtain ⟨⟨⟨⟨h0, hk⟩, ho⟩, hg⟩, hkan⟩ := h
  exact ⟨h0, hk, ho, hg, hkan⟩

/-- Completeness: the same finite conjunction, read backwards. -/
theorem tabellenVollstaendig : DomaenenTabellenVollstaendigAussage := by
  intro tab h
  simp only [pruefeDomaenenTab, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true]
  obtain ⟨h0, hk, ho, hg, hkan⟩ := h
  exact ⟨⟨⟨⟨h0, hk⟩, ho⟩, hg⟩, hkan⟩

/-- The equivalence from both legs. -/
theorem tabellenAequivalenz : DomaenenTabellenAequivalenzAussage := by
  intro tab
  exact ⟨tabellenKorrekt tab, tabellenVollstaendig tab⟩

/-- The collection root holds. -/
theorem tabellen_aussage : DomaenenTabellenAussage :=
  ⟨tabellenKorrekt, tabellenVollstaendig, tabellenAequivalenz⟩

/-- Coherent tables look up inside the declared domains: the context leg. -/
theorem tabKontext_kohaerent (tab : DomaenenTabelle) (h : tabKohaerent tab)
    (c : Kontext) : tabKontext tab c < tab.domaenen := by
  obtain ⟨h0, hk, _, _, _⟩ := h
  simp only [tabKontext]
  cases hfind : tab.kontexte.find? (fun e => decide (e.1 = c)) with
  | none => exact h0
  | some e =>
    have hmem : e ∈ tab.kontexte := List.mem_of_find?_eq_some hfind
    have hlt := hk e hmem
    exact hlt

/-- Coherent tables look up inside the declared domains: the memory-object leg. -/
theorem tabObjekt_kohaerent (tab : DomaenenTabelle) (h : tabKohaerent tab)
    (n : Nat) : tabObjekt tab n < tab.domaenen := by
  obtain ⟨h0, _, ho, _, _⟩ := h
  simp only [tabObjekt]
  cases hfind : tab.objekte.find? (fun e => decide (e.1 = n)) with
  | none => exact h0
  | some e =>
    have hmem : e ∈ tab.objekte := List.mem_of_find?_eq_some hfind
    have hlt := ho e hmem
    exact hlt

/-- Coherent tables look up inside the declared domains: the device-object leg. -/
theorem tabGeraet_kohaerent (tab : DomaenenTabelle) (h : tabKohaerent tab)
    (o : Objekt) : tabGeraet tab o < tab.domaenen := by
  obtain ⟨h0, _, _, hg, _⟩ := h
  simp only [tabGeraet]
  cases hfind : tab.geraete.find? (fun e => decide (e.1 = o)) with
  | none => exact h0
  | some e =>
    have hmem : e ∈ tab.geraete := List.mem_of_find?_eq_some hfind
    have hlt := hg e hmem
    exact hlt

/-- Every table embeds as a function-based plan through the total lookups. -/
def tabellePlan (tab : DomaenenTabelle) : DomaenenPlan where
  domaenen := tab.domaenen
  kontextDomaene := tabKontext tab
  objektDomaene := tabObjekt tab
  geraetDomaene := tabGeraet tab
  kanaele := tab.kanaele

/-- A coherent table passes both the old line (on the embedded plan) and the new
    line: the checker verdicts agree on coherent tables. -/
theorem tabellePlan_wohlgeformt (tab : DomaenenTabelle) (h : tabKohaerent tab) :
    (tabellePlan tab).wohlgeformt ∧ pruefeDomaenenTab tab = true := by
  have h0 : 0 < (tabellePlan tab).domaenen := h.1
  have hkan : ∀ k ∈ (tabellePlan tab).kanaele,
      k.1 < (tabellePlan tab).domaenen ∧ k.2 < (tabellePlan tab).domaenen :=
    h.2.2.2.2
  constructor
  · show pruefeDomaenen (tabellePlan tab) = true
    simp only [pruefeDomaenen, Bool.and_eq_true, decide_eq_true_eq,
      List.all_eq_true]
    exact ⟨h0, hkan⟩
  · exact tabellenVollstaendig tab h

/-- Table coherence is the old coherence of the embedded plan. -/
theorem tabellePlan_kohaerent (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι)
    (tab : DomaenenTabelle) (h : tabKohaerent tab) :
    DomaenenKohaerenz E (tabellePlan tab) := by
  refine ⟨fun c => tabKontext_kohaerent tab h c,
    fun x => tabObjekt_kohaerent tab h (E.einrichtung.speicherObjekt x),
    fun o => tabGeraet_kohaerent tab h o⟩

/-- The single-domain table passes the line. -/
theorem eineTabelle_akzeptiert : pruefeDomaenenTab eineTabelle = true := rfl

/-- The single-domain table is coherent. -/
theorem eineTabelle_kohaerent : tabKohaerent eineTabelle :=
  ⟨Nat.zero_lt_one, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim⟩

/-- Satisfiability of the table checker: line and coherence hold jointly. -/
theorem domaenenTabellen_erfuellbar :
    ∃ tab : DomaenenTabelle, pruefeDomaenenTab tab = true ∧ tabKohaerent tab :=
  ⟨eineTabelle, eineTabelle_akzeptiert, eineTabelle_kohaerent⟩

/-- The line refuses the empty-domain table. -/
theorem leereTabelle_verweigert : pruefeDomaenenTab leereTabelle = false := rfl

/-- Non-triviality of the table checker: it accepts and it refuses. -/
theorem domaenenTabellen_nichtTrivial :
    (∃ tab : DomaenenTabelle, pruefeDomaenenTab tab = false) ∧
      (∃ tab : DomaenenTabelle, pruefeDomaenenTab tab = true) :=
  ⟨⟨leereTabelle, leereTabelle_verweigert⟩, ⟨eineTabelle, eineTabelle_akzeptiert⟩⟩

end Gabbro.Core.Annahme
