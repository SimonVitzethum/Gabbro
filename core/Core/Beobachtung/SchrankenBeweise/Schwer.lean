/-
  File:      core/Core/Beobachtung/SchrankenBeweise/Schwer.lean
  Subject:   The hard M9 B9/B21 duties pinned in `SchrankenB9B21Pflichten`.

  The bridge duty moves the ideal bounds at cut `t + 1` across the run relation to
  the concrete post-state of any matched form step; the simulation hypothesis supplies
  the whole-run relation, so the step-level match itself needs no second analysis.
-/
module

public import Core.Beobachtung.SchrankenB9B21Pflichten
public import Core.Annahme.Schranken
public import Core.Katalog.Erfuellbar
public import Core.Ast.Semantik.Elaborierung

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine Annahme Gabbro.Core.Ast

/-- Every implementation form step inherits the bounds already proved for the aligned
    ideal cut `t + 1`: the simulation relation connects that cut to the concrete
    post-state, and both legs move across it. -/
theorem schrankenRegelAusLokal : schrankenRegelAusLokalAussage := by
  intro L Ort Wert Raum Lok Grund Bedingung Wahl Form instL
  intro E f pflicht simHyp regelSim
  intro h ρ lauf t c w spur vor nach
    vorEq kopf spurEq nachEq step stapelVor speicherVor
  obtain ⟨η, idealLauf, sim⟩ := simHyp lauf
  rcases sim with ⟨ordnung, matched, rest⟩
  have idealBounds := schranken_prefix_aus_lokal pflicht idealLauf (t + 1)
  obtain ⟨sNext, nextEq, bezugNach⟩ := matched.zustand (t + 1)
  have sNextEq : sNext = nach := Option.some.inj (nextEq.symm.trans nachEq)
  rw [sNextEq] at bezugNach
  exact ⟨(stapel_bezug pflicht.bezug bezugNach).mpr idealBounds.1,
    (speicher_bezug bezugNach).mpr idealBounds.2⟩

/-- The pinned call duty has no memory-footprint premise: a rule whose interior update
    revives two allocations satisfies its stack premise vacuously on an open stack, yet
    breaks the memory leg. The refutation uses an admissible ideal run whose every context
    step takes that rule. -/
theorem nicht_rufSchranken : ¬ rufSchrankenAussage := by
  intro getragen
  let k := Plattform.x86_64.katalog
  let bild : Bild := ⟨.elf, fun a => if a = 0 then some 0 else none, [0]⟩
  let entry := Semantik.eintritt
  let b : Semantik.Befehl := .rufe Semantik.mainName [] none
  let daten : Startdaten Int Nat Semantik.Rahmen PUnit :=
    ⟨fun _ => Semantik.Rahmen.start [],
      fun c => if c = entry then .laeuft else .ruht,
      fun core => ⟨if core = 0 then some entry else none, .nutzer, 0, fun _ => false, 0, false, []⟩,
      ⟨fun _ => false, fun _ => 0⟩⟩
  let e : Einrichtung Nat Semantik.Zelle Int Nat Semantik.Rahmen PUnit PUnit :=
    ⟨fun _ => 0, fun l => Semantik.Zelle.sperre l, fun _ => Semantik.Zelle.aussen, fun _ => 0, fun _ _ _ => False,
      fun _ _ => True, ⟨0, 0⟩, ⟨entry, 0, fun _ => daten, fun _ _ => 0⟩,
      fun _ => 0, fun _ _ _ => none⟩
  let plan : Semantik.Plan := Semantik.plan
  let update (_c : Kontext) (s : Semantik.Zustand) : Semantik.Zustand :=
    { s with
      rechte := ⟨fun j => decide (j = 0 ∨ j = 1), s.rechte.gen⟩,
      buchung := { s.buchung with umfang := fun j => if j = 0 ∨ j = 1 then [Semantik.Zelle.aussen] else [] } }
  let regel : Regel Semantik.Zustand Semantik.Plan PUnit :=
    ⟨fun c s _ plans u => plans = [plan] ∧ u = update c s,
      fun c s _ plans u => plans = [plan] ∧ u = update c s⟩
  let sy : MaschinenSystem Nat Semantik.Zelle Int Nat Semantik.Rahmen PUnit PUnit PUnit Semantik.Befehl :=
    ⟨fun _ => regel, fun _ c => if c = entry then some b else none,
      fun _ _ => False, fun _ _ _ => False⟩
  let E : Semantik.Einheit :=
    { katalog := k
      bild := bild
      einrichtung := e
      system := sy
      startdaten := fun _ => daten
      startmedium := fun _ _ => 0
      laden := fun _ _ => none
      lokalerBezug := Eq
      stotterLaenge := fun _ => 0
      quelltabellen := .leer
      schranken := { Schrankendaten.leer with
        speicher := some 1
        stapelTiefe := fun r => r.fortsetzungen.length } }
  have image : bild.gueltig k.plattform.ziel := by
    refine ⟨List.Mem.head _, ?_, ?_⟩
    · intro a byte present
      change (if a = 0 then some 0 else none) = some byte at present
      split at present
      · rename_i atZero
        subst a
        exact Nat.pow_pos (Nat.zero_lt_succ _)
      · cases present
    · intro a mem
      have ha : a = 0 := List.mem_singleton.mp mem
      subst a
      exact ⟨0, rfl⟩
  let sicht : Nat → AussenVerlauf → AussenSicht :=
    fun _ _ => ⟨fun _ => ⟨0, false, false, [], fun _ => 0⟩, fun _ _ => none, fun _ _ => none⟩
  let hw := Umgebung.referenzLauf k 1 sicht
  let h := Umgebung.referenz k 1 sicht
  have fair : FairLaeufe k h hw :=
    Umgebung.referenz_fair k 1 sicht Plattform.x86_64.katalog_wohlgeformt (Nat.zero_lt_succ _)
  obtain ⟨start, admissible⟩ := zulStart_erfuellbar fair.hardware image
  let z := (I.start E start).2
  let zustand (t : Nat) : Semantik.Zustand := Nat.rec z (fun _ => update entry) t
  have protocol (t : Nat) : (zustand t).kerne = z.kerne ∧ (zustand t).status = z.status := by
    induction t with
    | zero => exact ⟨rfl, rfl⟩
    | succ t ih => exact ih
  have dispatch : (z.kerne 0).laeuft = some entry := by
    change (if (0 : Nat) = 0 then some entry else none) = some entry
    simp only [if_true]
  have live : z.status entry = .laeuft := by
    change (if entry = entry then .laeuft else .ruht : Status Int PUnit) = .laeuft
    simp only [if_true]
  have opportunity (t : Nat) : hw.gelegenheit t 0 := congrArg some (Nat.mod_one t)
  have execute (t : Nat) (x : Semantik.Zustand) :
      FuehrtSchrittAus e t entry x (update entry x) plan ⟨[], []⟩ (update entry x) := by
    refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_,
      [], update entry x, .intern, .nil _, rfl⟩
    intro l hl
    cases (List.not_mem_nil hl)
  have step (t : Nat) : I.Schritt E.einrichtung E.system E.katalog hw t (zustand t)
      (.kontext entry (), ⟨[], []⟩) (zustand (t + 1)) := by
    exact .kontext rfl ⟨0, opportunity t,
      (congrArg (fun cores => (cores 0).laeuft) (protocol t).1).trans dispatch,
      (congrFun (protocol t).2 entry).trans live⟩
      ⟨b, rfl, rfl, rfl⟩ (execute t (zustand t))
  let zeit0 : Zeitlauf (I.Schritt E.einrichtung E.system E.katalog hw) :=
    ⟨zustand, fun _ => some (.kontext entry (), ⟨[], []⟩), fun t => .schritt rfl (step t)⟩
  have pause t x (stuck : KeinSchritt (I.Schritt E.einrichtung E.system E.katalog hw) t x) :
      ¬ AbsturzAngeboten E.katalog hw t :=
    fun offer => stuck _ _ (.absturz (absturz_schritt_erfuellbar _ _ offer x))
  let η : I.Lauf E := ⟨start, h, hw, zeit0.erlaubePausen pause, fun _ => none⟩
  have lauf : I.Laeufe E η :=
    ⟨fair.hardware, fair.konform, admissible, rfl,
      zeit0.erlaubePausen_maximal pause _ (fun _ => rfl), fun _ _ h => nomatch h⟩
  have okPrem : ∀ (c : Kontext) (s u : Semantik.Zustand) (w : PUnit) (plans : List Semantik.Plan),
      (E.system.regel b).ideal c s w plans u → ∀ n, E.schranken.stapel = some n →
        ((s.lokal c).fortsetzungen.length + 1 ≤ n ∨ (u.lokal c).stopp.isSome) ∧
        ((u.lokal c).stopp.isSome → (u.lokal c).fortsetzungen = (s.lokal c).fortsetzungen) := by
    intro c s u w plans ideal n hn
    cases hn
  have pflicht : RegelSchranken E b := getragen E (fun r => rfl) Semantik.mainName [] none okPrem
  have leer : LebendeZellen z = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro zz mem
    change (false = true ∧ zz.2 < 0) at mem
    cases mem.1
  have stapelVor : StapelZustand E z := stapelZustand_leer rfl z
  have speicherVor : SpeicherZustand E z := by
    intro n hn
    obtain rfl := Option.some.inj hn
    rw [leer, Set.encard_empty]
    exact bot_le
  have res := pflicht lauf 0 entry () ⟨[], []⟩ z (zustand 1)
    rfl rfl rfl rfl (step 0) stapelVor speicherVor
  have subset : ({(0, 0), (1, 0)} : Set (Nat × Nat)) ⊆ LebendeZellen (zustand 1) := by
    intro zz hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hz
    rcases hz with hz | hz
    · subst zz
      change true = true ∧ 0 < 1
      exact ⟨rfl, Nat.zero_lt_one⟩
    · subst zz
      change true = true ∧ 0 < 1
      exact ⟨rfl, Nat.zero_lt_one⟩
  have ungleich : ((0, 0) : Nat × Nat) ≠ (1, 0) := by
    intro h
    exact Nat.zero_ne_one (congrArg Prod.fst h)
  have enc : ({(0, 0), (1, 0)} : Set (Nat × Nat)).encard = 2 := by
    exact Set.encard_pair ungleich
  have zwei : 2 ≤ (LebendeZellen (zustand 1)).encard := by
    rw [← enc]
    exact Set.encard_le_encard subset
  have zuwenig : (2 : ℕ∞) ≤ (1 : ℕ∞) := zwei.trans (res.2 1 rfl)
  exact (Nat.not_succ_le_self 1) (ENat.natCast_le_natCast.mp zuwenig)

/-- The pinned memory-management duty places its depth premise under the finite-memory
    hypothesis. With an open ceiling the premise is vacuous, while a finite stack bound
    still constrains the state; a rule that flips a local flag breaks the stack leg. -/
theorem nicht_speicherverwaltungSchranken : ¬ speicherverwaltungSchrankenAussage := by
  intro getragen
  let k := Plattform.x86_64.katalog
  let bild : Bild := ⟨.elf, fun a => if a = 0 then some 0 else none, [0]⟩
  let entry := Kontext.faden 0
  let op : LowLevel.MemInstruction := .splitRegion 0 0
  let daten : Startdaten _root_.Unit _root_.Unit Bool _root_.Unit :=
    ⟨fun _ => false,
      fun c => if c = entry then .laeuft else .ruht,
      fun core => ⟨if core = 0 then some entry else none, .nutzer, (), fun _ => false, 0, false, []⟩,
      ⟨fun _ => false, fun _ => 0⟩⟩
  let e : Einrichtung _root_.Unit _root_.Unit _root_.Unit _root_.Unit Bool _root_.Unit _root_.Unit :=
    ⟨fun _ => (), fun _ => (), fun _ => (), fun _ => (), fun _ _ _ => False,
      fun _ _ => True, ⟨0, 1⟩, ⟨entry, 0, fun _ => daten, fun _ _ => ()⟩,
      fun _ => 0, fun _ _ _ => none⟩
  let plan : SchrittPlan _root_.Unit _root_.Unit _root_.Unit _root_.Unit :=
    ⟨.intern, [], [], fun _ => false, fun _ => .na, fun _ => ()⟩
  let update (_c : Kontext) (s : Zustand _root_.Unit _root_.Unit _root_.Unit _root_.Unit Bool _root_.Unit) :=
    { s with lokal := fun _ => true }
  let regel : Regel (Zustand _root_.Unit _root_.Unit _root_.Unit _root_.Unit Bool _root_.Unit) (SchrittPlan _root_.Unit _root_.Unit _root_.Unit _root_.Unit) _root_.Unit :=
    ⟨fun c s _ plans u => plans = [plan] ∧ u = update c s,
      fun c s _ plans u => plans = [plan] ∧ u = update c s⟩
  let sy : MaschinenSystem _root_.Unit _root_.Unit _root_.Unit _root_.Unit Bool _root_.Unit _root_.Unit _root_.Unit LowLevel.MemInstruction :=
    ⟨fun _ => regel, fun _ _ => some op, fun _ _ => False, fun _ _ _ => False⟩
  let E : Einheit _root_.Unit _root_.Unit _root_.Unit _root_.Unit Bool _root_.Unit _root_.Unit _root_.Unit LowLevel.MemInstruction :=
    { katalog := k
      bild := bild
      einrichtung := e
      system := sy
      startdaten := fun _ => daten
      startmedium := fun _ _ => 0
      laden := fun _ _ => none
      lokalerBezug := Eq
      stotterLaenge := fun _ => 0
      quelltabellen := .leer
      schranken := { Schrankendaten.leer with
        stapel := some 0
        stapelTiefe := fun b => if b then 1 else 0 } }
  have image : bild.gueltig k.plattform.ziel := by
    refine ⟨List.Mem.head _, ?_, ?_⟩
    · intro a byte present
      change (if a = 0 then some 0 else none) = some byte at present
      split at present
      · rename_i atZero
        subst a
        exact Nat.pow_pos (Nat.zero_lt_succ _)
      · cases present
    · intro a mem
      have ha : a = 0 := List.mem_singleton.mp mem
      subst a
      exact ⟨0, rfl⟩
  let sicht : Nat → AussenVerlauf → AussenSicht :=
    fun _ _ => ⟨fun _ => ⟨0, false, false, [], fun _ => 0⟩, fun _ _ => none, fun _ _ => none⟩
  let hw := Umgebung.referenzLauf k 1 sicht
  let h := Umgebung.referenz k 1 sicht
  have fair : FairLaeufe k h hw :=
    Umgebung.referenz_fair k 1 sicht Plattform.x86_64.katalog_wohlgeformt (Nat.zero_lt_succ _)
  obtain ⟨start, admissible⟩ := zulStart_erfuellbar fair.hardware image
  let z := (I.start E start).2
  let zustand (t : Nat) : Zustand _root_.Unit _root_.Unit _root_.Unit _root_.Unit Bool _root_.Unit := Nat.rec z (fun _ => update entry) t
  have protocol (t : Nat) : (zustand t).kerne = z.kerne ∧ (zustand t).status = z.status := by
    induction t with
    | zero => exact ⟨rfl, rfl⟩
    | succ t ih => exact ih
  have dispatch : (z.kerne 0).laeuft = some entry := by
    change (if (0 : Nat) = 0 then some entry else none) = some entry
    simp only [if_true]
  have live : z.status entry = .laeuft := by
    change (if entry = entry then .laeuft else .ruht : Status _root_.Unit _root_.Unit) = .laeuft
    simp only [if_true]
  have opportunity (t : Nat) : hw.gelegenheit t 0 := congrArg some (Nat.mod_one t)
  have execute (t : Nat) (x : Zustand _root_.Unit _root_.Unit _root_.Unit _root_.Unit Bool _root_.Unit) :
      FuehrtSchrittAus e t entry x (update entry x) plan ⟨[], []⟩ (update entry x) := by
    refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_,
      [], update entry x, .intern, .nil _, rfl⟩
    intro l hl
    cases (List.not_mem_nil hl)
  have step (t : Nat) : I.Schritt E.einrichtung E.system E.katalog hw t (zustand t)
      (.kontext entry (), ⟨[], []⟩) (zustand (t + 1)) := by
    exact .kontext rfl ⟨0, opportunity t,
      (congrArg (fun cores => (cores 0).laeuft) (protocol t).1).trans dispatch,
      (congrFun (protocol t).2 entry).trans live⟩
      ⟨op, rfl, rfl, rfl⟩ (execute t (zustand t))
  let zeit0 : Zeitlauf (I.Schritt E.einrichtung E.system E.katalog hw) :=
    ⟨zustand, fun _ => some (.kontext entry (), ⟨[], []⟩), fun t => .schritt rfl (step t)⟩
  have pause t x (stuck : KeinSchritt (I.Schritt E.einrichtung E.system E.katalog hw) t x) :
      ¬ AbsturzAngeboten E.katalog hw t :=
    fun offer => stuck _ _ (.absturz (absturz_schritt_erfuellbar _ _ offer x))
  let η : I.Lauf E := ⟨start, h, hw, zeit0.erlaubePausen pause, fun _ => none⟩
  have lauf : I.Laeufe E η :=
    ⟨fair.hardware, fair.konform, admissible, rfl,
      zeit0.erlaubePausen_maximal pause _ (fun _ => rfl), fun _ _ h => nomatch h⟩
  have okPrem : ∀ (c : Kontext) (s u : Zustand _root_.Unit _root_.Unit _root_.Unit _root_.Unit Bool _root_.Unit) (w : _root_.Unit)
      (plans : List (SchrittPlan _root_.Unit _root_.Unit _root_.Unit _root_.Unit)),
      (E.system.regel op).ideal c s w plans u → ∀ n, E.schranken.speicher = some n →
        ((LebendeZellen u).encard ≤ n ∨ LebendeZellen u ⊆ LebendeZellen s) ∧
        ∀ d, E.schranken.stapelTiefe (u.lokal d) ≤ E.schranken.stapelTiefe (s.lokal d) := by
    intro c s u w plans ideal n hn
    cases hn
  have pflicht : RegelSchranken E op := getragen E op okPrem
  have stapelVor : StapelZustand E z := by
    intro c m hm
    obtain rfl := Option.some.inj hm
    change 0 ≤ 0
    exact Nat.le_refl _
  have speicherVor : SpeicherZustand E z := by
    intro n hn
    cases hn
  have res := pflicht lauf 0 entry () ⟨[], []⟩ z (zustand 1)
    rfl rfl rfl rfl (step 0) stapelVor speicherVor
  have bad : (1 : Nat) ≤ 0 := by
    exact res.1 entry 0 rfl
  exact (Nat.not_succ_le_zero 0) bad

end Gabbro.Core.Beobachtung
