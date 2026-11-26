/-
  THE RUN-LEVEL NONINTERFERENCE OF AN ACCESS INSTRUCTION (MK-13). The pinned `ZugriffNIAussage`
  is the family duty for `.zugriff`; the step-level part is `ZugriffSchritt`, the graph coupling
  of public cells is the pinned `SpeicherGraphKopplungAussage`. This module connects them: a coupled
  left step with an access head forces the right run to take the same step (lockstep through the
  step kinds), the two memory event lists agree by the graph coupling, the non-memory part of the
  observation is empty (the unit labels nothing and the step has the internal protocol action),
  and the post-states are publicly equal with the machine fields and the graph coupling preserved.
-/
module

public import Core.Beobachtung.Fluss.Beweise.ZugriffKopplung
public import Core.Beobachtung.Fluss.Beweise.ZugriffSchritt
public import Core.Beobachtung.Fluss.Beweise.Gesamt
public import Core.Ast.Semantik.Runtime.Atom.Beweise.Komponierbar
public import Core.Ziel.Korrektheit.Zugriff

@[expose] public section

namespace Gabbro.Core.Beobachtung
open Katalog Maschine
open Ast.Semantik (Befehl Plan Schrittform Zustand)

/-- Step 1: the implementation step of a form is its ideal step. -/
theorem impl_ideal_gleich (f : Ast.Semantik.Befehl)
    {c : Kontext} {s u : Ast.Semantik.Zustand} {w : PUnit} {pl : Plan}
    (h : Ast.Semantik.Befehl.impl f c s w [pl] u) : Ast.Semantik.Befehl.ideal f c s w [pl] u := by
  simpa only [Ast.Semantik.Befehl.impl, Ast.Semantik.Befehl.ideal,
    Ast.Semantik.Schrittform.impl] using h

/-- The fragment unit labels nothing: every cell is public. -/
theorem fragment_zelle_oeffentlich (p : Ast.Semantik.Fragment) (plattform : Plattform) (x : Ast.Semantik.Zelle) :
    oeffentlich ((Ast.Semantik.Fragment.einheit p plattform).etiketten.ort x) = true := by
  simp only [Ast.Semantik.Fragment.einheit, Einheit.etiketten, Etiketten.leer, oeffentlich, decide_true]

/-- Every state of an accepted run has a consistent complete graph. -/
theorem fragment_speicher_gut {p : Ast.Semantik.Fragment} {plattform : Plattform}
    {h : Umgebung} {ρ : Lauf (p.einheit plattform)}
    (lauf : Laeufe (p.einheit plattform) h ρ) (t : Nat) :
    ∃ z, ρ.zeit.zustand t = some z ∧ z.SpeicherGut := by
  induction t with
  | zero =>
    refine ⟨(I.start (p.einheit plattform) ρ.start).2, ?_, ?_⟩
    rw [lauf.2.2.2]
    exact fragment_geladen p plattform lauf.1 lauf.2.2.1
    change Speicher.Zustand.leer.graph.Konsistent ∧ Speicher.Zustand.leer.graph.Vollstaendig
    exact ⟨Speicher.Zustand.leer_konsistent, Speicher.Zustand.leer_vollstaendig⟩
  | succ t ih =>
    obtain ⟨z, atZ, gut⟩ := ih
    cases tick : ρ.zeit.takt t with
    | schritt label step =>
      rw [atZ] at step
      cases nach : ρ.zeit.zustand (t + 1) with
      | none => rw [nach] at step; cases step
      | some next => rw [nach] at step; cases step with
        | schritt impl => exact ⟨next, rfl, impl_speicher_gut _ _ impl gut⟩
    | wartet label gleich _ => refine ⟨z, ?_, gut⟩; exact gleich.trans atZ

/-- An access step has the internal protocol action. -/
theorem zugriff_aktion_intern (z : Ast.Semantik.Zugriffsform) {c : Kontext}
    {s u : Ast.Semantik.Zustand} {w : PUnit} {p : Plan}
    (h : Ast.Semantik.Befehl.ideal (Ast.Semantik.Befehl.zugriff z) c s w [p] u) :
    p.aktion = .intern := by
  unfold Ast.Semantik.Befehl.ideal Ast.Semantik.Befehl.form at h
  unfold Ast.Semantik.Schrittform.ideal at h
  cases z <;> simp only [Ast.Semantik.Zugriffsform.klasse] at h
  all_goals
    unfold Ast.Semantik.Schrittform.zugriffsschritt at h
    rcases h with h | h
    · have hp : p = Ast.Semantik.plan := (List.cons.inj h.2.1).1
      rw [hp]
      rfl
    · obtain ⟨v, _, hp, _⟩ := h.2
      have hp' : p = _ := (List.cons.inj hp).1
      rw [hp']
      rfl

/-- Rewrite `HatQuelle` as a list-membership statement. -/
theorem hatQuelle_iff_mem {Ort Wert : Type}
    (ev : List (Speicher.Ereignis (SpeicherAkteur Ort) Ort Wert)) (x : Ort) :
    (∃ i, ∃ h : i < ev.length, (ev[i]'h).lab.art.schreibt ∧ (ev[i]'h).lab.ort = x) ↔
      ∃ e ∈ ev, e.lab.art.schreibt ∧ e.lab.ort = x := by
  constructor
  · rintro ⟨i, h, hs, ho⟩
    refine ⟨ev[i]'h, ?_, hs, ho⟩
    rw [List.mem_iff_getElem?]
    exact ⟨i, by rw [List.getElem?_eq_some_iff]; exact ⟨h, rfl⟩⟩
  · rintro ⟨e, he, hs, ho⟩
    rw [List.mem_iff_getElem?] at he
    obtain ⟨i, hi⟩ := he
    rw [List.getElem?_eq_some_iff] at hi
    obtain ⟨hli, heq⟩ := hi
    refine ⟨i, hli, ?_, ?_⟩
    · rw [heq]; exact hs
    · rw [heq]; exact ho

/-- Appending the same event list to two graphs that agree on `HatQuelle` keeps the agreement. -/
theorem hatQuelle_append_iff {Ort Wert : Type}
    {g₁ g₂ : SpeicherGraph Ort Wert}
    {es₁ es₂ : List (SpeicherAkteur Ort × Speicher.Etikett Ort Wert)}
    {g₁' g₂' : SpeicherGraph Ort Wert}
    (hev₁ : g₁'.ev = g₁.ev ++ es₁.map (fun x => ⟨x.1, x.2⟩))
    (hev₂ : g₂'.ev = g₂.ev ++ es₂.map (fun x => ⟨x.1, x.2⟩))
    (hes : es₁ = es₂) (hg : ∀ x, HatQuelle g₁ x ↔ HatQuelle g₂ x) :
    ∀ x, HatQuelle g₁' x ↔ HatQuelle g₂' x := by
  intro x
  rw [HatQuelle, HatQuelle, hev₁, hev₂, hatQuelle_iff_mem, hatQuelle_iff_mem, hes]
  constructor
  · rintro ⟨e, he, hs, ho⟩
    rw [List.mem_append] at he
    rcases he with he | he
    · have hq1 : HatQuelle g₁ x := (hatQuelle_iff_mem g₁.ev x).2 ⟨e, he, hs, ho⟩
      have hq2 : HatQuelle g₂ x := (hg x).1 hq1
      obtain ⟨e2, he2, hs2, ho2⟩ := (hatQuelle_iff_mem g₂.ev x).1 hq2
      exact ⟨e2, by rw [List.mem_append]; exact Or.inl he2, hs2, ho2⟩
    · exact ⟨e, by rw [List.mem_append]; exact Or.inr he, hs, ho⟩
  · rintro ⟨e, he, hs, ho⟩
    rw [List.mem_append] at he
    rcases he with he | he
    · have hq2 : HatQuelle g₂ x := (hatQuelle_iff_mem g₂.ev x).2 ⟨e, he, hs, ho⟩
      have hq1 : HatQuelle g₁ x := (hg x).2 hq2
      obtain ⟨e1, he1, hs1, ho1⟩ := (hatQuelle_iff_mem g₁.ev x).1 hq1
      exact ⟨e1, by rw [List.mem_append]; exact Or.inl he1, hs1, ho1⟩
    · exact ⟨e, by rw [List.mem_append]; exact Or.inr he, hs, ho⟩

/-- An access step records at most one memory label. -/
theorem zugriff_labels_form (z : Ast.Semantik.Zugriffsform) {c : Kontext}
    {s u : Ast.Semantik.Zustand} {w : PUnit} {p : Plan}
    (h : Ast.Semantik.Befehl.ideal (Ast.Semantik.Befehl.zugriff z) c s w [p] u) :
    p.lesen ++ schreibEreignisse p.fuss p.schreibt p.modus p.wert = [] ∨
      ∃ l, p.lesen ++ schreibEreignisse p.fuss p.schreibt p.modus p.wert = [l] := by
  unfold Ast.Semantik.Befehl.ideal Ast.Semantik.Befehl.form at h
  unfold Ast.Semantik.Schrittform.ideal at h
  cases z <;> simp only [Ast.Semantik.Zugriffsform.klasse] at h
  all_goals
    unfold Ast.Semantik.Schrittform.zugriffsschritt at h
    rcases h with h | h
    · have hp : p = Ast.Semantik.plan := (List.cons.inj h.2.1).1
      subst p
      left; rfl
    · obtain ⟨v, _, hp, _⟩ := h.2
      have hp' : p = _ := (List.cons.inj hp).1
      subst p
      first
      | left; rfl
      | right
        simp only [Ast.Semantik.Schrittform.plan, Ast.Semantik.Wirkungsklasse.plan,
          Ast.Semantik.Befehl.klasse, Ast.Semantik.Zugriffsform.klasse, Ast.Semantik.plan,
          List.append_nil, List.nil_append, List.filter_true, List.map_cons,
          List.map_nil, List.filter_cons_of_pos, List.filter_cons_of_neg,
          decide_eq_true_eq, eq_self_iff_true, not_false_eq_true, schreibEreignisse]
        refine ⟨_, rfl⟩

/-- `filterMap` of an if-then-some is the map over the boolean filter. -/
theorem filterMap_if_bool_eq {α β : Type} (f : α → Bool) (g : α → β) (l : List α) :
    l.filterMap (fun x => if f x then some (g x) else none) = (l.filter f).map g := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    cases hb : f x
    · have hneg : ¬ f x = true := by rw [hb]; decide
      simp only [List.filterMap_cons, hb, if_neg Bool.false_eq_true_eq_False,
        List.filter_cons_of_neg hneg, ih]
    · simp only [List.filterMap_cons, hb, if_true, List.filter_cons_of_pos,
        List.map_cons, ih]

/-- The public write tuples of a plan determine its write events. -/
theorem zugriff_schreibereignisse_gleich (p : Ast.Semantik.Fragment) (plattform : Plattform)
    {planL planR : Ast.Semantik.Plan}
    (h : PlanSicht (p.einheit plattform) planL = PlanSicht (p.einheit plattform) planR) :
    schreibEreignisse planL.fuss planL.schreibt planL.modus planL.wert =
      schreibEreignisse planR.fuss planR.schreibt planR.modus planR.wert := by
  have ht := congrArg (fun x => x.2.1) h
  rw [PlanSicht, PlanSicht] at ht
  simp only [Ast.Semantik.Fragment.einheit, Einheit.etiketten, Etiketten.leer,
    oeffentlich, decide_true, Bool.and_true, if_true] at ht
  rw [filterMap_if_bool_eq, filterMap_if_bool_eq] at ht
  rw [schreibEreignisse, schreibEreignisse]
  let zuEtikett : Ast.Semantik.Zelle × Speicher.Modus × Int → Speicher.Etikett Ast.Semantik.Zelle Int :=
    fun t => ⟨.schreiben, t.1, t.2.1, t.2.2, t.2.2⟩
  have hmapL : (planL.fuss.filter planL.schreibt).map
      (fun x => ⟨.schreiben, x, planL.modus x, planL.wert x, planL.wert x⟩) =
    ((planL.fuss.filter planL.schreibt).map
      (fun x => (x, planL.modus x, planL.wert x))).map zuEtikett := by
    rw [List.map_map]
    rfl
  have hmapR : (planR.fuss.filter planR.schreibt).map
      (fun x => ⟨.schreiben, x, planR.modus x, planR.wert x, planR.wert x⟩) =
    ((planR.fuss.filter planR.schreibt).map
      (fun x => (x, planR.modus x, planR.wert x))).map zuEtikett := by
    rw [List.map_map]
    rfl
  rw [hmapL, hmapR, ht]

/-- An access step leaves the machine-owned status as it was; the form only updates its frame. -/
theorem zugriff_status_gleich (z : Ast.Semantik.Zugriffsform) {c : Kontext}
    {s u : Zustand} {w : PUnit} {p : Plan}
    (h : Befehl.ideal (Befehl.zugriff z) c s w [p] u) :
    u.status = s.status := by
  unfold Befehl.ideal Befehl.form at h
  unfold Schrittform.ideal at h
  cases z <;> simp only [Ast.Semantik.Zugriffsform.klasse] at h
  all_goals
    unfold Schrittform.zugriffsschritt at h
    rcases h with h | h
    · have hu := h.2.2
      rw [hu]
      rfl
    · obtain ⟨_, _, _, hu⟩ := h.2
      rw [hu]
      rfl

/-- An access step books an address but adds no ledger effects. -/
theorem zugriff_buchung_wirkungen_gleich (z : Ast.Semantik.Zugriffsform) {c : Kontext}
    {s u : Zustand} {w : PUnit} {p : Plan}
    (h : Befehl.ideal (Befehl.zugriff z) c s w [p] u) :
    u.buchung.wirkungen = s.buchung.wirkungen := by
  unfold Befehl.ideal Befehl.form at h
  unfold Schrittform.ideal at h
  cases z <;> simp only [Ast.Semantik.Zugriffsform.klasse] at h
  all_goals
    unfold Schrittform.zugriffsschritt at h
    rcases h with h | h
    · have hu := h.2.2
      rw [hu]
      rfl
    · obtain ⟨_, _, _, hu⟩ := h.2
      rw [hu]
      simp only [Ast.Semantik.Schrittform.zugriffNach, Ast.Semantik.Schrittform.nach,
        Ast.Semantik.Schrittform.buchungNach, Ast.Semantik.Befehl.klasse,
        Ast.Semantik.Zugriffsform.klasse]

/-- A `Speicherfolge` with no labels records no events. -/
theorem speicherfolge_nil_es {Ort Wert : Type} {anfang : Ort → Wert}
    {f : SpeicherAkteur Ort} {g g' : SpeicherGraph Ort Wert} {es : List (SpeicherAkteur Ort × Speicher.Etikett Ort Wert)}
    (h : Speicherfolge anfang f g [] es g') : es = [] := by
  cases h
  rfl

/-- Both runs append the same finite observation and reach publicly equal post-states. -/
theorem kopplung_nach_gleicher_beob
    {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form} [DecidableEq L]
    {ρ₁ ρ₂ : Lauf E} {predictor : Praediktor} {t : Nat}
    (kopplung : Kopplung E ρ₁ ρ₂ predictor t t)
    (beobEq : schrittBeob ρ₁ predictor t = schrittBeob ρ₂ predictor t)
    (zustandPost : ∀ {v w}, ρ₁.zeit.zustand (t + 1) = some v → ρ₂.zeit.zustand (t + 1) = some w →
      QuellzustandGleich E v w ∧ v.epoche = w.epoche ∧ v.geliefert = w.geliefert ∧
        v.kerne = w.kerne ∧ v.status = w.status) :
    Kopplung E ρ₁ ρ₂ predictor (t + 1) (t + 1) := by
  obtain ⟨cov, st, len⟩ := kopplung
  refine ⟨?_, ?_, ?_⟩
  · change List.Forall₂ (EreignisAequiv E.fluss.freigabe)
      (NiedrigeBeob E ρ₁ predictor t ++ schrittBeob ρ₁ predictor t)
      ((NiedrigeBeob E ρ₂ predictor t ++ schrittBeob ρ₂ predictor t).take
        ((NiedrigeBeob E ρ₁ predictor t ++ schrittBeob ρ₁ predictor t).length))
    rw [beobEq]
    have hl : (NiedrigeBeob E ρ₂ predictor t ++ schrittBeob ρ₂ predictor t).length =
        (NiedrigeBeob E ρ₁ predictor t ++ schrittBeob ρ₂ predictor t).length := by
      rw [List.length_append, List.length_append, len]
    rw [List.take_of_length_le (le_of_eq hl)]
    have htakeB : (NiedrigeBeob E ρ₂ predictor t).take
        (NiedrigeBeob E ρ₁ predictor t).length = NiedrigeBeob E ρ₂ predictor t := by
      exact List.take_of_length_le (le_of_eq len.symm)
    rw [htakeB] at cov
    have reflMem : List.Forall₂ (EreignisAequiv E.fluss.freigabe)
        (schrittBeob ρ₂ predictor t) (schrittBeob ρ₂ predictor t) := by
      induction schrittBeob ρ₂ predictor t with
      | nil => exact .nil
      | cons e es ih => exact .cons (.gleich e) ih
    exact List.rel_append cov reflMem
  · intro v w hv hw
    exact zustandPost hv hw
  · change (NiedrigeBeob E ρ₁ predictor t ++ schrittBeob ρ₁ predictor t).length =
      (NiedrigeBeob E ρ₂ predictor t ++ schrittBeob ρ₂ predictor t).length
    rw [List.length_append, List.length_append, beobEq, len]


end Gabbro.Core.Beobachtung
