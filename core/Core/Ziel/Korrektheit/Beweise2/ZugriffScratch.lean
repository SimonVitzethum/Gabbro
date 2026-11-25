/-
  Scratch module for the access-NI implementation. Deleted before report.
-/
module

public import Core.Beobachtung.Fluss.Beweise.ZugriffKopplung
public import Core.Beobachtung.Fluss.Beweise.ZugriffSchritt
public import Core.Beobachtung.Fluss.Beweise.Gesamt
public import Core.Ast.Semantik.Runtime.Atom.Beweise.Komponierbar
public import Core.Ziel.Korrektheit.Zugriff

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit

open Gabbro.Core.Beobachtung
open Katalog Maschine
open Ast.Semantik (Befehl Plan Schrittform Zustand)

/-- Step 1: the implementation step of a form is its ideal step. -/
theorem test_impl_ideal (f : Ast.Semantik.Befehl)
    {c : Kontext} {s u : Ast.Semantik.Zustand} {w : PUnit} {pl : Plan}
    (h : Ast.Semantik.Befehl.impl f c s w [pl] u) : Ast.Semantik.Befehl.ideal f c s w [pl] u := by
  simpa only [Ast.Semantik.Befehl.impl, Ast.Semantik.Befehl.ideal,
    Ast.Semantik.Schrittform.impl] using h

/-- The fragment unit labels nothing: every cell is public. -/
theorem test_fragment_oeffentlich (p : Ast.Semantik.Fragment) (plattform : Plattform) (x : Ast.Semantik.Zelle) :
    oeffentlich ((Ast.Semantik.Fragment.einheit p plattform).etiketten.ort x) = true := by
  simp only [Ast.Semantik.Fragment.einheit, Einheit.etiketten, Etiketten.leer, oeffentlich, decide_true]

/-- Every state of an admitted run has a consistent complete graph. -/
theorem fragment_speicher_gut_scratch {p : Ast.Semantik.Fragment} {plattform : Plattform}
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
theorem test_zugriff_aktion (z : Ast.Semantik.Zugriffsform) {c : Kontext}
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
theorem test_schreib_gleich (p : Ast.Semantik.Fragment) (plattform : Plattform)
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

/-- The run-level noninterference of one access instruction: a coupled left step with an access head
    forces the right run to take the same step, with equal observations and publicly equal,
    graph-coupled post-states. -/
theorem zugriff_schritt_koppelt_scratch
    (existiert : ZugriffSchrittExistiertAussage)
    (graphKopplung : SpeicherGraphKopplungAussage)
    (p : Ast.Semantik.Fragment) (plattform : Plattform) (z : Ast.Semantik.Zugriffsform)
    {h₁ h₂ : Umgebung} {ρ₁ ρ₂ : Lauf (p.einheit plattform)}
    (vergleich : Vergleich (p.einheit plattform) h₁ h₂ ρ₁ ρ₂)
    (fluss : RegelFluss (p.einheit plattform) (Befehl.zugriff z))
    {predictor : Praediktor} {t : Nat} {c : Kontext} {w : PUnit}
    {spur : SchrittSpur Ast.Semantik.Zelle Int} {vor : Zustand}
    (zustand₁ : ρ₁.zeit.zustand t = some vor)
    (kopf₁ : (p.einheit plattform).system.kopf vor c = some (Befehl.zugriff z))
    (spurGlied₁ : ρ₁.zeit.spur t = some (.kontext c w, spur))
    (kopplung : Kopplung (p.einheit plattform) ρ₁ ρ₂ predictor t t) :
    Kopplung (p.einheit plattform) ρ₁ ρ₂ predictor (t + 1) (t + 1) := by
  classical
  rcases spur with ⟨speicher,aussen⟩
  let E := p.einheit plattform
  have kopplungOriginal := kopplung
  obtain ⟨cov, st, len⟩ := kopplung
  obtain ⟨v₂, zustand₂⟩ := fragment_zustand_some vergleich.rechts t
  obtain ⟨⟨lokGleich, endGleich, initialGleich, rechteGleich, leihenGleich, antwortGleich⟩,
    epocheEq, geliefertEq, kerneEq, statusEq⟩ := st vor v₂ zustand₁ zustand₂
  have quellGleich₁₂ : QuellzustandGleich E vor v₂ :=
    ⟨lokGleich, endGleich, initialGleich, rechteGleich, leihenGleich, antwortGleich⟩
  have kopf₂ : E.system.kopf v₂ c = some (Befehl.zugriff z) :=
    zugriffKopfGleich p plattform quellGleich₁₂ statusEq kopf₁
  obtain ⟨_, atVGut, gutVGut⟩ := fragment_speicher_gut_scratch vergleich.links t
  have zustandGut₁ : vor.SpeicherGut := by
    rw [Option.some.inj (zustand₁.symm.trans atVGut)]
    exact gutVGut
  obtain ⟨_, atWGut, gutWGut⟩ := fragment_speicher_gut_scratch vergleich.rechts t
  have zustandGut₂ : v₂.SpeicherGut := by
    rw [Option.some.inj (zustand₂.symm.trans atWGut)]
    exact gutWGut
  have graphGleich : SpeicherGraphKopplungZustand E vor v₂ :=
    graphKopplung p plattform vergleich predictor t kopplungOriginal vor v₂ zustand₁ zustand₂
  have takt₁ := ρ₁.zeit.takt t
  rw [spurGlied₁, zustand₁] at takt₁
  generalize hNext1 : ρ₁.zeit.zustand (t + 1) = nxt1 at takt₁
  cases takt₁ with
  | wartet label _ _ => cases label
  | schritt label step =>
    cases label
    cases step with
    | schritt impl =>
      cases impl with
      | kontext keinAbsturz₁ bereit₁ regel₁ aus₁ =>
        rename_i postL uL planL
        obtain ⟨f₁, kopfL, implL⟩ := regel₁
        have ff : Befehl.zugriff z = f₁ := Option.some.inj (kopf₁.symm.trans kopfL)
        subst f₁
        have idealL : Befehl.ideal (Befehl.zugriff z) c vor w [planL] uL := by
          simpa only [Befehl.impl, Befehl.ideal, Schrittform.impl, Befehl.regel, Ast.Semantik.system, Ast.Semantik.Fragment.einheit] using implL
        have fsL : FormSchritt E (Befehl.zugriff z) c vor w planL uL := ⟨kopf₁, idealL⟩
        have crashEq : (ρ₁.hw.angebot t).crash = (ρ₂.hw.angebot t).crash :=
          congrArg (fun pr => (pr.1 t).2.2.2.2.2.1) vergleich.politik
        have coreEq : (ρ₁.hw.angebot t).core = (ρ₂.hw.angebot t).core :=
          congrArg (fun pr => (pr.1 t).1) vergleich.politik
        have interruptEq : (ρ₁.hw.angebot t).interrupt = (ρ₂.hw.angebot t).interrupt :=
          congrArg (fun pr => (pr.1 t).2.1) vergleich.politik
        have signaleEq : (ρ₁.hw.angebot t).interrupts = (ρ₂.hw.angebot t).interrupts :=
          congrArg (fun pr => (pr.1 t).2.2.1) vergleich.politik
        have auswahlEq : (ρ₁.hw.angebot t).interruptAuswahl = (ρ₂.hw.angebot t).interruptAuswahl := by
          simp only [Gelegenheit.interruptAuswahl, signaleEq]
        have bereit₂ : KannSchreiten ρ₂.hw t c v₂ := by
          obtain ⟨k, geleg₁, kern₁, stat₁⟩ := bereit₁
          refine ⟨k, ?_, ?_, ?_⟩
          · change (ρ₂.hw.angebot t).core = some k
            rw [← coreEq]
            exact geleg₁
          · rw [← kerneEq]; exact kern₁
          · rw [← statusEq]; exact stat₁
        have auswahl₁none : (ρ₁.hw.angebot t).interruptAuswahl = none := by
          obtain ⟨k₁, geleg₁, _, _⟩ := bereit₁
          have core₁ : (ρ₁.hw.angebot t).core = some k₁ := geleg₁
          cases haus : (ρ₁.hw.angebot t).interruptAuswahl with
          | some _ =>
            have res := (vergleich.links.2.1.2 t).interrupt_reserviert haus
            rw [res.2.1] at core₁
            cases core₁
          | none => rfl
        have auswahl₂none : (ρ₂.hw.angebot t).interruptAuswahl = none := by
          rw [← auswahlEq]; exact auswahl₁none
        have crash₂false : (ρ₂.hw.angebot t).crash = false := by
          rw [← crashEq]; exact keinAbsturz₁
        have takt₂ := ρ₂.zeit.takt t
        rw [zustand₂] at takt₂
        generalize hNext2 : ρ₂.zeit.zustand (t + 1) = nxt2 at takt₂
        cases takt₂ with
        | wartet label₂ gleich₂ hp =>
          obtain ⟨wu, planR, uR, es, g, step, folge⟩ :=
            existiert p plattform z v₂ c kopf₂ zustandGut₂
          obtain ⟨spurR, sR, runR⟩ :=
            Ast.Semantik.zugriffKomponierbar p plattform z t v₂ c wu planR uR es g kopf₂ step folge
          have regelR : E.system.ImplSchritt c v₂ wu [planR] uR := by
            refine ⟨Befehl.zugriff z, kopf₂, ?_⟩
            dsimp [E]
            simpa only [Befehl.impl, Befehl.ideal, Schrittform.impl, Befehl.regel,
              Ast.Semantik.system, Ast.Semantik.Fragment.einheit] using step
          have crash₂ : (ρ₂.hw.angebot t).crash = false := by
            rw [← crashEq]; exact keinAbsturz₁
          have stepR : ImplSchritt E.einrichtung E.system E.katalog ρ₂.hw t v₂
              (.kontext c wu, spurR) sR := .kontext crash₂ bereit₂ regelR runR
          exact (hp _ _ (Lauffolge.schritt stepR)).elim
        | schritt label₂ step₂ =>
          have someEv : ∃ wahl spur', ρ₂.zeit.spur t = some (wahl, spur') := by
            cases hlab : ρ₂.zeit.spur t with
            | none => rw [hlab] at label₂; cases label₂
            | some ev =>
              obtain ⟨wahl', spur'⟩ := ev
              refine ⟨wahl', spur', ?_⟩
              simpa only using hlab
          obtain ⟨wahl₂, spur₂, label₂'⟩ := someEv
          rcases spur₂ with ⟨speicher2,aussen2⟩
          have evEq := Option.some.inj (label₂.symm.trans label₂')
          rw [evEq] at step₂
          cases wahl₂ with
          | antwort a => exact (antwortNI p plattform h₂ ρ₂ vergleich.rechts t a ⟨speicher2, aussen2⟩ label₂').elim
          | interrupt irqId =>
            cases step₂ with
            | schritt impl₂' =>
              cases impl₂' with
              | interrupt _ enters₂ =>
                obtain ⟨_, _, _, _, _, pending₂, _, _, _, _, _⟩ := enters₂
                have contra := pending₂.2.2.2.2
                rw [auswahl₂none] at contra
                cases contra
          | absturz =>
            cases step₂ with
            | schritt impl₂' =>
              cases impl₂' with
              | absturz crash₂ =>
                rw [crash₂.1.2] at crash₂false
                cases crash₂false
          | kontext c₂ wChoice₂ =>
            cases step₂ with
            | schritt impl₂' =>
              cases impl₂' with
              | kontext keinAbsturz₂ bereit₂' regel₂' aus₂' =>
                rename_i postR uR planR
                obtain ⟨f₂, kopfR, implR⟩ := regel₂'
                have cEq : c₂ = c := by
                  obtain ⟨k₁, geleg₁, kern₁, _⟩ := bereit₁
                  obtain ⟨k₂, geleg₂, kern₂, _⟩ := bereit₂'
                  have core₁ : (ρ₁.hw.angebot t).core = some k₁ := geleg₁
                  have core₂v : (ρ₂.hw.angebot t).core = some k₂ := geleg₂
                  have kk : k₁ = k₂ := Option.some.inj (core₁.symm.trans (coreEq.trans core₂v))
                  have gleich : (v₂.kerne k₂).laeuft = some c := by
                    rw [← kk, ← kerneEq]; exact kern₁
                  exact Option.some.inj (kern₂.symm.trans gleich)
                rw [cEq] at kopfR implR
                have ff₂ : f₂ = Befehl.zugriff z := (Option.some.inj (kopf₂.symm.trans kopfR)).symm
                subst f₂
                have idealR : Befehl.ideal (Befehl.zugriff z) c v₂ wChoice₂ [planR] uR := by
                  simpa only [Befehl.impl, Befehl.ideal, Schrittform.impl, Befehl.regel, Ast.Semantik.system, Ast.Semantik.Fragment.einheit] using implR
                have fsR : FormSchritt E (Befehl.zugriff z) c v₂ wChoice₂ planR uR := ⟨kopf₂, idealR⟩
                obtain ⟨postGleich, planSichtEq, ausgabeSichtEq⟩ :=
                  zugriffSchrittNI p plattform (Befehl.zugriff z) rfl fluss
                    quellGleich₁₂ fsL fsR
                rw [cEq] at aus₂'
                obtain ⟨rahmenL, _, _, _, fuehrtAusL, speicherfolgeL, s'EqL⟩ := aus₁
                have aktionL : planL.aktion = .intern := test_zugriff_aktion z idealL
                rw [aktionL] at fuehrtAusL
                cases fuehrtAusL
                simp only [List.nil_append, List.append_nil, List.map_nil] at speicherfolgeL
                obtain ⟨rahmenR, _, _, _, fuehrtAusR, speicherfolgeR, s'EqR⟩ := aus₂'
                have aktionR : planR.aktion = .intern := test_zugriff_aktion z idealR
                rw [aktionR] at fuehrtAusR
                cases fuehrtAusR
                simp only [List.nil_append, List.append_nil, List.map_nil] at speicherfolgeR
                have hlabels : planL.lesen ++ schreibEreignisse planL.fuss planL.schreibt planL.modus planL.wert =
                    planR.lesen ++ schreibEreignisse planR.fuss planR.schreibt planR.modus planR.wert := by
                  rw [zugriffPlanSicht_lesen p plattform planSichtEq,
                    test_schreib_gleich p plattform planSichtEq]
                have hgAll : ∀ x, HatQuelle vor.graph x ↔ HatQuelle v₂.graph x := by
                  intro x
                  exact graphGleich x (test_fragment_oeffentlich p plattform x)
                have speicherBeobEq : speicher.filterMap
                    (speicherBeob (Grund := PUnit) (Form := Befehl) E.etiketten) =
                    speicher2.filterMap
                    (speicherBeob (Grund := PUnit) (Form := Befehl) E.etiketten) := by
                  have initialEq : vor.initial = v₂.initial := by
                    funext x
                    have hx := initialGleich x
                    have hx' : some (vor.initial x) = some (v₂.initial x) := by
                      simpa only [Ast.Semantik.Fragment.einheit, Einheit.etiketten, Etiketten.leer,
                        oeffentlich, decide_true, sichtbar, if_true] using hx
                    exact Option.some.inj hx'
                  rw [initialEq] at speicherfolgeL
                  rw [← hlabels] at speicherfolgeR
                  rcases zugriff_labels_form z idealL with hleer | ⟨l, heinzel⟩
                  · rw [hleer] at speicherfolgeL speicherfolgeR
                    have hsL : speicher = [] := speicherfolge_nil_es speicherfolgeL
                    have hsR : speicher2 = [] := speicherfolge_nil_es speicherfolgeR
                    rw [hsL, hsR]
                  · rw [heinzel] at speicherfolgeL speicherfolgeR
                    exact zugriffSpeicherbeob_gleich_aus_kopplung E.etiketten
                      (fun _ => hgAll l.ort) speicherfolgeL speicherfolgeR
                have beobL : schrittBeob ρ₁ predictor t =
                    speicher.filterMap (speicherBeob E.etiketten) := by
                  have hKontext : kontextBeob ρ₁ predictor t c vor postL ⟨speicher, []⟩ = [] := by
                    rw [kontextBeob]
                    dsimp only
                    rw [kopf₁]
                    have hSpek : E.katalog.plattform.spekulationshuelle.zugriffe
                        (E.fluss.spekulativ (Befehl.zugriff z) (vor.lokal c) predictor) = [] := by
                      cases plattform <;> rfl
                    have hKonstant : E.fluss.konstantzeit (Befehl.zugriff z) = false := by rfl
                    have hCommit : commitBeob (Form := Befehl) E.katalog.plattform vor postL = [] := by
                      rw [commitBeob]
                      have hw : postL.buchung.wirkungen = vor.buchung.wirkungen := by
                        have h' : postL.buchung.wirkungen = uL.buchung.wirkungen := by rw [s'EqL]
                        exact h'.trans (zugriff_buchung_wirkungen_gleich z idealL)
                      rw [hw, List.drop_length, List.filterMap_nil]
                    have hAusgabe : ausgabeBeob E c (vor.lokal c) (postL.lokal c) = [] := by rfl
                    have hZeit : zeitBeob ρ₁ c (vor.lokal c) (postL.lokal c) = [] := by rfl
                    dsimp [E] at hSpek hKonstant hCommit hAusgabe hZeit
                    simp only [hSpek, hKonstant, Bool.false_eq_true, if_false,
                      List.map_nil, List.nil_append, hCommit, hAusgabe, hZeit]
                  have hEnde : ∀ d, (neuBeendet vor postL E.etiketten d).isSome = false := by
                    intro d
                    rw [neuBeendet]
                    have hs : postL.status d = vor.status d := by
                      have h' : postL.status = uL.status := by rw [s'EqL]
                      rw [h']
                      exact congrFun (zugriff_status_gleich z idealL) d
                    rw [hs]
                    cases hst : vor.status d <;> rfl
                  have hKeinEnde : ¬ ∃ d, (neuBeendet vor postL E.etiketten d).isSome = true := by
                    rintro ⟨d, hd⟩
                    rw [hEnde d] at hd
                    cases hd
                  rw [schrittBeob, spurGlied₁, zustand₁, hNext1]
                  dsimp [E] at hKontext hKeinEnde ⊢
                  simp only [hKontext, hKeinEnde, if_false, List.nil_append,
                    List.append_nil, List.flatMap_nil]
                have beobR : schrittBeob ρ₂ predictor t =
                    speicher2.filterMap (speicherBeob E.etiketten) := by
                  have hKontext : kontextBeob ρ₂ predictor t c v₂ postR ⟨speicher2, []⟩ = [] := by
                    rw [kontextBeob]
                    dsimp only
                    rw [kopf₂]
                    have hSpek : E.katalog.plattform.spekulationshuelle.zugriffe
                        (E.fluss.spekulativ (Befehl.zugriff z) (v₂.lokal c) predictor) = [] := by
                      cases plattform <;> rfl
                    have hKonstant : E.fluss.konstantzeit (Befehl.zugriff z) = false := by rfl
                    have hCommit : commitBeob (Form := Befehl) E.katalog.plattform v₂ postR = [] := by
                      rw [commitBeob]
                      have hw : postR.buchung.wirkungen = v₂.buchung.wirkungen := by
                        have h' : postR.buchung.wirkungen = uR.buchung.wirkungen := by rw [s'EqR]
                        exact h'.trans (zugriff_buchung_wirkungen_gleich z idealR)
                      rw [hw, List.drop_length, List.filterMap_nil]
                    have hAusgabe : ausgabeBeob E c (v₂.lokal c) (postR.lokal c) = [] := by rfl
                    have hZeit : zeitBeob ρ₂ c (v₂.lokal c) (postR.lokal c) = [] := by rfl
                    dsimp [E] at hSpek hKonstant hCommit hAusgabe hZeit
                    simp only [hSpek, hKonstant, Bool.false_eq_true, if_false,
                      List.map_nil, List.nil_append, hCommit, hAusgabe, hZeit]
                  have hEnde : ∀ d, (neuBeendet v₂ postR E.etiketten d).isSome = false := by
                    intro d
                    rw [neuBeendet]
                    have hs : postR.status d = v₂.status d := by
                      have h' : postR.status = uR.status := by rw [s'EqR]
                      rw [h']
                      exact congrFun (zugriff_status_gleich z idealR) d
                    rw [hs]
                    cases hst : v₂.status d <;> rfl
                  have hKeinEnde : ¬ ∃ d, (neuBeendet v₂ postR E.etiketten d).isSome = true := by
                    rintro ⟨d, hd⟩
                    rw [hEnde d] at hd
                    cases hd
                  rw [schrittBeob, label₂', zustand₂, hNext2, cEq]
                  dsimp [E] at hKontext hKeinEnde ⊢
                  simp only [hKontext, hKeinEnde, if_false, List.nil_append,
                    List.append_nil, List.flatMap_nil]
                have beobEq : schrittBeob ρ₁ predictor t = schrittBeob ρ₂ predictor t := by
                  rw [beobL, beobR, speicherBeobEq]
                apply kopplung_nach_gleicher_beob kopplungOriginal beobEq
                intro v w hv hw
                rw [hNext1] at hv
                rw [hNext2] at hw
                obtain rfl := Option.some.inj hv
                obtain rfl := Option.some.inj hw
                refine ⟨?_, ?_, ?_, ?_, ?_⟩
                · have qgl : QuellzustandGleich E postL uL := by
                    rw [s'EqL]
                    refine ⟨?_, ?_, ?_, rfl, rfl, ?_⟩
                    · intro c p hp; rfl
                    · intro c; rfl
                    · intro x; rfl
                    · intro c; rfl
                  have qgr : QuellzustandGleich E uR postR := by
                    rw [s'EqR]
                    refine ⟨?_, ?_, ?_, rfl, rfl, ?_⟩
                    · intro c p hp; rfl
                    · intro c; rfl
                    · intro x; rfl
                    · intro c; rfl
                  exact Gabbro.Core.Ast.Semantik.Beobachtung.QuellzustandGleich.trans qgl
                    (Gabbro.Core.Ast.Semantik.Beobachtung.QuellzustandGleich.trans postGleich qgr)
                · have eL : postL.epoche = uL.epoche := by rw [s'EqL]
                  have eR : postR.epoche = uR.epoche := by rw [s'EqR]
                  exact eL.trans (rahmenL.epoche.trans (epocheEq.trans (rahmenR.epoche.symm.trans eR.symm)))
                · have gL : postL.geliefert = uL.geliefert := by rw [s'EqL]
                  have gR : postR.geliefert = uR.geliefert := by rw [s'EqR]
                  exact gL.trans (rahmenL.geliefert.trans (geliefertEq.trans (rahmenR.geliefert.symm.trans gR.symm)))
                · have kL : postL.kerne = uL.kerne := by rw [s'EqL]
                  have kR : postR.kerne = uR.kerne := by rw [s'EqR]
                  exact kL.trans (rahmenL.kerne.trans (kerneEq.trans (rahmenR.kerne.symm.trans kR.symm)))
                · have sL : postL.status = uL.status := by rw [s'EqL]
                  have sR : postR.status = uR.status := by rw [s'EqR]
                  exact sL.trans ((zugriff_status_gleich z idealL).trans
                    (statusEq.trans ((zugriff_status_gleich z idealR).symm.trans sR.symm)))

end Gabbro.Core.Ziel.Korrektheit
