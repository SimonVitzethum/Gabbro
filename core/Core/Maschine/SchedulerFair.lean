/-
  File:      core/Core/Maschine/SchedulerFair.lean
  Subject:   THE TWO RUN PREMISES OF THE PROGRESS LEG — scheduler fairness and preemption return.

  `Laeufe` (in `Core/Maschine/Start.lean`) admits every maximal run: hardware conformance, an
  admitted start and the loaded initial state. Two run properties that admissibility does NOT
  supply are premises of the pinned progress statement `FortschrittAkzeptiertAussage` instead
  (owner decisions on MK-11):

  * `SchedulerFair`: a context that is dispatched, live and rule-enabled on a whole suffix —
    with a crash-free tick and a complete protocol step available — and that has opportunities
    on its dispatch core infinitely often, is stepped infinitely often. This is a property of
    the execution model, not a catalogue row: hardware rows speak about cores, deliveries and
    cycles only and never arbitrate which ready context takes a step, while the runtime
    dispatches its contexts with a generic dispatch proof (PERFECT-MODEL §3.4: executing the
    dispatch is a language obligation). A program therefore proves nothing about it.
  * `VerdraengungKehrtZurueck`: a live context displaced from its core by an interrupt is
    dispatched again on some core at a strictly later cut (the return of the preempting
    handler). The tightened `BleibtOffen` (a context dispatched on the whole suffix) is
    rejected: real runs preempt. Instead this premise excludes exactly the preemption without
    return, which would otherwise hang a context that `BleibtOffen` still covers.

  The fair schedule (`fairerZeit`) serves every continuously ready context infinitely often
  (`fairer_zeit_fair`), so `fairer_lauf_mit_hw` builds an admissible scheduler-fair run for
  every conformant hardware history. A fair run over a history without raised interrupts takes
  no interrupt step at all and hence satisfies `VerdraengungKehrtZurueck` vacuously.
-/
module

public import Core.Maschine.Start

@[expose] public section

namespace Gabbro.Core.Maschine

open Gabbro.Core.Katalog

variable {L Ort Wert Raum Lok Grund Bedingung Wahl ι : Type}
variable (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι)
variable [DecidableEq L]

/-- Scheduler fairness of an implementation run (PERFECT-MODEL §3.7, step M11): a context that is
    dispatched, live and rule-enabled on a whole suffix — with a crash-free tick and a complete
    protocol step available — and that has opportunities on its dispatch core infinitely often,
    is stepped infinitely often. A premise of the progress leg, not part of run admissibility. -/
def SchedulerFair (ρ : Lauf E) : Prop :=
  ∀ (a : Nat) (c : Kontext),
    (∀ t, a ≤ t → ∃ s, ρ.zeit.zustand t = some s ∧
      (∃ k, (s.kerne k).laeuft = some c) ∧ s.status c = .laeuft ∧
      (ρ.hw.angebot t).crash = false ∧
      ∃ w plan u spur s', E.system.ImplSchritt c s w [plan] u ∧
        FuehrtSchrittAus E.einrichtung t c s u plan spur s') →
    (∀ n, a ≤ n → ∃ t, n ≤ t ∧ ∃ k, ρ.hw.gelegenheit t k ∧
      ∃ s, ρ.zeit.zustand t = some s ∧ (s.kerne k).laeuft = some c) →
    ∀ n, a ≤ n → ∃ t, n ≤ t ∧ ∃ w spur, ρ.zeit.spur t = some (.kontext c w, spur)

/-- Preempted live contexts are reinstated on some core at a strictly later cut: whenever a live
    context dispatched on a core meets an interrupt tick, it is dispatched again afterwards (the
    return of the preempting handler). The strictness excludes the trivial pre-state witness. A
    premise of the progress leg, not part of run admissibility. -/
def VerdraengungKehrtZurueck (ρ : Lauf E) : Prop :=
  ∀ (c : Kontext) (k : Kern) (t : Nat),
    (∃ z, ρ.zeit.zustand t = some z ∧ (z.kerne k).laeuft = some c ∧ z.status c = .laeuft) →
    (∃ id spur, ρ.zeit.spur t = some (.interrupt id, spur)) →
    ∃ t', t < t' ∧ ∃ k', ∃ z', ρ.zeit.zustand t' = some z' ∧ (z'.kerne k').laeuft = some c

/-- A preferred step serves the context the opportunity core dispatches. -/
def BevorzugtSchritt (hw : HwLauf) (t : Nat) (s : Option (Zustand L Ort Wert Raum Lok Grund))
    (ev : SchrittWahl Wahl × SchrittSpur Ort Wert) : Prop :=
  ∃ c w spur k, ev = (.kontext c w, spur) ∧ hw.gelegenheit t k ∧
    ∃ z, s = some z ∧ (z.kerne k).laeuft = some c

/-- One fair tick: a preferred dispatched-context step if one exists, another possible step
    otherwise, and a pause only when no step exists at all. -/
noncomputable def fairerSchritt (hw : HwLauf) (t : Nat)
    (s : Option (Zustand L Ort Wert Raum Lok Grund)) :
    Option (Zustand L Ort Wert Raum Lok Grund) ×
      Option (SchrittWahl Wahl × SchrittSpur Ort Wert) := by
  classical
  exact if h1 : ∃ ev next, Lauffolge E hw t s ev next ∧ BevorzugtSchritt hw t s ev then
    (Classical.choose (Classical.choose_spec h1), some (Classical.choose h1))
  else if h2 : ∃ ev next, Lauffolge E hw t s ev next then
    (Classical.choose (Classical.choose_spec h2), some (Classical.choose h2))
  else (s, none)

theorem fairerSchritt_takt (hw : HwLauf) (t : Nat)
    (s : Option (Zustand L Ort Wert Raum Lok Grund)) :
    Takt (Lauffolge E hw) (KeinSchritt (Lauffolge E hw)) t s
      (fairerSchritt E hw t s).2 (fairerSchritt E hw t s).1 := by
  unfold fairerSchritt
  classical
  split
  · next h1 =>
    exact .schritt rfl (Classical.choose_spec (Classical.choose_spec h1)).1
  · next h1 =>
    split
    · next h2 =>
      exact .schritt rfl (Classical.choose_spec (Classical.choose_spec h2))
    · next h2 =>
      refine .wartet rfl rfl (fun ev next step => h2 ⟨ev, next, step⟩)

/-- The fair schedule from an initial state: preferred dispatched-context steps everywhere. -/
noncomputable def fairerFolge (hw : HwLauf) (init : Option (Zustand L Ort Wert Raum Lok Grund)) :
    Nat → Option (Zustand L Ort Wert Raum Lok Grund) ×
      Option (SchrittWahl Wahl × SchrittSpur Ort Wert)
  | 0 => (init, none)
  | t + 1 => fairerSchritt E hw t (fairerFolge hw init t).1

noncomputable def fairerZeit (hw : HwLauf) (init : Option (Zustand L Ort Wert Raum Lok Grund)) :
    Zeitlauf (Lauffolge E hw) where
  zustand := fun t => (fairerFolge E hw init t).1
  spur := fun t => (fairerFolge E hw init (t + 1)).2
  takt := fun t => fairerSchritt_takt E hw t (fairerFolge E hw init t).1

theorem fairerZeit_start (hw : HwLauf) (init : Option (Zustand L Ort Wert Raum Lok Grund)) :
    (fairerZeit E hw init).zustand 0 = init := rfl

/-- The fair schedule serves every continuously dispatched, live and rule-enabled context
    infinitely often whenever its dispatch core offers opportunities infinitely often: at such
    a joint tick the preferred branch fires, and the opportunity core dispatches exactly the
    waiting context. -/
theorem fairer_zeit_fair (hw : HwLauf) (init : Option (Zustand L Ort Wert Raum Lok Grund))
    (s : AussenStart) : SchedulerFair E ⟨s, hw, fairerZeit E hw init⟩ := by
  intro a c bereit opp n hn
  obtain ⟨t, ht, k, gelegenheit, z, eq, dispatch⟩ := opp (max n a) (Nat.le_max_right _ _)
  have hz : (fairerZeit E hw init).zustand t = some z := eq
  obtain ⟨z', eq', _, live, normal, w, plan, u, spur, s', regel, aus⟩ :=
    bereit t ((Nat.le_max_right n a).trans ht)
  have same : z' = z := Option.some.inj (eq'.symm.trans hz)
  subst z'
  have schritt : Lauffolge E hw t (some z) (.kontext c w, spur) s' :=
    .schritt (.kontext normal ⟨k, gelegenheit, dispatch, live⟩ regel aus)
  have bevorzugt : BevorzugtSchritt hw t (some z) (.kontext c w, spur) :=
    ⟨c, w, spur, k, rfl, gelegenheit, z, rfl, dispatch⟩
  have wahl : ∃ ev next, Lauffolge E hw t (some z) ev next ∧ BevorzugtSchritt hw t (some z) ev :=
    ⟨_, _, schritt, bevorzugt⟩
  have hstate : (fairerFolge E hw init t).1 = some z := hz
  have spurEq : (fairerZeit E hw init).spur t = some (Classical.choose wahl) := by
    show (fairerSchritt E hw t (fairerFolge E hw init t).1).2 = _
    rw [hstate]
    unfold fairerSchritt
    classical
    rw [dif_pos wahl]
  have spec := Classical.choose_spec (Classical.choose_spec wahl)
  obtain ⟨c', w', spur', k', hev, geleg', z0, hseq, dispatch'⟩ := spec.2
  have kk : k' = k := Option.some.inj (geleg'.symm.trans gelegenheit)
  subst kk
  have z0eq : z0 = z := Option.some.inj hseq.symm
  subst z0
  have gleich : c' = c := Option.some.inj (dispatch'.symm.trans dispatch)
  subst gleich
  exact ⟨t, (Nat.le_max_left n a).trans ht, w', spur', hev ▸ spurEq⟩

/-- A run over a history without raised interrupts takes no interrupt step, so every
    preemption return holds vacuously: an interrupt step would need a raised signal in
    the history. -/
theorem verdraengung_ohne_meldung (hw : HwLauf) (leer : ∀ i, (hw.angebot i).interrupts = [])
    (ρ : Lauf E) (hρ : ρ.hw = hw) : VerdraengungKehrtZurueck E ρ := by
  intro c k t _ hint
  obtain ⟨id, spur, hspur⟩ := hint
  cases hstt : ρ.zeit.zustand t with
  | none =>
    cases htakt : ρ.zeit.takt t with
    | schritt label step =>
      rw [hstt] at step
      cases step
    | wartet label _ _ =>
      rw [label] at hspur
      cases hspur
  | some s =>
    cases htakt : ρ.zeit.takt t with
    | schritt label step =>
      rw [hstt] at step
      cases step with
      | schritt trans =>
        cases trans with
        | kontext _ _ _ _ =>
          have hev := Option.some.inj (label.symm.trans hspur)
          have hfst := congrArg Prod.fst hev
          simp at hfst
        | antwort _ _ =>
          have hev := Option.some.inj (label.symm.trans hspur)
          have hfst := congrArg Prod.fst hev
          simp at hfst
        | interrupt _ h =>
          obtain ⟨_, _, _, _, _, haus, _, _, _, _, _⟩ := h
          have hang := haus.2.2.1
          rw [hρ, leer id.1] at hang
          simp only [List.getElem?_nil, reduceCtorEq] at hang
        | absturz _ =>
          have hev := Option.some.inj (label.symm.trans hspur)
          have hfst := congrArg Prod.fst hev
          simp at hfst
    | wartet label _ _ =>
      rw [label] at hspur
      cases hspur

/-- A fair run for the given hardware history: admissible and scheduler-fair by construction,
    with the exact start and hardware projection. -/
theorem fairer_lauf_mit_hw {h : Umgebung} {s : AussenStart} {hw : HwLauf}
    (hardware : Hardware E.katalog h) (start : E.ZulStart h s) (konform : hw.konform E.katalog h) :
    ∃ ρ, Laeufe E h ρ ∧ SchedulerFair E ρ ∧ ρ.start = s ∧ ρ.hw = hw := by
  refine ⟨⟨s, hw, fairerZeit E hw (E.laden s (h.lade E.bild))⟩,
    ⟨hardware, konform, start, fairerZeit_start E hw _⟩, fairer_zeit_fair E hw _ s, rfl, rfl⟩

end Gabbro.Core.Maschine
