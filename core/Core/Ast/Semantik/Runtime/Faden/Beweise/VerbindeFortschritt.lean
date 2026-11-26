/-
  File:      core/Core/Ast/Semantik/Runtime/Faden/Beweise/VerbindeFortschritt.lean
  Subject:   THE JOIN PROGRESS PROMISE IS NOT CARRIED BY ENABLEDNESS ALONE. The weak form of
             `VerbindeFortschrittAussage` (no fairness premise, no bound of the ideal run to the
             implementation run) is refuted here: a join of an ended thread by its recorded creator
             stays enabled on the whole suffix, yet the joiner hangs on a hardware-fair history.
-/
module

public import Core.Ast.Semantik.Runtime.Faden.Offen
public import Core.Fortschritt.Verdraengung
public import Core.Fortschritt.Beispiele
public import Core.Katalog.Erfuellbar
public import Core.Verfeinerung.Maschine
public import Core.Ziel.Korrektheit.Beweise.Fortschritt.SchedulerEinheit
public import Core.Ziel.Korrektheit.Beweise2.ZugriffSchrittExistiert
public import Core.Ziel.Korrektheit.Beweise.BegleitVerfeinerung

@[expose] public section

namespace Gabbro.Core.Fortschritt

open Gabbro.Core.Maschine
open Gabbro.Core.Katalog
open Gabbro.Core.Fortschritt

/-- The joiner. -/
def vfC : Kontext := Kontext.faden 0

/-- The joined context. -/
def vfKind : Kontext := Kontext.faden 1

/-- The step of the join form: a `.verbinde` with no memory events. -/
def vfPlan : SchrittPlan Unit Unit Unit Unit :=
  { togglePlan with aktion := .verbinde vfKind }

/-- Only the joiner runs; the joined context has ended with an outcome. -/
def vfStatus : Kontext → Status Unit Unit := fun c =>
  if c = vfC then .laeuft else if c = vfKind then .beendet (.wert ()) else .ruht

/-- The joiner is dispatched on core zero. -/
def vfKerne : Kern → KernZustand Unit := fun k =>
  if k = 0 then ⟨some vfC, .nutzer, (), fun _ => false, 0, false, []⟩
  else ⟨none, .nutzer, (), fun _ => false, 0, false, []⟩

/-- The state with an ended joined context and a persistent creator entry. -/
def vfZustand : Zustand Unit Unit Unit Unit Bool Unit :=
  let z := Zustand.start (fun _ => false) vfStatus vfKerne
    ⟨fun _ => false, fun _ => 0⟩ (fun _ => ()) (.leer (fun _ => 0))
  { z with erzeuger := fun c => if c = vfKind then some vfC else none }

/-- One form whose implementation and ideal rule are the same stuttering join. -/
def vfRegel : Regel (Zustand Unit Unit Unit Unit Bool Unit) (SchrittPlan Unit Unit Unit Unit) Unit where
  impl := fun _ _ _ es _ => es = [vfPlan]
  ideal := fun _ _ _ es _ => es = [vfPlan]

/-- A system in which every context has the join form at its head. -/
def vfSystem : MaschinenSystem Unit Unit Unit Unit Bool Unit Unit Unit Unit :=
  ⟨fun _ => vfRegel, fun _ _ => some (), fun _ _ => False, fun _ _ _ => False⟩

/-- The witness unit: a loader that fails, so the implementation run can pause everywhere. -/
def vfEinheit : Einheit Unit Unit Unit Unit Bool Unit Unit Unit Unit :=
  ⟨Plattform.x86_64.katalog, wBild, wEinrichtung (fun _ => none), vfSystem,
    fun _ => wDaten (fun _ => none), fun _ => 0, fun _ _ => none,
    Eq, fun _ => 1, .leer, eineTabelle, .leer, .leer, .leer⟩

def vfSicht : Nat → AussenVerlauf → AussenSicht := fun _ _ => AussenSicht.leer

def vfH : Umgebung := Umgebung.referenz Plattform.x86_64.katalog 1 vfSicht

def vfHw : HwLauf := Umgebung.referenzLauf Plattform.x86_64.katalog 1 vfSicht

def vfStart : AussenStart := ⟨0, fun _ => some 0, [], fun _ => none, vfSicht 0 []⟩

theorem vf_fair : FairLaeufe vfEinheit.katalog vfH vfHw :=
  Umgebung.referenz_fair _ _ _ Plattform.x86_64.katalog_wohlgeformt (by decide)

theorem vf_kein_absturz (t : Nat) : ¬ AbsturzAngeboten vfEinheit.katalog vfHw t := by
  simp only [AbsturzAngeboten, vfHw, Umgebung.referenzLauf, reduceCtorEq, and_false, not_false_eq_true]

/-- The ideal run never leaves the state with the join enabled. -/
def vfZeitI : Zeitlauf (I.Schritt vfEinheit.einrichtung vfEinheit.system vfEinheit.katalog vfHw)
    (fun t _ => ¬ AbsturzAngeboten vfEinheit.katalog vfHw t) where
  zustand := fun _ => vfZustand
  spur := fun _ => none
  takt := fun t => .wartet rfl rfl (vf_kein_absturz t)

/-- The ideal run of the witness. -/
def vfEta : I.Lauf vfEinheit := ⟨vfStart, vfH, vfHw, vfZeitI, fun _ => none⟩

/-- The implementation run: a failed load leaves the machine paused at every tick. -/
def vfZeitM : Zeitlauf (Lauffolge vfEinheit vfHw) (KeinSchritt (Lauffolge vfEinheit vfHw)) where
  zustand := fun _ => none
  spur := fun _ => none
  takt := fun t => .wartet rfl rfl (fun ev next step => by cases step)

/-- The implementation run of the witness. -/
def vfRho : Maschine.Lauf vfEinheit := ⟨vfStart, vfHw, vfZeitM⟩

theorem vf_zustand (t : Nat) : vfEta.zeit.zustand t = vfZustand := rfl

theorem vf_spur (t : Nat) : vfEta.zeit.spur t = none := rfl

theorem vf_live : vfZustand.status vfC = .laeuft := by
  simp only [vfZustand, Zustand.start, vfStatus, vfC, Kontext.faden.injEq, Nat.reduceEqDiff, ↓reduceIte]

theorem vf_ended : vfZustand.status vfKind = .beendet (.wert ()) := by
  simp only [vfZustand, Zustand.start, vfStatus, vfC, vfKind, Kontext.faden.injEq, Nat.reduceEqDiff, ↓reduceIte]

theorem vf_erzeuger : vfZustand.erzeuger vfKind = some vfC := by
  simp only [vfZustand, vfC, vfKind, Kontext.faden.injEq, Nat.reduceEqDiff, ↓reduceIte]

theorem vf_dispatch : (vfZustand.kerne 0).laeuft = some vfC := by
  simp only [vfZustand, Zustand.start, vfKerne, vfC, Kontext.faden.injEq, Nat.reduceEqDiff, ↓reduceIte]

theorem vf_schritt : vfEinheit.system.ISchritt vfC vfZustand () [vfPlan] vfZustand := by
  exact ⟨(), rfl, rfl⟩

/-- The joined thread has ended and its creator entry persists. -/
theorem vf_p1 : ∃ t ausgang, (vfEta.zeit.zustand t).status vfKind = .beendet ausgang ∧
    ∀ t', t ≤ t' → (vfEta.zeit.zustand t').erzeuger vfKind = some vfC := by
  refine ⟨0, .wert (), ?_, ?_⟩
  · rw [vf_zustand]
    exact vf_ended
  · intro t' _
    rw [vf_zustand]
    exact vf_erzeuger

/-- The join of the ended thread stays enabled. -/
theorem vf_p2 : ∃ a, ∀ t, a ≤ t → ∃ plan w u,
    vfEinheit.system.ISchritt vfC (vfEta.zeit.zustand t) w [plan] u ∧
      plan.aktion = .verbinde vfKind := by
  refine ⟨0, fun t _ => ?_⟩
  exact ⟨vfPlan, (), vfZustand, ⟨(), rfl, rfl⟩, rfl⟩

/-- A step of the joiner is never discharged, and the joiner is continuously ready. -/
theorem vf_hang : I.Haengt vfEinheit vfRho vfEta vfC := by
  refine ⟨?_, 0, (), ?_, ?_⟩
  · change FairLaeufe Plattform.x86_64.katalog vfH vfHw
    exact vf_fair
  · refine ⟨⟨0, ?_⟩, ?_⟩
    · rw [vf_zustand]
      exact vf_dispatch
    · intro t _
      refine ⟨?_, ?_, ?_⟩
      · rw [vf_zustand]
        rfl
      · rw [vf_zustand]
        exact vf_live
      · intro erl
        rcases erl with ⟨_, _, h⟩ | h | ⟨_, h⟩
        · rw [vf_spur] at h
          cases h
        · rw [vf_spur] at h
          cases h
        · rw [vf_zustand] at h
          rw [vf_live] at h
          cases h
  · left
    intro t _
    rw [vf_zustand]
    exact ⟨(), [vfPlan], vfZustand, vf_schritt⟩

/-- THE WEAK PROMISE IS FALSE: the two join premises alone do not exclude a hang, even with a
    hardware-fair implementation run. Feeds: the design change of `VerbindeFortschrittAussage`. -/
theorem verbindeFortschritt_ohneFairness_falsch :
    ∃ (E : Einheit Unit Unit Unit Unit Bool Unit Unit Unit Unit)
      (ρ : Maschine.Lauf E) (η : I.Lauf E) (c kind : Kontext),
      (∃ t ausgang, (η.zeit.zustand t).status kind = .beendet ausgang ∧
        ∀ t', t ≤ t' → (η.zeit.zustand t').erzeuger kind = some c) →
      (∃ a, ∀ t, a ≤ t → ∃ plan w u, E.system.ISchritt c (η.zeit.zustand t) w [plan] u ∧
        plan.aktion = .verbinde kind) →
      I.Haengt E ρ η c := by
  exact ⟨vfEinheit, vfRho, vfEta, vfC, vfKind, fun _ _ => vf_hang⟩

/-- A rule whose implementation stutters while its ideal rule offers the join. The mismatch is not
    checked here: `Laufabgleich` relates the traces, not the rules. -/
def vwRegel : Regel (Zustand Unit Unit Unit Unit Bool Unit) (SchrittPlan Unit Unit Unit Unit) Unit where
  impl := fun _ _ _ es _ => es = [togglePlan]
  ideal := fun _ _ _ es _ => es = [vfPlan]

def vwSystem : MaschinenSystem Unit Unit Unit Unit Bool Unit Unit Unit Unit :=
  ⟨fun _ => vwRegel, fun _ _ => some (), fun _ _ => False, fun _ _ _ => False⟩

/-- The witness unit whose loader succeeds, so the implementation run can step the joiner. -/
def vwEinheit : Einheit Unit Unit Unit Unit Bool Unit Unit Unit Unit :=
  ⟨Plattform.x86_64.katalog, wBild, wEinrichtung (fun _ => none), vwSystem,
    fun _ => wDaten (fun _ => none), fun _ => 0, fun _ _ => some vfZustand,
    fun _ _ => True, fun _ => 1, .leer, eineTabelle, .leer, .leer, .leer⟩

theorem vwBildGueltig : wBild.gueltig Plattform.x86_64.katalog.plattform.ziel := wBildV_gueltig

noncomputable def vwStart : AussenStart :=
  Classical.choose (Katalog.zulStart_erfuellbar
    (Umgebung.referenz_hardware Plattform.x86_64.katalog 1 sicht0
      Plattform.x86_64.katalog_wohlgeformt (by decide)) vwBildGueltig)

theorem vwZul : vwEinheit.ZulStart h1 vwStart :=
  Classical.choose_spec (Katalog.zulStart_erfuellbar
    (Umgebung.referenz_hardware Plattform.x86_64.katalog 1 sicht0
      Plattform.x86_64.katalog_wohlgeformt (by decide)) vwBildGueltig)

/-- The implementation states: every tick toggles the joiner's local bit only. -/
def vwZustandFolge : Nat → Zustand Unit Unit Unit Unit Bool Unit
  | 0 => vfZustand
  | t + 1 => toggleUpdate vfC (vwZustandFolge t)

theorem vw_kerne (t : Nat) : (vwZustandFolge t).kerne = vfZustand.kerne := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [vwZustandFolge, toggleUpdate, ih]

theorem vw_status (t : Nat) : (vwZustandFolge t).status = vfZustand.status := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [vwZustandFolge, toggleUpdate, ih]

theorem vw_protokoll (t : Nat) : I.Zustandsbezug vwEinheit (vwZustandFolge t) vfZustand := by
  refine ⟨?_, trivial⟩
  change { vwZustandFolge t with lokal := vfZustand.lokal } = vfZustand
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [vwZustandFolge, toggleUpdate]
    exact ih

theorem vf_kerne_succ (k : Nat) : (vfZustand.kerne (Nat.succ k)).laeuft = none := by
  simp only [vfZustand, Zustand.start, vfKerne, Kontext.faden.injEq, Nat.reduceEqDiff, ↓reduceIte]

def vwAusfuehr (t : Nat) (x : Zustand Unit Unit Unit Unit Bool Unit) :
    FuehrtSchrittAus vwEinheit.einrichtung t vfC x (toggleUpdate vfC x) togglePlan ⟨[], []⟩
      (toggleUpdate vfC x) :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    fun _ h => (List.not_mem_nil h).elim, [], toggleUpdate vfC x, .intern, .nil _, rfl⟩

theorem vw_regel (t : Nat) :
    vwEinheit.system.ImplSchritt vfC (vwZustandFolge t) () [togglePlan]
      (toggleUpdate vfC (vwZustandFolge t)) :=
  ⟨(), rfl, rfl⟩

/-- The preferred tick of the joiner. -/
def vwTaktK (t : Nat) : Takt (Lauffolge vwEinheit hw1) (KeinSchritt (Lauffolge vwEinheit hw1))
    t (some (vwZustandFolge t)) (some (.kontext vfC (), ⟨[], []⟩)) (some (vwZustandFolge (t + 1))) :=
  .schritt rfl (.schritt (ImplSchritt.kontext (hw1_crash t)
    ⟨0, hw1_opp0 t, by rw [vw_kerne]; exact vf_dispatch, by rw [vw_status]; exact vf_live⟩
    (vw_regel t) (vwAusfuehr t (vwZustandFolge t))))

noncomputable def vwRho : Maschine.Lauf vwEinheit :=
  ⟨vwStart, hw1, ⟨fun t => some (vwZustandFolge t), fun _ => some (.kontext vfC (), ⟨[], []⟩), vwTaktK⟩⟩

theorem vw_kein_absturz (t : Nat) : ¬ AbsturzAngeboten vwEinheit.katalog hw1 t := by
  simp only [AbsturzAngeboten, hw1, Umgebung.referenzLauf, reduceCtorEq, and_false, not_false_eq_true]

def vwZeitI : Zeitlauf (I.Schritt vwEinheit.einrichtung vwEinheit.system vwEinheit.katalog hw1)
    (fun t _ => ¬ AbsturzAngeboten vwEinheit.katalog hw1 t) where
  zustand := fun _ => vfZustand
  spur := fun _ => none
  takt := fun t => .wartet rfl rfl (vw_kein_absturz t)

/-- The ideal run keeps the join enabled and marks every tick as a private step of the joiner. -/
noncomputable def vwEta : I.Lauf vwEinheit := ⟨vwStart, h1, hw1, vwZeitI, fun _ => some vfC⟩

theorem vw_p1 : ∃ t ausgang, (vwEta.zeit.zustand t).status vfKind = .beendet ausgang ∧
    ∀ t', t ≤ t' → (vwEta.zeit.zustand t').erzeuger vfKind = some vfC := by
  refine ⟨0, .wert (), ?_, ?_⟩
  · exact vf_ended
  · intro t' _
    exact vf_erzeuger

theorem vw_p2 : ∃ a, ∀ t, a ≤ t → ∃ plan w u,
    vwEinheit.system.ISchritt vfC (vwEta.zeit.zustand t) w [plan] u ∧
      plan.aktion = .verbinde vfKind := by
  refine ⟨0, fun t _ => ?_⟩
  exact ⟨vfPlan, (), vfZustand, ⟨(), rfl, rfl⟩, rfl⟩

theorem vw_lauf : Laeufe vwEinheit h1 vwRho := by
  have fair := Umgebung.referenz_fair Plattform.x86_64.katalog 1 sicht0
    Plattform.x86_64.katalog_wohlgeformt (by decide)
  refine ⟨?_, ?_, ?_, ?_⟩
  · change Hardware Plattform.x86_64.katalog h1
    exact fair.hardware
  · change hw1.konform Plattform.x86_64.katalog h1
    exact fair.konform
  · exact vwZul
  · rfl

theorem vw_fair : FairLaeufe vwEinheit.katalog h1 vwRho.hw := by
  change FairLaeufe Plattform.x86_64.katalog h1 hw1
  exact Umgebung.referenz_fair _ _ _ Plattform.x86_64.katalog_wohlgeformt (by decide)

theorem vw_sf : SchedulerFair vwEinheit vwRho := by
  intro a c bereit opp n hn
  obtain ⟨s, hs, ⟨k, hk⟩, _, _, _, _, _, _⟩ := bereit n hn
  have hseq : s = vwZustandFolge n := Option.some.inj hs.symm
  rw [hseq, vw_kerne] at hk
  cases k with
  | zero =>
    have hvc : vfC = c := Option.some.inj (vf_dispatch.symm.trans hk)
    subst c
    exact ⟨n, Nat.le_refl n, (), ⟨[], []⟩, rfl⟩
  | succ k =>
    rw [vf_kerne_succ] at hk
    cases hk

theorem vw_ret : VerdraengungKehrtZurueck vwEinheit vwRho :=
  verdraengung_ohne_meldung vwEinheit hw1 (fun i => rfl) vwRho rfl

/-- The two runs are matched: the concrete stutter is a private tick, and the protocol fields agree. -/
theorem vw_match : I.Laufabgleich vwRho vwEta where
  hardware := rfl
  start := rfl
  zustand := fun t => ⟨vwZustandFolge t, rfl, vw_protokoll t⟩
  spur := fun t => .privat vfC ()
  frei := fun t => by
    simp only [vwEta, vwRho, vwZeitI, reduceCtorEq, false_or]
    constructor
    · intro h
      cases h
    · intro hne
      exact hne rfl
  belegt := fun t c hc => by
    have hc' : c = vfC := Option.some.inj hc.symm
    subst c
    exact ⟨(), (), rfl, rfl⟩

theorem vw_hang : I.Haengt vwEinheit vwRho vwEta vfC := by
  refine ⟨?_, 0, (), ?_, ?_⟩
  · change FairLaeufe Plattform.x86_64.katalog h1 hw1
    exact Umgebung.referenz_fair _ _ _ Plattform.x86_64.katalog_wohlgeformt (by decide)
  · refine ⟨⟨0, vf_dispatch⟩, ?_⟩
    intro t _
    refine ⟨rfl, vf_live, ?_⟩
    intro erl
    rcases erl with ⟨_, _, h⟩ | h | ⟨_, h⟩
    · cases h
    · cases h
    · change vfZustand.status vfC = Status.beendet _ at h
      rw [vf_live] at h
      cases h
  · left
    intro t _
    exact ⟨(), [vfPlan], vfZustand, ⟨(), rfl, rfl⟩⟩

/-- THE JOINT PREMISES ARE SATISFIABLE: an accepted elaborated unit admits an admissible,
    hardware-fair, scheduler-fair run without preemption. The concrete witness is the empty unit on
    x86-64, shared with `FortschrittAkzeptiertAussage.erfuellbar`. -/
theorem verbindeFortschritt_erfuellbar :
    ∃ (P : Plattform) (t : Ast.Unit) (H : Umgebung) (ρ : Maschine.Lauf (Ziel.Korrektheit.einheitVon P t)),
      Annahme.Akzeptiert (Ziel.Korrektheit.einheitVon P t) ∧
      Laeufe (Ziel.Korrektheit.einheitVon P t) H ρ ∧
      FairLaeufe (Ziel.Korrektheit.einheitVon P t).katalog H ρ.hw ∧
      SchedulerFair (Ziel.Korrektheit.einheitVon P t) ρ ∧
      VerdraengungKehrtZurueck (Ziel.Korrektheit.einheitVon P t) ρ := by
  exact Ziel.Korrektheit.FortschrittAkzeptiertAussage.erfuellbar

/-- The added run premises are load-bearing: dropping them admits the hang above. -/
theorem verbindeFortschritt_nichtTrivial :
    ∃ (E : Einheit Unit Unit Unit Unit Bool Unit Unit Unit Unit) (ρ : Maschine.Lauf E)
      (η : I.Lauf E) (c kind : Kontext),
      (∃ t ausgang, (η.zeit.zustand t).status kind = .beendet ausgang ∧
        ∀ t', t ≤ t' → (η.zeit.zustand t').erzeuger kind = some c) ∧
      (∃ a, ∀ t, a ≤ t → ∃ plan w u, E.system.ISchritt c (η.zeit.zustand t) w [plan] u ∧
        plan.aktion = .verbinde kind) ∧ I.Haengt E ρ η c := by
  exact ⟨vfEinheit, vfRho, vfEta, vfC, vfKind, vf_p1, vf_p2, vf_hang⟩

/-- FINDING: the strengthened statement is still false. A matched run may serve the joiner by
    private ticks forever; `Laufabgleich` alone neither discharges the ideal step nor bounds the
    stutter. Closing it needs the full progress duties (`Laeufe η`, `BelegungGeprueft`,
    `StotterSchranke`, `FortschrittsPflichten`), or the restriction to `einheitVon` where MK-11 has
    them. This witness satisfies every premise of `VerbindeFortschrittAussage` and still hangs. -/
theorem verbindeFortschritt_mitPraemissen_falsch :
    ∃ (E : Einheit Unit Unit Unit Unit Bool Unit Unit Unit Unit) (ρ : Maschine.Lauf E)
      (η : I.Lauf E) (hU : Umgebung) (c kind : Kontext),
      Laeufe E hU ρ ∧ FairLaeufe E.katalog hU ρ.hw ∧ SchedulerFair E ρ ∧
        VerdraengungKehrtZurueck E ρ ∧ I.Laufabgleich ρ η ∧ η.umgebung = hU ∧
        (∃ t ausgang, (η.zeit.zustand t).status kind = .beendet ausgang ∧
          ∀ t', t ≤ t' → (η.zeit.zustand t').erzeuger kind = some c) ∧
        (∃ a, ∀ t, a ≤ t → ∃ plan w u, E.system.ISchritt c (η.zeit.zustand t) w [plan] u ∧
          plan.aktion = .verbinde kind) ∧ I.Haengt E ρ η c := by
  exact ⟨vwEinheit, vwRho, vwEta, h1, vfC, vfKind, vw_lauf, vw_fair, vw_sf, vw_ret,
    vw_match, rfl, vw_p1, vw_p2, vw_hang⟩

/-- THE JOIN PROGRESS PROMISE HOLDS for accepted elaborated units. It is the per-context instance of
    MK-11's `fortschritt_akzeptiert`: on the matched ideal run that theorem constructs, the checker
    verdict has discharged every context's obligation, including the joiner's, so no free join,
    progress or scheduler parameter is needed. The join-specific premises of the former free-form
    statement are absent by design — no source form elaborates to `Befehl.faden`, so they would make
    the promise vacuous on `einheitVon`. -/
theorem verbindeFortschritt : Ast.Semantik.VerbindeFortschrittAussage := by
  intro P t akzeptiert H ρ lauf fair sf ret c
  obtain ⟨η, valid, sim, keineHaengt, klasse⟩ :=
    Ziel.Korrektheit.fortschritt_akzeptiert Ziel.Korrektheit.zugriffSchrittExistiert
      P t akzeptiert H ρ lauf fair sf ret
  exact ⟨η, valid, sim, keineHaengt c, klasse⟩

end Gabbro.Core.Fortschritt
