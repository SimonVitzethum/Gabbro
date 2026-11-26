/-
  File:      Core/Fortschritt/Beweise/SperrStarkHalter.lean
  Subject:   GLOBAL HOLDER ELIGIBILITY for the non-vacuous hand-over unit (M8 2b).

  The invariant says: the lock only ever contains statically dispatched contexts; before a
  restart every vector is masked, an NMI is active and A, B, C stay live and dispatched; after a
  restart none of A, B, C is dispatched and the lock is empty. Therefore every reachable holder
  is live, dispatched and release-offering, on EVERY ideal cut, not only on the witness run.
-/
module

public import Core.Fortschritt.Beweise.SperrStarkEinheit4

@[expose] public section

namespace Gabbro.Core.Fortschritt

open Gabbro.Core.Maschine
open Gabbro.Core.Katalog
open Gabbro.Core.Annahme
open Gabbro.Core.Beobachtung

/-- The lock only ever mentions statically dispatched contexts. -/
def lockStatisch4 (s : Zustand Unit Unit Unit Unit Bool Unit) : Prop :=
  (match (s.sperren ()).besitzer with
   | none => True
   | some h => statisch4 h) ∧
  ∀ c ∈ (s.sperren ()).schlange, statisch4 c

/-- Before a restart: no preemption and all three contexts live and dispatched. -/
def vorCrash4 (s : Zustand Unit Unit Unit Unit Bool Unit) : Prop :=
  (∀ k, (s.kerne k).nmiAktiv = true ∧ (s.kerne k).maske = fun _ => true) ∧
  ∀ c, statisch4 c → s.status c = .laeuft ∧ ∃ k, (s.kerne k).laeuft = some c

/-- After a restart: the entry context is outside the dispatched set and the lock is empty. -/
def nachCrash4 (s : Zustand Unit Unit Unit Unit Bool Unit) : Prop :=
  (∀ c, statisch4 c → ∀ k, (s.kerne k).laeuft ≠ some c) ∧
  (s.sperren ()).besitzer = none ∧ (s.sperren ()).schlange = []

def inv4 (s : Zustand Unit Unit Unit Unit Bool Unit) : Prop :=
  lockStatisch4 s ∧ (vorCrash4 s ∨ nachCrash4 s)

theorem e4_I_schritt_erhaelt_frei {hw : HwLauf} {t : Nat}
    {s : Zustand Unit Unit Unit Unit Bool Unit}
    {ev : SchrittWahl Unit × SchrittSpur Unit Unit} {s' : Zustand Unit Unit Unit Unit Bool Unit}
    (hpre : (s.sperren ()).besitzer = none)
    (step : I.Schritt E_4.einrichtung E_4.system E_4.katalog hw t s ev s') :
    (s'.sperren ()).besitzer = none := by
  cases step with
  | @kontext _ u plan spur c w _ _ hreg haus =>
    obtain ⟨_, _, hreg⟩ := hreg
    change e4RegelIdeal c s w [plan] u at hreg
    rcases hreg with ⟨_, _, hpeq, hueq⟩ | ⟨hpeq, hueq⟩
    · obtain rfl := (List.cons.inj hpeq).1
      subst u
      obtain ⟨_, _, _, _, hF, _, hziel⟩ := haus
      generalize hev : spur.aussen = evs at hF
      have hss : (s.sperren ()).Gibt c ((s.sperren ()).abgeben) := by
        -- the give plan carries a release step; extract it from the executed action
        obtain ⟨_, _, _, _, hF', _⟩ := haus
        have hakt : wGebenPlan.aktion = .sperre () .geben := rfl
        rw [hakt] at hF'
        cases hF' with
        | sperre hnext _ =>
          cases hnext with
          | geben hg => exact hg
          | ticket => simp at *
          | nehmen => simp at *
      rw [SperrZustand.Gibt.besitzt hss] at hpre
      cases hpre
    · obtain rfl := (List.cons.inj hpeq).1
      subst u
      obtain ⟨_, _, _, _, hF, _, hziel⟩ := haus
      have hakt : stutterPlan.aktion = .intern := rfl
      rw [hakt] at hF
      cases hF
      rw [hziel]
      exact hpre
  | antwort _ h =>
    obtain ⟨_, _, _, heq⟩ := h
    rw [heq]
    exact hpre
  | interrupt _ h =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, hstate⟩ := h
    rw [hstate]
    simpa only [Zustandseintritt] using hpre
  | absturz h =>
    exact (absturz_leert_schlange (l := ()) h).2

theorem e4_kein_besitzer_I (ρ : I.Lauf E_4) (lauf : I.Laeufe E_4 ρ) (t : Nat)
    (s : Zustand Unit Unit Unit Unit Bool Unit) (hzs : ρ.zeit.zustand t = s) :
    (s.sperren ()).besitzer = none := by
  revert s hzs
  induction t with
  | zero =>
    intro s hzs
    have h0 := lauf.2.2.2.1
    rw [h0] at hzs
    subst hzs
    exact rfl
  | succ t ih =>
    intro s hzs
    cases ρ.zeit.takt t with
    | wartet _ heq _ =>
      rw [heq] at hzs
      exact ih _ hzs
    | schritt _ step =>
      have hpre := ih _ rfl
      have hpost := e4_I_schritt_erhaelt_frei hpre step
      rw [hzs] at hpost
      exact hpost

theorem e4_halter : SperrHalterHalten E_4 := by
  intro ρ lauf t l h hown
  cases l
  have hfrei := e4_kein_besitzer_I ρ lauf t.val _ rfl
  rw [hfrei] at hown
  cases hown

theorem waechter_E_4 : WaechterHalten E_4 :=
  ⟨fun ρ _ t op args h => by
      dsimp [kanonischeVerwendung, E_4, Quelltabellen.leer] at h
      exact h.elim,
    fun ρ _ t hC => by
      obtain ⟨C, hC⟩ := hC
      obtain ⟨c, hc⟩ := hC.1
      obtain ⟨b, hblock, _, _, _⟩ := hC.2 c hc
      exact hblock,
    e4_halter⟩

theorem akzeptiert_E_4 : Akzeptiert E_4 :=
  ⟨⟨Plattform.x86_64.katalog_wohlgeformt, e4_regel_lokal,
     ⟨Gabbro.Core.Aussen.zulassung_m2 _, e4_aussen_gueltig⟩, e4_fluss,
     e4_schranken_lokal, e4_sec, e4_domaenen⟩, e4_klauseln, waechter_E_4⟩

end Gabbro.Core.Fortschritt
