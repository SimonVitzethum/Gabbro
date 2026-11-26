/-
  File:      Core/Fortschritt/SperrFairBeweis.lean
  Subject:   Discharge of the two non-vacuous progress sentences.

  The old vacuous discharge (through `faire_umgebung_nicht_eindeutig`) is deleted with the
  `∀ h'` premise it fed on. The substantive chain is:
  `SperrHalterImplBereitAussage` (per-cut impl bridge, proved from its agreement premise)
  supplies `SchedulerFair` readiness; the opportunity-alignment premise supplies the second
  `SchedulerFair` antecedent; the stepped holder accumulates `H + 1` own steps and
  `sperr_freigabe_bedingt` releases with the bound. Where ownership breaks early, the hold
  bound itself discharges the release (`besitzwechsel_ist_gibt` + `HalteSchranken`).
  `SperrWarteFairAussage` follows: `SperrFreigabeAussage` discharges the `hgibt` premise of
  `sperr_warte_schranke_bis` (fuel `i`).
-/
module

public import Core.Fortschritt.SperrFair
public import Core.Fortschritt.SperrFreigabe

@[expose] public section

namespace Gabbro.Core.Fortschritt

open Gabbro.Core.Maschine
open Gabbro.Core.Katalog
open Gabbro.Core.Annahme
open Gabbro.Core.Beobachtung

/-- Non-triviality of the impl bridge: the waiting twin satisfies every state-side premise
    at cut zero — live, dispatched, release-offering holder on a crash-free cut — yet no
    implementation step exists for the holder (its rule stays silent). The agreement premise
    of `SperrHalterImplBereitAussage` is hence load-bearing; the section row is covered by
    `sperr_freigabe_ohne_abschnitt_widerlegt`. -/
theorem sperrHalterImplBereit_nichtTrivial :
    (∃ s, ρ_w.zeit.zustand 0 = some s ∧ (s.sperren ()).besitzer = some stuckHalter ∧
      SperrHalterBereit E_wait s () stuckHalter ∧ s.status stuckHalter = .laeuft ∧
      (∃ k, (s.kerne k).laeuft = some stuckHalter) ∧ (ρ_w.hw.angebot 0).crash = false) ∧
    ¬ ∃ s w plan u spur s', ρ_w.zeit.zustand 0 = some s ∧
      E_wait.system.ImplSchritt stuckHalter s w [plan] u ∧
      FuehrtSchrittAus E_wait.einrichtung 0 stuckHalter s u plan spur s' := by
  refine ⟨⟨sW0, rfl, rfl, ew_halter_bereit, sW0_live _, ⟨0, sW0_kerne0⟩, hw2_crash 0⟩, ?_⟩
  rintro ⟨s, _, _, _, _, _, hzs, himpl, _⟩
  have hss : s = sW0 := Option.some.inj (hzs.symm.trans rfl)
  subst hss
  obtain ⟨i, _, himpl⟩ := himpl
  cases i
  exact absurd (Kontext.faden.inj himpl.1) (by decide)

end Gabbro.Core.Fortschritt
