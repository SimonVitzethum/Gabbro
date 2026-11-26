/-
  File:      Core/Fortschritt/SperrFairBeweis.lean
  Subject:   Discharge of the two MK-11-strengthened progress sentences.

  Both sentences are discharged through `faire_umgebung_nicht_eindeutig`: the universal
  hardware-fairness premise they inherit is unsatisfiable on an admissible run, so the
  strengthened statements stay vacuous. This is recorded as a finding, not a proof of the
  scheduling step: the substantive chain `sperr_freigabe_bedingt` + holder readiness +
  `SchedulerFair` needs a per-cut `ImplSchritt` witness, which `SperrHalterBereit` (an ideal
  `ISchritt`) does not supply without a refinement/`FortschrittsPflichten` premise. The
  waiting-bound statement additionally needs per-implementation-cut holder readiness from
  `Akzeptiert`, which only gives it at `I` cuts (`SperrHalterHalten`).
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

/-- The strengthened release sentence holds. The discharge uses the inherited universal
    fairness premise together with the new admissibility premise; see the file header for
    the missing substantive scheduling step. -/
theorem sperr_freigabe_aus_scheduler : SperrFreigabeAussage := by
  intro L Ort Wert Raum Lok Grund Bedingung Wahl F inst E ρ hU l h H b s
    bereit hhalte hhalten hsec hfair hlauf hsched hret hzs hown hcrash
  exfalso
  exact faire_umgebung_nicht_eindeutig hlauf hfair

/-- The strengthened waiting-bound sentence holds, by the same inherited premise. The
    intended chain through `sperr_warte_schranke_bis` (fuel `i`) is recorded as open above. -/
theorem sperr_warte_fair_aus_freigabe : SperrWarteFairAussage := by
  intro L Ort Wert Raum Lok Grund Bedingung Wahl F inst E ρ hU l c i H a
    akz hhalte hhalten hfair hlauf hsched hret hqueue hnodup hcrash
  exfalso
  exact faire_umgebung_nicht_eindeutig hlauf hfair

end Gabbro.Core.Fortschritt
