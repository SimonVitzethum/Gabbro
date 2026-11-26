/-
  THE ACCESS-FRAGMENT NONINTERFERENCE LEG from the run-level access coupling and the liveness of the
  memory model. The family dispatch uses `KlassenRein`: a form at the head of a step in an accepted
  fragment is frame-only or an access instruction, so `stummer_schritt_koppelt` and
  `zugriff_schritt_koppelt` cover all cases. The remaining open premises are the pinned
  `SpeicherGraphKopplungAussage` and `ZugriffSchrittExistiertAussage`.
-/
module

public import Core.Beobachtung.Fluss.Beweise.Zugriff.Lauf
public import Core.Ziel.Korrektheit.Beweise2.ZugriffNIFragment

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit

open Gabbro.Core
open Gabbro.Core.Beobachtung
open Katalog Maschine

/-- The fragment NI leg, from the run-level access coupling and the liveness of the memory model. -/
theorem zugriffNIFragmentAusTeilen
    (existiert : ZugriffSchrittExistiertAussage)
    (graphKopplung : SpeicherGraphKopplungAussage) : ZugriffNIFragmentAussage := by
  intro p plattform mitZugriff akzeptiert
  have klassenrein : p.KlassenRein := mitZugriff.1
  apply ni_akzeptierter_einheit (p.einheit plattform) akzeptiert (fragment_start_ni p plattform)
  · intro f fluss h₁ h₂ ρ₁ ρ₂ vergleich predictor t c w spur vor zustand kopf tick kopplung
    have fmem : f ∈ p.code := Ast.Semantik.kopf_mem (code := p.code) kopf
    rcases klassenrein f fmem with hpriv | ⟨z, hz⟩
    · exact stummer_schritt_koppelt vergleich zustand kopf tick
        (antwortNI p plattform h₂ ρ₂ vergleich.rechts t · ·) hpriv kopplung
    · subst f
      exact zugriff_schritt_koppelt existiert graphKopplung p plattform z vergleich
        fluss zustand kopf tick kopplung
  · intro h₁ h₂ ρ₁ ρ₂ v predictor t w spur tick protokoll kopplung
    cases w with
    | kontext _ _ => exact False.elim protokoll
    | antwort a => exact (antwortNI p plattform h₁ ρ₁ v.links t a spur tick).elim
    | interrupt _ => exact interruptNI p plattform v predictor t _ spur tick trivial kopplung
    | absturz => exact absturzNI p plattform v predictor t _ spur tick trivial kopplung
  · intro h₁ h₂ ρ₁ ρ₂ v predictor t idle kopplung
    exact pause_klassenrein existiert p plattform klassenrein v predictor t idle kopplung

end Gabbro.Core.Ziel.Korrektheit
