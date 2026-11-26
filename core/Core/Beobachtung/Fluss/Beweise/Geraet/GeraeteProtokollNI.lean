module

public import Core.Beobachtung.Fluss.Beweise.Geraet
public import Core.Beobachtung.Fluss.Beweise.GeraetKopplung
public import Core.Beobachtung.Fluss.Beweise.Geraet.LockstepKopplungAlle

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine
open Gabbro.Core.Ast

/-- The device unit discharges the two shared protocol duties: an answer, interrupt or
    crash tick and an idle tick each keep the coupling. For every duty the strengthened
    coupling is rebuilt at the cut `t` from the comparison (`geraete_kopplung_alle`),
    the matching preservation unit is applied once, and the result is projected back to
    `Kopplung` with `geraeteKopplung_kopplung`. The coupling premise of each duty is
    redundant and is kept only to match the pinned shape. -/
theorem geraeteProtokollNI : GeraeteProtokollNIAussage := by
  intro k scope locals d
  constructor
  · intro h₁ h₂ ρ₁ ρ₂ vergleich predictor t w spur hspur protokoll kopplung
    have gall := geraete_kopplung_alle (k := k) (scope := scope) (locals := locals) (d := d)
      h₁ h₂ ρ₁ ρ₂ vergleich predictor t
    cases w with
    | kontext _ _ => cases protokoll
    | antwort a =>
        exact geraeteKopplung_kopplung
          (geraete_antwort_erhalt (k := k) (scope := scope) locals d
            h₁ h₂ ρ₁ ρ₂ vergleich predictor t a spur gall hspur)
    | interrupt id =>
        exact geraeteKopplung_kopplung
          (geraete_interrupt_erhalt (k := k) (scope := scope) locals d
            h₁ h₂ ρ₁ ρ₂ vergleich predictor t id spur gall hspur)
    | absturz =>
        exact geraeteKopplung_kopplung
          (geraete_absturz_erhalt (k := k) (scope := scope) locals d
            h₁ h₂ ρ₁ ρ₂ vergleich predictor t spur gall hspur)
  · intro h₁ h₂ ρ₁ ρ₂ vergleich predictor t hspur kopplung
    have gall := geraete_kopplung_alle (k := k) (scope := scope) (locals := locals) (d := d)
      h₁ h₂ ρ₁ ρ₂ vergleich predictor t
    exact geraeteKopplung_kopplung
      (geraete_pause_erhalt (k := k) (scope := scope) locals d
        h₁ h₂ ρ₁ ρ₂ vergleich predictor t gall hspur)

end Gabbro.Core.Beobachtung
