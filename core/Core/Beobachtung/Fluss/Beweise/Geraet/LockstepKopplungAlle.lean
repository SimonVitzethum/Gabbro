module

public import Core.Beobachtung.Fluss.Beweise.Geraet.Lockstep
public import Core.Beobachtung.Fluss.Beweise.GeraetStart
public import Core.Beobachtung.Fluss.Beweise.Geraet.LockstepAbsturzErhalt
public import Core.Beobachtung.Fluss.Beweise.Geraet.LockstepAntwortErhalt
public import Core.Beobachtung.Fluss.Beweise.Geraet.LockstepInterruptErhalt
public import Core.Beobachtung.Fluss.Beweise.Geraet.LockstepPauseErhalt

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine
open Gabbro.Core.Ast.LowLevel.Device
open Gabbro.Core.Ast

variable {k : Katalog} {scope : Scope} {locals : Umgebung scope}
variable {d : Denotation k scope}

/-- The strengthened coupling holds at every cut of a compared device run,
    assuming the context-tick preservation unit. Cut zero comes from
    `geraete_start_kopplungAussage`; every later cut is obtained from the
    previous one by casing the left tick `ρ₁.zeit.spur t`: a context step uses
    the supplied unit, an answer, interrupt, crash or pause uses the matching
    proved `Erhalt` theorem. -/
theorem geraete_kopplung_alle_aus {k : Katalog} {scope : Scope} {locals : Umgebung scope}
    {d : Denotation k scope}
    (kontext : GeraeteKontextErhaltAussage (d := d) (locals := locals)) :
    GeraeteKopplungAlleAussage (d := d) (locals := locals) := by
  intro h₁ h₂ ρ₁ ρ₂ vergleich predictor t
  induction t with
  | zero =>
      exact geraete_start_kopplungAussage vergleich predictor
  | succ t ih =>
      cases hspur : ρ₁.zeit.spur t with
      | none =>
          exact geraete_pause_erhalt locals d h₁ h₂ ρ₁ ρ₂ vergleich predictor t ih hspur
      | some ev =>
          rcases ev with ⟨label, spur⟩
          cases label with
          | kontext c w =>
              exact kontext h₁ h₂ ρ₁ ρ₂ vergleich predictor t c w spur ih hspur
          | antwort a =>
              exact geraete_antwort_erhalt locals d h₁ h₂ ρ₁ ρ₂ vergleich predictor t a spur ih hspur
          | interrupt id =>
              exact geraete_interrupt_erhalt locals d h₁ h₂ ρ₁ ρ₂ vergleich predictor t id spur ih hspur
          | absturz =>
              exact geraete_absturz_erhalt locals d h₁ h₂ ρ₁ ρ₂ vergleich predictor t spur ih hspur

end Gabbro.Core.Beobachtung
