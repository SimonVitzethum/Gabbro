/-
  File:      core/Core/Beobachtung/SchrankenBeweise/Ressourcen.lean
  Subject:   The pinned per-form implementation bound statement `ressourcenRegelAussage`
             quantifies over an arbitrary unit without the checker row, so it is refuted.
             The missing premise is `SchrankenLokal E` together with the simulation match
             (`I.Sim` and `I.RegelSimSchritt E f`), which `schrankenRegelAusLokal` carries.
-/
module

public import Core.Beobachtung.SchrankenB9B21
public import Core.Annahme.HostedLauf

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine Annahme
open Annahme.Hosted

private def gegenEinheit : Modell :=
  { einheit with
    schranken := { Schrankendaten.leer with
      stapel := some 0,
      stapelTiefe := fun h => if h.isNone then 1 else 0 } }

private theorem folgeGegen {hw t vor label nach} :
    Lauffolge einheit hw t vor label nach ↔ Lauffolge gegenEinheit hw t vor label nach := by
  constructor <;> intro h <;> cases h with
  | schritt step => exact .schritt step

private def laufGegen (ρ : Lauf einheit) : Lauf gegenEinheit where
  start := ρ.start
  hw := ρ.hw
  zeit := ⟨ρ.zeit.zustand, ρ.zeit.spur, fun t => by
    cases ρ.zeit.takt t with
    | schritt label step => exact .schritt label (folgeGegen.mp step)
    | wartet label eq hp => exact .wartet label eq (fun label neu step => hp label neu (folgeGegen.mpr step))⟩

/-- The bare statement fails. On the hosted unit with a finite stack ceiling that reads a granted
    handle as depth zero and its absence as depth one, the admitted loader step turns a state
    within the bound into one outside it. The checker row is the missing premise. -/
theorem ressourcenRegelAussage_falsch :
    ¬ ∀ (E : Modell) (f : Unit), ressourcenRegelAussage E f := by
  intro all
  obtain ⟨start, zul⟩ :=
    zulStart_erfuellbar (Hosted.erlaubt []) Sicherheit.Laufkonstruktion.bild_gueltig
  obtain ⟨ρ, g, g', lauf, startEq, hwEq, cut0, cut1, cut2, cut3,
    spur0, spur1, spur2, idle⟩ := konkreter_lauf zul []
  let ρ' := laufGegen ρ
  have lauf' : Laeufe gegenEinheit (umgebung []) ρ' :=
    ⟨lauf.1, lauf.2.1, lauf.2.2.1, lauf.2.2.2⟩
  have takt := ρ'.zeit.takt 0
  rw [cut0, spur0, cut1] at takt
  have impf : ImplSchritt gegenEinheit.einrichtung gegenEinheit.system gegenEinheit.katalog ρ'.hw 0
      (startZustand start) (.kontext kontext (), ⟨[], []⟩) (binde (startZustand start)) := by
    cases takt with
    | schritt label step =>
      cases label
      cases step with
      | schritt step => exact step
    | wartet label eq hp => cases label
  have kopf : gegenEinheit.system.kopf (startZustand start) kontext = some () := rfl
  have stapelVor : StapelZustand gegenEinheit (startZustand start) := by
    intro c n bound
    cases Option.some.inj bound
    change (if (start.outside.channels .hosted 0).isNone then 1 else 0) ≤ 0
    rw [zul.2.2.2.2.2.2.2]
    rfl
  have speicherVor : SpeicherZustand gegenEinheit (startZustand start) := by
    intro n bound
    change none = some n at bound
    cases bound
  have grenzen := all gegenEinheit () lauf' 0 kontext () ⟨[], []⟩
    (startZustand start) (binde (startZustand start)) cut0 kopf spur0 cut1 impf
    stapelVor speicherVor
  have post := grenzen.1 kontext 0 rfl
  change 1 ≤ 0 at post
  omega

end Gabbro.Core.Beobachtung
