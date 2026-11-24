/-
  File:      Core/Fortschritt/Klasse.lean
  Subject:   THE CHECKED PROGRESS CLASSES (PERFECT-MODEL §3.7, step M8, constructor-independent part).

  The four classes over `I` runs under hardware-only fairness (`FairLaeufe`), never assuming a
  scheduler. `deadlockFree` is the absence of a closed waiting set (§3.2, §3.4: an internal
  deadlock, including a lone `await` no context can enable); `starvationFree` is the per-thread
  promise `¬ Hängt` (weak continuously-enabled obligations and strong lock-acquisition
  obligations, per `Aktiviert`); `lockFree` is system-wide completion for the checked forms on
  top of the per-cut alternatives; `waitFree` bounds every waiting context's discharge by the
  unit's checked stutter length applied to its own implementation steps (`Kontextkosten`,
  M9 hold-bound shape) — unit data, never existential.

  `deadlockFree` and `lockFree`/`starvationFree` are complementary, not chained: `Hängt`
  sees only enabled-but-never-stepping instances, `GeschlossenWartend` only blocked ones.
  The one definitional chain is `lockFree →` per-cut alternatives (`lockfrei_percut`).
  `waitFree →` no weak hang is `Saetze.waitfrei_schliesst_schwaches_haengen_aus`.
-/
module

public import Core.Verfeinerung.Fortschritt
public import Core.Ideal.Komposition
public import Core.Annahme.Waechter
public import Core.Beobachtung.Schranken

@[expose] public section

namespace Gabbro.Core.Fortschritt

open Gabbro.Core.Maschine
open Gabbro.Core.Katalog
open Gabbro.Core.Annahme
open Gabbro.Core.Beobachtung

variable {L Ort Wert Raum Lok Grund Bedingung Wahl F : Type} [DecidableEq L]
variable {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl F}

/-- The checked progress classes (PERFECT-MODEL §3.7). `lockFree` carries the checked forms,
    exactly as `FortschrittsKlasse` does; the other classes are form-independent. -/
inductive Klasse (F : Type) where
  | deadlockFree
  | starvationFree
  | lockFree (einheiten : F → Prop)
  | waitFree

/-- `deadlockFree`: no ideal cut contains a closed waiting set — no internal deadlock and no
    lone `await` no context can enable (§3.2 `WaechterHalten`, §3.4). -/
def DeadlockFrei (η : I.Lauf E) : Prop :=
  ∀ t, ¬ ∃ C : Kontext → Prop, GeschlossenWartend E (η.zeit.zustand t) C

/-- `starvationFree`: the per-thread promise — no context hangs on a fair hardware history. -/
def StarvationFrei (ρ : Maschine.Lauf E) (η : I.Lauf E) : Prop :=
  ∀ c, ¬ I.Haengt E ρ η c

/-- `lockFree`: system-wide completion for the checked forms, on top of the per-cut
    alternatives (`FortschrittDerKlasse`). -/
def LockFrei (formen : F → Prop) (η : I.Lauf E) : Prop :=
  I.FortschrittDerKlasse (.lockFree formen) η

/-- The per-cut alternatives every live dispatched context has: step, finished, blocked with a
    reason, crash, or a withheld core opportunity (the hardware-delay leg of §3.7). This is the
    first conjunct of `FortschrittDerKlasse`, shared by both classes that build on it. -/
def PerCutFrei (η : I.Lauf E) : Prop :=
  ∀ t c, (η.zeit.zustand t).status c = .laeuft →
    (∃ k, ((η.zeit.zustand t).kerne k).laeuft = some c) →
    I.FortschrittAm E.einrichtung E.system E.katalog η.hw t (η.zeit.zustand t) c

/-- `waitFree`: every waiting context — head form `f` kept, live, dispatched once, still at the
    head, still live, still enabled — is discharged once its own implementation steps exceed the
    unit's checked stutter length. The bound `E.stotterLaenge f` is unit data; the counting is
    over the context's own steps (`Kontextkosten`), never over wall ticks or a scheduler. -/
def WaitFrei (ρ : Maschine.Lauf E) (η : I.Lauf E) : Prop :=
  ∀ c f a, E.system.kopf (η.zeit.zustand a) c = some f →
    (η.zeit.zustand a).status c = .laeuft →
    (∃ k, ((η.zeit.zustand a).kerne k).laeuft = some c) →
    (∀ t, a ≤ t → E.system.kopf (η.zeit.zustand t) c = some f) →
    (∀ t, a ≤ t → (η.zeit.zustand t).status c = .laeuft) →
    (∀ t, a ≤ t → I.Bereit (η.zeit.zustand t) c) →
    ∀ n, E.stotterLaenge f < Kontextkosten ρ c a n →
      ∃ t, a ≤ t ∧ t < a + n ∧ I.Erledigt η c t

/-- The class promise over both runs — the shape `Rahmen.Fortschritt` takes at M12. -/
def KlassenFortschritt (klasse : Klasse F) (ρ : Maschine.Lauf E) (η : I.Lauf E) : Prop :=
  match klasse with
  | .deadlockFree => DeadlockFrei η
  | .starvationFree => StarvationFrei ρ η
  | .lockFree formen => LockFrei formen η
  | .waitFree => WaitFrei ρ η

theorem KlassenFortschritt.deadlockFree :
    KlassenFortschritt (.deadlockFree : Klasse F) ρ η = DeadlockFrei (E := E) η := rfl

theorem KlassenFortschritt.starvationFree :
    KlassenFortschritt (.starvationFree : Klasse F) ρ η = StarvationFrei (E := E) ρ η := rfl

theorem KlassenFortschritt.lockFree (formen : F → Prop) :
    KlassenFortschritt (.lockFree formen : Klasse F) ρ η = LockFrei (E := E) formen η := rfl

theorem KlassenFortschritt.waitFree :
    KlassenFortschritt (.waitFree : Klasse F) ρ η = WaitFrei (E := E) ρ η := rfl

/-- `lockFree` contains the per-cut alternatives definitionally. -/
theorem lockfrei_percut {formen : F → Prop} {η : I.Lauf E}
    (h : LockFrei (E := E) formen η) : PerCutFrei (E := E) η :=
  h.1

end Gabbro.Core.Fortschritt
