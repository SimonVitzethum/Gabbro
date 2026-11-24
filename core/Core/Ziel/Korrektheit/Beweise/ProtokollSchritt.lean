/-
  File:      core/Core/Ziel/Korrektheit/Beweise/ProtokollSchritt.lean
  Subject:   THE PROTOCOL INVARIANTS ARE PRESERVED BY ONE STEP OF EITHER MACHINE (pinned statement
             `ProtokollSchrittErhaeltAussage`). Feeds: `impl_speicher_gut`, `ideal_speicher_gut`,
             `ImplSchritt.verbrauch`, `FuehrtSchrittAus.verbrauch`, `kontextSchritt_sperren`,
             `antwortSchritt_sperren`, `interruptSchritt_sperren`, `nimmt_inv`, `abgeben_nodup`,
             `gibt_abgeben`, `absturz_leert_schlange`. Proof sketch: prove the lock invariant once over
             `SperrSchritt` (ticket needs both guards, take and hand-off keep it, crash wipes it), lift it over
             `FuehrtAus` (only `sperre` moves one lock) and over the four shared protocol cases, then apply the
             same four cases to `ImplSchritt` and to `I.Schritt`. The lock lemmas of `Fortschritt` are phrased
             over `E.einrichtung`; generic versions parametrized by an arbitrary `Einrichtung` are used here so
             the statement holds for every elaborated unit. `sperr_schritt_erfuellbar` shows the lock rules fire.
-/
module

public import Core.Ziel.Korrektheit.Maschine
public import Core.Fortschritt.SperrErhalt
public import Core.Verfeinerung.Sicherheit

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit

open Gabbro.Core
open Gabbro.Core.Maschine
open Gabbro.Core.Fortschritt
open Gabbro.Core.Katalog

variable {L Ort Wert Raum Lok Grund Bedingung Wahl ι : Type} [DecidableEq L]
variable {e : Einrichtung L Ort Wert Raum Lok Grund Bedingung}
variable {Sy : MaschinenSystem L Ort Wert Raum Lok Grund Bedingung Wahl ι}
variable {k : Katalog.Katalog} {hw : Katalog.HwLauf} {t : Nat}

/-- The lock invariant of one lock: a duplicate-free queue whose owner is not queued. -/
abbrev SperrGut (z : SperrZustand) : Prop :=
  z.schlange.Nodup ∧ ∀ c, z.besitzer = some c → c ∉ z.schlange

/-- Every lock rule keeps `SperrGut`. The ticket guard `keinTicket` is essential: without it a context
    already queued could draw a second ticket. The owner guard is equally essential. -/
theorem sperrSchritt_erhaelt {a : SperrAktion} {c : Kontext} {z z' : SperrZustand}
    (h : SperrSchritt a c z z') (gut : SperrGut z) : SperrGut z' := by
  cases h with
  | ticket keinBesitz keinTicket =>
    constructor
    · change (z.schlange ++ [c]).Nodup
      refine List.nodup_append.mpr ⟨gut.1, List.nodup_singleton c, ?_⟩
      intro x hx y hy
      rw [List.mem_singleton] at hy
      subst y
      intro hxc
      exact keinTicket (hxc ▸ hx)
    · change ∀ d, z.besitzer = some d → d ∉ z.schlange ++ [c]
      intro d hbes
      rw [List.mem_append]
      intro hmem
      rcases hmem with hmem | hmem
      · exact (gut.2 d hbes) hmem
      · have hdc : d = c := List.mem_singleton.mp hmem
        apply keinBesitz
        rw [hbes, hdc]
  | nehmen hn =>
    obtain ⟨r, hz, hz'⟩ := nimmt_inv hn
    subst z
    subst z'
    constructor
    · exact (List.nodup_cons.mp gut.1).2
    · intro d hbes
      have hdc : d = c := Option.some.inj hbes.symm
      subst d
      exact (List.nodup_cons.mp gut.1).1
  | geben hg =>
    obtain ⟨q, hz, hz'⟩ := gibt_abgeben hg
    subst z
    subst z'
    constructor
    · exact abgeben_nodup gut.1
    · intro d hbes
      cases q with
      | nil =>
        change none = some d at hbes
        cases hbes
      | cons h₀ rest =>
        change some h₀ = some d at hbes
        have hdc : d = h₀ := Option.some.inj hbes.symm
        subst d
        change h₀ ∉ rest
        exact (List.nodup_cons.mp gut.1).1

/-- Inversion for the lock part of a generic `sperre` protocol step. -/
theorem fuehrtAus_sperre_inv_e {t c s u mem ev v} {l a}
    (h : FuehrtAus e t c s u (.sperre l a) mem ev v) :
    ∃ next, SperrSchritt a c (s.sperren l) next ∧ v.sperren l = next ∧
      ∀ m, m ≠ l → v.sperren m = s.sperren m := by
  cases h with
  | sperre hss _ =>
    exact ⟨_, hss, Function.update_self _ _ _,
      fun m hm => Function.update_of_ne hm _ _⟩

/-- The lock invariant survives one form action: every action but `sperre` keeps the lock field of
    the frame, and `sperre` moves one lock by a `SperrSchritt`. -/
theorem fuehrtAus_sperren_gut {t c s u aktion mem ev v}
    (rahmen : Zustandsrahmen s u) (h : FuehrtAus e t c s u aktion mem ev v)
    (gut : ProtokollGut s) :
    ∀ l, SperrGut (v.sperren l) := by
  intro l
  match haktion : aktion with
  | .intern =>
    cases h
    have hl : v.sperren l = s.sperren l := congrFun rahmen.sperren l
    rwa [hl]
  | .warte _ =>
    cases h
    have hl : v.sperren l = s.sperren l := congrFun rahmen.sperren l
    rwa [hl]
  | .sperre ll a =>
    obtain ⟨next, hss, hvl, hvlne⟩ := fuehrtAus_sperre_inv_e h
    by_cases hl : l = ll
    · subst hl
      rw [hvl]
      exact sperrSchritt_erhaelt hss (gut.sperren ll)
    · have h' : v.sperren l = s.sperren l := hvlne l hl
      rwa [h']
  | .frage _ =>
    cases h
    have hl : v.sperren l = s.sperren l := congrFun rahmen.sperren l
    rwa [hl]
  | .verbrauche _ =>
    cases h
    have hl : v.sperren l = s.sperren l := congrFun rahmen.sperren l
    rwa [hl]
  | .rueckkehr =>
    cases h
    have hl : v.sperren l = s.sperren l := congrFun rahmen.sperren l
    rwa [hl]

/-- A context step keeps all three invariants. -/
theorem fuehrtSchrittAus_erhaelt {t c s u plan spur s'}
    (aus : FuehrtSchrittAus e t c s u plan spur s') (gut : ProtokollGut s) : ProtokollGut s' := by
  refine ⟨(aus.viele e).gut gut.speicher.1 gut.speicher.2, aus.verbrauch gut.verbrauch, ?_⟩
  obtain ⟨rahmen, _, _, v, haus, _, state⟩ := aus
  have hsperr : ∀ l, s'.sperren l = v.sperren l := fun l =>
    (congrArg (fun z : Zustand L Ort Wert Raum Lok Grund => z.sperren l) state).trans rfl
  intro l
  rw [hsperr l]
  exact fuehrtAus_sperren_gut rahmen haus gut l

/-- An arrival keeps all three invariants. -/
theorem antwortSchritt_erhaelt {s spur s'} {a : AntwortEreignis}
    (h : AntwortSchritt e k hw t a s spur s') (gut : ProtokollGut s) : ProtokollGut s' := by
  refine ⟨(h.viele e).gut gut.speicher.1 gut.speicher.2, ?_, ?_⟩
  · rw [h.2.2.2]
    exact Zustand.antwort_verbrauch gut.verbrauch a
  · intro l
    have hs : s'.sperren l = s.sperren l :=
      (congrArg (fun z : Zustand L Ort Wert Raum Lok Grund => z.sperren l) h.2.2.2).trans rfl
    rwa [hs]

/-- An interrupt entry keeps all three invariants. -/
theorem interruptSchritt_erhaelt {s spur s'} {id : Nat × Nat}
    (h : UnterbrechungsSchritt e hw t id s spur s') (gut : ProtokollGut s) : ProtokollGut s' := by
  refine ⟨(h.viele e).gut gut.speicher.1 gut.speicher.2, ?_, ?_⟩
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, state⟩ := h
    rw [state]
    exact gut.verbrauch
  · intro l
    obtain ⟨_, _, _, _, _, _, _, _, _, _, state⟩ := h
    have hs : s'.sperren l = s.sperren l :=
      (congrArg (fun z : Zustand L Ort Wert Raum Lok Grund => z.sperren l) state).trans rfl
    rwa [hs]

/-- A crash keeps the memory and consumption invariants and wipes every lock. -/
theorem absturzSchritt_erhaelt {region : Strecke} {w : Wiederanlauf Ort Wert Raum Lok Grund}
    {s spur s'} (h : AbsturzSchritt region w k hw t s spur s') (gut : ProtokollGut s) :
    ProtokollGut s' := by
  refine ⟨h.neustart.2.2.2.2.2.2.2, ?_, ?_⟩
  · exact (h.verbrauch gut.verbrauch).1
  · intro l
    have hs := absturz_leert_schlange (l := l) h
    constructor
    · rw [hs.1]
      exact List.nodup_nil
    · intro c hbes
      rw [hs.2] at hbes
      cases hbes

theorem protokoll_schritt_erhaelt : ProtokollSchrittErhaeltAussage := by
  intro L Ort Wert Raum Lok Grund Bedingung Wahl ι inst e Sy k hw t s s' spur gut
  constructor
  · intro step
    cases step with
    | kontext _ _ _ aus => exact fuehrtSchrittAus_erhaelt aus gut
    | antwort _ h => exact antwortSchritt_erhaelt h gut
    | interrupt _ h => exact interruptSchritt_erhaelt h gut
    | absturz h => exact absturzSchritt_erhaelt h gut
  · intro step
    cases step with
    | kontext _ _ _ aus => exact fuehrtSchrittAus_erhaelt aus gut
    | antwort _ h => exact antwortSchritt_erhaelt h gut
    | interrupt _ h => exact interruptSchritt_erhaelt h gut
    | absturz h => exact absturzSchritt_erhaelt h gut

end Gabbro.Core.Ziel.Korrektheit
