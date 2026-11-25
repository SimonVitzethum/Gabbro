/-
  File:      core/Core/Ziel/Korrektheit/Beweise/SchedulerFairEinheit.lean
  Subject:   CONTEXT FAIRNESS FOR ELABORATED UNITS — the scheduler premise closed,
              the progress statement unconditional, and the two load-bearing
              statements.

  DECISION (MK-11): context fairness is a property of the execution model, not
  a catalogue row. PERFECT-MODEL §3.4 schedules runtime-dispatched contexts
  with a generic dispatch proof and makes executing the dispatch a language
  obligation; §3.7 assumes fairness of the environment as hardware only (cores
  step, interrupts are delivered: catalogue rows) and never assumes a
  scheduler. `FairLaeufe` speaks about cores, deliveries and cycles only and
  never arbitrates which ready context takes a step, so the per-context
  liveness of `FortschrittAkzeptiertAussage` is not derivable from it. The
  missing selection fairness therefore lives in run admissibility
  (`SchedulerFair`, part of `Laeufe`), which every admissible platform
  satisfies by construction (`fairerZeit`); no user proves anything, and no
  catalogue row is added.

  On that basis the four scheduler fields of `FortschrittsPflichten` hold for
  every elaborated unit (`scheduler_fuer_einheitVon`): the recorded run
  itself selects (`nutzbar` = the run's own context steps, so `wahl` is
  immediate and `angebot` follows from the step's opportunity), and an open,
  enabled context is served infinitely often because `SchedulerFair` fires on
  the constant dispatch core of `SchedulerFairDispatch.lean`. With it the
  pinned `FortschrittAkzeptiertAussage` closes unconditionally
  (`fortschritt_akzeptiert`); its statement is unchanged. `FairLaeufe` still
  does not rule out a hang on its own (`kontextFairness_nichtTrivial`, the
  starvation run), and fair scheduler-admissible runs exist for every
  accepted elaborated unit (`einheitVon_fair_lauf_erfuellbar`).
-/
module

public import Core.Ziel.Korrektheit.Beweise.SchedulerFairDispatch
public import Core.Fortschritt.Verzoegerung
public import Core.Fortschritt.Verhungern

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit

open Gabbro.Core
open Gabbro.Core.Maschine

/-- The scheduler duties hold for every elaborated unit: take the run's own
    context steps as the selection. Offering follows from the step's physical
    opportunity, choice is immediate, and an open, enabled context is served
    infinitely often by scheduler fairness on its constant dispatch core. Lock
    acquisition as a second activation form is vacuous for elaborated units
    (`einheitVon_kein_sperre`); the system-wide duty is vacuous for the
    blocking class. -/
theorem scheduler_fuer_einheitVon : SchedulerFortschrittVoraussetzung := by
  intro P t _akzeptiert H ρ lauf _fair η valid matched environment
  obtain ⟨fertig, regeln, komponierbar, eindeutig⟩ := einheit_fortschrittsfelder P t
  refine ⟨(fun t c => ∃ w spur, ρ.zeit.spur t = some (.kontext c w, spur)),
    fertig, regeln, komponierbar, eindeutig, ?_, ?_, ?_, ?_⟩
  · intro t' c slot
    obtain ⟨w, spur, hstep⟩ := slot
    obtain ⟨s, hs, kann⟩ := Fortschritt.impl_schritt_braucht_gelegenheit hstep
    obtain ⟨k, geleg, disp, _⟩ := kann
    have hseq : s = η.zeit.zustand t' :=
      einheitVon_bezug_gleich P t matched t' s hs
    refine ⟨k, ?_, ?_⟩
    · rw [hseq] at disp
      exact disp
    · rw [matched.hardware]
      exact geleg
  · intro t' c slot _
    obtain ⟨w, spur, hstep⟩ := slot
    exact ⟨w, spur, hstep⟩
  · intro fair' a c f opened enabled n hn
    cases enabled with
    | inl bereitAlle =>
      have crashfrei : ∀ t', a ≤ t' → (ρ.hw.angebot t').crash = false := by
        intro t' ht'
        by_cases hc : (ρ.hw.angebot t').crash = false
        · exact hc
        · have htrue : (ρ.hw.angebot t').crash = true := by
            cases hcr : (ρ.hw.angebot t').crash with
            | false => exact (hc hcr).elim
            | true => rfl
          have konform : ρ.hw.konform (einheitVon P t).katalog H := lauf.2.1
          have gueltig := konform.2 t'
          have selected : (einheitVon P t).katalog.enthaelt .persistence :=
            gueltig.2.2.2.2 (Or.inr htrue)
          have offer : AbsturzAngeboten (einheitVon P t).katalog ρ.hw t' :=
            ⟨selected, htrue⟩
          have offerη : AbsturzAngeboten (einheitVon P t).katalog η.hw t' := by
            rw [matched.hardware]
            exact offer
          have hspurη := (Maschine.I.absturz_am_schnitt (einheitVon P t) η offerη).1
          exact ((opened.2 t' ht').2.2 (Or.inr (Or.inl hspurη))).elim
      obtain ⟨kstar, hkonst⟩ :=
        einheitVon_dispatch_konstant P t valid matched opened
      obtain ⟨sa, hsa, _⟩ := matched.zustand a
      have hsaEq : sa = η.zeit.zustand a :=
        einheitVon_bezug_gleich P t matched a sa hsa
      have hvalid := einheitVon_dispatch_gueltig P t lauf valid matched hsa
      have hstar : kstar < H.kernzahl := by
        have hd : (sa.kerne kstar).laeuft = some c := by
          rw [hsaEq]
          exact hkonst a (Nat.le_refl _)
        exact hvalid.1 kstar c hd
      have hstarη : kstar < η.umgebung.kernzahl := by
        rw [environment]
        exact hstar
      have suffixReady : ∀ t'', a ≤ t'' → ∃ s, ρ.zeit.zustand t'' = some s ∧
          (∃ k, (s.kerne k).laeuft = some c) ∧ s.status c = .laeuft ∧
          (ρ.hw.angebot t'').crash = false ∧
          ∃ w plan u spur s', (einheitVon P t).system.ImplSchritt c s w [plan] u ∧
            FuehrtSchrittAus (einheitVon P t).einrichtung t'' c s u plan spur s' := by
        intro t'' ht''
        obtain ⟨s, hs, _⟩ := matched.zustand t''
        have hseq : s = η.zeit.zustand t'' :=
          einheitVon_bezug_gleich P t matched t'' s hs
        have hd : ((η.zeit.zustand t'').kerne kstar).laeuft = some c :=
          hkonst t'' ht''
        have hlive : (η.zeit.zustand t'').status c = .laeuft :=
          (opened.2 t'' ht'').2.1
        have hcrash := crashfrei t'' ht''
        obtain ⟨w, plan, u, spur, s', himpl, haus⟩ :=
          einheitVon_bereit_vollzug P t t'' (bereitAlle t'' ht'')
        rw [← hseq] at himpl haus hd hlive
        exact ⟨s, hs, ⟨kstar, hd⟩, hlive, hcrash, w, plan, u, spur, s', himpl, haus⟩
      have opportunities : ∀ m, a ≤ m → ∃ t'', m ≤ t'' ∧ ∃ k,
          ρ.hw.gelegenheit t'' k ∧ ∃ s, ρ.zeit.zustand t'' = some s ∧
            (s.kerne k).laeuft = some c := by
        intro m hm
        obtain ⟨t'', ht'', hgeleg⟩ := fair'.kerne.2 kstar hstarη m
        obtain ⟨s, hs, _⟩ := matched.zustand t''
        have hseq : s = η.zeit.zustand t'' :=
          einheitVon_bezug_gleich P t matched t'' s hs
        have hd : ((η.zeit.zustand t'').kerne kstar).laeuft = some c :=
          hkonst t'' (Nat.le_trans hm ht'')
        rw [← hseq] at hd
        exact ⟨t'', ht'', kstar, hgeleg, s, hs, hd⟩
      have scheduler := lauf.2.2.2.2
      obtain ⟨t', ht', w, spur, hstep⟩ := scheduler a c suffixReady opportunities n hn
      exact ⟨t', ht', ⟨w, spur, hstep⟩, bereitAlle t' (Nat.le_trans hn ht')⟩
    | inr lockOft =>
      obtain ⟨_, _, _, w, plan, u, _, ischritt, hakt⟩ := lockOft a (Nat.le_refl _)
      exact (einheitVon_kein_sperre P t ischritt hakt).elim
  · intro _
    trivial

/-- The pinned progress statement, closed unconditionally: the scheduler duties
    for the elaborated unit are theorems, so `sim_ziel_fortschritt_im_lauf`
    consumes them directly. The statement is unchanged. -/
theorem fortschritt_akzeptiert : FortschrittAkzeptiertAussage :=
  fortschritt_akzeptiert_aus_scheduler scheduler_fuer_einheitVon

/-- Fair scheduler-admissible runs exist for every accepted elaborated unit:
    the catalogue is well-formed by acceptance, the entry image is valid on
    every platform, and the fair schedule constructs the run. -/
theorem einheitVon_fair_lauf_erfuellbar (P : Katalog.Plattform) (t : Ast.Unit)
    (akzeptiert : Annahme.Akzeptiert (einheitVon P t)) :
    ∃ (H : Katalog.Umgebung) (ρ : Maschine.Lauf (einheitVon P t)),
      Maschine.Laeufe (einheitVon P t) H ρ ∧
      Katalog.FairLaeufe (einheitVon P t).katalog H ρ.hw := by
  have wohlgeformt : Katalog.KatalogWohlgeformt (einheitVon P t).katalog :=
    Annahme.akzeptiert_katalog _ akzeptiert
  have hformat : Katalog.Bildformat.elf ∈ P.ziel.imageFormats :=
    (Katalog.ziele_gut P).2.2.2.2.2.2.2.2.2
  have gueltig : (einheitVon P t).bild.gueltig
      (einheitVon P t).katalog.plattform.ziel := by
    have hbild : (einheitVon P t).bild =
        ⟨.elf, fun a => if a = 0 then some 0 else none, [0]⟩ := rfl
    rw [hbild]
    have hplat : (einheitVon P t).katalog.plattform = P := rfl
    rw [hplat]
    refine ⟨hformat, ?_, ?_⟩
    · intro a byte present
      change (if a = 0 then some 0 else none) = some byte at present
      split at present
      · rename_i atZero
        subst a
        exact Nat.pow_pos (Nat.zero_lt_succ _)
      · cases present
    · intro a mem
      have h : a = 0 := List.mem_singleton.mp mem
      subst a
      exact ⟨0, rfl⟩
  obtain ⟨h, _, _, ρ, _, fair, run, _, _⟩ :=
    Maschine.lauf_erfuellbar (einheitVon P t) wohlgeformt gueltig
  exact ⟨h, ρ, run, fair⟩

/-- Without context fairness a context hangs, on a fair hardware history: one
    context steps forever while another stays dispatched, enabled and never
    discharged. Fair hardware alone does not rule out a hang; the scheduler
    duty is load-bearing. -/
theorem kontextFairness_nichtTrivial :
    ∃ (E : Maschine.Einheit Unit Unit Unit Unit Bool Unit Unit Unit Unit)
      (ρ : Maschine.Lauf E) (η : Maschine.I.Lauf E) (c : Maschine.Kontext),
      Katalog.FairLaeufe E.katalog η.umgebung ρ.hw ∧
      ∃ a f, Maschine.I.BleibtOffen η c f a ∧ Maschine.I.Aktiviert η c a ∧
        (∀ t, a ≤ t → ∀ w spur, η.zeit.spur t ≠ some (.kontext c w, spur)) := by
  refine ⟨Fortschritt.E_w Fortschritt.dispatch2, Fortschritt.ρAB, Fortschritt.ηAB,
    Fortschritt.B, Fortschritt.fair2, 0, (), ?_, Or.inl ?_, ?_⟩
  · refine ⟨fun t _ => ⟨1, ?_⟩, fun t _ => ⟨rfl, ?_, Fortschritt.nie_erledigt_B t⟩⟩
    · rw [Fortschritt.ηAB_zustand, Fortschritt.zAB_kerne]
      exact Fortschritt.zAB0_dispatch1
    · rw [Fortschritt.ηAB_zustand, Fortschritt.zAB_status]
      exact Fortschritt.zAB0_live _
  · intro t _
    exact Fortschritt.bereit_B t (Nat.zero_le t)
  · intro t _ w spur hstep
    exact Fortschritt.nie_erledigt_B t (Or.inl ⟨w, spur, hstep⟩)

end Gabbro.Core.Ziel.Korrektheit
