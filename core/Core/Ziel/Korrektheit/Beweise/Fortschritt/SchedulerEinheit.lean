/-
  File:      core/Core/Ziel/Korrektheit/Beweise/Fortschritt/SchedulerEinheit.lean
  Subject:   THE SCHEDULER LEG FOR ELABORATED UNITS — the two run premises deliver the
             selection duties, and the pinned progress statement.

  On an open suffix no live context is ever displaced (`einheitVon_keine_verdraengung`,
  via the return premise), so the dispatch core is constant (`einheitVon_dispatch_konstant_neu`).
  Scheduler fairness on that constant core serves the context infinitely often
  (`einheitVon_scheduler_pflichten`): the recorded run itself selects (`nutzbar` = the run's
  own context steps, so `wahl` is immediate and `angebot` follows from the step's
  opportunity), and an open, enabled context is offered again past every cut. Lock
  acquisition as a second activation form is vacuous for elaborated units
  (`einheitVon_kein_sperre`); the system-wide duty is vacuous for the blocking class. With
  the two owner-approved run premises the pinned `FortschrittAkzeptiertAussage` closes
  (`fortschritt_akzeptiert`); its statement is otherwise unchanged. A fair run without
  preemption satisfies both premises (`einheitVon_fair_lauf_erfuellbar`, from `fairerZeit`).
-/
module

public import Core.Ziel.Korrektheit.Beweise.Fortschritt.VerdraengungKonstanz
public import Core.Fortschritt.Verzoegerung
public import Core.Fortschritt.Verhungern

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit

open Gabbro.Core
open Gabbro.Core.Maschine
open Gabbro.Core.Fortschritt

/-- The selection duties hold for every elaborated unit under the two run premises: take the
    run's own context steps as the selection. Offering follows from the step's physical
    opportunity, choice is immediate, and an open, enabled context is served infinitely often
    by scheduler fairness on its constant dispatch core. -/
theorem einheitVon_scheduler_pflichten (P : Katalog.Plattform) (t : Ast.Unit)
    {H : Katalog.Umgebung} {ρ : Maschine.Lauf (einheitVon P t)}
    (lauf : Maschine.Laeufe (einheitVon P t) H ρ)
    (sf : Maschine.SchedulerFair (einheitVon P t) ρ)
    (ret : Maschine.VerdraengungKehrtZurueck (einheitVon P t) ρ)
    {η : Maschine.I.Lauf (einheitVon P t)} (valid : Maschine.I.Laeufe (einheitVon P t) η)
    (matched : Maschine.I.Laufabgleich ρ η) (environment : η.umgebung = H) :
    ∃ nutzbar, Maschine.I.FortschrittsPflichten
      (Maschine.I.FortschrittsKlasse.blockierend : Maschine.I.FortschrittsKlasse Ast.Semantik.Befehl)
      ρ η nutzbar := by
  obtain ⟨fertig, regeln, komponierbar, eindeutig⟩ := einheit_fortschrittsfelder P t
  refine ⟨(fun t c => ∃ w spur, ρ.zeit.spur t = some (.kontext c w, spur)),
    fertig, regeln, komponierbar, eindeutig, ?_, ?_, ?_, ?_⟩
  · intro t' c slot
    obtain ⟨w, spur, hstep⟩ := slot
    obtain ⟨s, hs, kann⟩ := Fortschritt.impl_schritt_braucht_gelegenheit hstep
    obtain ⟨k, geleg, disp, _⟩ := kann
    have hseq : s = η.zeit.zustand t' :=
      einheitVon_zustand_gleich P t matched t' s hs
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
      have crashfrei := einheitVon_ohne_crash P t lauf matched environment opened
      obtain ⟨kstar, hkonst⟩ :=
        einheitVon_dispatch_konstant_neu P t lauf valid matched opened crashfrei ret
      obtain ⟨sa, hsa, _⟩ := matched.zustand a
      have hvalid := einheitVon_dispatch_gueltig P t lauf valid matched hsa
      have hstar : kstar < H.kernzahl := by
        have hd : (sa.kerne kstar).laeuft = some c := hkonst a (Nat.le_refl _) sa hsa
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
          einheitVon_zustand_gleich P t matched t'' s hs
        have hd : (s.kerne kstar).laeuft = some c := hkonst t'' ht'' s hs
        have hlive : (η.zeit.zustand t'').status c = .laeuft :=
          (opened.2 t'' ht'').2.1
        have hcrash := crashfrei t'' ht''
        obtain ⟨w, plan, u, spur, s', himpl, haus⟩ :=
          einheitVon_bereit_vollzug P t t'' (bereitAlle t'' ht'')
        rw [← hseq] at himpl haus hlive
        exact ⟨s, hs, ⟨kstar, hd⟩, hlive, hcrash, w, plan, u, spur, s', himpl, haus⟩
      have opportunities : ∀ m, a ≤ m → ∃ t'', m ≤ t'' ∧ ∃ k,
          ρ.hw.gelegenheit t'' k ∧ ∃ s, ρ.zeit.zustand t'' = some s ∧
            (s.kerne k).laeuft = some c := by
        intro m hm
        obtain ⟨t'', ht'', hgeleg⟩ := fair'.kerne.2 kstar hstarη m
        obtain ⟨s, hs, _⟩ := matched.zustand t''
        have hd : (s.kerne kstar).laeuft = some c :=
          hkonst t'' (Nat.le_trans hm ht'') s hs
        exact ⟨t'', ht'', kstar, hgeleg, s, hs, hd⟩
      obtain ⟨t', ht', w, spur, hstep⟩ := sf a c suffixReady opportunities n hn
      exact ⟨t', ht', ⟨w, spur, hstep⟩, bereitAlle t' (Nat.le_trans hn ht')⟩
    | inr lockOft =>
      obtain ⟨_, _, _, w, plan, u, _, ischritt, hakt⟩ := lockOft a (Nat.le_refl _)
      exact (einheitVon_kein_sperre P t ischritt hakt).elim
  · intro _
    trivial

/-- The pinned progress statement, closed under the two run premises: the selection duties
    for the elaborated unit follow from scheduler fairness and preemption return, so
    `sim_ziel_fortschritt_im_lauf` consumes them directly. The statement is otherwise
    unchanged. -/
theorem fortschritt_akzeptiert : FortschrittAkzeptiertAussage := by
  intro P t akzeptiert H ρ lauf fair sf ret
  have pflicht : Maschine.I.SimPflichten (einheitVon P t) :=
    (Ast.Semantik.Fragment.simBasis (Ast.Semantik.fragment Ast.Category.unit t) P).mit_formen
      (Ast.Semantik.sim_formen (Ast.Semantik.fragment Ast.Category.unit t) P)
  obtain ⟨η, valid, sim, _, rest⟩ :=
    Maschine.I.sim_ziel_fortschritt_im_lauf
      (klasse := (Maschine.I.FortschrittsKlasse.blockierend : Maschine.I.FortschrittsKlasse Ast.Semantik.Befehl))
      pflicht lauf
      (fun η valid matched environment fairness =>
        einheitVon_scheduler_pflichten P t lauf sf ret valid matched environment)
  exact ⟨η, valid, sim, (rest fair).1, (rest fair).2⟩

/-- Both run premises hold jointly for an accepted elaborated unit: the catalogue is
    well-formed by acceptance, the entry image is valid on every platform, and the fair
    schedule over a history without raised interrupts constructs the run — scheduler-fair
    by construction and preemption-free by the silent history. -/
theorem einheitVon_fair_lauf_erfuellbar (P : Katalog.Plattform) (t : Ast.Unit)
    (akzeptiert : Annahme.Akzeptiert (einheitVon P t)) :
    ∃ (H : Katalog.Umgebung) (ρ : Maschine.Lauf (einheitVon P t)),
      Maschine.Laeufe (einheitVon P t) H ρ ∧
      Katalog.FairLaeufe (einheitVon P t).katalog H ρ.hw ∧
      Maschine.SchedulerFair (einheitVon P t) ρ ∧
      Maschine.VerdraengungKehrtZurueck (einheitVon P t) ρ := by
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
  let sicht : Nat → Katalog.AussenVerlauf → Katalog.AussenSicht :=
    fun _ _ => Katalog.AussenSicht.leer
  let h := Katalog.Umgebung.referenz (einheitVon P t).katalog 2 sicht
  let hw := Katalog.Umgebung.referenzLauf (einheitVon P t).katalog 2 sicht
  have hardware := Katalog.Umgebung.referenz_hardware (einheitVon P t).katalog 2 sicht
    wohlgeformt (by decide)
  have fair := Katalog.Umgebung.referenz_fair (einheitVon P t).katalog 2 sicht
    wohlgeformt (by decide)
  obtain ⟨s, zul⟩ := Katalog.zulStart_erfuellbar hardware gueltig
  obtain ⟨ρ, run, sched, _, hwEq⟩ :=
    Maschine.fairer_lauf_mit_hw (einheitVon P t) hardware zul fair.konform
  refine ⟨h, ρ, run, ?_, sched, ?_⟩
  · rw [← hwEq]
    exact fair
  · exact Maschine.verdraengung_ohne_meldung hw (fun i => rfl) ρ hwEq

end Gabbro.Core.Ziel.Korrektheit
