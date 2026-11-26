module

public import Core.Beobachtung.Fluss.Beweise.Geraet.Lockstep
public import Core.Beobachtung.Fluss.Beweise.Geraet.Recovery
public import Core.Beobachtung.Fluss.Beweise.Geraet.LockstepInvariant
public import Core.Beobachtung.Fluss.Beweise.Geraet.LockstepAbsturz
public import Core.Ast.LowLevel.DeviceUnit

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine
open Gabbro.Core.Ast.LowLevel.Device
open Gabbro.Core.Ast.LowLevel (entryContext)
open Gabbro.Core.Ast

variable {k : Katalog} {scope : Scope} {locals : Umgebung scope}
variable {d : Denotation k scope}

/-- Every state along an admitted device run has a consistent complete graph. -/
theorem geraete_lauf_speicher_gut {h : Umgebung} {ρ : Lauf (d.unit locals)}
    (lauf : Laeufe (d.unit locals) h ρ) (t : Nat) {v : State}
    (atV : ρ.zeit.zustand t = some v) : v.SpeicherGut := by
  revert v atV
  induction t with
  | zero =>
      intro v atV
      have z0 := lauf.2.2.2
      cases hload : (d.unit locals).laden ρ.start (h.lade (d.unit locals).bild) with
      | none =>
        rw [hload] at z0
        rw [atV] at z0
        cases z0
      | some z =>
        have hv : v = z := Option.some.inj (atV.symm.trans (z0.trans hload))
        subst v
        dsimp only [Denotation.unit, Gabbro.Core.Ast.LowLevel.Device.unit] at hload
        split at hload
        · obtain rfl := Option.some.inj hload
          change Speicher.Zustand.leer.graph.Konsistent ∧ Speicher.Zustand.leer.graph.Vollstaendig
          exact ⟨Speicher.Zustand.leer_konsistent, Speicher.Zustand.leer_vollstaendig⟩
        · cases hload
  | succ t ih =>
      intro v atV
      cases hz : ρ.zeit.zustand t with
      | none =>
        have tick := ρ.zeit.takt t
        rw [hz] at tick
        cases tick with
        | schritt _ step => cases step
        | wartet _ eq _ =>
          rw [eq] at atV
          cases atV
      | some s =>
        have tick := ρ.zeit.takt t
        rw [hz] at tick
        cases hev : ρ.zeit.spur t with
        | none =>
          rw [hev] at tick
          cases tick with
          | schritt label _ => cases label
          | wartet _ eq _ =>
            obtain rfl : v = s := Option.some.inj (atV.symm.trans eq)
            exact ih hz
        | some ev =>
          rw [hev] at tick
          cases hpost : ρ.zeit.zustand (t + 1) with
          | none =>
            rw [hpost] at tick
            cases tick with
            | schritt _ step => cases step
            | wartet _ eq _ => cases eq
          | some s' =>
            have hv : v = s' := Option.some.inj (atV.symm.trans hpost)
            subst v
            rw [hpost] at tick
            cases tick with
            | wartet label _ _ => cases label
            | schritt _ step =>
              cases step with
              | schritt impl => exact impl_speicher_gut (d.unit locals).einrichtung (d.unit locals).system impl (ih hz)

/-- The register-machine invariant holds at every state of an admitted device run. -/
theorem geraete_lauf_invariante {h : Umgebung} {ρ : Lauf (d.unit locals)}
    (lauf : Laeufe (d.unit locals) h ρ) (t : Nat) {v : State}
    (atV : ρ.zeit.zustand t = some v) : GeraeteInvariantAussage d.binding v := by
  obtain ⟨binding, access, required, target, ruleEq, hbind⟩ :
      ∃ binding access required target,
        d.rule locals = Rule.machine binding access required target ∧ binding = d.binding := by
    cases d with
    | read dest b off => exact ⟨b, .read off, .ready, none, rfl, rfl⟩
    | fallibleRead dest b off promise handler =>
      exact ⟨b, .fallibleRead off promise, .ready, none, rfl, rfl⟩
    | write b off value =>
      exact ⟨b, .write off (value.wert locals).wert.toNat, .ready, none, rfl, rfl⟩
    | transition decl =>
      exact ⟨decl.binding, .write decl.row.offset decl.data, decl.changes.prior,
        some decl.changes.after, rfl, rfl⟩
  subst binding
  revert v atV
  induction t with
  | zero =>
      intro v atV
      have z0 := lauf.2.2.2
      cases hload : (d.unit locals).laden ρ.start (h.lade (d.unit locals).bild) with
      | none =>
        rw [hload] at z0
        rw [atV] at z0
        cases z0
      | some z =>
        have hinv := geraete_invariante_start (d := d) hload
        obtain rfl : v = z := Option.some.inj (atV.symm.trans (z0.trans hload))
        exact hinv
  | succ t ih =>
      intro v atV
      have tick := ρ.zeit.takt t
      cases hz : ρ.zeit.zustand t with
      | none =>
        rw [hz] at tick
        cases tick with
        | schritt _ step => cases step
        | wartet _ eq _ =>
          rw [eq] at atV
          cases atV
      | some s =>
        rw [hz] at tick
        cases hev : ρ.zeit.spur t with
        | none =>
          rw [hev] at tick
          cases tick with
          | schritt label _ => cases label
          | wartet _ eq _ =>
            obtain rfl : v = s := Option.some.inj (atV.symm.trans eq)
            exact ih hz
        | some ev =>
          rw [hev] at tick
          cases hpost : ρ.zeit.zustand (t + 1) with
          | none =>
            rw [hpost] at tick
            cases tick with
            | schritt _ step => cases step
            | wartet _ eq _ => cases eq
          | some s' =>
            have hv : v = s' := Option.some.inj (atV.symm.trans hpost)
            subst v
            rw [hpost] at tick
            cases tick with
            | wartet label _ _ => cases label
            | schritt _ step =>
              cases step with
              | schritt impl =>
                cases impl with
                | kontext _ _ regel aus =>
                  obtain ⟨_, plan', hplans, rule⟩ := geraete_kontext_regel ruleEq regel
                  cases rule with
                  | issue owned idle =>
                    have htick := geraete_issue_tick (target := target) aus hplans rfl owned idle
                    obtain ⟨_, hfragen, _, hantworten, hverbraucht, hverworfen,
                      hbuchung, hepoche, _, _, _, hlokal, _, _, _, _, _, _, _, _, _⟩ := htick
                    have hinv := ih hz
                    have hinv' := geraete_issue_erhaelt_invariante (target := target)
                      (t := t) hinv owned idle
                    unfold GeraeteInvariantAussage at hinv' ⊢
                    rw [hlokal, hfragen, hantworten, hverbraucht, hverworfen, hbuchung, hepoche]
                    simpa only [Zustand.frage, setFrame] using hinv'
                  | consume owned pending ready sameQuestion =>
                    have htick := geraete_consume_tick (target := target)
                      aus hplans rfl owned pending ready sameQuestion
                    have hfragen := htick.2.1
                    have hantworten := htick.2.2.2.1
                    have hverbraucht := htick.2.2.2.2.1
                    have hverworfen := htick.2.2.2.2.2.1
                    have hbuchung := htick.2.2.2.2.2.2.1
                    have hepoche := htick.2.2.2.2.2.2.2.1
                    have hlokal := htick.2.2.2.2.2.2.2.2.2.2.2.1
                    have hinv := ih hz
                    have hinv' := geraete_consume_erhaelt_invariante (target := target)
                      hinv owned pending ready sameQuestion
                    unfold GeraeteInvariantAussage at hinv' ⊢
                    rw [hlokal, hfragen, hantworten, hverbraucht, hverworfen, hbuchung, hepoche]
                    simpa only [Zustand.verbrauche, setFrame, geraete_consume_rahmen] using hinv'
                | antwort _ h =>
                  obtain ⟨offered, _, _, stateEq⟩ := h
                  have hinv := ih hz
                  have hinv' := geraete_ankunft_invariant (binding := d.binding) hinv offered
                  unfold GeraeteInvariantAussage at hinv' ⊢
                  rw [stateEq]
                  simpa only [Zustand.antwort] using hinv'
                | interrupt _ h =>
                  obtain ⟨kk, irq, cc, nmi, _, _, _, _, _, _, nextEq⟩ := h
                  have hinv := ih hz
                  rw [nextEq]
                  exact geraete_interrupt_invariant (binding := d.binding) (s := s)
                    (kern := kk) (c := cc) (nmi := nmi) (graph := s'.graph) hinv
                | absturz crash =>
                  obtain ⟨_, stateEq⟩ := AbsturzSchritt.genau crash
                  have hcut := geraete_schnitt_schranke lauf t s hz
                  have hinv := ih hz
                  rw [stateEq]
                  have rein : ∀ c,
                      (((d.unit locals).einrichtung.wiederanlauf.daten
                        (nachAbsturz s.persistenz).dauerhaft).lokal c).pending = none := by
                    intro c
                    dsimp only [Denotation.unit, Gabbro.Core.Ast.LowLevel.Device.unit,
                      setup, bootFor]
                    by_cases hc : c = entryContext <;> simp only [hc, if_true, if_false]
                  exact geraete_absturz_invariant_mit_neustart hinv hcut.1 rein

end Gabbro.Core.Beobachtung
