module

public import Core.Beobachtung.Fluss.Beweise.Geraet.Hilfe
public import Core.Beobachtung.Fluss.Beweise.Geraet.Issue
public import Core.Beobachtung.Fluss.Beweise.Geraet.Consume
public import Core.Beobachtung.Fluss.Beweise.GeraetIssueKontext

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine
open Gabbro.Core.Ast.LowLevel.Device
open Gabbro.Core.Ast
open Gabbro.Core.Ast.LowLevel (entryContext)

variable {k : Katalog} {scope : Scope} {locals : Umgebung scope}
variable {d : Denotation k scope}

/-- Every recorded question predates its cut and the epoch never overtakes it:
    issues stamp the current cut, every other step preserves both. -/
theorem geraete_schnitt_schranke {h : Umgebung} {ρ : Lauf (d.unit locals)}
    (lauf : Laeufe (d.unit locals) h ρ) (t : Nat) (v : State)
    (atV : ρ.zeit.zustand t = some v) :
    (∀ q ∈ v.fragen, q.cut < t) ∧ v.epoche ≤ t := by
  obtain ⟨binding, access, required, target, ruleEq⟩ := geraete_rule_form locals d
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
      have hfragen := geraete_laden_ledger_leer hload
      have hload' := hload
      have hep : z.epoche = 0 := by
        unfold Denotation.unit Gabbro.Core.Ast.LowLevel.Device.unit at hload'
        dsimp only at hload'
        split at hload'
        · obtain rfl := Option.some.inj hload'
          rfl
        · cases hload'
      obtain rfl := Option.some.inj (atV.symm.trans (z0.trans hload))
      refine ⟨?_, ?_⟩
      · intro q hq
        rw [hfragen.1] at hq
        cases hq
      · rw [hep]
  | succ t ih =>
    intro v atV
    have tick := ρ.zeit.takt t
    cases hz : ρ.zeit.zustand t with
    | none =>
      rw [hz] at tick
      cases tick with
      | schritt _ step => cases step
      | wartet _ eq _ =>
        rw [eq, hz] at atV
        cases atV
    | some s =>
      rw [hz] at tick
      cases hev : ρ.zeit.spur t with
      | none =>
        rw [hev] at tick
        cases tick with
        | schritt label _ => cases label
        | wartet _ eq _ =>
          have heq : v = s := Option.some.inj (atV.symm.trans eq)
          subst heq
          obtain ⟨ihfragen, ihepo⟩ := ih s hz
          exact ⟨fun q hq => Nat.lt_succ_of_lt (ihfragen q hq), Nat.le_succ ihepo⟩
      | some ev =>
        rw [hev] at tick
        revert atV
        cases hpost : ρ.zeit.zustand (t + 1) with
        | none =>
          intro atV
          rw [hpost] at tick
          cases tick with
          | schritt _ step => cases step
          | wartet _ eq _ => cases eq
        | some s' =>
          intro atV
          rw [hpost] at tick
          obtain rfl := Option.some.inj atV
          cases tick with
          | schritt _ step =>
            cases ev with
            | mk wahl sp =>
              cases wahl with
              | kontext c w =>
                cases step with
                | schritt impl =>
                  cases impl with
                  | kontext _ _ regel aus =>
                    obtain ⟨kopfEq, plan', hplans, rule⟩ := geraete_kontext_regel ruleEq regel
                    cases rule with
                    | issue owned idle =>
                      have htick := geraete_issue_tick (target := target) aus hplans rfl owned idle
                      obtain ⟨-, hfragen, -, -, -, -, -, hepoche, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := htick
                      obtain ⟨ihfragen, ihepo⟩ := ih s hz
                      refine ⟨?_, ?_⟩
                      · intro q hq
                        rw [hfragen, List.mem_append] at hq
                        cases hq with
                        | inl hmem => exact Nat.lt_succ_of_lt (ihfragen q hmem)
                        | inr hsingle =>
                          rw [List.mem_singleton.mp hsingle]
                          exact Nat.lt_succ_self t
                      · rw [hepoche]
                        exact Nat.le_succ ihepo
                    | consume owned pending ready sameQuestion =>
                      have htick := geraete_consume_tick (target := target) aus hplans rfl
                        owned pending ready sameQuestion
                      obtain ⟨-, hfragen, -, -, -, -, -, hepoche, -, -, -, -, -, -, -, -, -⟩ := htick
                      obtain ⟨ihfragen, ihepo⟩ := ih s hz
                      refine ⟨fun q hq => ?_, ?_⟩
                      · rw [hfragen] at hq
                        exact Nat.lt_succ_of_lt (ihfragen q hq)
                      · rw [hepoche]
                        exact Nat.le_succ ihepo
              | antwort a =>
                cases step with
                | schritt impl =>
                  cases impl with
                  | antwort _ h =>
                    obtain ⟨offered, spurEq, append, stateEq⟩ := h
                    have hfragen : s'.fragen = s.fragen := by
                      simp only [stateEq]
                    have hep : s'.epoche = s.epoche := by
                      simp only [stateEq]
                    obtain ⟨ihfragen, ihepo⟩ := ih s hz
                    refine ⟨fun q hq => ?_, ?_⟩
                    · rw [hfragen] at hq
                      exact Nat.lt_succ_of_lt (ihfragen q hq)
                    · rw [hep]
                      exact Nat.le_succ ihepo
              | interrupt id =>
                cases step with
                | schritt impl =>
                  cases impl with
                  | interrupt _ h =>
                    obtain ⟨kk, irq, cc, nmi, offer, pend, nimmt, ruht, aussen, append, nextEq⟩ := h
                    have hfragen : s'.fragen = s.fragen := by
                      simp only [nextEq]
                    have hep : s'.epoche = s.epoche := by
                      simp only [nextEq]
                    obtain ⟨ihfragen, ihepo⟩ := ih s hz
                    refine ⟨fun q hq => ?_, ?_⟩
                    · rw [hfragen] at hq
                      exact Nat.lt_succ_of_lt (ihfragen q hq)
                    · rw [hep]
                      exact Nat.le_succ ihepo
              | absturz =>
                cases step with
                | schritt h =>
                  have hfragen : s'.fragen = s.fragen := by
                    simp only [h.genau.2]
                  have hep : s'.epoche = t + 1 := by
                    simp only [h.genau.2]
                  obtain ⟨ihfragen, _⟩ := ih s hz
                  refine ⟨fun q hq => ?_, ?_⟩
                  · rw [hfragen] at hq
                    exact Nat.lt_succ_of_lt (ihfragen q hq)
                  · rw [hep]
          | wartet label _ _ =>
            cases label

end Gabbro.Core.Beobachtung
