module

public import Core.Beobachtung.Fluss.Beweise.Geraet.Hilfe
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
  induction t generalizing v with
  | zero =>
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
      refine ⟨fun q hq => by rw [hfragen.1] at hq; cases hq, ?_⟩
      rw [hep]
  | succ t ih =>
    intro w atW
    have tick := ρ.zeit.takt t
    cases hz : ρ.zeit.zustand t with
    | none =>
      rw [hz] at tick
      generalize hN : ρ.zeit.zustand (t + 1) = post at tick
      cases tick with
      | schritt _ step => cases step
      | wartet _ eq _ =>
        rw [hN] at atW
        rw [eq, hz] at atW
        cases atW
    | some s =>
      rw [hz] at tick
      generalize hN : ρ.zeit.zustand (t + 1) = post at tick
      cases tick with
      | schritt _ step =>
        cases step with
        | schritt impl =>
          cases impl with
          | kontext _ _ regel aus =>
            obtain ⟨kopfEq, plan', hplans, rule⟩ := geraete_kontext_regel ruleEq regel
            cases rule with
            | issue owned idle =>
              have hplan : plan' = { internal with aktion := .frage (binding.question access) } :=
                (List.cons.inj hplans).1
              subst hplan
              cases spur with
              | mk speicher aussen =>
                obtain ⟨rahmen, auth, sperren, v, fuehrtAus, speicherfolge, nEqState⟩ := aus
                cases fuehrtAus with
                | frage q =>
                  have hfragen : s'.fragen =
                      s.fragen ++ [s.stelleFrage t c (binding.question access)] := by
                    simp only [nEqState]
                  have hep : s'.epoche = s.epoche := by
                    simp only [nEqState]
                  obtain rfl := Option.some.inj atW
                  obtain ⟨ihfragen, ihepo⟩ := ih s hz
                  refine ⟨?_, ?_⟩
                  · intro q hq
                    rw [hfragen, List.mem_append] at hq
                    cases hq with
                    | inl hmem => exact Nat.lt_succ_of_lt (ihfragen q hmem)
                    | inr hsingle =>
                      rw [List.mem_singleton.mp hsingle]
                      exact Nat.lt_succ_self t
                  · rw [hep]
                    exact Nat.le_succ ihepo
            | consume owned pending ready sameQuestion =>
              have hplan : plan' = { internal with aktion := .verbrauche answer } :=
                (List.cons.inj hplans).1
              subst hplan
              cases spur with
              | mk speicher aussen =>
                obtain ⟨rahmen, auth, sperren, v, fuehrtAus, speicherfolge, nEqState⟩ := aus
                cases fuehrtAus with
                | verbrauche ready' =>
                  have hfragen : s'.fragen = s.fragen := by
                    simp only [nEqState]
                  have hep : s'.epoche = s.epoche := by
                    simp only [nEqState]
                  obtain rfl := Option.some.inj atW
                  obtain ⟨ihfragen, ihepo⟩ := ih s hz
                  refine ⟨fun q hq => ?_, ?_⟩
                  · rw [hfragen] at hq
                    exact Nat.lt_succ_of_lt (ihfragen q hq)
                  · rw [hep]
                    exact Nat.le_succ ihepo
          | antwort _ h =>
            obtain ⟨offered, spurEq, append, stateEq⟩ := h
            have hfragen : s'.fragen = s.fragen := by
              simp only [stateEq]
            have hep : s'.epoche = s.epoche := by
              simp only [stateEq]
            obtain rfl := Option.some.inj atW
            obtain ⟨ihfragen, ihepo⟩ := ih s hz
            refine ⟨fun q hq => ?_, ?_⟩
            · rw [hfragen] at hq
              exact Nat.lt_succ_of_lt (ihfragen q hq)
            · rw [hep]
              exact Nat.le_succ ihepo
          | interrupt _ h =>
            obtain ⟨k, irq, c, nmi, offer, pend, nimmt, ruht, aussen, append, nextEq⟩ := h
            have hfragen : s'.fragen = s.fragen := by
              simp only [nextEq]
            have hep : s'.epoche = s.epoche := by
              simp only [nextEq]
            obtain rfl := Option.some.inj atW
            obtain ⟨ihfragen, ihepo⟩ := ih s hz
            refine ⟨fun q hq => ?_, ?_⟩
            · rw [hfragen] at hq
              exact Nat.lt_succ_of_lt (ihfragen q hq)
            · rw [hep]
              exact Nat.le_succ ihepo
          | absturz h =>
            have hfragen : s'.fragen = s.fragen := by
              simp only [h.genau.2]
            have hep : s'.epoche = t + 1 := by
              simp only [h.genau.2]
            obtain rfl := Option.some.inj atW
            obtain ⟨ihfragen, _⟩ := ih s hz
            refine ⟨fun q hq => ?_, ?_⟩
            · rw [hfragen] at hq
              exact Nat.lt_succ_of_lt (ihfragen q hq)
            · rw [hep]
      | wartet _ eq _ =>
        rw [hN] at atW
        have heq : w = s := Option.some.inj (atW.symm.trans (eq.trans hz))
        subst heq
        obtain ⟨ihfragen, ihepo⟩ := ih s hz
        exact ⟨fun q hq => Nat.lt_succ_of_lt (ihfragen q hq), Nat.le_succ ihepo⟩

end Gabbro.Core.Beobachtung
