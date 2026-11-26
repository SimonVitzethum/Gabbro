/-
  File:      core/Core/Beobachtung/SchrankenBeweise/BindungKosten.lean
  Subject:   THE COST AND HOLD DUTIES OF BOUND UNITS (M9, MK-12). `einheitMitSchranken` binds the
             declared cost and hold ceilings into the unit; the per-form and protocol cost/hold
             duties (`KHRegelPflicht`, `KHProtokollPflicht` of `SchrankenbindungOffenAussage`) close
             in two halves. The OPEN half is vacuous and lives in `BindungOffen`: with no cost
             ceiling and no hold entries every prefix meets its bound. This file carries the FINITE
             half: the declaration must cover the step. The class contributes exactly one tick per
             step (`klassenKosten`, through `Wirkungsklasse.kostenZeile`), so the missing premise
             is the slack of the declaration over the current counters (`bindungKlassenKHRegel`,
             `bindungKostenProtokoll_unterSlack`). The slack is the exact remainder: it is checker
             arithmetic over the declaration, not a language rule. The remaining conjuncts of
             `SchrankenbindungOffenAussage` (time, per-pass, checker row, resource duties, resource
             start) belong to the elaboration and loader steps beside this one and are named in the
             report, not proved here.
-/
module

public import Core.Beobachtung.SchrankenBeweise.BindungOffen
public import Core.Beobachtung.SchrankenB8Beweise
public import Core.Ast.Semantik.Runtime.Klasse.Kosten

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine Annahme
open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik

/-- A context tick adds exactly one to the run cost: the tick is occupied. -/
theorem laufkosten_schritt_besetzt {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type}
    [DecidableEq L] {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form} {ρ : Lauf E}
    {t : Nat} {w : SchrittWahl Wahl} {spurv : SchrittSpur Ort Wert}
    (hit : ρ.zeit.spur t = some (w, spurv)) :
    Laufkosten ρ 0 (t + 1) = Laufkosten ρ 0 t + 1 := by
  simp only [Laufkosten, I.zaehle, Nat.zero_add, hit, Option.isSome_some, ite_true, if_true,
    Nat.add_zero]

/-- A context tick of its own context adds exactly one to that context's cost. -/
theorem kontextkosten_schritt_gleich {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type}
    [DecidableEq L] {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form} {ρ : Lauf E}
    {c : Kontext} {a k t : Nat} {w : Wahl} {spurv : SchrittSpur Ort Wert}
    (eq : a + k = t) (hit : ρ.zeit.spur t = some (.kontext c w, spurv)) :
    Kontextkosten ρ c a (k + 1) = Kontextkosten ρ c a k + 1 := by
  simp only [Kontextkosten, I.zaehle, eq, hit, eq_self_iff_true, decide_true, ite_true, if_true,
    Nat.add_zero, Nat.zero_add]

/-- The finite per-form cost/hold duty under the declaration slack: the step adds one tick
    (`klassenKosten`: one plan per class step, through `Wirkungsklasse.kostenZeile`), so the
    cost prefix survives exactly when the declaration covers the current cost plus the class
    cost, and a hold interval ending at the new cut survives exactly when the declaration
    covers the current context cost plus the class cost. The slack is checker arithmetic over
    the declaration, not a language rule: with it, the duty closes; without it, the bound is
    genuinely exceeded. -/
theorem bindungKlassenKHRegel (P : Katalog.Plattform) (u : UnitMitSchranken) (f : Befehl)
    (kostenSlack : ∀ {h : Umgebung} {ρ : Lauf (einheitMitSchranken P u)} (t : Nat),
      KostenPrefix (einheitMitSchranken P u) ρ t →
      UnterGrenze (einheitMitSchranken P u).schranken.kosten
        (Laufkosten ρ 0 t + (f.klasse.kostenZeile).kosten))
    (halteSlack : ∀ {h : Umgebung} {ρ : Lauf (einheitMitSchranken P u)} (t : Nat) (c : Kontext),
      HaltePrefix (einheitMitSchranken P u) ρ t →
      ∀ (l : Nat) (a k : Nat), a + k = t →
        (∀ t', a ≤ t' → t' < a + (k + 1) →
          ∃ s, ρ.zeit.zustand t' = some s ∧ (s.sperren l).besitzer = some c) →
        UnterGrenze ((einheitMitSchranken P u).schranken.halten l)
          (Kontextkosten ρ c a k + (f.klasse.kostenZeile).kosten)) :
    KHRegelPflicht (einheitMitSchranken P u) f := by
  intro h ρ lauf t c w spur vor nach kostenP halteP vorEq kopf spurEq nachEq
  refine ⟨?_, ?_⟩
  · have hocc := laufkosten_schritt_besetzt spurEq
    have hcost := kostenSlack (h := h) t kostenP
    rw [Wirkungsklasse.kostenZeile_kosten] at hcost
    show UnterGrenze (einheitMitSchranken P u).schranken.kosten (Laufkosten ρ 0 (t + 1))
    rw [hocc]
    exact hcost
  · intro l c' a n bound own
    by_cases hle : a + n ≤ t
    · exact halteP l c' a n hle own
    · have heq : a + n = t + 1 := by omega
      by_cases hn0 : n = 0
      · subst hn0
        intro m _
        have h0 : Kontextkosten ρ c' a 0 = 0 := by simp only [Kontextkosten, I.zaehle]
        rw [h0]
        exact Nat.zero_le m
      · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
        have hak : a + k = t := by omega
        by_cases hcc : c' = c
        · have hinc := kontextkosten_schritt_gleich (E := einheitMitSchranken P u) hak spurEq
          rw [hcc] at own
          have hslack := halteSlack (h := h) t c halteP l a k hak own
          rw [Wirkungsklasse.kostenZeile_kosten] at hslack
          rw [hcc, hinc]
          exact hslack
        · have fremd : ∀ (d : Kontext) (w' : PUnit) (s : SchrittSpur Zelle Int),
              ρ.zeit.spur t = some (.kontext d w', s) → d ≠ c' := by
            intro d w' s hcontra
            have hd : d = c := by
              have h2 := Option.some.inj (spurEq.symm.trans hcontra)
              obtain ⟨hc, _⟩ := Prod.mk.inj h2
              cases hc
              rfl
            rw [hd]
            exact Ne.symm hcc
          exact halteFremd _ _ _ _ _ _ _ _ _ _ ρ c' t fremd halteP l a (k + 1)
            bound own

/-- The finite protocol cost/hold duty under the cost slack: a protocol tick adds one run tick
    and is foreign to every context, so the cost prefix needs the same declaration slack while
    the hold prefix follows from `halteFremd` with no slack at all. -/
theorem bindungKostenProtokoll_unterSlack (P : Katalog.Plattform) (u : UnitMitSchranken)
    (kostenSlack : ∀ {h : Umgebung} {ρ : Lauf (einheitMitSchranken P u)} (t : Nat),
      KostenPrefix (einheitMitSchranken P u) ρ t →
      UnterGrenze (einheitMitSchranken P u).schranken.kosten (Laufkosten ρ 0 t + 1)) :
    KHProtokollPflicht (einheitMitSchranken P u) := by
  intro h ρ lauf t w spur vor nach kostenP halteP vorEq spurEq wahl nachEq
  refine ⟨?_, ?_⟩
  · have hocc := laufkosten_schritt_besetzt spurEq
    have hcost := kostenSlack (h := h) t kostenP
    show UnterGrenze (einheitMitSchranken P u).schranken.kosten (Laufkosten ρ 0 (t + 1))
    rw [hocc]
    exact hcost
  · intro l c' a n bound own
    have fremd : ∀ (d : Kontext) (w' : PUnit) (s : SchrittSpur Zelle Int),
        ρ.zeit.spur t = some (.kontext d w', s) → d ≠ c' := by
      intro d w' s hcontra
      rw [spurEq] at hcontra
      cases w with
      | antwort _ => cases hcontra
      | interrupt _ => cases hcontra
      | absturz => cases hcontra
      | kontext _ _ => exact wahl.elim
    exact halteFremd _ _ _ _ _ _ _ _ _ _ ρ c' t fremd halteP l a n bound own

end Gabbro.Core.Beobachtung
