module

public import Core.Beobachtung.Fluss.Beweise.Geraet.LockstepTransport

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine
open Gabbro.Core.Ast.LowLevel.Device
open Gabbro.Core.Ast

variable {k : Katalog} {scope : Scope} {locals : Umgebung scope}
variable {d : Denotation k scope}

/-- An answer tick appends exactly the answer event and its register address; the memory
    trace is outside-only and the arrival records no end. -/
private theorem geraete_antwort_beob_tick {ρ : Lauf (d.unit locals)} {predictor : Praediktor}
    {t : Nat} {a : AntwortEreignis} {s n : State} {spur : SchrittSpur Nat UInt8}
    (hlabel : ρ.zeit.spur t = some (.antwort a, spur))
    (atS : ρ.zeit.zustand t = some s) (atN : ρ.zeit.zustand (t + 1) = some n)
    (step : AntwortSchritt (d.unit locals).einrichtung (d.unit locals).katalog ρ.hw t a s spur n) :
    schrittBeob ρ predictor t = aussenBeob (d.unit locals) (.antwort a) := by
  obtain ⟨offered, spurEq, append, stateEq⟩ := step
  have haussen : ∀ l ∈ [aussenEtikett (d.unit locals).einrichtung (.antwort a)], l.art = .aussen := by
    intro l hl
    cases List.mem_singleton.mp hl
    rfl
  have hstill := geraete_speicher_still (k := k) (scope := scope) (locals := locals) (d := d)
    append haussen
  have hende : ¬ ∃ c, (neuBeendet s n (d.unit locals).etiketten c).isSome = true := by
    rintro ⟨c, hc⟩
    have hnone : neuBeendet s n (d.unit locals).etiketten c = none := by
      rw [stateEq]
      cases hs : s.status c <;> simp [neuBeendet, hs]
    rw [hnone] at hc
    cases hc
  rw [schrittBeob, hlabel, atS, atN]
  simp only [hstill, spurEq, List.filterMap_nil, List.nil_append, List.append_nil,
    List.flatMap_cons, List.flatMap_nil, hende, if_false]

/-- The strengthened coupling survives a left answer arrival; see `Lockstep.lean`. -/
theorem geraete_antwort_erhalt (locals : Umgebung scope) (d : Denotation k scope) :
    GeraeteAntwortErhaltAussage (d := d) (locals := locals) := by
  intro h₁ h₂ ρ₁ ρ₂ vergleich predictor t a spur hkopp hlabel
  have tick₁ := ρ₁.zeit.takt t
  rw [hlabel] at tick₁
  cases tick₁ with
  | wartet lab _ _ => cases lab
  | schritt lab step =>
    cases hz₁ : ρ₁.zeit.zustand t with
    | none => rw [hz₁] at step; cases step
    | some s₁ =>
      rw [hz₁] at step
      cases hn₁ : ρ₁.zeit.zustand (t + 1) with
      | none => rw [hn₁] at step; cases step
      | some n₁ =>
        rw [hn₁] at step
        cases step with
        | schritt impl =>
          cases impl with
          | kontext _ _ _ _ => cases lab
          | absturz _ => cases lab
          | interrupt _ _ => cases lab
          | antwort hkein₁ h1 =>
            obtain ⟨v₁, s₂, hv₁, hz₂⟩ := (geraete_zustand_gemeinsam vergleich t).resolve_left
              (by intro h; rw [hz₁] at h; cases h.1)
            have hvEq : v₁ = s₁ := Option.some.inj (hv₁.symm.trans hz₁)
            subst v₁
            have gut₂ : s₂.SpeicherGut := geraete_lauf_speicher_gut vergleich.rechts t hz₂
            obtain ⟨spur₂, n₂t, hstep₂t, spurEq₂⟩ :=
              geraete_antwort_transport vergleich hkopp hz₁ hz₂ gut₂ h1
            obtain ⟨offered₁, spurEq₁, append₁, stateEq₁⟩ := h1
            have hang := geraete_angebot_gleich vergleich t
            have hkein₂ : (ρ₂.hw.angebot t).crash = false := by
              rw [← hang]
              exact hkein₁
            have st₂ : Lauffolge (d.unit locals) ρ₂.hw t (some s₂) (.antwort a, spur₂) (some n₂t) :=
              .schritt (ImplSchritt.antwort hkein₂ hstep₂t)
            have tick₂ := ρ₂.zeit.takt t
            cases tick₂ with
            | wartet lab₂ _ hkein => exact (hkein (.antwort a, spur₂) _ st₂).elim
            | schritt lab₂ step₂ =>
              cases hn₂ : ρ₂.zeit.zustand (t + 1) with
              | none => rw [hn₂] at step₂; cases step₂
              | some n₂ =>
                rw [hn₂] at step₂
                cases step₂ with
                | schritt impl₂ =>
                  have hinv₂ : GeraeteInvariantAussage d.binding s₂ :=
                    geraete_lauf_invariante vergleich.rechts t hz₂
                  obtain ⟨hfragen, hverlauf, hantworten, _, _⟩ :=
                    geraeteKopplung_ledger hkopp hz₁ hz₂
                  have hepoche := ((geraeteKopplung_kopplung hkopp).2.1 s₁ s₂ hz₁ hz₂).2.1
                  have offered₂ : s₂.AntwortAngeboten (d.unit locals).katalog ρ₂.hw t a :=
                    geraete_angeboten_transport vergleich offered₁ hfragen hverlauf hantworten hepoche
                  cases impl₂ with
                  | kontext keinAbsturz₂ bereit₂ regel₂ aus₂ =>
                    obtain ⟨_, plan', hplans', rule₂⟩ := geraete_kontext_regel (geraete_rule_form locals d) regel₂
                    cases rule₂ with
                    | issue owned idle =>
                      exact (geraete_issue_schliesst_ankunft_aus (d := d) hinv₂ owned idle
                        ⟨a, ρ₂.hw, t, offered₂⟩).elim
                    | consume owned pending ready sameQ =>
                      exact (geraete_consume_schliesst_ankunft_aus (d := d) hinv₂ owned pending ready sameQ
                        ⟨a, ρ₂.hw, t, offered₂⟩).elim
                  | interrupt keinAbsturz₂ enters₂ =>
                    obtain ⟨kk, irq, c₂, nmi, _, pend₂, _, _, _, _, _⟩ := enters₂
                    have gueltig := vergleich.rechts.2.1.2 t
                    exact geraete_interrupt_schliesst_antwort_aus gueltig pend₂.2.2.2.2
                      offered₂.2.1.1
                  | absturz crash₂ =>
                    exact (Bool.false_ne_true (crash₂.1.2.symm.trans hkein₂)).elim
                  | antwort hkein₂' h2 =>
                    obtain ⟨a', offered₂', spurEq₂', append₂, stateEq₂⟩ := h2
                    have aeq : a' = a := geraete_antwort_eindeutig (d := d) hinv₂ offered₂' offered₂
                    subst a'
                    have hspurEq' : spur = spur₂' := congrArg Prod.snd (Option.some.inj lab₂)
                    have hbeob₂' := h2
                    have hbeob₁ := geraete_antwort_beob_tick (predictor := predictor) hlabel hz₁ hn₁ h1
                    have hbeob₂ := geraete_antwort_beob_tick (predictor := predictor) lab₂ hz₂ hn₂ hbeob₂'
                    have hlen := kopplung_laenge (geraeteKopplung_kopplung hkopp)
                    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
                    · simp only [NiedrigeBeob, NiedrigeBeob.praefix, hbeob₁, hbeob₂]
                      let L₁ := NiedrigeBeob (d.unit locals) ρ₁ predictor t
                      let L₂ := NiedrigeBeob (d.unit locals) ρ₂ predictor t
                      let A := aussenBeob (d.unit locals) (.antwort a)
                      have hlenP : L₁.length = L₂.length := by simpa only [L₁, L₂, E, NiedrigeBeob] using hlen
                      have happLen : (L₂ ++ A).length = (L₁ ++ A).length := by
                        simp only [List.length_append, hlenP]
                      have ht : (L₂ ++ A).take ((L₁ ++ A).length) = L₂ ++ A :=
                        List.take_of_length_le (le_of_eq happLen)
                      rw [ht]
                      have reflA : List.Forall₂ (EreignisAequiv (d.unit locals).fluss.freigabe) A A := by
                        induction A with
                        | nil => exact List.Forall₂.nil
                        | cons x xs ih => exact List.Forall₂.cons (EreignisAequiv.gleich _) ih
                      exact List.rel_append (by simpa only [L₁, L₂, E, NiedrigeBeob] using
                        (geraeteKopplung_kopplung hkopp).1) reflA
                    · intro v w hv hw
                      obtain rfl : v = n₁ := Option.some.inj (hv.symm.trans hn₁)
                      obtain rfl : w = n₂ := Option.some.inj (hw.symm.trans hn₂)
                      have hquell₁ : QuellzustandGleich (d.unit locals) s₁ s₂ :=
                        ((geraeteKopplung_kopplung hkopp).2.1 s₁ s₂ hz₁ hz₂).1
                      have hstatus := ((geraeteKopplung_kopplung hkopp).2.1 s₁ s₂ hz₁ hz₂).2.2.2.2
                      have hkerne := ((geraeteKopplung_kopplung hkopp).2.1 s₁ s₂ hz₁ hz₂).2.2.2.1
                      have hgeliefert := ((geraeteKopplung_kopplung hkopp).2.1 s₁ s₂ hz₁ hz₂).2.2.1
                      have hep := ((geraeteKopplung_kopplung hkopp).2.1 s₁ s₂ hz₁ hz₂).2.1
                      refine ⟨?_, hep, hgeliefert, hkerne, hstatus⟩
                      -- QuellzustandGleich of post states
                      unfold QuellzustandGleich at hquell₁ ⊢
                      refine ⟨hquell₁.1, ?_, hquell₁.2.2.1, hquell₁.2.2.2.1,
                        hquell₁.2.2.2.2.1, ?_⟩
                      · intro c
                        simpa only [stateEq₁, stateEq₂] using hquell₁.2.1 c
                      · intro c
                        unfold AntwortSicht
                        simp only [Zustand.naechsteAntwort, Zustand.angekommen,
                          stateEq₁, stateEq₂, hantworten]
                    · simp only [NiedrigeBeob, NiedrigeBeob.praefix, hbeob₁, hbeob₂,
                        List.length_append]
                      simp only [NiedrigeBeob] at hlen
                      exact congrArg (fun n => n + (aussenBeob (d.unit locals) (.antwort a)).length) hlen
                    · intro v w hv hw
                      obtain rfl : v = n₁ := Option.some.inj (hv.symm.trans hn₁)
                      obtain rfl : w = n₂ := Option.some.inj (hw.symm.trans hn₂)
                      refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, rfl⟩
                      · rw [stateEq₁, stateEq₂, hfragen]
                      · rw [stateEq₁, stateEq₂, hverlauf]
                      · rw [stateEq₁, stateEq₂, hantworten]
                      · rfl
                      · rfl

end Gabbro.Core.Beobachtung
