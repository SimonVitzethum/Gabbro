module

public import Core.Beobachtung.Fluss.Beweise.Geraet.LockstepTransport
public import Core.Beobachtung.Fluss.Interrupt

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine
open Gabbro.Core.Ast.LowLevel.Device
open Gabbro.Core.Ast.LowLevel (entryContext)
open Gabbro.Core.Ast

variable {k : Katalog} {scope : Scope} {locals : Umgebung scope}
variable {d : Denotation k scope}

/-- An interrupt tick emits exactly one catalogue event: the memory trace is outside-only and
    entering a handler sets `status` to `.laeuft`, never to `.beendet`. -/
private theorem geraete_interrupt_beob_tick {ρ : Lauf (d.unit locals)} {predictor : Praediktor}
    {t : Nat} {id : Nat × Nat} {kern : Nat} {irq : Unterbrechung} {c : Kontext} {nmi : Bool}
    {s n : State} {spur : SchrittSpur Nat UInt8}
    (hlabel : ρ.zeit.spur t = some (.interrupt id, spur))
    (atS : ρ.zeit.zustand t = some s) (atN : ρ.zeit.zustand (t + 1) = some n)
    (aussen : spur.aussen = [.interrupt kern irq .handler])
    (append : Speicherfolge s.initial .aussen s.graph
      [aussenEtikett (d.unit locals).einrichtung (.interrupt kern irq .handler)]
      spur.speicher n.graph)
    (ruht : s.status c = .ruht)
    (next : n = { Zustandseintritt s kern id c nmi with graph := n.graph }) :
    schrittBeob ρ predictor t = aussenBeob (d.unit locals) (.interrupt kern irq .handler) := by
  have haussen : ∀ l ∈ [aussenEtikett (d.unit locals).einrichtung (.interrupt kern irq .handler)],
      l.art = .aussen := by
    intro l hl
    cases List.mem_singleton.mp hl
    rfl
  have hstill := geraete_speicher_still (k := k) (scope := scope) (locals := locals) (d := d)
    append haussen
  have hende : ¬ ∃ c', (neuBeendet s n (d.unit locals).etiketten c').isSome = true := by
    rintro ⟨c', hc⟩
    have hnone : neuBeendet s n (d.unit locals).etiketten c' = none := by
      rw [neuBeendet]
      by_cases hcc : c' = c
      · subst c'
        have statusN : n.status c = .laeuft := by
          rw [next]
          simp only [Zustandseintritt, Function.update_self]
        rw [statusN, ruht]
      · have statusN : n.status c' = s.status c' := by
          rw [next]
          simp only [Zustandseintritt, Function.update]
          split
          · rename_i hcd
            exact (hcc hcd).elim
          · rfl
        rw [statusN]
        cases hs : s.status c' <;> rfl
    rw [hnone] at hc
    cases hc
  rw [schrittBeob, hlabel, atS, atN]
  simp only [hstill, aussen, aussenBeob, List.flatMap_cons, List.flatMap_nil,
    List.nil_append, List.append_nil, hende, if_false]

/-- Decompose an implementation step whose label is an interrupt. -/
private theorem geraete_impl_interrupt {ρ : Lauf (d.unit locals)} {t : Nat} {s n : State}
    {id : Nat × Nat} {spur : SchrittSpur Nat UInt8}
    (h : ImplSchritt (d.unit locals).einrichtung (d.unit locals).system
      (d.unit locals).katalog ρ.hw t s (.interrupt id, spur) n) :
    (ρ.hw.angebot t).crash = false ∧
      UnterbrechungsSchritt (d.unit locals).einrichtung ρ.hw t id s spur n := by
  cases h with
  | interrupt hk hs => exact ⟨hk, hs⟩

/-- The strengthened coupling survives a left interrupt entry; see `Lockstep.lean`. -/
theorem geraete_interrupt_erhalt (locals : Umgebung scope) (d : Denotation k scope) :
    GeraeteInterruptErhaltAussage (d := d) (locals := locals) := by
  intro h₁ h₂ ρ₁ ρ₂ vergleich predictor t id spur hkopp hlabel
  let E := d.unit locals
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
          have hstepTyp : ImplSchritt E.einrichtung E.system E.katalog ρ₁.hw t s₁
              (.interrupt id, spur) n₁ := by
            rw [← Option.some.inj lab] at impl
            exact impl
          obtain ⟨hkein₁, h1⟩ := geraete_impl_interrupt hstepTyp
          have h1copy := h1
          obtain ⟨kern, irq, c, nmi, offer₁, pending₁, nimmt₁, ruht₁, spurEq₁,
            append₁, nextEq₁⟩ := h1
          obtain ⟨v₁, s₂, hv₁, hz₂⟩ := (geraete_zustand_gemeinsam vergleich t).resolve_left
            (by intro h; rw [hz₁] at h; cases h.1)
          have hvEq : v₁ = s₁ := Option.some.inj (hv₁.symm.trans hz₁)
          subst v₁
          have gut₂ : s₂.SpeicherGut := geraete_lauf_speicher_gut vergleich.rechts t hz₂
          obtain ⟨spur₂, n₂t, hstep₂t, spurEq₂⟩ :=
            geraete_interrupt_transport vergleich hkopp hz₁ hz₂ gut₂ h1copy
          have hang := geraete_angebot_gleich vergleich t
          have hkein₂ : (ρ₂.hw.angebot t).crash = false := by
            rw [← hang]
            exact hkein₁
          have st₂ : Lauffolge E ρ₂.hw t (some s₂) (.interrupt id, spur₂) (some n₂t) :=
            .schritt (ImplSchritt.interrupt hkein₂ hstep₂t)
          have tick₂ := ρ₂.zeit.takt t
          rw [hz₂] at tick₂
          cases tick₂ with
          | wartet lab₂ _ hkein => exact (hkein (.interrupt id, spur₂) _ st₂).elim
          | schritt lab₂ step₂ =>
            cases hn₂ : ρ₂.zeit.zustand (t + 1) with
            | none => rw [hn₂] at step₂; cases step₂
            | some n₂ =>
              rw [hn₂] at step₂
              cases step₂ with
              | schritt impl₂ =>
                have gueltig := vergleich.rechts.2.1.2 t
                have wahl₂ : (ρ₂.hw.angebot t).interruptAuswahl = some (kern, id, irq) := by
                  rw [← hang]
                  exact pending₁.2.2.2.2
                cases impl₂ with
                | kontext _ bereit₂ _ _ =>
                    exact (geraete_interrupt_schliesst_kontext_aus (E := E) gueltig wahl₂ bereit₂).elim
                | antwort _ hAnt =>
                    rename_i spurAns ans
                    have hdelivered := hAnt.1.2.1.1
                    rw [hAnt.1.1] at hdelivered
                    exact (geraete_interrupt_schliesst_antwort_aus (a := ans) gueltig wahl₂ hdelivered).elim
                | absturz crash₂ =>
                    exfalso
                    rw [crash₂.1.2] at hkein₂
                    cases hkein₂
                | interrupt _ h₂' =>
                  have auswahlEq : (ρ₁.hw.angebot t).interruptAuswahl =
                      (ρ₂.hw.angebot t).interruptAuswahl := by
                    rw [hang]
                  obtain ⟨idEq, aussenEq⟩ :=
                    interruptspur_gleich (e := E.einrichtung) auswahlEq h1copy h₂'
                  cases idEq
                  obtain ⟨kernR, irqR, cR, nmiR, offerR, pendingR, enterR, ruhtR,
                    aussenR, appendR, nextEqR⟩ := h₂'
                  have headEq : Ereignis.interrupt kern irq .handler =
                      Ereignis.interrupt kernR irqR .handler :=
                    (List.cons.inj (spurEq₁.symm.trans (aussenEq.trans aussenR))).1
                  injection headEq with hkEq hirqEq
                  subst kernR
                  subst irqR
                  obtain ⟨⟨lokGleich, endeGleich, initialGleich, rechteGleich, leihenGleich,
                    antwortGleich⟩, epocheEq, geliefertEq, kerneEq, statusEq⟩ :=
                    (geraeteKopplung_kopplung hkopp).2.1 s₁ s₂ hz₁ hz₂
                  have enterR' : NimmtUnterbrechung (s₁.kerne kern) kern
                      (Nat.pair id.1 id.2) irq cR nmiR := by
                    rw [kerneEq]
                    exact enterR
                  have cnEq : c = cR ∧ nmi = nmiR := by
                    cases nimmt₁ <;> cases enterR' <;> exact ⟨rfl, rfl⟩
                  obtain ⟨hcEq, hnEq⟩ := cnEq
                  subst cR
                  subst nmiR
                  have hbeob₁ := geraete_interrupt_beob_tick (predictor := predictor)
                    hlabel hz₁ hn₁ spurEq₁ append₁ ruht₁ nextEq₁
                  have hbeob₂ : schrittBeob ρ₂ predictor t =
                      aussenBeob E (.interrupt kern irq .handler) := by
                    exact geraete_interrupt_beob_tick (predictor := predictor)
                      (by simpa using lab₂) hz₂ hn₂ aussenR appendR ruhtR nextEqR
                  have hlen := kopplung_laenge (geraeteKopplung_kopplung hkopp)
                  obtain ⟨hfragen, hverlauf, hantworten, hverbraucht, hverworfen⟩ :=
                    geraeteKopplung_ledger hkopp hz₁ hz₂
                  have hbuch := geraeteKopplung_buchung hkopp hz₁ hz₂
                  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
                  · simp only [NiedrigeBeob, NiedrigeBeob.praefix, hbeob₁, hbeob₂]
                    let L₁ := NiedrigeBeob.praefix E ρ₁ predictor t
                    let L₂ := NiedrigeBeob.praefix E ρ₂ predictor t
                    let A := aussenBeob E (.interrupt kern irq .handler)
                    have hlenP : L₁.length = L₂.length := by
                      simpa only [L₁, L₂, E, NiedrigeBeob] using hlen
                    have happLen : (L₂ ++ A).length = (L₁ ++ A).length := by
                      simp only [List.length_append, hlenP]
                    have ht : (L₂ ++ A).take ((L₁ ++ A).length) = L₂ ++ A :=
                      List.take_of_length_le (le_of_eq happLen)
                    rw [ht]
                    have hcov : List.Forall₂ (EreignisAequiv E.fluss.freigabe) L₁ L₂ := by
                      have hc := (geraeteKopplung_kopplung hkopp).1
                      simp only [NiedrigeBeob] at hc
                      rw [hlenP] at hc
                      simpa only [L₁, L₂, E, List.take_length] using hc
                    have reflA : List.Forall₂ (EreignisAequiv E.fluss.freigabe) A A := by
                      induction A with
                      | nil => exact List.Forall₂.nil
                      | cons x xs ih => exact List.Forall₂.cons (EreignisAequiv.gleich _) ih
                    exact List.rel_append (by simpa only [L₁, L₂, E] using hcov) reflA
                  · intro v w hv hw
                    obtain rfl : v = n₁ := Option.some.inj (hv.symm.trans hn₁)
                    obtain rfl : w = n₂ := Option.some.inj (hw.symm.trans hn₂)
                    refine ⟨?_, ?_, ?_, ?_, ?_⟩
                    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
                      · intro d place hp
                        rw [nextEq₁, nextEqR]
                        simp only [Zustandseintritt]
                        exact lokGleich d place hp
                      · intro d
                        rw [nextEq₁, nextEqR]
                        simp only [Zustandseintritt, statusEq]
                      · intro x
                        rw [nextEq₁, nextEqR]
                        simp only [Zustandseintritt]
                        exact initialGleich x
                      · rw [nextEq₁, nextEqR]
                        simp only [Zustandseintritt]
                        exact rechteGleich
                      · rw [nextEq₁, nextEqR]
                        simp only [Zustandseintritt]
                        exact leihenGleich
                      · intro d
                        rw [nextEq₁, nextEqR]
                        simp only [Zustandseintritt, AntwortSicht]
                        exact antwortGleich d
                    · rw [nextEq₁, nextEqR]
                      simp only [Zustandseintritt, epocheEq]
                    · rw [nextEq₁, nextEqR]
                      simp only [Zustandseintritt, geliefertEq]
                    · rw [nextEq₁, nextEqR]
                      simp only [Zustandseintritt, Function.update_self, kerneEq]
                    · rw [nextEq₁, nextEqR]
                      simp only [Zustandseintritt, Function.update_self, statusEq]
                  · simp only [NiedrigeBeob, NiedrigeBeob.praefix, hbeob₁, hbeob₂,
                      List.length_append]
                    simp only [NiedrigeBeob] at hlen
                    exact congrArg (fun n => n + (aussenBeob E (.interrupt kern irq .handler)).length) hlen
                  · intro v w hv hw
                    obtain rfl : v = n₁ := Option.some.inj (hv.symm.trans hn₁)
                    obtain rfl : w = n₂ := Option.some.inj (hw.symm.trans hn₂)
                    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
                    · rw [nextEq₁, nextEqR]
                      simpa only [Zustandseintritt] using hfragen
                    · rw [nextEq₁, nextEqR]
                      simpa only [Zustandseintritt] using hverlauf
                    · rw [nextEq₁, nextEqR]
                      simpa only [Zustandseintritt] using hantworten
                    · rw [nextEq₁, nextEqR]
                      simpa only [Zustandseintritt] using hverbraucht
                    · rw [nextEq₁, nextEqR]
                      simpa only [Zustandseintritt] using hverworfen
                    · rw [nextEq₁, nextEqR]
                      simpa only [Zustandseintritt] using hbuch

end Gabbro.Core.Beobachtung
