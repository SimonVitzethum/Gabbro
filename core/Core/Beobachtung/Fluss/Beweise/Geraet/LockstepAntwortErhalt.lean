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
      cases hs : s.status c <;> simp [neuBeendet, hs, Zustand.antwort]
    rw [hnone] at hc
    cases hc
  rw [schrittBeob, hlabel, atS, atN]
  simp only [hstill, spurEq, List.filterMap_nil, List.nil_append, List.append_nil,
    List.flatMap_cons, List.flatMap_nil, hende, if_false]


/-- Decompose an implementation step whose label is an answer. -/
private theorem geraete_impl_antwort {ρ : Lauf (d.unit locals)} {t : Nat} {s n : State}
    {a : AntwortEreignis} {spur : SchrittSpur Nat UInt8}
    (h : ImplSchritt (d.unit locals).einrichtung (d.unit locals).system
      (d.unit locals).katalog ρ.hw t s (.antwort a, spur) n) :
    (ρ.hw.angebot t).crash = false ∧
      AntwortSchritt (d.unit locals).einrichtung (d.unit locals).katalog ρ.hw t a s spur n := by
  cases h with
  | antwort hk hs => exact ⟨hk, hs⟩

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
          have hstepTyp : ImplSchritt (d.unit locals).einrichtung (d.unit locals).system
              (d.unit locals).katalog ρ₁.hw t s₁ (.antwort a, spur) n₁ := by
            rw [← Option.some.inj lab] at impl
            exact impl
          obtain ⟨hkein₁, h1⟩ := geraete_impl_antwort hstepTyp
          have h1typ : AntwortSchritt (d.unit locals).einrichtung (d.unit locals).katalog
              ρ₁.hw t a s₁ spur n₁ := h1
          have h1copy := h1typ
          obtain ⟨offered₁, spurEq₁, append₁, stateEq₁⟩ := h1typ
          obtain ⟨v₁, s₂, hv₁, hz₂⟩ := (geraete_zustand_gemeinsam vergleich t).resolve_left
            (by intro h; rw [hz₁] at h; cases h.1)
          have hvEq : v₁ = s₁ := Option.some.inj (hv₁.symm.trans hz₁)
          subst v₁
          have gut₂ : s₂.SpeicherGut := geraete_lauf_speicher_gut vergleich.rechts t hz₂
          obtain ⟨spur₂, n₂t, hstep₂t, spurEq₂⟩ :=
            geraete_antwort_transport vergleich hkopp hz₁ hz₂ gut₂ h1copy
          have hang := geraete_angebot_gleich vergleich t
          have hkein₂ : (ρ₂.hw.angebot t).crash = false := by
            rw [← hang]
            exact hkein₁
          have st₂ : Lauffolge (d.unit locals) ρ₂.hw t (some s₂) (.antwort a, spur₂) (some n₂t) :=
            .schritt (ImplSchritt.antwort hkein₂ hstep₂t)
          have tick₂ := ρ₂.zeit.takt t
          rw [hz₂] at tick₂
          cases tick₂ with
          | wartet lab₂ _ hkein => exact (hkein (.antwort a, spur₂) _ st₂).elim
          | schritt lab₂ step₂ =>
            cases hn₂ : ρ₂.zeit.zustand (t + 1) with
            | none =>
              rw [hn₂] at step₂
              cases step₂
            | some n₂ =>
              rw [hn₂] at step₂
              cases step₂ with
              | schritt impl₂ =>
                have hinv₂ : GeraeteInvariantAussage d.binding s₂ :=
                  geraete_lauf_invariante vergleich.rechts t hz₂
                obtain ⟨hfragen, hverlauf, hantworten, hverbraucht, hverworfen⟩ :=
                  geraeteKopplung_ledger hkopp hz₁ hz₂
                have hepoche := ((geraeteKopplung_kopplung hkopp).2.1 s₁ s₂ hz₁ hz₂).2.1
                have offered₂ : s₂.AntwortAngeboten (d.unit locals).katalog ρ₂.hw t a :=
                  geraete_angeboten_transport vergleich offered₁ hfragen hverlauf hantworten hepoche
                cases impl₂ with
                | kontext keinAbsturz₂ bereit₂ regel₂ aus₂ =>
                  obtain ⟨binding, access, required, target, ruleEq, hbind⟩ := geraete_rule_binding locals d
                  subst binding
                  obtain ⟨_, plan', hplans', rule₂'⟩ := geraete_kontext_regel ruleEq regel₂
                  rcases geraete_rule_faelle rule₂' with hcase | hcase
                  · obtain ⟨owned, idle, _⟩ := hcase
                    exact (geraete_issue_schliesst_ankunft_aus (d := d) (target := target) hinv₂ owned idle
                      ⟨a, ρ₂.hw, t, offered₂⟩).elim
                  · obtain ⟨owned, pending, answer, ready, _, _⟩ := hcase
                    exact (geraete_consume_schliesst_ankunft_aus (d := d) (target := target) hinv₂ owned pending ready
                      ⟨a, ρ₂.hw, t, offered₂⟩).elim
                | interrupt keinAbsturz₂ enters₂ =>
                  obtain ⟨kk, irq, c₂, nmi, _, pend₂, _, _, _, _, _⟩ := enters₂
                  have gueltig := vergleich.rechts.2.1.2 t
                  have hdel : (ρ₂.hw.angebot t).delivery a.question.endpoint = true := by
                    rw [← offered₁.1]
                    exact offered₂.2.1.1
                  exact (geraete_interrupt_schliesst_antwort_aus gueltig pend₂.2.2.2.2 hdel).elim
                | absturz crash₂ =>
                  exfalso
                  rw [crash₂.1.2] at hkein₂
                  cases hkein₂
                | antwort hkein₂' h2 =>
                  have offered₂' := h2.1
                  have spurEq₂' := h2.2.1
                  have append₂ := h2.2.2.1
                  have stateEq₂ := h2.2.2.2
                  have aeq := geraete_antwort_eindeutig hinv₂ offered₂' offered₂
                  have hbeob₁ := geraete_antwort_beob_tick (predictor := predictor) hlabel hz₁ hn₁ h1typ
                  have hbeob₂ : schrittBeob ρ₂ predictor t = aussenBeob (d.unit locals) (.antwort a) := by
                    rw [← aeq]
                    exact geraete_antwort_beob_tick (predictor := predictor)
                      (by simpa using lab₂) hz₂ hn₂ h2
                  have hlen := kopplung_laenge (geraeteKopplung_kopplung hkopp)
                  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
                  · simp only [NiedrigeBeob, NiedrigeBeob.praefix, hbeob₁, hbeob₂]
                    let L₁ := NiedrigeBeob (d.unit locals) ρ₁ predictor t
                    let L₂ := NiedrigeBeob (d.unit locals) ρ₂ predictor t
                    let A := aussenBeob (d.unit locals) (.antwort a)
                    have hlenP : L₁.length = L₂.length := by
                      simpa only [L₁, L₂, NiedrigeBeob] using hlen
                    have happLen : (L₂ ++ A).length = (L₁ ++ A).length := by
                      simp only [List.length_append, hlenP]
                    have ht : (L₂ ++ A).take ((L₁ ++ A).length) = L₂ ++ A :=
                      List.take_of_length_le (le_of_eq happLen)
                    rw [ht]
                    have reflA : List.Forall₂ (EreignisAequiv (d.unit locals).fluss.freigabe) A A := by
                      induction A with
                      | nil => exact List.Forall₂.nil
                      | cons x xs ih => exact List.Forall₂.cons (EreignisAequiv.gleich _) ih
                    exact List.rel_append (by simpa only [L₁, L₂, NiedrigeBeob] using
                      (geraeteKopplung_kopplung hkopp).1) reflA
                  have hn1lokal : n₁.lokal = s₁.lokal := by rw [stateEq₁]; rfl
                  have hn2lokal : n₂.lokal = s₂.lokal := by rw [stateEq₂]; rfl
                  have hn1status : n₁.status = s₁.status := by rw [stateEq₁]; rfl
                  have hn2status : n₂.status = s₂.status := by rw [stateEq₂]; rfl
                  have hn1initial : n₁.initial = s₁.initial := by rw [stateEq₁]; rfl
                  have hn2initial : n₂.initial = s₂.initial := by rw [stateEq₂]; rfl
                  have hn1rechte : n₁.rechte = s₁.rechte := by rw [stateEq₁]; rfl
                  have hn2rechte : n₂.rechte = s₂.rechte := by rw [stateEq₂]; rfl
                  have hn1leihen : n₁.leihen = s₁.leihen := by rw [stateEq₁]; rfl
                  have hn2leihen : n₂.leihen = s₂.leihen := by rw [stateEq₂]; rfl
                  have hn1fragen : n₁.fragen = s₁.fragen ++ [a] := by
                    rw [stateEq₁]
                    rfl
                  have hn2fragen : n₂.fragen = s₂.fragen ++ [a] := by
                    have h := congrArg Zustand.fragen stateEq₂
                    simpa only [Zustand.fragen, aeq] using h
                  have hn1verlauf : n₁.verlauf = s₁.verlauf ++ [(a.cut, .antwort a.question a.reply)] := by
                    rw [stateEq₁]
                    rfl
                  have hn2verlauf : n₂.verlauf = s₂.verlauf ++ [(a.cut, .antwort a.question a.reply)] := by
                    have h := congrArg Zustand.verlauf stateEq₂
                    simpa only [Zustand.verlauf, aeq] using h
                  have hn1antworten : n₁.antworten = s₁.antworten ++ [a] := by
                    rw [stateEq₁]
                    rfl
                  have hn2antworten : n₂.antworten = s₂.antworten ++ [a] := by
                    have h := congrArg Zustand.antworten stateEq₂
                    simpa only [Zustand.antwort, aeq] using h
                  have hn1verbraucht : n₁.verbraucht = s₁.verbraucht := by rw [stateEq₁]; rfl
                  have hn2verbraucht : n₂.verbraucht = s₂.verbraucht := by rw [stateEq₂]; rfl
                  have hn1verworfen : n₁.verworfen = s₁.verworfen := by rw [stateEq₁]; rfl
                  have hn2verworfen : n₂.verworfen = s₂.verworfen := by rw [stateEq₂]; rfl
                  have hn1buchung : n₁.buchung = s₁.buchung := by rw [stateEq₁]; rfl
                  have hn2buchung : n₂.buchung = s₂.buchung := by rw [stateEq₂]; rfl
                  have hn1naechste : n₁.naechsteAntwort = (s₁.antwort a).naechsteAntwort := by
                    rw [stateEq₁]
                    rfl
                  have hn2naechste : n₂.naechsteAntwort = (s₂.antwort a).naechsteAntwort := by
                    rw [stateEq₂]
                    rw [aeq]
                    rfl
                  have hnaPost : ∀ c, AntwortSicht (d.unit locals) n₁ c = AntwortSicht (d.unit locals) n₂ c := by
                    intro c
                    unfold AntwortSicht
                    rw [hn1naechste, hn2naechste]
                    simp only [Zustand.naechsteAntwort, Zustand.angekommen, Zustand.antwort,
                      hantworten, hverbraucht, hverworfen, aeq]
                  · intro v w hv hw
                    subst v
                    subst w
                    have hstate := (geraeteKopplung_kopplung hkopp).2.1 s₁ s₂ hz₁ hz₂
                    refine ⟨?_, ?_, ?_, ?_, ?_⟩
                    · have hq := hstate.1
                      unfold QuellzustandGleich at hq ⊢
                      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
                      · simpa only [hn1lokal, hn2lokal] using hq.1
                      · intro c
                        simpa only [hn1status, hn2status] using hq.2.1 c
                      · intro x
                        simpa only [hn1initial, hn2initial] using hq.2.2.1 x
                      · simpa only [hn1rechte, hn2rechte] using hq.2.2.2.1
                      · simpa only [hn1leihen, hn2leihen] using hq.2.2.2.2.1
                      · exact hnaPost c
                    · rw [hn1lokal, hn2lokal, hstate.2.2.2.2]
                    · rw [hn1rechte, hn2rechte, hstate.2.2.2.1]
                    · rw [hn1status, hn2status, hstate.2.2.2.2]
                    · rw [hn1status, hn2status, hstate.2.2.2.2]
                  · simp only [NiedrigeBeob, NiedrigeBeob.praefix, hbeob₁, hbeob₂,
                      List.length_append]
                    simp only [NiedrigeBeob] at hlen
                    exact congrArg (fun n => n + (aussenBeob (d.unit locals) (.antwort a)).length) hlen
                  · intro v w hv hw
                    subst v
                    subst w
                    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
                    · rw [hn1fragen, hn2fragen, hfragen]
                    · rw [hn1verlauf, hn2verlauf, hverlauf]
                    · rw [hn1antworten, hn2antworten, hantworten]
                    · rw [hn1verbraucht, hn2verbraucht]
                    · rw [hn1verworfen, hn2verworfen]
                    · rw [hn1buchung, hn2buchung]

end Gabbro.Core.Beobachtung
