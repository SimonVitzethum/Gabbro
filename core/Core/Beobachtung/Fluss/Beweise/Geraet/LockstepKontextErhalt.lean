module

public import Core.Beobachtung.Fluss.Beweise.Geraet.LockstepHilfe
public import Core.Beobachtung.Fluss.Beweise.Geraet.LockstepTransport

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine
open Gabbro.Core.Ast.LowLevel.Device
open Gabbro.Core.Ast.LowLevel (entryContext)
open Gabbro.Core.Ast

variable {k : Katalog} {scope : Scope} {locals : Umgebung scope}
variable {d : Denotation k scope}

private theorem geraete_ereignis_aequiv_refl (A : List (NiedrigesEreignis Nat UInt8 PUnit PUnit)) :
    List.Forall₂ (EreignisAequiv (d.unit locals).fluss.freigabe) A A := by
  induction A with
  | nil => exact List.Forall₂.nil
  | cons x xs ih => exact List.Forall₂.cons (EreignisAequiv.gleich _) ih

/-- One shared low observation extends the prefix cover and the length equality. -/
private theorem geraete_gleich_beob_schritt {ρ₁ ρ₂ : Lauf (d.unit locals)} {predictor : Praediktor}
    {t : Nat} {A : List (NiedrigesEreignis Nat UInt8 PUnit PUnit)}
    (hkopp : GeraeteKopplungAussage (d.unit locals) ρ₁ ρ₂ predictor t t)
    (hb₁ : schrittBeob ρ₁ predictor t = A) (hb₂ : schrittBeob ρ₂ predictor t = A) :
    List.Forall₂ (EreignisAequiv (d.unit locals).fluss.freigabe)
      (NiedrigeBeob (d.unit locals) ρ₁ predictor (t + 1))
      ((NiedrigeBeob (d.unit locals) ρ₂ predictor (t + 1)).take
        (NiedrigeBeob (d.unit locals) ρ₁ predictor (t + 1)).length) ∧
      (NiedrigeBeob (d.unit locals) ρ₁ predictor (t + 1)).length =
        (NiedrigeBeob (d.unit locals) ρ₂ predictor (t + 1)).length := by
  have hlen := kopplung_laenge (geraeteKopplung_kopplung hkopp)
  simp only [NiedrigeBeob, NiedrigeBeob.praefix, hb₁, hb₂]
  let L₁ := NiedrigeBeob.praefix (d.unit locals) ρ₁ predictor t
  let L₂ := NiedrigeBeob.praefix (d.unit locals) ρ₂ predictor t
  have hlenP : L₁.length = L₂.length := by
    simpa only [L₁, L₂, NiedrigeBeob] using hlen
  have htake : (L₂ ++ A).take ((L₁ ++ A).length) = L₂ ++ A := by
    apply List.take_of_length_le
    simpa only [List.length_append, hlenP]
  rw [htake]
  have hcov : List.Forall₂ (EreignisAequiv (d.unit locals).fluss.freigabe) L₁ L₂ := by
    have hc := (geraeteKopplung_kopplung hkopp).1
    simp only [NiedrigeBeob] at hc
    rw [hlenP] at hc
    simpa only [L₁, L₂, List.take_length] using hc
  have reflA : List.Forall₂ (EreignisAequiv (d.unit locals).fluss.freigabe) A A :=
    geraete_ereignis_aequiv_refl A
  refine ⟨?_, ?_⟩
  · exact List.rel_append hcov reflA
  · simp only [List.length_append]
    exact congrArg (fun n => n + A.length) hlen

/-- A left context tick keeps the strengthened coupling. The left label forces an issue or
    consume implementation step; a reserved interrupt and a crash are excluded on both sides by
    the offer equality, and an arrival on the right is excluded by the single-run invariant on
    the right state using the transported authority and ledger shape. The right therefore takes
    the same elaborated rule; the step-level ticks give equal ledgers and machine fields, and
    step-level information flow gives the post `QuellzustandGleich`. Observations are one question
    event for an issue and none for a consume on each side. -/
theorem geraete_kontext_erhalt (locals : Umgebung scope) (d : Denotation k scope) :
    GeraeteKontextErhaltAussage (d := d) (locals := locals) := by
  intro h₁ h₂ ρ₁ ρ₂ vergleich predictor t c w spur hkopp hlabel
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
          rw [← Option.some.inj lab] at impl
          cases impl with
          | kontext keinAbsturz₁ bereit₁ regel₁ aus₁ =>
            obtain ⟨v₁, s₂, hv₁, hz₂⟩ := (geraete_zustand_gemeinsam vergleich t).resolve_left
              (by intro h; rw [hz₁] at h; cases h.1)
            have hvEq : v₁ = s₁ := Option.some.inj (hv₁.symm.trans hz₁)
            subst v₁
            obtain ⟨binding, access, required, target, ruleEq, hbind⟩ := geraete_rule_binding locals d
            subst binding
            obtain ⟨kopf₁, plan', hplans', rule₁'⟩ := geraete_kontext_regel ruleEq regel₁
            obtain ⟨quell, hepoche, hgeliefert, hkerne, hstatus⟩ :=
              (geraeteKopplung_kopplung hkopp).2.1 s₁ s₂ hz₁ hz₂
            obtain ⟨hfragen, hverlauf, hantworten, hverbraucht, hverworfen⟩ :=
              geraeteKopplung_ledger hkopp hz₁ hz₂
            have hbuch := geraeteKopplung_buchung hkopp hz₁ hz₂
            have hinv₁ : GeraeteInvariantAussage d.binding s₁ :=
              geraete_lauf_invariante vergleich.links t hz₁
            have hinv₂ : GeraeteInvariantAussage d.binding s₂ :=
              geraete_lauf_invariante vergleich.rechts t hz₂
            have keinInterrupt₁ : (ρ₁.hw.angebot t).interruptAuswahl = none := by
              cases hI : (ρ₁.hw.angebot t).interruptAuswahl with
              | none => rfl
              | some auswahl =>
                obtain ⟨kern, id, irq⟩ := auswahl
                exact (geraete_interrupt_schliesst_kontext_aus
                  (vergleich.links.2.1.2 t) hI bereit₁).elim
            have keinAbsturz₂ : (ρ₂.hw.angebot t).crash = false := by
              rw [← geraete_angebot_gleich vergleich t]
              exact keinAbsturz₁
            have auswahlGleich : (ρ₁.hw.angebot t).interruptAuswahl =
                (ρ₂.hw.angebot t).interruptAuswahl := by
              rw [geraete_angebot_gleich vergleich t]
            have bereit₂ : KannSchreiten ρ₂.hw t c s₂ := by
              obtain ⟨kern, geleg₁, lauf₁, statusL₁⟩ := bereit₁
              refine ⟨kern, ?_, ?_, ?_⟩
              · dsimp only [HwLauf.gelegenheit]
                rw [← congrArg (fun a => a.core) (geraete_angebot_gleich vergleich t)]
                exact geleg₁
              · rw [← hkerne]
                exact lauf₁
              · rw [← hstatus]
                exact statusL₁
            cases rule₁' with
            | issue owned₁ idle₁ =>
              have owned₂ : Befugt d.binding required access s₂ c :=
                geraete_befugt_transport owned₁ hbuch (geraete_lokal_gleich quell)
              have idle₂ : (s₂.lokal c).pending = none := by
                rw [← geraete_kopplung_pending hkopp hz₁ hz₂ c]
                exact idle₁
              have keineAntwort₂ : ¬ ∃ a hw t', s₂.AntwortAngeboten (d.unit locals).katalog hw t' a :=
                geraete_issue_schliesst_ankunft_aus (target := target) hinv₂ owned₂ idle₂
              have gut₂ : s₂.SpeicherGut := geraete_lauf_speicher_gut vergleich.rechts t hz₂
              obtain ⟨spur₂, u₂t, n₂t, regel₂t, aus₂t, _, _, _, _, _, _, _⟩ :=
                geraete_issue_transport vergleich hkopp hz₁ hz₂ gut₂ quell regel₁ ruleEq aus₁
                  hplans' rfl owned₁ idle₁
              have tick₂ := ρ₂.zeit.takt t
              rw [hz₂] at tick₂
              cases tick₂ with
              | wartet lab₂ _ hkein₂ =>
                exfalso
                have st₂ : Lauffolge (d.unit locals) ρ₂.hw t (some s₂) (.kontext c w, spur₂) (some n₂t) :=
                  .schritt (ImplSchritt.kontext keinAbsturz₂ bereit₂ regel₂t aus₂t)
                exact (hkein₂ (.kontext c w, spur₂) _ st₂).elim
              | schritt lab₂ step₂ =>
                cases hn₂ : ρ₂.zeit.zustand (t + 1) with
                | none => rw [hn₂] at step₂; cases step₂
                | some n₂ =>
                  rw [hn₂] at step₂
                  cases step₂ with
                  | schritt impl₂ =>
                    cases impl₂ with
                    | kontext _ bereit₂a regel₂a aus₂a =>
                      obtain ⟨kopf₂, plan'A, hplansA', rule'A⟩ := geraete_kontext_regel ruleEq regel₂a
                      obtain ⟨kern₁, geleg₁, lauf₁, _⟩ := bereit₁
                      obtain ⟨kernA, gelegA, laufA, _⟩ := bereit₂a
                      have gelegEq : kernA = kern₁ := by
                        dsimp only [HwLauf.gelegenheit] at geleg₁ gelegA
                        exact Option.some.inj (gelegA.symm.trans geleg₁)
                      subst kernA
                      have laufA' : (s₁.kerne kern₁).laeuft = some _ := by
                        rw [hkerne]
                        exact laufA
                      cases (laufA'.symm.trans lauf₁)
                      cases rule'A with
                      | issue owned₂A idle₂A =>
                        have impl₁Ideal : ((d.unit locals).system.regel ()).ideal c s₁ () _ u₁ := by
                          dsimp only [Denotation.unit, Gabbro.Core.Ast.LowLevel.Device.unit]
                          rw [ruleEq]
                          dsimp only [Rule.machine]
                          exact ⟨plan', hplans', Rule.issue owned₁ idle₁⟩
                        have impl₂Ideal : ((d.unit locals).system.regel ()).ideal c s₂ () _ u₂t := by
                          dsimp only [Denotation.unit, Gabbro.Core.Ast.LowLevel.Device.unit]
                          rw [ruleEq]
                          dsimp only [Rule.machine]
                          exact ⟨plan'A, hplansA', Rule.issue owned₂A idle₂A⟩
                        obtain ⟨_, hfragen₁, hverlauf₁, hantworten₁, hverbraucht₁, hverworfen₁,
                          hbuchung₁, hepoche₁, hgeliefert₁, hkerne₁, hstatus₁, hlokal₁, _, hinitial₁,
                          hrechte₁, hleihen₁, _, _, _, _, _⟩ :=
                          geraete_issue_tick (target := target) aus₁ hplans' rfl owned₁ idle₁
                        obtain ⟨_, hfragen₂, hverlauf₂, hantworten₂, hverbraucht₂, hverworfen₂,
                          hbuchung₂, hepoche₂, hgeliefert₂, hkerne₂, hstatus₂, hlokal₂, _, hinitial₂,
                          hrechte₂, hleihen₂, _, _, _, _, _⟩ :=
                          geraete_issue_tick (target := target) aus₂a hplansA' rfl owned₂A idle₂A
                        have hbeob₁ : schrittBeob ρ₁ predictor t =
                            [.frage c.nummer s₁.fragen.length (d.binding.question access)] :=
                          geraete_issue_beob_tick (predictor := predictor) hlabel hz₁ hn₁ aus₁
                            hplans' rfl kopf₁ hbuchung₁.symm hstatus₁
                        have hbeob₂ : schrittBeob ρ₂ predictor t =
                            [.frage c.nummer s₁.fragen.length (d.binding.question access)] := by
                          have h := geraete_issue_beob_tick (predictor := predictor)
                            (by simpa using lab₂) hz₂ hn₂ aus₂a hplansA' rfl kopf₂
                            hbuchung₂.symm hstatus₂
                          simpa only [hfragen] using h
                        have hquell : QuellzustandGleich (d.unit locals) n₁ n₂ := by
                          have hq := (geraeteSchrittNI locals d c s₁ s₂ () _ _ u₁ u₂t quell
                            ⟨kopf₁, impl₁Ideal⟩ ⟨kopf₂, impl₂Ideal⟩).1
                          have n1lokal : n₁.lokal = u₁.lokal := by rw [hlokal₁]; rfl
                          have n2lokal : n₂.lokal = u₂t.lokal := by rw [hlokal₂]; rfl
                          have n1status : n₁.status = u₁.status := by rw [hstatus₁]; rfl
                          have n2status : n₂.status = u₂t.status := by rw [hstatus₂]; rfl
                          have n1initial : n₁.initial = u₁.initial := by rw [hinitial₁]; rfl
                          have n2initial : n₂.initial = u₂t.initial := by rw [hinitial₂]; rfl
                          have n1rechte : n₁.rechte = u₁.rechte := by rw [hrechte₁]; rfl
                          have n2rechte : n₂.rechte = u₂t.rechte := by rw [hrechte₂]; rfl
                          have n1leihen : n₁.leihen = u₁.leihen := by rw [hleihen₁]; rfl
                          have n2leihen : n₂.leihen = u₂t.leihen := by rw [hleihen₂]; rfl
                          have n1antwort : n₁.naechsteAntwort = u₁.naechsteAntwort := by
                            funext c'
                            simp only [Zustand.naechsteAntwort, Zustand.angekommen, hantworten₁,
                              hverbraucht₁, hverworfen₁, Zustand.frage, setFrame]
                          have n2antwort : n₂.naechsteAntwort = u₂t.naechsteAntwort := by
                            funext c'
                            simp only [Zustand.naechsteAntwort, Zustand.angekommen, hantworten₂,
                              hverbraucht₂, hverworfen₂, Zustand.frage, setFrame]
                          unfold QuellzustandGleich at hq ⊢
                          unfold AntwortSicht at hq ⊢
                          simpa only [n1lokal, n2lokal, n1status, n2status, n1initial, n2initial,
                            n1rechte, n2rechte, n1leihen, n2leihen, n1antwort, n2antwort] using hq
                        have hbeob := geraete_gleich_beob_schritt hkopp hbeob₁ hbeob₂
                        refine ⟨⟨hbeob.1, ?_, hbeob.2⟩, ?_⟩
                        · intro v w hv hw
                          obtain rfl : v = n₁ := Option.some.inj (hv.symm.trans hn₁)
                          obtain rfl : w = n₂ := Option.some.inj (hw.symm.trans hn₂)
                          refine ⟨hquell, ?_, ?_, ?_, ?_⟩
                          · rw [hepoche₁, hepoche₂, hepoche]
                          · rw [hgeliefert₁, hgeliefert₂, hgeliefert]
                          · rw [hkerne₁, hkerne₂, hkerne]
                          · rw [hstatus₁, hstatus₂, hstatus]
                        · intro v w hv hw
                          obtain rfl : v = n₁ := Option.some.inj (hv.symm.trans hn₁)
                          obtain rfl : w = n₂ := Option.some.inj (hw.symm.trans hn₂)
                          refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
                          · rw [hfragen₁, hfragen₂, hfragen]
                          · rw [hverlauf₁, hverlauf₂, hverlauf]
                          · rw [hantworten₁, hantworten₂, hantworten]
                          · rw [hverbraucht₁, hverbraucht₂, hverbraucht]
                          · rw [hverworfen₁, hverworfen₂, hverworfen]
                          · rw [hbuchung₁, hbuchung₂, hbuch]
                      | @consume owned₂A answer₂A pending₂A ready₂A sameQuestion₂A =>
                        exfalso
                        rw [idle₂] at pending₂A
                        cases pending₂A
                    | antwort _ h =>
                      obtain ⟨offered₂', _, _, _⟩ := h
                      exact (keineAntwort₂ ⟨_, ρ₂.hw, t, offered₂'⟩).elim
                    | interrupt _ h =>
                      obtain ⟨k, irq, _, _, _, pending, _, _, _, _, _⟩ := h
                      have auswahl₂ := pending.2.2.2.2
                      rw [← auswahlGleich] at auswahl₂
                      rw [keinInterrupt₁] at auswahl₂
                      cases auswahl₂
                    | absturz h =>
                      exact (Bool.false_ne_true (keinAbsturz₂.symm.trans h.1.2)).elim
            | @consume owned₁ answer₁ pending₁ ready₁ sameQuestion₁ =>
              have owned₂ : Befugt d.binding required access s₂ c :=
                geraete_befugt_transport owned₁ hbuch (geraete_lokal_gleich quell)
              have pending₂ : (s₂.lokal c).pending = some (d.binding.question access) := by
                rw [← geraete_kopplung_pending hkopp hz₁ hz₂ c]
                exact pending₁
              have ready₂ : s₂.naechsteAntwort c = some answer₁ := by
                rw [← geraete_antwort_gleich quell]
                exact ready₁
              have keineAntwort₂ : ¬ ∃ a hw t', s₂.AntwortAngeboten (d.unit locals).katalog hw t' a :=
                geraete_consume_schliesst_ankunft_aus (target := target) hinv₂ owned₂ pending₂ ready₂
              obtain ⟨spur₂, u₂t, n₂t, regel₂t, aus₂t⟩ :=
                geraete_consume_transport vergleich hkopp hz₁ hz₂ quell regel₁ ruleEq aus₁
                  hplans' rfl owned₁ pending₁ ready₁ sameQuestion₁
              have tick₂ := ρ₂.zeit.takt t
              rw [hz₂] at tick₂
              cases tick₂ with
              | wartet lab₂ _ hkein₂ =>
                exfalso
                have st₂ : Lauffolge (d.unit locals) ρ₂.hw t (some s₂) (.kontext c w, spur₂) (some n₂t) :=
                  .schritt (ImplSchritt.kontext keinAbsturz₂ bereit₂ regel₂t aus₂t)
                exact (hkein₂ (.kontext c w, spur₂) _ st₂).elim
              | schritt lab₂ step₂ =>
                cases hn₂ : ρ₂.zeit.zustand (t + 1) with
                | none => rw [hn₂] at step₂; cases step₂
                | some n₂ =>
                  rw [hn₂] at step₂
                  cases step₂ with
                  | schritt impl₂ =>
                    cases impl₂ with
                    | kontext _ bereit₂a regel₂a aus₂a =>
                      obtain ⟨kopf₂, plan'A, hplansA', rule'A⟩ := geraete_kontext_regel ruleEq regel₂a
                      obtain ⟨kern₁, geleg₁, lauf₁, _⟩ := bereit₁
                      obtain ⟨kernA, gelegA, laufA, _⟩ := bereit₂a
                      have gelegEq : kernA = kern₁ := by
                        dsimp only [HwLauf.gelegenheit] at geleg₁ gelegA
                        exact Option.some.inj (gelegA.symm.trans geleg₁)
                      subst kernA
                      have laufA' : (s₁.kerne kern₁).laeuft = some _ := by
                        rw [hkerne]
                        exact laufA
                      cases (laufA'.symm.trans lauf₁)
                      cases rule'A with
                      | @consume owned₂A answer₂A pending₂A ready₂A sameQuestion₂A =>
                        have impl₁Ideal : ((d.unit locals).system.regel ()).ideal c s₁ () _ u₁ := by
                          dsimp only [Denotation.unit, Gabbro.Core.Ast.LowLevel.Device.unit]
                          rw [ruleEq]
                          dsimp only [Rule.machine]
                          exact ⟨plan', hplans', Rule.consume owned₁ pending₁ ready₁ sameQuestion₁⟩
                        have impl₂Ideal : ((d.unit locals).system.regel ()).ideal c s₂ () _ u₂t := by
                          dsimp only [Denotation.unit, Gabbro.Core.Ast.LowLevel.Device.unit]
                          rw [ruleEq]
                          dsimp only [Rule.machine]
                          exact ⟨plan'A, hplansA',
                            Rule.consume owned₂A pending₂A ready₂A sameQuestion₂A⟩
                        obtain ⟨_, hfragen₁, hverlauf₁, hantworten₁, hverbraucht₁, hverworfen₁,
                          hbuchung₁, hepoche₁, hgeliefert₁, hkerne₁, hstatus₁, hlokal₁, _, hinitial₁,
                          hrechte₁, hleihen₁, _⟩ :=
                          geraete_consume_tick (target := target) aus₁ hplans' rfl owned₁
                            pending₁ ready₁ sameQuestion₁
                        obtain ⟨_, hfragen₂, hverlauf₂, hantworten₂, hverbraucht₂, hverworfen₂,
                          hbuchung₂, hepoche₂, hgeliefert₂, hkerne₂, hstatus₂, hlokal₂, _, hinitial₂,
                          hrechte₂, hleihen₂, _⟩ :=
                          geraete_consume_tick (target := target) aus₂a hplansA' rfl owned₂A
                            pending₂A ready₂A sameQuestion₂A
                        have hbeob₁ : schrittBeob ρ₁ predictor t = [] :=
                          geraete_consume_beob_tick (predictor := predictor) hlabel hz₁ hn₁ aus₁
                            hplans' rfl kopf₁ hbuchung₁.symm hstatus₁
                        have hbeob₂ : schrittBeob ρ₂ predictor t = [] :=
                          geraete_consume_beob_tick (predictor := predictor)
                            (by simpa using lab₂) hz₂ hn₂ aus₂a hplansA' rfl kopf₂
                            hbuchung₂.symm hstatus₂
                        have hquell : QuellzustandGleich (d.unit locals) n₁ n₂ := by
                          have hq := (geraeteSchrittNI locals d c s₁ s₂ () _ _ u₁ u₂t quell
                            ⟨kopf₁, impl₁Ideal⟩ ⟨kopf₂, impl₂Ideal⟩).1
                          refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
                          · simpa only [hlokal₁, hlokal₂] using hq.1
                          · simpa only [hstatus₁, hstatus₂] using hq.2.1
                          · simpa only [hinitial₁, hinitial₂] using hq.2.2.1
                          · simpa only [hrechte₁, hrechte₂] using hq.2.2.2.1
                          · simpa only [hleihen₁, hleihen₂] using hq.2.2.2.2.1
                          · intro c'
                            unfold AntwortSicht
                            simp only [Zustand.naechsteAntwort, Zustand.angekommen, hantworten₁,
                              hantworten₂, hverbraucht₁, hverbraucht₂, hverworfen₁, hverworfen₂,
                              hantworten, hverbraucht, hverworfen, Function.update_self]
                        have hbeob := geraete_gleich_beob_schritt hkopp hbeob₁ hbeob₂
                        refine ⟨⟨hbeob.1, ?_, hbeob.2⟩, ?_⟩
                        · intro v w hv hw
                          obtain rfl : v = n₁ := Option.some.inj (hv.symm.trans hn₁)
                          obtain rfl : w = n₂ := Option.some.inj (hw.symm.trans hn₂)
                          refine ⟨hquell, ?_, ?_, ?_, ?_⟩
                          · rw [hepoche₁, hepoche₂, hepoche]
                          · rw [hgeliefert₁, hgeliefert₂, hgeliefert]
                          · rw [hkerne₁, hkerne₂, hkerne]
                          · rw [hstatus₁, hstatus₂, hstatus]
                        · intro v w hv hw
                          obtain rfl : v = n₁ := Option.some.inj (hv.symm.trans hn₁)
                          obtain rfl : w = n₂ := Option.some.inj (hw.symm.trans hn₂)
                          refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
                          · rw [hfragen₁, hfragen₂, hfragen]
                          · rw [hverlauf₁, hverlauf₂, hverlauf]
                          · rw [hantworten₁, hantworten₂, hantworten]
                          · rw [hverbraucht₁, hverbraucht₂, hverbraucht]
                          · rw [hverworfen₁, hverworfen₂, hverworfen]
                          · rw [hbuchung₁, hbuchung₂, hbuch]
                      | issue _ _ =>
                        exfalso
                        rw [pending₂] at idle₂A
                        cases idle₂A
                    | antwort _ h =>
                      obtain ⟨offered₂', _, _, _⟩ := h
                      exact (keineAntwort₂ ⟨_, ρ₂.hw, t, offered₂'⟩).elim
                    | interrupt _ h =>
                      obtain ⟨k, irq, _, _, _, pending, _, _, _, _, _⟩ := h
                      have auswahl₂ := pending.2.2.2.2
                      rw [← auswahlGleich] at auswahl₂
                      rw [keinInterrupt₁] at auswahl₂
                      cases auswahl₂
                    | absturz h =>
                      exact (Bool.false_ne_true (keinAbsturz₂.symm.trans h.1.2)).elim

end Gabbro.Core.Beobachtung
