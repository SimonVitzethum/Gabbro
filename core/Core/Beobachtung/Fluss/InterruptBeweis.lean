module

public import Core.Beobachtung.Fluss.Interrupt
public import Core.Verfeinerung.Sicherheit

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine
open Ast.Semantik (Fragment)

/-- An interrupt tick preserves the coupling: the public attempt is the same on both sides, so the
    right run takes the same delivery at the same cut; the handler entry is computed from the
    coupled machine fields, and both low observations consist of the same catalogue event. -/
theorem interruptNI : InterruptNIAussage := by
  intro p plattform
  dsimp only
  let E := p.einheit plattform
  intro h₁ h₂ ρ₁ ρ₂ vergleich predictor t w spur tick wahl kopplung
  cases w with
  | kontext _ _ => cases wahl
  | antwort _ => cases wahl
  | absturz => cases wahl
  | interrupt id =>
    classical
    have bereit₁ := interrupt_bereit_aus_tick (E := E) (ρ := ρ₁) (t := t) (id := id) (spur := spur) tick
    obtain ⟨v₁, next₁, zustand₁, zustandNach₁, unter₁⟩ := bereit₁
    have takt₁ := ρ₁.zeit.takt t
    rw [tick, zustand₁] at takt₁
    generalize hn₁ : ρ₁.zeit.zustand (t + 1) = na₁ at takt₁
    have keinAbsturz₁ : (ρ₁.hw.angebot t).crash = false := by
      cases takt₁ with
      | wartet label _ _ => cases label
      | schritt label step₁ =>
        rename_i ev₁
        have evEq : (SchrittWahl.interrupt id, spur) = ev₁ := Option.some.inj label
        rw [← evEq] at step₁
        cases step₁ with
        | schritt impl =>
          cases impl with
          | interrupt h _ => exact h
    obtain ⟨v₂, zustand₂⟩ := fragment_zustand_some vergleich.rechts t
    obtain ⟨cov, st, len⟩ := kopplung
    obtain ⟨⟨lokGleich, endeGleich, initialGleich, rechteGleich, leihenGleich, antwortGleich⟩,
      epocheEq, geliefertEq, kerneEq, statusEq⟩ := st v₁ v₂ zustand₁ zustand₂
    have unter₁Original := unter₁
    obtain ⟨k, irq, c, nmi, offer₁, pending₁, enter₁, ruht₁, aussen₁, append₁, nextEq₁⟩ := unter₁
    have auswahlEq : (ρ₁.hw.angebot t).interruptAuswahl = (ρ₂.hw.angebot t).interruptAuswahl :=
      gleiche_interruptwahl (E := E) vergleich.politik t
    have auswahl₂ : (ρ₂.hw.angebot t).interruptAuswahl = some (k, id, irq) := by
      rw [← auswahlEq]
      exact pending₁.2.2.2.2
    obtain ⟨_, keinKern₂, keineAntwort₂⟩ := (vergleich.rechts.2.1.2 t).interrupt_reserviert auswahl₂
    have crashEq : (ρ₁.hw.angebot t).crash = (ρ₂.hw.angebot t).crash :=
      congrArg (fun proj => (proj.1 t).2.2.2.2.2.1) vergleich.politik
    have crash₂ : (ρ₂.hw.angebot t).crash = false := by
      rw [← crashEq]
      exact keinAbsturz₁
    have interruptEq : (ρ₁.hw.angebot t).interrupt k = (ρ₂.hw.angebot t).interrupt k :=
      congrArg (fun proj => (proj.1 t).2.1 k) vergleich.politik
    have offer₂ : (ρ₂.hw.angebot t).interrupt k = true := by
      rw [← interruptEq]
      exact offer₁
    have signalsEq : (ρ₁.hw.angebot id.1).interrupts = (ρ₂.hw.angebot id.1).interrupts :=
      congrArg (fun proj => (proj.1 id.1).2.2.1) vergleich.politik
    have pending₂ : UnterbrechungAusstehend v₂ ρ₂.hw t k id irq := by
      refine ⟨?_, pending₁.2.1, ?_, ?_, auswahl₂⟩
      · rw [← epocheEq]
        exact pending₁.1
      · rw [← signalsEq]
        exact pending₁.2.2.1
      · rw [← geliefertEq]
        exact pending₁.2.2.2.1
    have enter₂ : NimmtUnterbrechung (v₂.kerne k) k (Nat.pair id.1 id.2) irq c nmi := by
      rw [← kerneEq]
      exact enter₁
    have ruht₂ : v₂.status c = .ruht := by
      rw [← statusEq]
      exact ruht₁
    have init₂ : ∃ z, ρ₂.zeit.zustand 0 = some z ∧ I.ProtokollBezug z (I.start E ρ₂.start).2 := by
      refine ⟨(I.start E ρ₂.start).2, ?_, I.ProtokollBezug.refl _⟩
      rw [vergleich.rechts.2.2.2]
      exact fragment_geladen p plattform vergleich.rechts.1 vergleich.rechts.2.2.1
    obtain ⟨wGut, atW, gutW, _⟩ := speicher_verbrauch_im_lauf (E := E) init₂ t
    have wGl : wGut = v₂ := Option.some.inj (atW.symm.trans zustand₂)
    subst wGut
    let label := aussenEtikett E.einrichtung (Ereignis.interrupt k irq Eintritt.handler)
    have initialisierung : Initialisierung v₂.initial label v₂.graph [] v₂.graph :=
      .ohne (Or.inl (by rfl))
    obtain ⟨g₁, hs⟩ := Speicher.Zustand.schritt_ohne_lesen gutW.1 gutW.2 .aussen label
      (by simp only [label, aussenEtikett, Speicher.Art.liest, not_false_eq_true])
    let spur₂ : SchrittSpur PUnit Int :=
      { speicher := [(.aussen, label)]
        aussen := [Ereignis.interrupt k irq Eintritt.handler] }
    let next₂ := { Zustandseintritt v₂ k id c nmi with graph := g₁ }
    have folge₂ : Speicherfolge v₂.initial .aussen v₂.graph [label] spur₂.speicher next₂.graph := by
      dsimp only [spur₂, next₂]
      exact Speicherfolge.cons initialisierung hs (Speicherfolge.nil _)
    have unter₂ : UnterbrechungsSchritt E.einrichtung ρ₂.hw t id v₂ spur₂ next₂ := by
      refine ⟨k, irq, c, nmi, offer₂, pending₂, enter₂, ruht₂, ?_, folge₂, ?_⟩
      · rfl
      · rfl
    have takt₂ := ρ₂.zeit.takt t
    rw [zustand₂] at takt₂
    generalize hn₂ : ρ₂.zeit.zustand (t + 1) = na₂ at takt₂
    cases takt₂ with
    | wartet label₂ same hp =>
      exact (hp _ _ (Lauffolge.schritt (.interrupt crash₂ unter₂))).elim
    | schritt label₂ step₂ =>
      rename_i ev₂
      cases step₂ with
      | schritt impl₂ =>
        cases impl₂ with
        | kontext _ bereit₂ _ _ =>
          obtain ⟨k', geleg₂, _, _⟩ := bereit₂
          change (ρ₂.hw.angebot t).core = some k' at geleg₂
          rw [keinKern₂] at geleg₂
          cases geleg₂
        | antwort _ hAnt =>
          have delivery := hAnt.1.2.1.1
          rw [hAnt.1.1, keineAntwort₂] at delivery
          cases delivery
        | absturz hCrash =>
          obtain ⟨offerCrash, _, _⟩ := hCrash
          exact (Bool.false_ne_true (crash₂.symm.trans offerCrash.2)).elim
        | interrupt _ h₂' =>
          obtain ⟨idEq, aussenEq⟩ :=
            interruptspur_gleich (e := E.einrichtung) auswahlEq unter₁Original h₂'
          cases idEq
          obtain ⟨kR, irqR, cR, nmiR, offerR, pendingR, enterR, ruhtR, aussenR, appendR, nextEqR⟩ := h₂'
          have krEq : k = kR ∧ irq = irqR := by
            have headEq : Ereignis.interrupt k irq Eintritt.handler =
                Ereignis.interrupt kR irqR Eintritt.handler :=
              (List.cons.inj (aussen₁.symm.trans (aussenEq.trans aussenR))).1
            injection headEq with hk hirq
            exact ⟨hk, hirq⟩
          obtain ⟨hkEq, hirqEq⟩ := krEq
          cases hkEq
          cases hirqEq
          have cnEq : c = cR ∧ nmi = nmiR := by
            have enterR' : NimmtUnterbrechung (v₁.kerne k) k (Nat.pair id.1 id.2) irq cR nmiR := by
              rw [kerneEq]
              exact enterR
            cases enter₁ <;> cases enterR' <;> exact ⟨rfl, rfl⟩
          obtain ⟨hcEq, hnEq⟩ := cnEq
          cases hcEq
          cases hnEq
          have interruptBeob :
              ∀ (ρ : Lauf E) (spurρ : SchrittSpur PUnit Int) (vρ nρ : Ast.Semantik.Zustand),
                ρ.zeit.spur t = some (SchrittWahl.interrupt id, spurρ) →
                ρ.zeit.zustand t = some vρ →
                ρ.zeit.zustand (t + 1) = some nρ →
                spurρ.aussen = [Ereignis.interrupt k irq Eintritt.handler] →
                Speicherfolge vρ.initial .aussen vρ.graph [label] spurρ.speicher nρ.graph →
                vρ.status c = .ruht →
                nρ = { Zustandseintritt vρ k id c nmi with graph := nρ.graph } →
                schrittBeob ρ predictor t = [.katalog (.interrupt k irq .handler)] := by
            intro ρ spurρ vρ nρ tickρ atV atN aussenρ appendρ ruhtρ nextρ
            have speicherLeer : spurρ.speicher.filterMap (speicherBeob E.etiketten) = [] := by
              have sp : spurρ.speicher = [(.aussen, label)] := by
                cases appendρ with
                | cons vor hsAppend nach =>
                  cases vor with
                  | ohne _ =>
                    cases nach
                    rfl
                  | erste mem _ _ =>
                    exact (mem rfl).elim
              rw [sp]
              rfl
            have keinEnde : ¬ ∃ d, (neuBeendet vρ nρ E.etiketten d).isSome = true := by
              rintro ⟨d, hd⟩
              have eqNone : neuBeendet vρ nρ E.etiketten d = none := by
                rw [neuBeendet]
                by_cases hdc : d = c
                · subst d
                  have statusN : nρ.status c = .laeuft := by
                    rw [nextρ]
                    rfl
                  rw [statusN, ruhtρ]
                  rfl
                · have statusN : nρ.status d = vρ.status d := by
                    rw [nextρ]
                    simp only [Function.update, hdc, Ne.symm hdc, ↓reduceIte]
                  rw [statusN]
                  cases hst : vρ.status d <;> rfl
              rw [eqNone] at hd
              cases hd
            rw [schrittBeob, tickρ, atV, atN]
            simp only [speicherLeer, aussenρ, List.flatMap_cons, aussenBeob, List.flatMap_nil,
              List.nil_append, List.append_nil, keinEnde, if_false]
          have beobEq : schrittBeob ρ₁ predictor t = schrittBeob ρ₂ predictor t := by
            exact (interruptBeob ρ₁ spur v₁ next₁ tick zustand₁ zustandNach₁ aussen₁ append₁ ruht₁ nextEq₁).trans
              (interruptBeob ρ₂ _ v₂ _ label₂ zustand₂ hn₂ aussenR appendR ruhtR nextEqR).symm
          have e₁ : NiedrigeBeob E ρ₁ predictor (t + 1) =
              NiedrigeBeob E ρ₁ predictor t ++ schrittBeob ρ₁ predictor t := by
            change NiedrigeBeob E ρ₁ predictor t ++ schrittBeob ρ₁ predictor t = _
            rfl
          have e₂ : NiedrigeBeob E ρ₂ predictor (t + 1) =
              NiedrigeBeob E ρ₂ predictor t ++ schrittBeob ρ₂ predictor t := by
            change NiedrigeBeob E ρ₂ predictor t ++ schrittBeob ρ₂ predictor t = _
            rfl
          let L₁ := NiedrigeBeob E ρ₁ predictor t
          let L₂ := NiedrigeBeob E ρ₂ predictor t
          let sObs := schrittBeob ρ₂ predictor t
          have len' : L₁.length = L₂.length := by
            dsimp only [L₁, L₂]
            exact len
          have cov' : List.Forall₂ (EreignisAequiv E.fluss.freigabe) L₁ L₂ := by
            have takeEq : L₂.take L₁.length = L₂ := by
              rw [len', List.take_length]
            dsimp only [L₁, L₂] at takeEq ⊢
            rw [takeEq] at cov
            exact cov
          have reflS : List.Forall₂ (EreignisAequiv E.fluss.freigabe) sObs sObs := by
            induction sObs with
            | nil => exact .nil
            | cons e es ih => exact .cons (.gleich e) ih
          have appendForall : ∀ {a b s : List (NiedrigesEreignis PUnit Int PUnit Ast.Semantik.Befehl)},
              List.Forall₂ (EreignisAequiv E.fluss.freigabe) a b →
              List.Forall₂ (EreignisAequiv E.fluss.freigabe) s s →
              List.Forall₂ (EreignisAequiv E.fluss.freigabe) (a ++ s) (b ++ s) := by
            intro a b s hab hs
            induction hab with
            | nil => exact hs
            | cons hTail ih => exact .cons hTail ih
          refine ⟨?_, ?_, ?_⟩
          · rw [e₁, e₂, beobEq]
            have lenApp : (L₁ ++ sObs).length = (L₂ ++ sObs).length := by
              rw [List.length_append, List.length_append, len']
            rw [lenApp, List.take_length]
            exact appendForall cov' reflS
          · intro v' w' hv' hw'
            rw [zustandNach₁] at hv'
            rw [hn₂] at hw'
            obtain rfl := Option.some.inj hv'
            obtain rfl := Option.some.inj hw'
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
              simp only [Zustandseintritt, kerneEq]
            · rw [nextEq₁, nextEqR]
              simp only [Zustandseintritt, statusEq]
          · rw [e₁, e₂, beobEq, List.length_append, List.length_append, len']

end Gabbro.Core.Beobachtung
