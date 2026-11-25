module

public import Core.Beobachtung.Fluss.Beweise.Geraet.LockstepHilfe

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine
open Gabbro.Core.Ast.LowLevel.Device
open Gabbro.Core.Ast.LowLevel (entryContext)
open Gabbro.Core.Ast

variable {k : Katalog} {scope : Scope} {locals : Umgebung scope}
variable {d : Denotation k scope}

/-- The crash of a device step appends exactly the persistence event: the memory part is empty
    and recovery enters a running context, never an ended one. -/
private theorem geraete_absturz_beob_tick {ρ : Lauf (d.unit locals)} {predictor : Praediktor}
    {t : Nat} {s n : State}
    (hlabel : ρ.zeit.spur t = some (.absturz, absturzSpur))
    (atS : ρ.zeit.zustand t = some s) (atN : ρ.zeit.zustand (t + 1) = some n)
    (hneu : ∀ c, ¬ ∃ e, n.status c = .beendet e) :
    schrittBeob ρ predictor t = [.katalog (.persistenz .crash)] := by
  have habschluss : ¬ ∃ c, (neuBeendet s n (d.unit locals).etiketten c).isSome = true := by
    rintro ⟨c, hc⟩
    have hnone : neuBeendet s n (d.unit locals).etiketten c = none := by
      cases hs : s.status c with
      | beendet _ =>
        cases hn : n.status c with
        | beendet e => exact (hneu c ⟨e, hn⟩).elim
        | ruht | laeuft => simp only [neuBeendet, hs, hn]
      | ruht | laeuft =>
        cases hn : n.status c with
        | beendet e => exact (hneu c ⟨e, hn⟩).elim
        | ruht | laeuft => simp only [neuBeendet, hs, hn]
    rw [hnone] at hc
    cases hc
  rw [schrittBeob, hlabel, atS, atN]
  simp only [absturzSpur, List.filterMap_nil, List.flatMap_nil, aussenBeob,
    List.flatMap_cons, List.append_nil, List.nil_append, habschluss, if_false]

/-- A left crash keeps the strengthened coupling: the crash offer is the same on both runs, so
    both reset through the device unit's fixed recovery; every carried ledger is equal and the
    new epoch, booking and machine fields agree. -/
theorem geraete_absturz_erhalt (locals : Umgebung scope) (d : Denotation k scope) :
    GeraeteAbsturzErhaltAussage (d := d) (locals := locals) := by
  intro h₁ h₂ ρ₁ ρ₂ vergleich predictor t spur hkopp hlabel
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
          cases impl with
          | absturz crash₁ =>
            rename_i spur₁
            obtain ⟨spurEq₁, n₁Eq⟩ := AbsturzSchritt.genau crash₁
            have hpair : ((SchrittWahl.absturz : SchrittWahl PUnit), spur) =
                (SchrittWahl.absturz, spur₁) := Option.some.inj lab
            have hspurEq : spur = spur₁ := congrArg Prod.snd hpair
            rw [hspurEq, spurEq₁] at hlabel
            have offer₁ : AbsturzAngeboten E.katalog ρ₁.hw t := crash₁.1
            have crashOffer₂ : (ρ₂.hw.angebot t).crash = true := by
              rw [← geraete_angebot_gleich vergleich t]
              exact offer₁.2
            obtain ⟨v₁, s₂, hv₁, hz₂⟩ := (geraete_zustand_gemeinsam vergleich t).resolve_left
              (by intro h; rw [hz₁] at h; cases h.1)
            have hvEq : v₁ = s₁ := Option.some.inj (hv₁.symm.trans hz₁)
            subst v₁
            have tick₂ := ρ₂.zeit.takt t
            rw [hz₂] at tick₂
            cases tick₂ with
            | wartet lab₂ _ hkein =>
              exfalso
              let st : Lauffolge E ρ₂.hw t (some s₂) (.absturz, absturzSpur)
                  (some (s₂.wiederanlauf E.einrichtung.wiederanlauf t (nachAbsturz s₂.persistenz))) :=
                .schritt (.absturz (absturz_schritt_erfuellbar E.einrichtung.persistenzRegion
                  E.einrichtung.wiederanlauf ⟨offer₁.1, crashOffer₂⟩ s₂))
              exact (hkein (.absturz, absturzSpur) _ st).elim
            | schritt lab₂ st =>
              cases hn₂ : ρ₂.zeit.zustand (t + 1) with
              | none => rw [hn₂] at st; cases st
              | some n₂ =>
                rw [hn₂] at st
                cases st with
                | schritt impl₂ =>
                  cases impl₂ with
                  | absturz crash₂ =>
                    obtain ⟨spurEq₂, n₂Eq⟩ := AbsturzSchritt.genau crash₂
                    have labEq : ρ₂.zeit.spur t = some (.absturz, absturzSpur) := by
                      rw [lab₂]
                      cases spurEq₂
                      rfl
                    obtain ⟨hfragen, hverlauf, hantworten, hverbraucht, hverworfen⟩ :=
                      geraeteKopplung_ledger hkopp hz₁ hz₂
                    have hbuch := geraeteKopplung_buchung hkopp hz₁ hz₂
                    obtain ⟨hq₁, hepoche, hgeliefert, hkerne, hstatus⟩ :=
                      (geraeteKopplung_kopplung hkopp).2.1 s₁ s₂ hz₁ hz₂
                    have hneu₁ : ∀ c, ¬ ∃ e, n₁.status c = .beendet e := by
                      intro c h
                      obtain ⟨e, he⟩ := h
                      rw [n₁Eq] at he
                      dsimp only [Zustand.wiederanlauf, Zustand.start] at he
                      by_cases hc : c = E.einrichtung.wiederanlauf.eintritt
                      · rw [if_pos hc] at he
                        cases he
                      · rw [if_neg hc] at he
                        cases he
                    have hneu₂ : ∀ c, ¬ ∃ e, n₂.status c = .beendet e := by
                      intro c h
                      obtain ⟨e, he⟩ := h
                      rw [n₂Eq] at he
                      dsimp only [Zustand.wiederanlauf, Zustand.start] at he
                      by_cases hc : c = E.einrichtung.wiederanlauf.eintritt
                      · rw [if_pos hc] at he
                        cases he
                      · rw [if_neg hc] at he
                        cases he
                    have hbeob₁ := geraete_absturz_beob_tick (predictor := predictor) hlabel hz₁ hn₁ hneu₁
                    have hbeob₂ := geraete_absturz_beob_tick (predictor := predictor) labEq hz₂ hn₂ hneu₂
                    have hlen := kopplung_laenge (geraeteKopplung_kopplung hkopp)
                    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
                    · simp only [NiedrigeBeob, NiedrigeBeob.praefix, hbeob₁, hbeob₂]
                      change List.Forall₂ _ (NiedrigeBeob E ρ₁ predictor t ++ [.katalog (.persistenz .crash)])
                        ((NiedrigeBeob E ρ₂ predictor t ++ [.katalog (.persistenz .crash)]).take
                          ((NiedrigeBeob E ρ₁ predictor t).length + 1))
                      have htake : (NiedrigeBeob E ρ₂ predictor t ++ [.katalog (.persistenz .crash)]).take
                          ((NiedrigeBeob E ρ₁ predictor t).length + 1) =
                          (NiedrigeBeob E ρ₂ predictor t).take
                            ((NiedrigeBeob E ρ₁ predictor t).length) ++
                            [.katalog (.persistenz .crash)] := by
                        rw [List.take_append]
                        simp only [hlen, List.take_succ_eq_append_getElem, List.getElem?_eq_none,
                          List.length_take, Nat.sub_self, List.take_zero, List.append_nil]
                      rw [htake]
                      exact List.rel_append (geraeteKopplung_kopplung hkopp).1
                        (List.Forall₂.cons (EreignisAequiv.gleich _) List.Forall₂.nil)
                    · intro v w hv hw
                      obtain rfl : v = n₁ := Option.some.inj hv
                      obtain rfl : w = n₂ := Option.some.inj hw
                      rw [n₁Eq, n₂Eq]
                      have hEP : (s₁.wiederanlauf E.einrichtung.wiederanlauf t
                          (nachAbsturz s₁.persistenz)).epoche =
                          (s₂.wiederanlauf E.einrichtung.wiederanlauf t
                          (nachAbsturz s₂.persistenz)).epoche := rfl
                      have hGel : (s₁.wiederanlauf E.einrichtung.wiederanlauf t
                          (nachAbsturz s₁.persistenz)).geliefert =
                          (s₂.wiederanlauf E.einrichtung.wiederanlauf t
                          (nachAbsturz s₂.persistenz)).geliefert := rfl
                      refine ⟨?_, hEP, hGel, ?_, ?_⟩
                      · refine ⟨?_, ?_, ?_, rfl, rfl, ?_⟩
                        · dsimp only [LokaleGleich, Denotation.unit,
                            Gabbro.Core.Ast.LowLevel.Device.unit, Einheit.fluss, Flussdaten.leer,
                            Flussdaten.lokal, LokaleEtiketten.ganz, LokaleEtiketten.gleich]
                          intro c p hp
                          rfl
                        · intro c
                          dsimp only [EndeSicht, Zustand.wiederanlauf, Zustand.start]
                          by_cases hc : c = E.einrichtung.wiederanlauf.eintritt
                          · rw [if_pos hc]
                            rfl
                          · rw [if_neg hc]
                            rfl
                        · intro x
                          dsimp only [Zustand.wiederanlauf, Denotation.unit,
                            Gabbro.Core.Ast.LowLevel.Device.unit, setup]
                          rfl
                        · intro c
                          dsimp only [AntwortSicht]
                          have hn1 : (s₁.wiederanlauf E.einrichtung.wiederanlauf t
                              (nachAbsturz s₁.persistenz)).naechsteAntwort c = s₁.naechsteAntwort c := by
                            dsimp only [Zustand.naechsteAntwort, Zustand.wiederanlauf, Zustand.angekommen]
                            rw [hantworten, hverbraucht, hverworfen]
                          have hn2 : (s₂.wiederanlauf E.einrichtung.wiederanlauf t
                              (nachAbsturz s₂.persistenz)).naechsteAntwort c = s₂.naechsteAntwort c := by
                            rfl
                          rw [hn1, hn2]
                          exact geraete_antwort_gleich (d := d) hq₁
                      · dsimp only [Zustand.wiederanlauf, Denotation.unit,
                          Gabbro.Core.Ast.LowLevel.Device.unit, setup]
                        rfl
                      · dsimp only [Zustand.wiederanlauf]
                        by_cases hc : c = E.einrichtung.wiederanlauf.eintritt
                        · rw [if_pos hc]; rfl
                        · rw [if_neg hc]; rfl
                    · intro v w hv hw
                      obtain rfl : v = n₁ := Option.some.inj hv
                      obtain rfl : w = n₂ := Option.some.inj hw
                      rw [n₁Eq, n₂Eq]
                      refine ⟨hfragen, hverlauf, hantworten, hverbraucht, ?_, rfl⟩
                      funext c
                      dsimp only [Zustand.wiederanlauf, Zustand.angekommen]
                      rw [hantworten, hverbraucht]
                    · rw [hbeob₁, hbeob₂, hlen]
                      simp only [List.length_append, List.length_singleton]
                  | kontext nc _ _ _ => exact (Bool.false_ne_true (nc.symm.trans crashOffer₂)).elim
                  | antwort nc _ => exact (Bool.false_ne_true (nc.symm.trans crashOffer₂)).elim
                  | interrupt nc _ => exact (Bool.false_ne_true (nc.symm.trans crashOffer₂)).elim
          | kontext _ _ _ _ => cases lab
          | antwort _ _ => cases lab
          | interrupt _ _ => cases lab

end Gabbro.Core.Beobachtung
