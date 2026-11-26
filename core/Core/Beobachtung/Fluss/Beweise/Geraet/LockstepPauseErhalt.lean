module

public import Core.Beobachtung.Fluss.Beweise.Geraet.LockstepTransport

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine
open Gabbro.Core.Ast.LowLevel.Device
open Gabbro.Core.Ast.LowLevel (entryContext)
open Gabbro.Core.Ast

variable {k : Katalog} {scope : Scope} {locals : Umgebung scope}
variable {d : Denotation k scope}

/-- At a single cut the strengthened coupling is symmetric: the coverage is a
    same-length prefix relation (reversible event by event), the source state and
    machine-field equalities are equalities, and the ledgers and booking are
    equalities. This is what lets the forward transport lemmas run in reverse. -/
private theorem geraeteKopplung_umkehren {ρ₁ ρ₂ : Lauf (d.unit locals)} {predictor : Praediktor}
    {t : Nat} (h : GeraeteKopplungAussage (d.unit locals) ρ₁ ρ₂ predictor t t) :
    GeraeteKopplungAussage (d.unit locals) ρ₂ ρ₁ predictor t t := by
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · have hlen := kopplung_laenge (geraeteKopplung_kopplung h)
      have htake : (NiedrigeBeob (d.unit locals) ρ₂ predictor t).take
          (NiedrigeBeob (d.unit locals) ρ₁ predictor t).length =
          NiedrigeBeob (d.unit locals) ρ₂ predictor t :=
        List.take_of_length_le (le_of_eq hlen.symm)
      have hcover : List.Forall₂ (EreignisAequiv (d.unit locals).fluss.freigabe)
          (NiedrigeBeob (d.unit locals) ρ₁ predictor t)
          (NiedrigeBeob (d.unit locals) ρ₂ predictor t) := by
        simpa only [htake] using (geraeteKopplung_kopplung h).1
      have hrel : ∀ {a b : NiedrigesEreignis Nat UInt8 PUnit PUnit},
          EreignisAequiv (d.unit locals).fluss.freigabe a b →
          EreignisAequiv (d.unit locals).fluss.freigabe b a := by
        intro a b hr
        cases hr with
        | gleich _ => exact .gleich _
        | freigabe c id l r g decl auth =>
            exact .freigabe c id r l g decl auth.symm
      have hforall : ∀ {as bs : List (NiedrigesEreignis Nat UInt8 PUnit PUnit)},
          List.Forall₂ (EreignisAequiv (d.unit locals).fluss.freigabe) as bs →
          List.Forall₂ (EreignisAequiv (d.unit locals).fluss.freigabe) bs as := by
        intro as bs hfb
        induction hfb with
        | nil => exact List.Forall₂.nil
        | cons hab tail ih => exact List.Forall₂.cons (hrel hab) ih
      have htake' : (NiedrigeBeob (d.unit locals) ρ₁ predictor t).take
          (NiedrigeBeob (d.unit locals) ρ₂ predictor t).length =
          NiedrigeBeob (d.unit locals) ρ₁ predictor t :=
        List.take_of_length_le (le_of_eq hlen)
      rw [htake']
      exact hforall hcover
    · intro v w hv hw
      obtain ⟨q, ep, ge, ke, st⟩ := (geraeteKopplung_kopplung h).2.1 w v hw hv
      exact ⟨Gabbro.Core.Ast.Semantik.Beobachtung.QuellzustandGleich.symm q,
        ep.symm, ge.symm, ke.symm, st.symm⟩
    · exact (kopplung_laenge (geraeteKopplung_kopplung h)).symm
  · intro v w hv hw
    obtain ⟨ledger, buch⟩ := h.2 w v hw hv
    exact ⟨ledger.symm, buch.symm⟩

/-- A paused cut keeps the strengthened coupling. The left `KeinSchritt` rules out every
    right step kind: the forward transport lemmas are applied with the comparison and the
    coupling reversed, so a right context/answer/interrupt step produces a left step; a right
    crash is rebuilt from the equal crash offer. The remaining right tick is a pause, and
    both low prefixes and both states then stay unchanged. See `Lockstep.lean`. -/
theorem geraete_pause_erhalt (locals : Umgebung scope) (d : Denotation k scope) :
    GeraetePauseErhaltAussage (d := d) (locals := locals) := by
  intro h₁ h₂ ρ₁ ρ₂ vergleich predictor t hkopp idle₁
  classical
  let E := d.unit locals
  have warte₁ := ρ₁.zeit.wartet idle₁
  have keinSchritt₁ : KeinSchritt (Lauffolge E ρ₁.hw) t (ρ₁.zeit.zustand t) := warte₁.2
  have zustandGleich₁ : ρ₁.zeit.zustand (t + 1) = ρ₁.zeit.zustand t := warte₁.1
  have hkoppUmkehr := geraeteKopplung_umkehren (d := d) (locals := locals) hkopp
  cases hzustände : geraete_zustand_gemeinsam vergleich t with
  | inl hnone =>
      obtain ⟨hz₁none, hz₂none⟩ := hnone
      have hz₁post : ρ₁.zeit.zustand (t + 1) = none := zustandGleich₁.trans hz₁none
      have tick₂ := ρ₂.zeit.takt t
      rw [hz₂none] at tick₂
      cases tick₂ with
      | schritt _ step₂ => cases step₂
      | wartet label₂ gleich₂ _ =>
          have idle₂ : ρ₂.zeit.spur t = none := label₂
          refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
          · rw [beob_pause (E := E) ρ₁ predictor t idle₁,
              beob_pause (E := E) ρ₂ predictor t idle₂]
            exact (geraeteKopplung_kopplung hkopp).1
          · intro v w hv hw
            rw [hz₁post] at hv
            cases hv
          · rw [beob_pause (E := E) ρ₁ predictor t idle₁,
              beob_pause (E := E) ρ₂ predictor t idle₂]
            exact kopplung_laenge (geraeteKopplung_kopplung hkopp)
          · intro v w hv hw
            rw [hz₁post] at hv
            cases hv
  | inr hsome =>
      obtain ⟨s₁, s₂, hz₁, hz₂⟩ := hsome
      have gut₁ : s₁.SpeicherGut := geraete_lauf_speicher_gut vergleich.links t hz₁
      have quell₁₂ : QuellzustandGleich E s₁ s₂ :=
        ((geraeteKopplung_kopplung hkopp).2.1 s₁ s₂ hz₁ hz₂).1
      have hkerne : s₁.kerne = s₂.kerne :=
        ((geraeteKopplung_kopplung hkopp).2.1 s₁ s₂ hz₁ hz₂).2.2.2.1
      have hstatus : s₁.status = s₂.status :=
        ((geraeteKopplung_kopplung hkopp).2.1 s₁ s₂ hz₁ hz₂).2.2.2.2
      have hang := geraete_angebot_gleich vergleich t
      have tick₂ := ρ₂.zeit.takt t
      rw [hz₂] at tick₂
      generalize hn₂ : ρ₂.zeit.zustand (t + 1) = n₂t at tick₂
      cases tick₂ with
      | wartet label₂ gleich₂ _ =>
          have idle₂ : ρ₂.zeit.spur t = none := label₂
          refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
          · rw [beob_pause (E := E) ρ₁ predictor t idle₁,
              beob_pause (E := E) ρ₂ predictor t idle₂]
            exact (geraeteKopplung_kopplung hkopp).1
          · intro v w hv hw
            have hvEq : v = s₁ := Option.some.inj (hv.symm.trans ((zustandGleich₁.trans hz₁)))
            have hwEq : w = s₂ := Option.some.inj (hw.symm.trans (hn₂.trans gleich₂))
            subst v
            subst w
            exact (geraeteKopplung_kopplung hkopp).2.1 s₁ s₂ hz₁ hz₂
          · rw [beob_pause (E := E) ρ₁ predictor t idle₁,
              beob_pause (E := E) ρ₂ predictor t idle₂]
            exact kopplung_laenge (geraeteKopplung_kopplung hkopp)
          · intro v w hv hw
            have hvEq : v = s₁ := Option.some.inj (hv.symm.trans ((zustandGleich₁.trans hz₁)))
            have hwEq : w = s₂ := Option.some.inj (hw.symm.trans (hn₂.trans gleich₂))
            subst v
            subst w
            exact ⟨geraeteKopplung_ledger hkopp hz₁ hz₂,
              geraeteKopplung_buchung hkopp hz₁ hz₂⟩
      | schritt label₂ step₂ =>
          have someEv : ∃ wahl spur', ρ₂.zeit.spur t = some (wahl, spur') := by
            cases hlab : ρ₂.zeit.spur t with
            | none =>
                rw [hlab] at label₂
                cases label₂
            | some ev =>
                have heta : some ev = some (ev.1, ev.2) := by
                  cases ev
                  rfl
                exact ⟨ev.1, ev.2, heta⟩
          obtain ⟨wahl, spur', label'⟩ := someEv
          have evEq := Option.some.inj (label₂.symm.trans label')
          rw [evEq] at step₂
          cases step₂ with
          | schritt impl₂ =>
            cases wahl with
            | kontext c₂ w₂ =>
                cases impl₂ with
                | kontext keinAbsturz₂ bereit₂ regel₂ aus₂ =>
                    obtain ⟨binding, access, required, target, ruleEq, hbind⟩ :=
                      geraete_rule_binding locals d
                    obtain ⟨_, plan', hplans', rule₂⟩ := geraete_kontext_regel ruleEq regel₂
                    have regel₂' := regel₂
                    rw [hplans'] at regel₂'
                    have keinAbsturz₁ : (ρ₁.hw.angebot t).crash = false := by
                      rw [hang]
                      exact keinAbsturz₂
                    obtain ⟨kk, geleg₂, kern₂, stat₂⟩ := bereit₂
                    have bereit₁ : KannSchreiten ρ₁.hw t c₂ s₁ := by
                      refine ⟨kk, ?_, ?_, ?_⟩
                      · change (ρ₁.hw.angebot t).core = some kk
                        rw [hang]
                        exact geleg₂
                      · rw [hkerne]
                        exact kern₂
                      · rw [hstatus]
                        exact stat₂
                    cases rule₂ with
                    | issue owned₂ idle₂ =>
                        obtain ⟨spur₁', u₁', n₁', regel₁, aus₁, _, _, _, _, _, _, _, _⟩ :=
                          geraete_issue_transport (locals := locals) (d := d)
                            (vergleich := vergleich.symm) (t := t) (binding := binding)
                            (access := access) (required := required) (target := target)
                            (c := c₂) (w := w₂) (s₁ := s₂) (s₂ := s₁)
                            (spur₁ := spur')
                            hkoppUmkehr hz₂ hz₁ gut₁
                            (Gabbro.Core.Ast.Semantik.Beobachtung.QuellzustandGleich.symm quell₁₂)
                            regel₂' ruleEq aus₂ rfl rfl owned₂ idle₂
                        have step₁ : ImplSchritt E.einrichtung E.system E.katalog ρ₁.hw t s₁
                            (.kontext c₂ w₂, spur₁') n₁' :=
                          .kontext keinAbsturz₁ bereit₁ regel₁ aus₁
                        exact (keinSchritt₁ (.kontext c₂ w₂, spur₁') (some n₁') (by
                          rw [hz₁]
                          exact Lauffolge.schritt step₁)).elim
                    | @consume owned₂ answer₂ pending₂ ready₂ sameQuestion₂ =>
                        obtain ⟨spur₁', u₁', n₁', regel₁, aus₁, _, _, _, _, _, _, _, _⟩ :=
                          geraete_consume_transport (locals := locals) (d := d)
                            (vergleich := vergleich.symm) (t := t) (binding := binding)
                            (access := access) (required := required) (target := target)
                            (c := c₂) (w := w₂) (s₁ := s₂) (s₂ := s₁)
                            (spur₁ := spur') (answer := answer₂)
                            hkoppUmkehr hz₂ hz₁
                            (Gabbro.Core.Ast.Semantik.Beobachtung.QuellzustandGleich.symm quell₁₂)
                            regel₂' ruleEq aus₂ rfl rfl owned₂ pending₂ ready₂ sameQuestion₂
                        have step₁ : ImplSchritt E.einrichtung E.system E.katalog ρ₁.hw t s₁
                            (.kontext c₂ w₂, spur₁') n₁' :=
                          .kontext keinAbsturz₁ bereit₁ regel₁ aus₁
                        exact (keinSchritt₁ (.kontext c₂ w₂, spur₁') (some n₁') (by
                          rw [hz₁]
                          exact Lauffolge.schritt step₁)).elim
            | antwort a =>
                cases impl₂ with
                | antwort keinAbsturz₂ h₂ =>
                    have keinAbsturz₁ : (ρ₁.hw.angebot t).crash = false := by
                      rw [hang]
                      exact keinAbsturz₂
                    obtain ⟨spur₁', n₁', h₁', _⟩ :=
                      geraete_antwort_transport (locals := locals) (d := d)
                        (vergleich := vergleich.symm) (t := t) (a := a)
                        (s₁ := s₂) (s₂ := s₁) (spur₁ := spur')
                        hkoppUmkehr hz₂ hz₁ gut₁ h₂
                    have step₁ : ImplSchritt E.einrichtung E.system E.katalog ρ₁.hw t s₁
                        (.antwort a, spur₁') n₁' := .antwort keinAbsturz₁ h₁'
                    exact (keinSchritt₁ (.antwort a, spur₁') (some n₁') (by
                      rw [hz₁]
                      exact Lauffolge.schritt step₁)).elim
            | interrupt id =>
                cases impl₂ with
                | interrupt keinAbsturz₂ h₂ =>
                    have keinAbsturz₁ : (ρ₁.hw.angebot t).crash = false := by
                      rw [hang]
                      exact keinAbsturz₂
                    obtain ⟨spur₁', n₁', h₁', _⟩ :=
                      geraete_interrupt_transport (locals := locals) (d := d)
                        (vergleich := vergleich.symm) (t := t) (id := id)
                        (s₁ := s₂) (s₂ := s₁) (spur₁ := spur')
                        hkoppUmkehr hz₂ hz₁ gut₁ h₂
                    have step₁ : ImplSchritt E.einrichtung E.system E.katalog ρ₁.hw t s₁
                        (.interrupt id, spur₁') n₁' := .interrupt keinAbsturz₁ h₁'
                    exact (keinSchritt₁ (.interrupt id, spur₁') (some n₁') (by
                      rw [hz₁]
                      exact Lauffolge.schritt step₁)).elim
            | absturz =>
                cases impl₂ with
                | absturz h₂ =>
                    have offer₂ : AbsturzAngeboten E.katalog ρ₂.hw t := h₂.1
                    have crashOffer₁ : (ρ₁.hw.angebot t).crash = true := by
                      rw [hang]
                      exact offer₂.2
                    have offer₁ : AbsturzAngeboten E.katalog ρ₁.hw t := ⟨offer₂.1, crashOffer₁⟩
                    have crashStep₁ : AbsturzSchritt E.einrichtung.persistenzRegion
                        E.einrichtung.wiederanlauf E.katalog ρ₁.hw t s₁ absturzSpur
                        (s₁.wiederanlauf E.einrichtung.wiederanlauf t (nachAbsturz s₁.persistenz)) :=
                      absturz_schritt_erfuellbar _ _ offer₁ s₁
                    have step₁ : ImplSchritt E.einrichtung E.system E.katalog ρ₁.hw t s₁
                        (.absturz, absturzSpur)
                        (s₁.wiederanlauf E.einrichtung.wiederanlauf t (nachAbsturz s₁.persistenz)) :=
                      .absturz crashStep₁
                    exact (keinSchritt₁ (.absturz, absturzSpur)
                      (s₁.wiederanlauf E.einrichtung.wiederanlauf t (nachAbsturz s₁.persistenz)) (by
                        rw [hz₁]
                        exact Lauffolge.schritt step₁)).elim

end Gabbro.Core.Beobachtung
