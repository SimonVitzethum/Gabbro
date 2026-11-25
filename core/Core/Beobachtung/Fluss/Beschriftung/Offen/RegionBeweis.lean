
module

public import Core.Beobachtung.Fluss.Beschriftung.Offen.Region
public import Core.Beobachtung.Fluss.Beschriftung.Offen.RegionBeweisHelpers

@[expose] public section

namespace Gabbro.Core.Beobachtung

/-- Source flow rules carry the noninterference duty for every low-level instruction:
    the only context step is the instruction itself, it is silent, and the right run
    takes the same step under the same hardware opportunities. -/
theorem regionNI : RegionNIAussage := by
  classical
  intro k op f fluss
  intro h₁ h₂ ρ₁ ρ₂ vergleich predictor t c wahl spur vor
    zustand kopf spurGlied kopplung
  rcases kopplung with ⟨cov, st, len⟩
  have kt := kopf_heraus op kopf
  have fop : f = op := kt.1
  subst f
  have still₁ := unit_kontext_still op (ρ := ρ₁) (predictor := predictor)
    (t := t) (c := c) (wahl := wahl) (spur := spur) spurGlied
  cases hz₂ : ρ₂.zeit.zustand t with
  | none =>
      have hn₂ : ρ₂.zeit.zustand (t + 1) = none := zustand_nach hz₂
      have still₂ : schrittBeob ρ₂ predictor t = [] := by
        cases hs : ρ₂.zeit.spur t with
        | none => simp only [schrittBeob, hs]
        | some _ => simp only [schrittBeob, hs, hz₂]
      have e₁ : NiedrigeBeob (unit op) ρ₁ predictor (t + 1) =
          NiedrigeBeob (unit op) ρ₁ predictor t := by
        change NiedrigeBeob (unit op) ρ₁ predictor t ++ schrittBeob ρ₁ predictor t = _
        rw [still₁, List.append_nil]
      have e₂ : NiedrigeBeob (unit op) ρ₂ predictor (t + 1) =
          NiedrigeBeob (unit op) ρ₂ predictor t := by
        change NiedrigeBeob (unit op) ρ₂ predictor t ++ schrittBeob ρ₂ predictor t = _
        rw [still₂, List.append_nil]
      refine ⟨?_, ?_, ?_⟩
      · rw [e₁, e₂]
        exact cov
      · intro a' b' ha' hb'
        rw [hn₂] at hb'
        cases hb'
      · rw [e₁, e₂]
        exact len
  | some v₂ =>
      have stv := st vor v₂ zustand hz₂
      have qv := stv.1
      have epocheEq := stv.2.1
      have geliefertEq := stv.2.2.1
      have kerneEq := stv.2.2.2.1
      have statusEq := stv.2.2.2.2
      have hlok := qsg_lokal op qv
      have hre := qsg_rechte op qv
      have hle := qsg_leihen op qv
      have heval := evaluate_isSome_gleich op (c := c) hlok hre hle
      have kopf₂ : (unit op).system.kopf v₂ c = some op := by
        have hk := kopf
        simp only [unit, Ast.LowLevel.system] at hk ⊢
        unfold Ast.LowLevel.head at hk ⊢
        rw [← hlok, ← statusEq, ← heval]
        exact hk
      -- left step
      have takt₁ := ρ₁.zeit.takt t
      rw [spurGlied, zustand] at takt₁
      generalize hN₁ : ρ₁.zeit.zustand (t + 1) = n₁ at takt₁
      cases takt₁ with
      | wartet label _ _ => cases label
      | schritt label laufstep =>
          cases laufstep with
          | schritt impl =>
              cases impl with
              | kontext keinAbsturz₁ bereit₁ regel₁ aus₁ =>
                  cases label
                  obtain ⟨i, kopf_i, implI₁⟩ := regel₁
                  have ifop : i = op := (Option.some.inj (kopf.symm.trans kopf_i)).symm
                  subst i
                  obtain ⟨transfer₁, eval₁, planEq₁, hu₁⟩ := Instruction.implTransfer (w := wahl) implI₁
                  cases (List.cons.inj planEq₁).1
                  simp only [unit] at aus₁
                  obtain ⟨traceEq₁, nextEq₁⟩ := Instruction.genauInternal aus₁
                  have leftNext : ρ₁.zeit.zustand (t + 1) = some (transfer₁.apply c vor) := by
                    rw [hN₁, nextEq₁, hu₁]
                  -- public control label
                  have pub : oeffentlich ((unit op).fluss.kontrolle op) = true := by
                    simp only [unit, Flussdaten.leer, oeffentlich, decide_true]
                  have formSchritt₁ : FormSchritt (unit op) op c vor wahl Ast.LowLevel.plan
                      (transfer₁.apply c vor) := by
                    refine ⟨kopf, ?_⟩
                    change op.ideal c vor wahl [Ast.LowLevel.plan] (transfer₁.apply c vor)
                    exact ⟨transfer₁, eval₁, rfl, rfl⟩
                  -- hardware offers coincide
                  have crashEq : (ρ₁.hw.angebot t).crash = (ρ₂.hw.angebot t).crash :=
                    congrArg (fun p => (p.1 t).2.2.2.2.2.1) vergleich.politik
                  have coreEq : (ρ₁.hw.angebot t).core = (ρ₂.hw.angebot t).core :=
                    congrArg (fun p => (p.1 t).1) vergleich.politik
                  have signale : (ρ₁.hw.angebot t).interrupts = (ρ₂.hw.angebot t).interrupts :=
                    congrArg (fun p => (p.1 t).2.2.1) vergleich.politik
                  have auswahlEq : (ρ₁.hw.angebot t).interruptAuswahl =
                      (ρ₂.hw.angebot t).interruptAuswahl := by
                    simp only [Gelegenheit.interruptAuswahl, signale]
                  have crash₂ : (ρ₂.hw.angebot t).crash = false := by
                    rw [← crashEq]
                    exact keinAbsturz₁
                  have auswahl₁none : (ρ₁.hw.angebot t).interruptAuswahl = none := by
                    obtain ⟨k, geleg₁, _, _⟩ := bereit₁
                    have core₁ : (ρ₁.hw.angebot t).core = some k := geleg₁
                    cases haus : (ρ₁.hw.angebot t).interruptAuswahl with
                    | some _ =>
                        have res := (vergleich.links.2.1.2 t).interrupt_reserviert haus
                        rw [res.2.1] at core₁
                        cases core₁
                    | none => rfl
                  have auswahl₂none : (ρ₂.hw.angebot t).interruptAuswahl = none := by
                    rw [← auswahlEq]
                    exact auswahl₁none
                  -- right transfer and constructed context step
                  have hv₂some : ∃ tr, op.evaluate v₂ c = some tr := by
                    cases he : op.evaluate v₂ c with
                    | none =>
                        have hs : (op.evaluate v₂ c).isSome = false := by
                          rw [he]
                          rfl
                        rw [← heval, kt.2.2.2.1] at hs
                        cases hs
                    | some tr => exact ⟨tr, rfl⟩
                  obtain ⟨transfer₂, eval₂⟩ := hv₂some
                  have bereit₂ : KannSchreiten ρ₂.hw t c v₂ := by
                    obtain ⟨k, geleg₁, kern₁, stat₁⟩ := bereit₁
                    refine ⟨k, ?_, ?_, ?_⟩
                    · unfold HwLauf.gelegenheit
                      unfold HwLauf.gelegenheit at geleg₁
                      rw [← coreEq]
                      exact geleg₁
                    · rw [← kerneEq]
                      exact kern₁
                    · rw [← statusEq]
                      exact stat₁
                  have step₂ : ImplSchritt (unit op).einrichtung (unit op).system (unit op).katalog
                      ρ₂.hw t v₂ (.kontext c wahl, ⟨[], []⟩) (transfer₂.apply c v₂) := by
                    refine .kontext (plan := Ast.LowLevel.plan) (u := transfer₂.apply c v₂)
                      crash₂ bereit₂ ?_ ?_
                    · refine ⟨op, kopf₂, ?_⟩
                      change op.impl c v₂ wahl [Ast.LowLevel.plan] (transfer₂.apply c v₂)
                      unfold Instruction.impl
                      rw [eval₂]
                      exact ⟨rfl, rfl⟩
                    · simpa only [unit] using Instruction.vollzug op transfer₂ t c v₂
                  -- right step kind
                  have hspur₂ : ρ₂.zeit.spur t ≠ none := by
                    intro hnone
                    have tak₂ := ρ₂.zeit.takt t
                    rw [hz₂, hnone] at tak₂
                    cases tak₂ with
                    | wartet _ _ hp => exact (hp (.kontext c wahl, ⟨[], []⟩)
                        (transfer₂.apply c v₂) (Lauffolge.schritt step₂)).elim
                    | schritt label _ => cases label
                  cases hspurWahl : ρ₂.zeit.spur t with
                  | none => exact (hspur₂ hspurWahl).elim
                  | some ev =>
                      cases ev with
                      | mk wahl₂ spur₂ =>
                          cases wahl₂ with
                          | antwort a =>
                              exact (unit_keine_antwort op vergleich.rechts t a spur₂ hspurWahl).elim
                          | interrupt id =>
                              have tak₂ := ρ₂.zeit.takt t
                              rw [hz₂, hspurWahl] at tak₂
                              generalize hN₂ : ρ₂.zeit.zustand (t + 1) = n₂ at tak₂
                              cases tak₂ with
                              | wartet label _ _ => cases label
                              | schritt label laufstep =>
                                  cases laufstep with
                                  | schritt impl =>
                                      cases impl with
                                      | kontext _ _ _ _ => cases label
                                       | interrupt _ hinterrupt =>
                                          obtain ⟨k, irq, ch, nmi, hoff, hpending, hnimmt,
                                            hstat, hspurAus, hmem, hnext⟩ := hinterrupt
                                          have haws := hpending.2.2.2.2
                                          rw [auswahl₂none] at haws
                                          cases haws
                                      | antwort _ _ => cases label
                                      | absturz _ => cases label
                          | absturz =>
                              have tak₂ := ρ₂.zeit.takt t
                              rw [hz₂, hspurWahl] at tak₂
                              generalize hN₂ : ρ₂.zeit.zustand (t + 1) = n₂ at tak₂
                              cases tak₂ with
                              | wartet label _ _ => cases label
                              | schritt label laufstep =>
                                  cases laufstep with
                                  | schritt impl =>
                                      cases impl with
                                      | absturz habs =>
                                          obtain ⟨angebot, _, _⟩ := habs
                                          have hc : (ρ₂.hw.angebot t).crash = true := angebot.2
                                          rw [crash₂] at hc
                                          cases hc
                                      | kontext _ _ _ _ => cases label
                                      | antwort _ _ => cases label
                                      | interrupt _ _ => cases label
                          | kontext c₂ w₂ =>
                              have tak₂ := ρ₂.zeit.takt t
                              rw [hz₂, hspurWahl] at tak₂
                              generalize hN₂ : ρ₂.zeit.zustand (t + 1) = n₂ at tak₂
                              cases tak₂ with
                              | wartet label _ _ => cases label
                              | schritt label laufstep =>
                                  cases laufstep with
                                  | schritt impl =>
                                      cases impl with
                                      | kontext _ _ regel₂ aus₂ =>
                                          obtain ⟨j, kopf_j, implI₂⟩ := regel₂
                                          obtain ⟨_, cR, _, _, _⟩ := kopf_heraus op kopf_j
                                          have c_eq := cR.trans kt.2.1.symm
                                          rw [c_eq] at kopf_j
                                          have jop : j = op := (Option.some.inj (kopf₂.symm.trans kopf_j)).symm
                                          subst j
                                          obtain ⟨transfer₂', eval₂', planEq₂, hu₂⟩ :=
                                            Instruction.implTransfer (w := w₂) implI₂
                                          rw [c_eq] at eval₂' hu₂
                                          cases (List.cons.inj planEq₂).1
                                          simp only [unit] at aus₂
                                          obtain ⟨traceEq₂, nextEq₂⟩ := Instruction.genauInternal aus₂
                                          have rightNext : ρ₂.zeit.zustand (t + 1) =
                                              some (transfer₂'.apply c v₂) := by
                                            rw [hN₂, nextEq₂, hu₂]
                                          have formSchritt₂ : FormSchritt (unit op) op c v₂ w₂
                                              Ast.LowLevel.plan (transfer₂'.apply c v₂) := by
                                            refine ⟨kopf₂, ?_⟩
                                            change op.ideal c v₂ w₂ [Ast.LowLevel.plan] (transfer₂'.apply c v₂)
                                            exact ⟨transfer₂', eval₂', rfl, rfl⟩
                                          have qpost := (fluss.2 pub c vor wahl Ast.LowLevel.plan
                                            (transfer₁.apply c vor) v₂ w₂ Ast.LowLevel.plan
                                            (transfer₂'.apply c v₂) qv formSchritt₁ formSchritt₂).1
                                          have still₂ : schrittBeob ρ₂ predictor t = [] :=
                                            unit_kontext_still op (ρ := ρ₂) (predictor := predictor)
                                              (t := t) (c := c₂) (wahl := w₂) (spur := spur₂) hspurWahl
                                          have e₁ : NiedrigeBeob (unit op) ρ₁ predictor (t + 1) =
                                              NiedrigeBeob (unit op) ρ₁ predictor t := by
                                            change NiedrigeBeob (unit op) ρ₁ predictor t ++
                                              schrittBeob ρ₁ predictor t = _
                                            rw [still₁, List.append_nil]
                                          have e₂ : NiedrigeBeob (unit op) ρ₂ predictor (t + 1) =
                                              NiedrigeBeob (unit op) ρ₂ predictor t := by
                                            change NiedrigeBeob (unit op) ρ₂ predictor t ++
                                              schrittBeob ρ₂ predictor t = _
                                            rw [still₂, List.append_nil]
                                          refine ⟨?_, ?_, ?_⟩
                                          · rw [e₁, e₂]
                                            exact cov
                                          · intro a' b' ha' hb'
                                            have ea : a' = transfer₁.apply c vor :=
                                              Option.some.inj (ha'.symm.trans leftNext)
                                            have eb : b' = transfer₂'.apply c v₂ :=
                                              Option.some.inj (hb'.symm.trans rightNext)
                                            subst a'
                                            subst b'
                                            exact ⟨qpost, epocheEq, geliefertEq, kerneEq, statusEq⟩
                                          · rw [e₁, e₂]
                                            exact len
                                      | antwort _ _ => cases label
                                      | interrupt _ _ => cases label
                                      | absturz _ => cases label
              | antwort _ _ => cases label
              | interrupt _ _ => cases label
              | absturz _ => cases label

end Gabbro.Core.Beobachtung
