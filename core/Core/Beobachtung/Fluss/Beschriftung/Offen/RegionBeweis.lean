module

public import Core.Ast.LowLevel.Execution
public import Core.Ast.LowLevel.Proofs.Preservation
public import Core.Beobachtung.Fluss.Beschriftung.Offen.Region
public import Core.Beobachtung.Review.Spur
public import Core.Beobachtung.Nichtinterferenz

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine
open Ast.LowLevel (Instruction unit)

/-- Every source place of the low-level unit is public, so source-state equality is equality
    of the local stores. -/
private theorem qsg_lokal {k : Katalog} (op : Instruction k) {v u : Ast.LowLevel.State k}
    (h : QuellzustandGleich (unit op) v u) : v.lokal = u.lokal := by
  unfold QuellzustandGleich LokaleGleich at h
  dsimp [unit, Flussdaten.leer, LokaleEtiketten.ganz, LokaleEtiketten.gleich, Etiketten.leer] at h
  funext c
  exact h.1 c ⟨0, Nat.zero_lt_one⟩ (by decide)

private theorem qsg_rechte {k : Katalog} (op : Instruction k) {v u : Ast.LowLevel.State k}
    (h : QuellzustandGleich (unit op) v u) : v.rechte = u.rechte := by
  unfold QuellzustandGleich at h
  exact h.2.2.2.1

private theorem qsg_leihen {k : Katalog} (op : Instruction k) {v u : Ast.LowLevel.State k}
    (h : QuellzustandGleich (unit op) v u) : v.leihen = u.leihen := by
  unfold QuellzustandGleich at h
  exact h.2.2.2.2.1

private theorem qsg_initial {k : Katalog} (op : Instruction k) {v u : Ast.LowLevel.State k}
    (h : QuellzustandGleich (unit op) v u) : v.initial = u.initial := by
  unfold QuellzustandGleich at h
  have hx := h.2.2.1
  funext x
  exact Option.some.inj (by
    simpa only [unit, Etiketten.leer, sichtbar, oeffentlich, decide_true, if_true] using hx x)

private theorem frage_leer {Ort : Type} (e : Etiketten Ort)
    (ho : ∀ o, e.objekt o = ∅) (hp : ∀ p, e.endpunkt p = ∅) (q : Frage) : e.frage q = ∅ := by
  unfold Etiketten.frage
  rw [hp q.endpoint]
  induction q.zugriffe with
  | nil => rfl
  | cons t ts ih =>
      rw [List.map_cons, List.foldl_cons, ho t.handle.origin.object, Finset.empty_union]
      exact ih

private theorem etiketten_leer_frage {Ort : Type} (q : Frage) : (Etiketten.leer : Etiketten Ort).frage q = ∅ :=
  frage_leer (Etiketten.leer : Etiketten Ort) (fun _ => rfl) (fun _ => rfl) q

private theorem bind_some {α : Type} (x : Option α) : x.bind some = x := by
  cases x <;> rfl

private theorem qsg_antwort {k : Katalog} (op : Instruction k) {v u : Ast.LowLevel.State k}
    (h : QuellzustandGleich (unit op) v u) (c : Kontext) : v.naechsteAntwort c = u.naechsteAntwort c := by
  unfold QuellzustandGleich at h
  have hx := h.2.2.2.2.2 c
  simpa only [unit, Flussdaten.leer, AntwortSicht, sichtbar, oeffentlich,
    decide_true, if_true, etiketten_leer_frage, bind_some] using hx

private theorem zustand_nach {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]
    {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form}
    {ρ : Lauf E} {t : Nat} (h : ρ.zeit.zustand t = none) : ρ.zeit.zustand (t + 1) = none := by
  have tak := ρ.zeit.takt t
  rw [h] at tak
  cases tak with
  | wartet _ eq _ => exact eq
  | schritt _ step => cases step

private theorem held_gleich {k : Katalog} {v u : Ast.LowLevel.State k} {c : Kontext} {slot : Nat}
    (hl : v.lokal = u.lokal) (hre : v.rechte = u.rechte) (hle : v.leihen = u.leihen) :
    Ast.LowLevel.heldRegion v c slot = Ast.LowLevel.heldRegion u c slot := by
  unfold Ast.LowLevel.heldRegion
  rw [hl, hre, hle]

/-- Whether evaluation succeeds is decided by the public frame, rights and loans. -/
private theorem evaluate_isSome_gleich {k : Katalog} (op : Instruction k)
    {v u : Ast.LowLevel.State k} {c : Kontext}
    (hl : v.lokal = u.lokal) (hre : v.rechte = u.rechte) (hle : v.leihen = u.leihen) :
    (op.evaluate v c).isSome = (op.evaluate u c).isSome := by
  cases op with
  | denoteAddress _ _ _ => rfl
  | selectEnvironment _ _ _ _ => rfl
  | projectAddress slot =>
      simp only [Instruction.evaluate, held_gleich hl hre hle]
  | borrowView slot shape =>
      simp only [Instruction.evaluate, held_gleich hl hre hle]

/-- Inverting the low-level head: only the instruction itself runs at the entry, once. -/
private theorem kopf_heraus {k : Katalog} (op : Instruction k) {v : Ast.LowLevel.State k}
    {c : Kontext} {f : Instruction k} (hv : (unit op).system.kopf v c = some f) :
    f = op ∧ c = Ast.LowLevel.entryContext ∧ (v.lokal c).pc = 0 ∧
      (op.evaluate v c).isSome = true ∧ v.status c = .laeuft := by
  simp only [unit, Ast.LowLevel.system] at hv
  unfold Ast.LowLevel.head at hv
  cases hs : v.status c with
  | ruht =>
      rw [hs] at hv
      cases hv
  | beendet _ =>
      rw [hs] at hv
      cases hv
  | laeuft =>
      rw [hs] at hv
      by_cases hcond : c = Ast.LowLevel.entryContext ∧ (v.lokal c).pc = 0 ∧
          (op.evaluate v c).isSome = true
      · rw [if_pos hcond] at hv
        exact ⟨(Option.some.inj hv).symm, hcond.1, hcond.2.1, hcond.2.2, rfl⟩
      · rw [if_neg hcond] at hv
        cases hv

/-- The low-level unit never issues a question, so no reached state carries a pending one. -/
private theorem unit_fragen_leer_an {k : Katalog} (op : Instruction k) {h : Umgebung}
    {ρ : Lauf (unit op)} (lauf : Laeufe (unit op) h ρ)
    (t : Nat) (s : Ast.LowLevel.State k) (hs : ρ.zeit.zustand t = some s) : s.fragen = [] := by
  induction t generalizing s with
  | zero =>
      rw [lauf.2.2.2] at hs
      simp only [unit] at hs
      unfold Ast.LowLevel.loaded at hs
      split at hs
      · have eqs := Option.some.inj hs
        rw [← eqs]
        rfl
      · cases hs
  | succ t ih =>
      have tak := ρ.zeit.takt t
      cases hv : ρ.zeit.zustand t with
      | none =>
          rw [hv] at tak
          cases tak with
          | wartet _ eq _ => rw [eq] at hs; cases hs
          | schritt _ laufstep => cases laufstep
      | some s0 =>
          have ihs := ih s0 hv
          rw [hv, hs] at tak
          cases tak with
          | wartet label eq _ =>
              have ss : s = s0 := Option.some.inj eq
              subst s
              exact ihs
          | schritt _ laufstep =>
              cases laufstep with
              | schritt impl =>
                  cases impl with
                  | kontext _ _ regel aus =>
                      obtain ⟨_, _, implI⟩ := regel
                      obtain ⟨transfer, _, planEq, hu⟩ := Instruction.implTransfer (w := ()) implI
                      cases (List.cons.inj planEq).1
                      simp only [unit] at aus
                      obtain ⟨_, nextEq⟩ := Instruction.genauInternal aus
                      rw [nextEq, hu]
                      exact ihs
                  | antwort _ hantwort =>
                      obtain ⟨_, _, _, nextEq⟩ := hantwort
                      rw [nextEq]
                      exact ihs
                  | interrupt _ hinterrupt =>
                      obtain ⟨_, _, _, _, _, _, _, _, _, _, nextEq⟩ := hinterrupt
                      rw [nextEq]
                      exact ihs
                  | absturz habsturz =>
                      obtain ⟨_, nextEq⟩ := AbsturzSchritt.genau habsturz
                      rw [nextEq]
                      unfold Zustand.wiederanlauf
                      rw [ihs]

private theorem unit_keine_antwort {k : Katalog} (op : Instruction k) {h : Umgebung}
    {ρ : Lauf (unit op)} (lauf : Laeufe (unit op) h ρ)
    (t : Nat) (a : AntwortEreignis) (spur : SchrittSpur Nat UInt8) :
    ρ.zeit.spur t ≠ some (.antwort a, spur) := by
  intro heq
  have tak := ρ.zeit.takt t
  cases hv : ρ.zeit.zustand t with
  | none =>
      rw [hv] at tak
      cases tak with
      | wartet label _ _ => cases label.symm.trans heq
      | schritt _ laufstep => cases laufstep
  | some s0 =>
      rw [hv, heq] at tak
      generalize hN : ρ.zeit.zustand (t + 1) = nOpt at tak
      cases tak with
      | wartet label _ _ => cases label
      | schritt label laufstep =>
          cases laufstep with
          | schritt impl =>
              cases impl with
              | kontext _ _ _ _ => cases label
              | antwort _ hantwort =>
                  obtain ⟨angebot, _, _, _⟩ := hantwort
                  obtain ⟨q, hqmem, _, _⟩ := angebot.2.2.2.1
                  have leer := unit_fragen_leer_an op lauf t s0 hv
                  rw [leer] at hqmem
                  cases hqmem
              | interrupt _ _ => cases label
              | absturz _ => cases label

/-- A context step of a low-level unit records no public event: its plan is the internal plan,
    its trace is empty and the transfer leaves status and bookkeeping unchanged. -/
private theorem unit_kontext_still {k : Katalog} (op : Instruction k) {ρ : Lauf (unit op)}
    {predictor : Praediktor} {t : Nat} {c : Kontext} {wahl : PUnit} {spur : SchrittSpur Nat UInt8}
    (spurGlied : ρ.zeit.spur t = some (.kontext c wahl, spur)) :
    schrittBeob ρ predictor t = [] := by
  have tak := ρ.zeit.takt t
  rw [spurGlied] at tak
  generalize hS : ρ.zeit.zustand t = sOpt at tak
  generalize hN : ρ.zeit.zustand (t + 1) = nOpt at tak
  cases tak with
  | wartet label _ _ => cases label
      | schritt label laufstep =>
          cases laufstep with
          | schritt impl =>
              rename_i s sN
              cases impl with
              | kontext _ _ regel aus =>
                  cases label
                  obtain ⟨i, kopfI, implI⟩ := regel
                  obtain ⟨transfer, _, planEq, hu⟩ := Instruction.implTransfer (w := wahl) implI
                  cases (List.cons.inj planEq).1
                  simp only [unit] at aus
                  obtain ⟨traceEq, nextEq⟩ := Instruction.genauInternal aus
                  subst spur
                  rw [nextEq, hu] at hN
                  have hEnde : ∀ d, (neuBeendet s (transfer.apply c s) (unit op).etiketten d).isSome = false := by
                    intro d
                    unfold neuBeendet
                    have hst : (transfer.apply c s).status = s.status := rfl
                    rw [hst]
                    cases hd : s.status d <;> simp only [hd] <;> rfl
                  have hKeinEnde : ¬ ∃ d, (neuBeendet s (transfer.apply c s) (unit op).etiketten d).isSome = true := by
                    rintro ⟨d, hd⟩
                    rw [hEnde d] at hd
                    cases hd
                  have hbuch : (transfer.apply c s).buchung = s.buchung := rfl
                  have hcommit : commitBeob (Form := Instruction k) k.plattform s (transfer.apply c s) = [] := by
                    simp only [commitBeob, hbuch, List.drop_length, List.filterMap_nil]
                  have hausgabe : ausgabeBeob (unit op) c (s.lokal c) ((transfer.apply c s).lokal c) = [] := by
                    simp only [ausgabeBeob, unit, Flussdaten.leer, Flussdaten.ausgabeZuwachs,
                      List.drop_nil, List.filter_nil, List.map_nil]
                  have hzeit : zeitBeob ρ c (s.lokal c) ((transfer.apply c s).lokal c) = [] := by
                    simp only [zeitBeob, unit, Schrankendaten.leer, List.filter_nil, List.filterMap_nil]
                  have hspec : (k.plattform.spekulationshuelle).zugriffe ([] : List (Option Nat)) = [] := by
                    cases k.plattform.spekulationshuelle with
                    | mk fenster =>
                        cases fenster <;> simp only [Spekulationshuelle.zugriffe, List.filterMap_nil, List.take_nil]
                  have hcommitE : commitBeob (Form := Instruction k) (unit op).katalog.plattform s
                      (transfer.apply c s) = [] := by
                    simpa only [unit] using hcommit
                  have hKontext : kontextBeob ρ predictor t c s (transfer.apply c s) ⟨[], []⟩ = [] := by
                    unfold kontextBeob
                    dsimp only
                    rw [hcommitE, hausgabe, hzeit, kopfI]
                    simp only [unit, Flussdaten.leer, Bool.false_eq_true, if_false, hspec,
                      List.map_nil, List.nil_append, List.append_nil]
                  rw [schrittBeob, spurGlied, hS, hN]
                  simp only [List.filterMap_nil, List.flatMap_nil, hKontext, hKeinEnde, if_false,
                    List.nil_append]
              | antwort _ _ => cases label
              | interrupt _ _ => cases label
              | absturz _ => cases label

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
                                             hstat, hspurAus, hmem, haws⟩ := hinterrupt
                                           rw [auswahl₂none] at haws
                                           cases haws
                                      | antwort _ _ => cases label
                                      | absturz _ => cases label
                          | absturz =>
                              have tak₂ := ρ₂.zeit.takt t
                              rw [hz₂, hspurWahl] at tak₂
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
                                      | kontext _ bereit₂' regel₂ aus₂ =>
                                          have c_eq : c₂ = c := by
                                            obtain ⟨k₁, geleg₁, kern₁, _⟩ := bereit₁
                                            obtain ⟨k₂, geleg₂, kern₂, _⟩ := bereit₂'
                                            unfold HwLauf.gelegenheit at geleg₁ geleg₂
                                            have core₁ : (ρ₁.hw.angebot t).core = some k₁ := geleg₁
                                            have core₂ : (ρ₂.hw.angebot t).core = some k₂ := geleg₂
                                            have kk : k₁ = k₂ :=
                                              Option.some.inj (core₁.symm.trans (coreEq.trans core₂))
                                            have gleich : (v₂.kerne k₂).laeuft = some c := by
                                              rw [← kk, ← kerneEq]
                                              exact kern₁
                                            exact Option.some.inj (kern₂.symm.trans gleich)
                                          obtain ⟨j, kopf_j, implI₂⟩ := regel₂
                                          rw [c_eq] at kopf_j
                                          have jop : j = op := (Option.some.inj (kopf₂.symm.trans kopf_j)).symm
                                          subst j
                                          obtain ⟨transfer₂', eval₂', planEq₂, hu₂⟩ :=
                                            Instruction.implTransfer (w := w₂) implI₂
                                          rw [c_eq] at eval₂' hu₂ hspurWahl
                                          cases (List.cons.inj planEq₂).1
                                          simp only [unit] at aus₂
                                          rw [c_eq] at aus₂
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
                                              (t := t) (c := c) (wahl := w₂) (spur := spur₂) hspurWahl
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
