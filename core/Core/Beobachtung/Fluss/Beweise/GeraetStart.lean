module

public import Core.Beobachtung.Fluss.Beweise.GeraetKopplung
public import Core.Ast.LowLevel.DeviceUnit

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine
open Gabbro.Core.Ast.LowLevel.Device

/-- Public source-state equality is reflexive for every unit. -/
theorem geraet_quellgleich_refl {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type}
    {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form} (v : Zustand L Ort Wert Raum Lok Grund) :
    QuellzustandGleich E v v := by
  refine ⟨?_, ?_, ?_, rfl, rfl, ?_⟩
  · intro c p _
    rfl
  · intro c
    rfl
  · intro x
    rfl
  · intro c
    rfl

/-- The device loader installs empty ledgers: a successful load starts with no
    question, no history, no answer and no consumption. -/
theorem geraete_laden_ledger_leer {k : Katalog} {scope : Gabbro.Core.Ast.Scope}
    {locals : Gabbro.Core.Ast.Umgebung scope} {d : Denotation k scope}
    {start : AussenStart} {load : Ladung} {z : State}
    (geladen : ((d.unit locals).laden start load) = some z) :
    z.fragen = [] ∧ z.verlauf = [] ∧ z.antworten = [] ∧ z.verbraucht = fun _ => 0 := by
  unfold Denotation.unit Gabbro.Core.Ast.LowLevel.Device.unit at geladen
  dsimp only at geladen
  split at geladen
  · obtain rfl := Option.some.inj geladen
    exact ⟨rfl, rfl, rfl, rfl⟩
  · cases geladen

/-- The two device loads coincide under a compared start: the load bytes and
    starts agree through the low environment projection, and the boot core
    agrees through the low start projection. Hence both runs load the same
    implementation state. -/
theorem geraete_laden_gleich {k : Katalog} {scope : Gabbro.Core.Ast.Scope}
    {locals : Gabbro.Core.Ast.Umgebung scope} {d : Denotation k scope}
    {h₁ h₂ : Umgebung} {s₁ s₂ : AussenStart}
    (umgebung : GleicheNiedrigeUmgebung (d.unit locals) h₁ h₂)
    (start : NiedrigGleich (d.unit locals) s₁ s₂) :
    (d.unit locals).laden s₁ (h₁.lade (d.unit locals).bild) =
      (d.unit locals).laden s₂ (h₂.lade (d.unit locals).bild) := by
  have hladeFun := congrArg (fun p => p.2.2.2.2.1) umgebung
  have hbild := congrFun hladeFun (d.unit locals).bild
  have hstarts : (h₁.lade (d.unit locals).bild).starts = (h₂.lade (d.unit locals).bild).starts := by
    have h := congrArg (fun b : Ladebild => b.starts) hbild
    simp only at h
    exact h
  have hbytes : (h₁.lade (d.unit locals).bild).bytes = (h₂.lade (d.unit locals).bild).bytes := by
    have h := congrArg (fun b : Ladebild => b.startBytes) hbild
    simp only [Bild.beobachtung] at h
    exact h
  have hassign : s₁.assignment = s₂.assignment :=
    congrArg (fun p => p.2.1) start
  have hstarts0 : (h₁.lade (d.unit locals).bild).starts 0 = (h₂.lade (d.unit locals).bild).starts 0 := by
    simp only [hstarts]
  have hbytes0 : (h₁.lade (d.unit locals).bild).bytes 0 = (h₂.lade (d.unit locals).bild).bytes 0 := by
    simp only [hbytes]
  have hcore : s₁.assignment 0 = s₂.assignment 0 := by
    simp only [hassign]
  have hmed : Gabbro.Core.Ast.LowLevel.medium s₁ = Gabbro.Core.Ast.LowLevel.medium s₂ := rfl
  simp only [Denotation.unit, Gabbro.Core.Ast.LowLevel.Device.unit] at ⊢
  by_cases hcond : (h₁.lade (d.unit locals).bild).starts 0 = some 0 ∧
      (h₁.lade (d.unit locals).bild).bytes 0 = some 0
  · have hcond₂ : (h₂.lade (d.unit locals).bild).starts 0 = some 0 ∧
        (h₂.lade (d.unit locals).bild).bytes 0 = some 0 := by
      obtain ⟨hs, hb⟩ := hcond
      exact ⟨hstarts0 ▸ hs, hbytes0 ▸ hb⟩
    rw [if_pos hcond, if_pos hcond₂, hcore, hmed]
  · have hcond₂ : ¬ ((h₂.lade (d.unit locals).bild).starts 0 = some 0 ∧
        (h₂.lade (d.unit locals).bild).bytes 0 = some 0) := by
      intro hcon
      apply hcond
      obtain ⟨hs, hb⟩ := hcon
      exact ⟨hstarts0.trans hs, hbytes0.trans hb⟩
    rw [if_neg hcond, if_neg hcond₂]

/-- The strengthened coupling holds at cut zero for every compared device run:
    both runs load the same state, so the low prefixes, the public states, the
    machine fields and the four ledgers all agree. -/
theorem geraete_start_kopplungAussage {k : Katalog} {scope : Gabbro.Core.Ast.Scope}
    {locals : Gabbro.Core.Ast.Umgebung scope} {d : Denotation k scope}
    {h₁ h₂ : Umgebung} {ρ₁ ρ₂ : Lauf (d.unit locals)}
    (vergleich : Vergleich (d.unit locals) h₁ h₂ ρ₁ ρ₂) (predictor : Praediktor) :
    GeraeteKopplungAussage (d.unit locals) ρ₁ ρ₂ predictor 0 0 := by
  have ladenEq := geraete_laden_gleich (d := d) vergleich.umgebung vergleich.start
  have zustand₁ : ρ₁.zeit.zustand 0 = (d.unit locals).laden ρ₁.start (h₁.lade (d.unit locals).bild) :=
    vergleich.links.2.2.2
  have zustand₂ : ρ₂.zeit.zustand 0 = (d.unit locals).laden ρ₂.start (h₂.lade (d.unit locals).bild) :=
    vergleich.rechts.2.2.2
  have zustandEq : ρ₁.zeit.zustand 0 = ρ₂.zeit.zustand 0 := by
    simp only [zustand₁, zustand₂, ladenEq]
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · have hpre : NiedrigeBeob (d.unit locals) ρ₁ predictor 0 =
          NiedrigeBeob (d.unit locals) ρ₂ predictor 0 := by
        simp only [NiedrigeBeob, NiedrigeBeob.praefix, zustandEq]
      have hrefl : ∀ L : List (NiedrigesEreignis Nat UInt8 PUnit PUnit),
          List.Forall₂ (EreignisAequiv (d.unit locals).fluss.freigabe) L L := by
        intro L
        induction L with
        | nil => exact List.Forall₂.nil
        | cons x xs ih => exact List.Forall₂.cons (EreignisAequiv.gleich x) ih
      simp only [hpre, List.take_length]
      exact hrefl _
    · intro v w hv hw
      have vw : v = w := Option.some.inj (hv.symm.trans (zustandEq.trans hw))
      subst vw
      exact ⟨geraet_quellgleich_refl _, rfl, rfl, rfl, rfl⟩
    · have hpre : NiedrigeBeob (d.unit locals) ρ₁ predictor 0 =
          NiedrigeBeob (d.unit locals) ρ₂ predictor 0 := by
        simp only [NiedrigeBeob, NiedrigeBeob.praefix, zustandEq]
      simp only [hpre]
  · intro v w hv hw
    have vw : v = w := Option.some.inj (hv.symm.trans (zustandEq.trans hw))
    subst vw
    exact GeraeteLedgerGleichAussage.refl _

end Gabbro.Core.Beobachtung
