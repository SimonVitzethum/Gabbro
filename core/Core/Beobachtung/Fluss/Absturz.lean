module

public import Core.Beobachtung.Fluss.Fragment

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine Ast.Semantik

private theorem absturz_angebot_aus_spur {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form}
    [DecidableEq L] {ρ : Lauf E} {t spur}
    (h : ρ.zeit.spur t = some (.absturz, spur)) : AbsturzAngeboten E.katalog ρ.hw t := by
  have ht := ρ.zeit.takt t
  generalize hspur : ρ.zeit.spur t = ev at h ht
  cases ht with
  | wartet hl _ _ =>
    rw [hl] at h
    cases h
  | schritt hl step =>
    rw [hl] at h
    cases h
    generalize hzustand : ρ.zeit.zustand t = z at step
    generalize hnext : ρ.zeit.zustand (t + 1) = n at step
    cases step with
    | schritt impl =>
      cases impl with
      | absturz astep => exact astep.1

private theorem zustand_aus_spur {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form}
    [DecidableEq L] {ρ : Lauf E} {t spur}
    (h : ρ.zeit.spur t = some (.absturz, spur)) :
    ∃ s n, ρ.zeit.zustand t = some s ∧ ρ.zeit.zustand (t + 1) = some n := by
  have ht := ρ.zeit.takt t
  generalize hspur : ρ.zeit.spur t = ev at h ht
  cases ht with
  | wartet hl _ _ =>
    rw [hl] at h
    cases h
  | schritt hl step =>
    rw [hl] at h
    cases h
    generalize hzustand : ρ.zeit.zustand t = z at step
    generalize hnext : ρ.zeit.zustand (t + 1) = n at step
    cases step with
    | schritt impl =>
      cases impl with
      | absturz astep => exact ⟨_, _, rfl, rfl⟩

private theorem schrittBeob_absturz {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form}
    [DecidableEq L] {ρ : Lauf E} {t}
    (atCut : ∃ s, ρ.zeit.zustand t = some s)
    (offer : AbsturzAngeboten E.katalog ρ.hw t) {p : Praediktor} :
    schrittBeob ρ p t = [.katalog (.persistenz .crash)] := by
  obtain ⟨s, hs⟩ := atCut
  obtain ⟨n, hspur, hn, hstep⟩ := absturz_am_schnitt (ρ := ρ) hs offer
  have keinEnde : ∀ c, (neuBeendet s n E.etiketten c).isNone = true := by
    intro c
    rw [hstep.genau.2]
    by_cases hc : c = E.einrichtung.wiederanlauf.eintritt
    · simp only [Zustand.wiederanlauf, Zustand.start, neuBeendet, hc, if_pos, if_neg]
      cases s.status E.einrichtung.wiederanlauf.eintritt <;> rfl
    · simp only [Zustand.wiederanlauf, Zustand.start, neuBeendet, hc, if_pos, if_neg]
      cases s.status c <;> rfl
  have keineAussage : ¬ ∃ c, (neuBeendet s n E.etiketten c).isSome = true := by
    rintro ⟨c, hc⟩
    have hnone := keinEnde c
    cases hne : neuBeendet s n E.etiketten c with
    | none => simp only [hne] at hc; cases hc
    | some e => simp only [hne] at hnone; cases hnone
  simp only [schrittBeob, hspur, hs, hn, absturzSpur, List.nil_append,
    aussenBeob, List.nil_append]
  rw [if_neg keineAussage]
  rfl

private theorem angebot_gleich {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form}
    [DecidableEq L] {ρ₁ ρ₂ : Lauf E} (politik : GleichePolitik E ρ₁ ρ₂) (t : Nat) :
    (ρ₁.hw.angebot t).crash = (ρ₂.hw.angebot t).crash := by
  exact congrArg (fun p => (p.1 t).2.2.2.2.2.1) politik

private theorem niedrigeBeob_prefix {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form}
    [DecidableEq L] (ρ : Lauf E) (predictor : Praediktor) {a b : Nat} (h : a ≤ b) :
    ∃ rest, NiedrigeBeob E ρ predictor b = NiedrigeBeob E ρ predictor a ++ rest := by
  induction h with
  | refl => exact ⟨[], by rw [List.append_nil]⟩
  | @step b hab ih =>
    obtain ⟨rest, hrest⟩ := ih
    refine ⟨rest ++ schrittBeob ρ predictor b, ?_⟩
    change NiedrigeBeob E ρ predictor b ++ schrittBeob ρ predictor b = _
    rw [hrest, List.append_assoc]

/-- The stronger invariant: comparison runs have low traces of equal length at every cut. -/
def GleicheNiedrigLaenge (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    [DecidableEq L] (ρ₁ ρ₂ : Lauf E) : Prop :=
  ∀ predictor t, (NiedrigeBeob E ρ₁ predictor t).length =
    (NiedrigeBeob E ρ₂ predictor t).length

private theorem forall2_append_singleton {α : Type} {R : α → α → Prop} {a b : List α} {x y : α}
    (h : List.Forall₂ R a b) (hx : R x y) : List.Forall₂ R (a ++ [x]) (b ++ [y]) := by
  induction h with
  | nil => exact .cons hx .nil
  | cons h₁ h₂ ih => exact .cons h₁ ih

/-- Under equal low-trace lengths, a crash at t preserves prefix coverage. -/
theorem absturzNI_aus_laengengleichheit (p : Fragment) (plattform : Plattform)
    {h₁ h₂ : Umgebung} {ρ₁ ρ₂ : Lauf (p.einheit plattform)}
    (v : Vergleich (p.einheit plattform) h₁ h₂ ρ₁ ρ₂)
    (laengen : GleicheNiedrigLaenge (p.einheit plattform) ρ₁ ρ₂)
    {predictor t spur} (tick₁ : ρ₁.zeit.spur t = some (.absturz, spur))
    (atCut₂ : ∃ s, ρ₂.zeit.zustand t = some s) :
    PraefixAbgedeckt (p.einheit plattform) ρ₁ ρ₂ predictor t →
      PraefixAbgedeckt (p.einheit plattform) ρ₁ ρ₂ predictor (t + 1) := by
  intro abgedeckt
  let E := p.einheit plattform
  have offer₁ := absturz_angebot_aus_spur tick₁
  have atCut₁ := zustand_aus_spur tick₁
  have offer₂ : AbsturzAngeboten E.katalog ρ₂.hw t :=
    ⟨offer₁.1, by rw [← angebot_gleich v.politik t]; exact offer₁.2⟩
  obtain ⟨s, n, hs, hn⟩ := zustand_aus_spur tick₁
  have atCut₁' : ∃ s, ρ₁.zeit.zustand t = some s := ⟨s, hs⟩
  have crash₁ := schrittBeob_absturz (ρ := ρ₁) (t := t) atCut₁' offer₁ (p := predictor)
  have crash₂ := schrittBeob_absturz (ρ := ρ₂) (t := t) atCut₂ offer₂ (p := predictor)
  have trace₁ : NiedrigeBeob E ρ₁ predictor (t + 1) =
      NiedrigeBeob E ρ₁ predictor t ++ [.katalog (.persistenz .crash)] := by
    change NiedrigeBeob E ρ₁ predictor t ++ schrittBeob ρ₁ predictor t = _
    rw [crash₁]
  have trace₂ : NiedrigeBeob E ρ₂ predictor (t + 1) =
      NiedrigeBeob E ρ₂ predictor t ++ [.katalog (.persistenz .crash)] := by
    change NiedrigeBeob E ρ₂ predictor t ++ schrittBeob ρ₂ predictor t = _
    rw [crash₂]
  unfold PraefixAbgedeckt at abgedeckt ⊢
  obtain ⟨u, hu⟩ := abgedeckt
  let L₁ := NiedrigeBeob E ρ₁ predictor t
  let L₂ := NiedrigeBeob E ρ₂ predictor t
  let crashEvent : NiedrigesEreignis PUnit.{1} Int PUnit.{1} Befehl :=
    .katalog (.persistenz .crash)
  have len : L₁.length = L₂.length := laengen predictor t
  have lenU : L₁.length ≤ (NiedrigeBeob E ρ₂ predictor u).length := by
    have hmin : L₁.length = min L₁.length (NiedrigeBeob E ρ₂ predictor u).length := by
      simpa only [List.length_take] using hu.length_eq
    rw [hmin]
    exact Nat.min_le_right _ _
  have takeUGleich : (NiedrigeBeob E ρ₂ predictor u).take L₁.length = L₂ := by
    rcases le_total u t with hut | htu
    · obtain ⟨rest, hrest⟩ := niedrigeBeob_prefix ρ₂ predictor hut
      have hlenrest := congrArg List.length hrest
      rw [List.length_append] at hlenrest
      have heqadd : L₂.length = (NiedrigeBeob E ρ₂ predictor u).length + rest.length := by
        simpa [L₂] using hlenrest
      have hleadd : (NiedrigeBeob E ρ₂ predictor u).length + rest.length ≤
          (NiedrigeBeob E ρ₂ predictor u).length := by
        rw [← heqadd, ← len]
        exact lenU
      have heqrest : (NiedrigeBeob E ρ₂ predictor u).length + rest.length =
          (NiedrigeBeob E ρ₂ predictor u).length + 0 :=
        le_antisymm hleadd (Nat.le_add_right _ _)
      have hrestlen0 : rest.length = 0 := Nat.add_left_cancel heqrest
      cases rest with
      | nil =>
        simp only [List.append_nil] at hrest
        rw [← hrest]
        change (NiedrigeBeob E ρ₂ predictor t).take L₁.length = L₂
        rw [len]
        exact List.take_length
      | cons x xs => simp at hrestlen0
    · obtain ⟨rest, hrest⟩ := niedrigeBeob_prefix ρ₂ predictor htu
      rw [hrest]
      change List.take L₁.length (L₂ ++ rest) = L₂
      rw [len]
      exact List.take_left
  have hu' : List.Forall₂ (EreignisAequiv E.fluss.freigabe) L₁ L₂ := by
    rw [takeUGleich] at hu
    exact hu
  have takeGleich : (NiedrigeBeob E ρ₂ predictor (t + 1)).take L₁.length = L₂ := by
    rw [trace₂]
    change List.take L₁.length (L₂ ++ [crashEvent]) = L₂
    rw [len]
    exact List.take_left
  refine ⟨t + 1, ?_⟩
  rw [trace₁, trace₂, List.length_append, List.length_singleton]
  have htake : (L₂ ++ [crashEvent]).take (L₁.length + 1) = L₂ ++ [crashEvent] := by
    rw [show L₁.length + 1 = (L₂ ++ [crashEvent]).length by simp only [List.length_append, List.length_singleton, len]]
    simpa using (List.take_length (L₂ ++ [crashEvent]))
  rw [htake]
  exact forall2_append_singleton hu' (.gleich _)

def AbsturzNIAussage : Prop :=
  ProtokollwahlNI fun
    | .absturz => True
    | _ => False

end Gabbro.Core.Beobachtung
