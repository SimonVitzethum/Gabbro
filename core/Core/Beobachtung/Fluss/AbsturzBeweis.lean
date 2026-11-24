module

public import Core.Beobachtung.Fluss.Absturz

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine Ast.Semantik

/-- A recorded crash tick forces the crash offer at that cut: the other three
    `ImplSchritt` constructors carry different labels, so only `absturz` remains. -/
private theorem absturz_offer_aus_tick
    {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]
    {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form}
    {ρ : Lauf E} {t : Nat} {spur : SchrittSpur Ort Wert}
    (tick : ρ.zeit.spur t = some (.absturz, spur)) : AbsturzAngeboten E.katalog ρ.hw t := by
  have takt := ρ.zeit.takt t
  generalize hspur : ρ.zeit.spur t = ev at tick takt
  cases takt with
  | wartet hl _ _ =>
    rw [hl] at tick
    cases tick
  | schritt hl step =>
    rw [hl] at tick
    cases tick
    generalize hzustand : ρ.zeit.zustand t = z at step
    generalize hnext : ρ.zeit.zustand (t + 1) = n at step
    cases step with
    | schritt impl =>
      cases impl with
      | absturz astep => exact astep.1

/-- The crash bit of the hardware offer is part of the public policy projection. -/
private theorem crash_angebot_gleich
    {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]
    {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form}
    {ρ₁ ρ₂ : Lauf E} (politik : GleichePolitik E ρ₁ ρ₂) (t : Nat) :
    (ρ₁.hw.angebot t).crash = (ρ₂.hw.angebot t).crash := by
  exact congrArg (fun p => (p.1 t).2.2.2.2.2.1) politik

/-- A forced crash emits exactly one public persistence-crash event and no
    end event: the restart state has no newly ended context. -/
private theorem crash_schrittBeob
    {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]
    {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form}
    {ρ : Lauf E} {t : Nat} (atCut : ∃ s, ρ.zeit.zustand t = some s)
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

private theorem forall2_append_singleton {α : Type} {R : α → α → Prop} {a b : List α} {x y : α}
    (h : List.Forall₂ R a b) (hx : R x y) : List.Forall₂ R (a ++ [x]) (b ++ [y]) := by
  induction h with
  | nil => exact .cons hx .nil
  | cons h₁ h₂ ih => exact .cons h₁ ih

/-- After a restart the discarded-and-consumed answer index is always at or
    past the end of the arrived list, so no context can take an answer. No
    separate `Verbrauch` invariant of the pre-state is needed. -/
private theorem wiederanlauf_keineAntwort
    {L Ort Wert Raum Lok Grund : Type}
    (s : Zustand L Ort Wert Raum Lok Grund)
    (w : Wiederanlauf Ort Wert Raum Lok Grund) (t : Nat) (p : PersistZustand) (c : Kontext) :
    (s.wiederanlauf w t p).naechsteAntwort c = none := by
  simp only [Zustand.wiederanlauf, Zustand.start, Zustand.naechsteAntwort]
  change (s.angekommen c)[(s.angekommen c).length - s.verbraucht c + s.verbraucht c]? = none
  apply List.getElem?_eq_none
  by_cases h : s.verbraucht c ≤ (s.angekommen c).length
  · rw [Nat.sub_add_cancel h]
  · have hlt : (s.angekommen c).length < s.verbraucht c := Nat.lt_of_not_ge h
    rw [Nat.sub_eq_zero_of_le hlt.le, Nat.zero_add]
    exact hlt.le

/-- When the two restart declarations derive the same start data and initial
    memory, the observable part of the two post-crash states agrees, even
    though their answer ledgers may differ. -/
private theorem wiederanlauf_beobachtungsgleich
    {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]
    (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    {s₁ s₂ : Zustand L Ort Wert Raum Lok Grund} {t : Nat}
    (datEq : E.einrichtung.wiederanlauf.daten (nachAbsturz s₁.persistenz).dauerhaft =
        E.einrichtung.wiederanlauf.daten (nachAbsturz s₂.persistenz).dauerhaft)
    (initEq : E.einrichtung.wiederanlauf.initial (nachAbsturz s₁.persistenz).dauerhaft =
        E.einrichtung.wiederanlauf.initial (nachAbsturz s₂.persistenz).dauerhaft) :
    QuellzustandGleich E
        (s₁.wiederanlauf E.einrichtung.wiederanlauf t (nachAbsturz s₁.persistenz))
        (s₂.wiederanlauf E.einrichtung.wiederanlauf t (nachAbsturz s₂.persistenz)) ∧
    (s₁.wiederanlauf E.einrichtung.wiederanlauf t (nachAbsturz s₁.persistenz)).epoche =
        (s₂.wiederanlauf E.einrichtung.wiederanlauf t (nachAbsturz s₂.persistenz)).epoche ∧
    (s₁.wiederanlauf E.einrichtung.wiederanlauf t (nachAbsturz s₁.persistenz)).geliefert =
        (s₂.wiederanlauf E.einrichtung.wiederanlauf t (nachAbsturz s₂.persistenz)).geliefert ∧
    (s₁.wiederanlauf E.einrichtung.wiederanlauf t (nachAbsturz s₁.persistenz)).kerne =
        (s₂.wiederanlauf E.einrichtung.wiederanlauf t (nachAbsturz s₂.persistenz)).kerne ∧
    (s₁.wiederanlauf E.einrichtung.wiederanlauf t (nachAbsturz s₁.persistenz)).status =
        (s₂.wiederanlauf E.einrichtung.wiederanlauf t (nachAbsturz s₂.persistenz)).status := by
  let w := E.einrichtung.wiederanlauf
  let p₁ := nachAbsturz s₁.persistenz
  let p₂ := nachAbsturz s₂.persistenz
  have datEq' : w.daten p₁.dauerhaft = w.daten p₂.dauerhaft := by
    simpa only [w, p₁] using datEq
  have initEq' : w.initial p₁.dauerhaft = w.initial p₂.dauerhaft := by
    simpa only [w, p₁] using initEq
  have kerneEq : (s₁.wiederanlauf w t p₁).kerne = (s₂.wiederanlauf w t p₂).kerne := by
    simp only [Zustand.wiederanlauf]
    rw [datEq']
  have statusEq : (s₁.wiederanlauf w t p₁).status = (s₂.wiederanlauf w t p₂).status := by
    rfl
  refine ⟨?_, by rfl, by rfl, kerneEq, statusEq⟩
  unfold QuellzustandGleich
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c q hq
    simp only [Zustand.wiederanlauf, Zustand.start]
    rw [datEq']
  · intro c
    simp only [Zustand.wiederanlauf, Zustand.start]
    rw [statusEq]
  · intro x
    simp only [Zustand.wiederanlauf, Zustand.start]
    rw [initEq']
  · simp only [Zustand.wiederanlauf, Zustand.start]
    rw [datEq']
  · rfl
  · intro c
    simp only [AntwortSicht]
    rw [wiederanlauf_keineAntwort s₁ w t p₁ c, wiederanlauf_keineAntwort s₂ w t p₂ c]

theorem absturzNI : AbsturzNIAussage := by
  intro p plattform h₁ h₂ ρ₁ ρ₂ vergleich predictor t w spur tick formw kopplung
  cases w with
  | kontext _ _ => cases formw
  | antwort _ => cases formw
  | interrupt _ => cases formw
  | absturz =>
    let E := p.einheit plattform
    obtain ⟨cov, st, len⟩ := kopplung
    have offer₁ : AbsturzAngeboten E.katalog ρ₁.hw t := absturz_offer_aus_tick tick
    obtain ⟨s₁, hs₁⟩ := fragment_zustand_some vergleich.links t
    obtain ⟨s₂, hs₂⟩ := fragment_zustand_some vergleich.rechts t
    have offer₂ : AbsturzAngeboten E.katalog ρ₂.hw t :=
      ⟨offer₁.1, by rw [← crash_angebot_gleich vergleich.politik t]; exact offer₁.2⟩
    have crash₁ := crash_schrittBeob (ρ := ρ₁) ⟨s₁, hs₁⟩ offer₁ (p := predictor)
    have crash₂ := crash_schrittBeob (ρ := ρ₂) ⟨s₂, hs₂⟩ offer₂ (p := predictor)
    have trace₁ : NiedrigeBeob E ρ₁ predictor (t + 1) =
        NiedrigeBeob E ρ₁ predictor t ++ [.katalog (.persistenz .crash)] := by
      change NiedrigeBeob E ρ₁ predictor t ++ schrittBeob ρ₁ predictor t = _
      rw [crash₁]
    have trace₂ : NiedrigeBeob E ρ₂ predictor (t + 1) =
        NiedrigeBeob E ρ₂ predictor t ++ [.katalog (.persistenz .crash)] := by
      change NiedrigeBeob E ρ₂ predictor t ++ schrittBeob ρ₂ predictor t = _
      rw [crash₂]
    have cov' : List.Forall₂ (EreignisAequiv E.fluss.freigabe)
        (NiedrigeBeob E ρ₁ predictor t) (NiedrigeBeob E ρ₂ predictor t) := by
      rw [len, List.take_length] at cov
      exact cov
    have prefix : List.Forall₂ (EreignisAequiv E.fluss.freigabe)
        (NiedrigeBeob E ρ₁ predictor (t + 1))
        ((NiedrigeBeob E ρ₂ predictor (t + 1)).take (NiedrigeBeob E ρ₁ predictor (t + 1)).length) := by
      rw [trace₁, trace₂]
      have hlen : (NiedrigeBeob E ρ₁ predictor t ++ [.katalog (.persistenz .crash)]).length =
          (NiedrigeBeob E ρ₂ predictor t ++ [.katalog (.persistenz .crash)]).length := by
        simp only [List.length_append, List.length_singleton, len]
      rw [hlen, List.take_length]
      exact forall2_append_singleton cov' (.gleich _)
    obtain ⟨n₁, tick₁eq, hn₁, step₁⟩ := absturz_am_schnitt (ρ := ρ₁) hs₁ offer₁
    obtain ⟨n₂, tick₂eq, hn₂, step₂⟩ := absturz_am_schnitt (ρ := ρ₂) hs₂ offer₂
    have datEq : E.einrichtung.wiederanlauf.daten (nachAbsturz s₁.persistenz).dauerhaft =
        E.einrichtung.wiederanlauf.daten (nachAbsturz s₂.persistenz).dauerhaft := by
      simp only [E, Ast.Semantik.Fragment.einheit, Ast.Semantik.einrichtung]
    have initEq : E.einrichtung.wiederanlauf.initial (nachAbsturz s₁.persistenz).dauerhaft =
        E.einrichtung.wiederanlauf.initial (nachAbsturz s₂.persistenz).dauerhaft := by
      simp only [E, Ast.Semantik.Fragment.einheit, Ast.Semantik.einrichtung]
    refine ⟨prefix, ?_, ?_⟩
    · intro v w' hv hw
      have eqv : v = n₁ := Option.some.inj (hv.symm.trans hn₁)
      have eqw : w' = n₂ := Option.some.inj (hw.symm.trans hn₂)
      subst v
      subst w'
      rw [step₁.genau.2, step₂.genau.2]
      exact wiederanlauf_beobachtungsgleich E datEq initEq
    · rw [trace₁, trace₂]
      simp only [List.length_append, List.length_singleton, len]

end Gabbro.Core.Beobachtung
