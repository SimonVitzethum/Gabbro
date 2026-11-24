module

public import Core.Beobachtung.Fluss.Beschriftung.AufrufSchleife
public import Core.Beobachtung.Fluss.Beschriftung.AufgabenBeweise

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Beobachtung Katalog

/-- The view of a frame after a counter-touching program-counter change. Control state, in
    particular the counter table, is copied by `Rahmen.sicht` unchanged. -/
theorem sicht_pcZaehler_ansicht (β : Beschriftung) (r : Rahmen) (q : Nat) (z : Option Nat) :
    ({ r with pc := q, zaehler := Function.update r.zaehler r.pc z } : Rahmen).sicht β =
      { r.sicht β with
        pc := q
        temp := fun s => if oeffentlich (β.temp q s) = true then r.temp s else none
        lokale := maskiere (β.lokal q) 0 r.lokale
        zaehler := Function.update r.zaehler r.pc z } := rfl

/-- A counter-touching program-counter change keeps equal views when the labels at the new
    position are at least as secret. -/
theorem sicht_pcZaehler (β : Beschriftung) (q₁ q₂ : Nat) (z : Option Nat)
    (r₁ r₂ : Rahmen)
    (hT : ∀ s, oeffentlich (β.temp q₁ s) = true → oeffentlich (β.temp r₁.pc s) = true)
    (hL : ∀ i, oeffentlich (β.lokal q₁ i) = true → oeffentlich (β.lokal r₁.pc i) = true)
    (h : r₁.sicht β = r₂.sicht β) (hq : q₁ = q₂) :
    ({ r₁ with pc := q₁, zaehler := Function.update r₁.zaehler r₁.pc z } : Rahmen).sicht β =
      ({ r₂ with pc := q₂, zaehler := Function.update r₂.zaehler r₂.pc z } : Rahmen).sicht β := by
  subst hq
  obtain ⟨pcEq, tempPub, lokEq⟩ := sicht_oeffentliche_teile h
  have hTe : (fun s => if oeffentlich (β.temp q₁ s) = true then r₁.temp s else none) =
      (fun s => if oeffentlich (β.temp q₁ s) = true then r₂.temp s else none) := by
    funext s
    by_cases hp : oeffentlich (β.temp q₁ s) = true
    · simp only [hp, if_true]
      exact tempPub s (hT s hp)
    · simp only [if_neg hp]
  have hLe : maskiere (β.lokal q₁) 0 r₁.lokale = maskiere (β.lokal q₁) 0 r₂.lokale :=
    maskiere_gleich_mono hL 0 _ _ lokEq
  have hZaehler : r₁.zaehler = r₂.zaehler := by
    simpa only [Rahmen.sicht] using congrArg (fun r : Rahmen => (r.sicht β).zaehler) h
  rw [sicht_pcZaehler_ansicht, sicht_pcZaehler_ansicht, h, hTe, hLe, hZaehler, pcEq]

/-- A pass with a public test keeps equal views: the two counter-reading branches change only
    the program counter and the always-visible counter table, the overflow branch halts. -/
theorem passSicht (β : Beschriftung) (pc : Nat) (test : Bool) (exit : Nat)
    (handler : Option Identifier)
    (hs : ∀ q, q = pc + 1 ∨ q = pc + exit →
      (∀ s, oeffentlich (β.temp q s) = true → oeffentlich (β.temp pc s) = true) ∧
      (∀ i, oeffentlich (β.lokal q i) = true → oeffentlich (β.lokal pc i) = true))
    (r₁ r₂ : Rahmen) (hpc : r₁.pc = pc) (h : r₁.sicht β = r₂.sicht β) :
    (r₁.pass test exit handler).sicht β = (r₂.pass test exit handler).sicht β := by
  subst hpc
  obtain ⟨pcEq, _, _⟩ := sicht_oeffentliche_teile h
  have hZaehler : r₁.zaehler = r₂.zaehler := by
    simpa only [Rahmen.sicht] using congrArg (fun r : Rahmen => (r.sicht β).zaehler) h
  have hzGleich : r₁.zaehler r₁.pc = r₂.zaehler r₂.pc := by
    rw [hZaehler, pcEq]
  simp only [Rahmen.pass, hzGleich]
  by_cases hcond : (!test) = true
  · simp only [hcond, if_true]
    have hs' := hs (r₁.pc + exit) (Or.inr rfl)
    exact sicht_pcZaehler β (r₁.pc + exit) (r₂.pc + exit) none r₁ r₂
      hs'.1 hs'.2 h (by rw [pcEq])
  · simp only [hcond, Bool.false_eq_true, if_false]
    cases hz : r₂.zaehler r₂.pc with
    | none =>
      simp only [hz, sicht_halt]
      rw [h]
    | some n =>
      cases n with
      | zero =>
        simp only [hz, sicht_halt]
        rw [h]
      | succ n =>
        simp only [hz]
        have hs' := hs (r₁.pc + 1) (Or.inl rfl)
        exact sicht_pcZaehler β (r₁.pc + 1) (r₂.pc + 1) (some n) r₁ r₂
          hs'.1 hs'.2 h (by rw [pcEq])

/-- The identity monad's `pure` does not change the frame or its view. -/
theorem sicht_pure (β : Beschriftung) (r : Rahmen) : (pure r : Id Rahmen).sicht β = r.sicht β := by
  rfl

/-- A halt in the identity monad has the same view as a direct halt. -/
theorem sicht_halt_pure (β : Beschriftung) (r : Rahmen) (grund : Abschluss) :
    (pure (r.halt grund) : Id Rahmen).sicht β = { r.sicht β with stopp := some grund } := by
  change (r.halt grund).sicht β = _
  exact sicht_halt β r grund

/-- Equal views and a public local 0 give equal joined heads of the local stack. -/
theorem sicht_lokal0 (β : Beschriftung) (r₁ r₂ : Rahmen)
    (h0 : oeffentlich (β.lokal r₁.pc 0) = true)
    (h : r₁.sicht β = r₂.sicht β) :
    r₁.lokale.head?.join = r₂.lokale.head?.join := by
  obtain ⟨_, _, lokEq⟩ := sicht_oeffentliche_teile h
  simpa only [List.head?_eq_getElem?] using
    (maskiere_eintrag 0 r₁.lokale r₂.lokale 0 lokEq h0)

/-- `whileTest`: a public test forks public control; both successors keep the labels at
    least as secret and both counter-reading branches are handled by `passSicht`. -/
theorem whileTestSicht : WhileTestSichtAussage := by
  intro β pc quelle ende handler hq hs r₁ r₂ live hpc h
  subst hpc
  obtain ⟨pcEq, tempPub, _⟩ := sicht_oeffentliche_teile h
  have gleich : r₁.temp quelle = r₂.temp quelle := tempPub quelle hq
  simp only [Befehl.auswerten, pcEq, gleich]
  cases hB : (r₂.temp quelle).bind alsBoolean with
  | none =>
    simp only [hB, sicht_halt]
    rw [h]
  | some test =>
    simp only [hB]
    exact passSicht β r₁.pc test ende (some handler) hs r₁ r₂ rfl h

/-- The view after the pushing branch of `forAnfang`: the program counter advances by one,
    one freshly converted local is pushed, and the always-visible bound and counter tables
    gain one entry. -/
theorem sicht_forAnfang_push (β : Beschriftung) (r : Rahmen) (initial : Dynamisch) (next : Nat)
    (b : Ganzzahl) (d : Nat) :
    ({ r with
      pc := next
      lokale := some initial :: r.lokale
      obergrenzen := Function.update r.obergrenzen next (some b)
      zaehler := Function.update r.zaehler next (some d) } : Rahmen).sicht β =
      { r.sicht β with
        pc := next
        temp := fun s => if oeffentlich (β.temp next s) = true then r.temp s else none
        lokale := maskiere (β.lokal next) 0 (some initial :: r.lokale)
        obergrenzen := Function.update r.obergrenzen next (some b)
        zaehler := Function.update r.zaehler next (some d) } := rfl

theorem sicht_forAnfang_push_pure (β : Beschriftung) (r : Rahmen) (initial : Dynamisch) (next : Nat)
    (b : Ganzzahl) (d : Nat) :
    (pure ({ r with
      pc := next
      lokale := some initial :: r.lokale
      obergrenzen := Function.update r.obergrenzen next (some b)
      zaehler := Function.update r.zaehler next (some d) } : Rahmen) : Id Rahmen).sicht β =
      { r.sicht β with
        pc := next
        temp := fun s => if oeffentlich (β.temp next s) = true then r.temp s else none
        lokale := maskiere (β.lokal next) 0 (some initial :: r.lokale)
        obergrenzen := Function.update r.obergrenzen next (some b)
        zaehler := Function.update r.zaehler next (some d) } := by
  change ({ r with
    pc := next
    lokale := some initial :: r.lokale
    obergrenzen := Function.update r.obergrenzen next (some b)
    zaehler := Function.update r.zaehler next (some d) } : Rahmen).sicht β = _
  rfl

/-- `forAnfang`: two public bounds decide between halt, jump and push. The push follows the
    `installSchemaSicht` pattern with the lower bound at the head of the fresh local. -/
theorem forAnfangSicht : ForAnfangSichtAussage := by
  intro β pc unter ober index skipEmpty shadowed missingHandler hunter hober
    hT hL hKopf hsTemp hsLok r₁ r₂ live hpc h
  subst hpc
  obtain ⟨pcEq, tempPub, lokEq⟩ := sicht_oeffentliche_teile h
  have hZUnter : r₁.zahl unter = r₂.zahl unter := by
    simp only [Rahmen.zahl, tempPub unter hunter]
  have hZOber : r₁.zahl ober = r₂.zahl ober := by
    simp only [Rahmen.zahl, tempPub ober hober]
  have hObergrenzen : r₁.obergrenzen = r₂.obergrenzen := by
    simpa only [Rahmen.sicht] using congrArg (fun r : Rahmen => (r.sicht β).obergrenzen) h
  have hZaehler : r₁.zaehler = r₂.zaehler := by
    simpa only [Rahmen.sicht] using congrArg (fun r : Rahmen => (r.sicht β).zaehler) h
  simp only [Befehl.auswerten, Id.run, pcEq, hZUnter, hZOber]
  cases hzA : r₂.zahl unter with
  | none =>
    simp only [hzA, sicht_halt_pure]
    rw [h]
  | some a =>
    cases hzB : r₂.zahl ober with
    | none =>
      simp only [hzA, hzB, sicht_halt_pure]
      rw [h]
    | some b =>
      simp only [hzA, hzB]
      by_cases hbad :
          (shadowed || (missingHandler && decide (a.zahl.wert < b.zahl.wert))) = true
      · simp only [if_pos hbad, sicht_halt_pure]
        rw [h]
      · simp only [if_neg hbad]
        by_cases hle : b.zahl.wert ≤ a.zahl.wert
        · simp only [if_pos hle]
          exact sicht_pcWechsel hsTemp hsLok h
        · simp only [if_neg hle]
          cases hwi : wertIn index a.pack with
          | none =>
            simp only [hwi, sicht_halt_pure]
            rw [h]
          | some initial =>
            simp only [hwi]
            have hTe :
                (fun s => if oeffentlich (β.temp (r₁.pc + 1) s) = true then r₁.temp s else none) =
                (fun s => if oeffentlich (β.temp (r₁.pc + 1) s) = true then r₂.temp s else none) := by
              funext s
              by_cases hp : oeffentlich (β.temp (r₁.pc + 1) s) = true
              · simp only [hp, if_true]
                exact tempPub s (hT s hp)
              · simp only [if_neg hp]
            have hLe := maskiere_einschieben (l₀ := β.lokal r₁.pc) (l₁ := β.lokal (r₁.pc + 1))
              (xs := r₁.lokale) (ys := r₂.lokale) (v₁ := some initial) (v₂ := some initial)
              hL (fun _ => rfl) lokEq
            rw [sicht_forAnfang_push_pure, sicht_forAnfang_push_pure,
              h, hTe, hLe, hObergrenzen, hZaehler]

/-- `forTest`: a public local 0 gives the same test; the pass branches are handled just as
    for `whileTest`. -/
theorem forTestSicht : ForTestSichtAussage := by
  intro β pc ende handler h0 hs r₁ r₂ live hpc h
  subst hpc
  obtain ⟨pcEq, _, _⟩ := sicht_oeffentliche_teile h
  have hKopf : r₁.lokale.head?.join = r₂.lokale.head?.join := sicht_lokal0 β r₁ r₂ h0 h
  have hCurrent : r₁.lokale.head?.join.bind alsGanzzahl =
      r₂.lokale.head?.join.bind alsGanzzahl := by rw [hKopf]
  have hObergrenzen : r₁.obergrenzen = r₂.obergrenzen := by
    simpa only [Rahmen.sicht] using congrArg (fun r : Rahmen => (r.sicht β).obergrenzen) h
  simp only [Befehl.auswerten, Id.run, pcEq, hCurrent, hObergrenzen]
  cases hzC : r₂.lokale.head?.join.bind alsGanzzahl with
  | none =>
    simp only [hzC, sicht_halt_pure]
    rw [h]
  | some current =>
    cases hzU : r₂.obergrenzen r₁.pc with
    | none =>
      simp only [hzC, hzU, sicht_halt_pure]
      rw [h]
    | some upper =>
      simp only [hzC, hzU]
      exact passSicht β r₁.pc (decide (current.zahl.wert < upper.zahl.wert)) ende handler
        hs r₁ r₂ rfl h

/-- Replacing the head of a nonempty list is the same as setting index zero. -/
theorem kopf_ersetzt {α : Type} (v : α) (xs : List α) (hne : xs ≠ []) :
    v :: xs.drop 1 = xs.set 0 v := by
  cases xs with
  | nil => exact (hne rfl).elim
  | cons x xs => rfl

/-- The view after the incrementing branch of `forNaechster`: the program counter moves back,
    the head local is replaced by the incremented value and the rest of the stack is kept. -/
theorem sicht_forNaechster_schritt (β : Beschriftung) (r : Rahmen) (q : Nat)
    (loks : List (Option Dynamisch)) :
    ({ r with pc := q, lokale := loks } : Rahmen).sicht β =
      { r.sicht β with
        pc := q
        temp := fun s => if oeffentlich (β.temp q s) = true then r.temp s else none
        lokale := maskiere (β.lokal q) 0 loks } := rfl

theorem sicht_forNaechster_schritt_pure (β : Beschriftung) (r : Rahmen) (q : Nat)
    (loks : List (Option Dynamisch)) :
    (pure ({ r with pc := q, lokale := loks } : Rahmen) : Id Rahmen).sicht β =
      { r.sicht β with
        pc := q
        temp := fun s => if oeffentlich (β.temp q s) = true then r.temp s else none
        lokale := maskiere (β.lokal q) 0 loks } := by
  change ({ r with pc := q, lokale := loks } : Rahmen).sicht β = _
  rfl

/-- `forNaechster`: a public head decides between halt and increment. The increment replaces
    local 0 (`maskiere_set` at index 0) and moves the program counter backwards. -/
theorem forNaechsterSicht : ForNaechsterSichtAussage := by
  intro β pc zurueck index h0 hT hL₀ Kopf r₁ r₂ live hpc h
  subst hpc
  obtain ⟨pcEq, tempPub, lokEq⟩ := sicht_oeffentliche_teile h
  have hKopf : r₁.lokale.head?.join = r₂.lokale.head?.join := sicht_lokal0 β r₁ r₂ h0 h
  have hCurrent : r₁.lokale.head?.join.bind alsGanzzahl =
      r₂.lokale.head?.join.bind alsGanzzahl := by rw [hKopf]
  simp only [Befehl.auswerten, Id.run, pcEq, hCurrent]
  cases hzC : r₂.lokale.head?.join.bind alsGanzzahl with
  | none =>
    simp only [hzC, sicht_halt_pure]
    rw [h]
  | some current =>
    cases hwi : wertIn index (Ganzzahl.pack ⟨current.zahl.wert + 1, current.zahl.wert + 1,
        Zahl.literal (current.zahl.wert + 1)⟩) with
    | none =>
      simp only [hzC, hwi, sicht_halt_pure]
      rw [h]
    | some value =>
      simp only [hzC, hwi]
      have hne₂ : r₂.lokale ≠ [] := by
        intro he
        rw [he] at hzC
        cases hzC
      have hne₁ : r₁.lokale ≠ [] := by
        intro he
        rw [he] at hKopf
        have hz' : r₂.lokale.head?.join.bind alsGanzzahl = none := by
          rw [← hKopf]
          rfl
        rw [hz'] at hzC
        cases hzC
      have hset₁ : some value :: r₁.lokale.drop 1 = r₁.lokale.set 0 (some value) :=
        kopf_ersetzt (some value) r₁.lokale hne₁
      have hset₂ : some value :: r₂.lokale.drop 1 = r₂.lokale.set 0 (some value) :=
        kopf_ersetzt (some value) r₂.lokale hne₂
      have hLe := maskiere_set (l₀ := β.lokal r₁.pc) (l₁ := β.lokal (r₁.pc - zurueck))
        (index := 0) (xs := r₁.lokale) (ys := r₂.lokale)
        (v₁ := some value) (v₂ := some value)
        (fun j hj hjpub => hL₀ j hj hjpub) (fun _ => rfl) lokEq
      have hTe :
          (fun s => if oeffentlich (β.temp (r₁.pc - zurueck) s) = true then r₁.temp s else none) =
          (fun s => if oeffentlich (β.temp (r₁.pc - zurueck) s) = true then r₂.temp s else none) := by
        funext s
        by_cases hp : oeffentlich (β.temp (r₁.pc - zurueck) s) = true
        · simp only [hp, if_true]
          exact tempPub s (hT s hp)
        · simp only [if_neg hp]
      rw [sicht_forNaechster_schritt_pure, sicht_forNaechster_schritt_pure,
        h, hTe, hset₁, hset₂, hLe]

end Gabbro.Core.Ast.Semantik
