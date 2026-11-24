module

public import Core.Beobachtung.SchrankenB8Aussagen

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine

variable {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]
variable {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form}

/-- A last tick whose mark is absent does not change the count. -/
private theorem zaehle_still {markiert : Nat → Bool} {anfang k : Nat}
    (still : markiert (anfang + k) = false) :
    I.zaehle markiert anfang (k + 1) = I.zaehle markiert anfang k := by
  simp only [I.zaehle, still, Bool.false_eq_true, if_false, Nat.add_zero]

/-- The count splits over adjacent intervals. -/
private theorem zaehle_teil (markiert : Nat → Bool) (a m n : Nat) :
    I.zaehle markiert a (m + n) = I.zaehle markiert a m + I.zaehle markiert (a + m) n := by
  induction n with
  | zero => simp only [Nat.add_zero, I.zaehle]
  | succ n ih =>
    have h1 : m + (n + 1) = (m + n) + 1 := (Nat.add_assoc m n 1).symm
    have h2 : a + (m + n) = (a + m) + n := (Nat.add_assoc a m n).symm
    rw [h1]
    simp only [I.zaehle]
    rw [h2, ih]
    omega

/-- A tick that is no context step of `c` adds nothing to the context cost of `c`. -/
private theorem kontextkosten_fremd {ρ : Lauf E} {c : Kontext} {a k t : Nat}
    (eq : a + k = t)
    (fremd : ∀ d w spur, ρ.zeit.spur t = some (.kontext d w, spur) → d ≠ c) :
    Kontextkosten ρ c a (k + 1) = Kontextkosten ρ c a k := by
  have tick : ∀ d w spur, ρ.zeit.spur (a + k) = some (.kontext d w, spur) → d ≠ c := by
    intro d w spur h
    rw [eq] at h
    exact fremd d w spur h
  have still : (fun t =>
      match ρ.zeit.spur t with
      | some (.kontext d _, _) => decide (c = d)
      | some (.antwort _, _) | some (.interrupt _, _) | some (.absturz, _) | none => false)
      (a + k) = false := by
    change (match ρ.zeit.spur (a + k) with
      | some (.kontext d _, _) => decide (c = d)
      | some (.antwort _, _) | some (.interrupt _, _) | some (.absturz, _) | none => false)
      = false
    cases hsp : ρ.zeit.spur (a + k) with
    | none => rfl
    | some label =>
      rcases label with ⟨w, spur⟩
      cases w with
      | antwort _ | interrupt _ | absturz => rfl
      | kontext d _ =>
        show decide (c = d) = false
        exact decide_eq_false (Ne.symm (tick d _ _ hsp))
  simp only [Kontextkosten]
  rw [zaehle_still still]

/-- An idle tick preserves the hold prefix. -/
private theorem halte_leerlauf {ρ : Lauf E} {t : Nat}
    (idle : ρ.zeit.spur t = none) (halte : HaltePrefix E ρ t) :
    HaltePrefix E ρ (t + 1) := by
  intro l c a n bound own
  by_cases h : a + n ≤ t
  · exact halte l c a n h own
  · cases n with
    | zero =>
        intro lim _
        simp only [Kontextkosten, I.zaehle]
        exact Nat.zero_le lim
    | succ k =>
        have ak_le : a + k ≤ t := by omega
        have ak_ge : t ≤ a + k := by omega
        have ak : a + k = t := Nat.le_antisymm ak_le ak_ge
        have own' : ∀ t', a ≤ t' → t' < a + k →
            ∃ s, ρ.zeit.zustand t' = some s ∧ (s.sperren l).besitzer = some c := by
          intro t' h1 h2
          exact own t' h1 (by omega)
        have zb := halte l c a k (le_of_eq ak) own'
        have fremd : ∀ d w spur, ρ.zeit.spur t = some (.kontext d w, spur) → d ≠ c := by
          intro d w spur hstep
          rw [idle] at hstep
          cases hstep
        rw [kontextkosten_fremd ak fremd]
        exact zb

theorem kostenNull : kostenNullAussage := by
  intro L Ort Wert Raum Lok Grund Bedingung Wahl Form inst E ρ c anfang
  simp only [Laufkosten, Kontextkosten, I.zaehle]
  exact ⟨trivial, trivial⟩

theorem kostenSchritt : kostenSchrittAussage := by
  intro L Ort Wert Raum Lok Grund Bedingung Wahl Form inst E ρ t
  constructor
  · intro idle
    simp only [Laufkosten, I.zaehle, Nat.zero_add, idle, Option.isSome_none,
      Bool.false_eq_true, if_false, Nat.add_zero]
  · intro w spur hit
    simp only [Laufkosten, I.zaehle, Nat.zero_add, hit, Option.isSome_some,
      ite_true, if_true, Nat.add_zero]

theorem kostenTeilung : kostenTeilungAussage := by
  intro L Ort Wert Raum Lok Grund Bedingung Wahl Form inst E ρ c anfang m n
  constructor
  · simp only [Laufkosten]
    exact zaehle_teil (fun t => (ρ.zeit.spur t).isSome) anfang m n
  · simp only [Kontextkosten]
    exact zaehle_teil (fun t =>
      match ρ.zeit.spur t with
      | some (.kontext d _, _) => decide (c = d)
      | some (.antwort _, _) | some (.interrupt _, _) | some (.absturz, _) | none => false)
      anfang m n

theorem kostenMonoton : kostenMonotonAussage := by
  intro L Ort Wert Raum Lok Grund Bedingung Wahl Form inst E ρ anfang m n hmn
  have hnd : n = m + (n - m) := (Nat.add_sub_of_le hmn).symm
  rw [hnd]
  simp only [Laufkosten]
  rw [zaehle_teil (fun t => (ρ.zeit.spur t).isSome) anfang m (n - m)]
  exact Nat.le_add_right _ _

theorem kostenAnfang : kostenAnfangAussage := by
  intro L Ort Wert Raum Lok Grund Bedingung Wahl Form inst E ρ
  change ∀ n, E.schranken.kosten = some n → Laufkosten ρ 0 0 ≤ n
  simp only [Laufkosten, I.zaehle]
  intro n hn
  exact Nat.zero_le n

theorem halteAnfang : halteAnfangAussage := by
  intro L Ort Wert Raum Lok Grund Bedingung Wahl Form inst E ρ
  intro l c a n bound own
  have ha : a = 0 := by omega
  have hn : n = 0 := by omega
  subst a
  subst n
  change ∀ m, E.schranken.halten l = some m → Kontextkosten ρ c 0 0 ≤ m
  simp only [Kontextkosten, I.zaehle]
  intro m hm
  exact Nat.zero_le m

theorem khLeerlauf : khLeerlaufAussage := by
  intro L Ort Wert Raum Lok Grund Bedingung Wahl Form inst E ρ t idle kosten halte
  constructor
  · change UnterGrenze E.schranken.kosten (Laufkosten ρ 0 (t + 1))
    have hstep : Laufkosten ρ 0 (t + 1) = Laufkosten ρ 0 t := by
      simp only [Laufkosten, I.zaehle, Nat.zero_add, idle, Option.isSome_none,
        Bool.false_eq_true, if_false, Nat.add_zero]
    rw [hstep]
    exact kosten
  · exact halte_leerlauf idle halte

/-- A foreign tick preserves the hold leg for its foreign context: an interval ending at
    the new cut either already ended before (induction hypothesis at `t`), or its last tick
    is the foreign one and contributes nothing to that context's cost. -/
theorem halteFremd : halteFremdAussage := by
  intro L Ort Wert Raum Lok Grund Bedingung Wahl Form inst E ρ c t fremd halte l a n bound own
  by_cases h : a + n ≤ t
  · exact halte l c a n h own
  · cases n with
    | zero =>
        intro lim _
        simp only [Kontextkosten, I.zaehle]
        exact Nat.zero_le lim
    | succ k =>
        have ak_le : a + k ≤ t := by omega
        have ak_ge : t ≤ a + k := by omega
        have ak : a + k = t := Nat.le_antisymm ak_le ak_ge
        have own' : ∀ t', a ≤ t' → t' < a + k →
            ∃ s, ρ.zeit.zustand t' = some s ∧ (s.sperren l).besitzer = some c := by
          intro t' h1 h2
          exact own t' h1 (by omega)
        have zb := halte l c a k (le_of_eq ak) own'
        have hcc : Kontextkosten ρ c a (k + 1) = Kontextkosten ρ c a k :=
          kontextkosten_fremd ak fremd
        rw [hcc]
        exact zb

end Gabbro.Core.Beobachtung
