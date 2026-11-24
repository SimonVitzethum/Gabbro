module

public import Core.Beobachtung.SchrankenB8Aussagen
public import Core.Fortschritt.WarteBeispiel

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

/-- The pinned claim is false: the foreign hypothesis is about one context `c`, while the
    conclusion quantifies over every context. Counterexample: a context `B` owns a lock with
    bound `0` and takes an internal step at cut `1`; `A` has no step there, so the premise holds
    at cut `1`, but the hold interval `[1,2)` for `B` then costs one against bound zero. -/
theorem halteFremd : ¬ halteFremdAussage := by
  intro H
  let sB : Zustand Unit Unit Unit Unit Bool Unit :=
    { (I.start Fortschritt.E_1 Fortschritt.s0).2 with
      sperren := fun _ => ⟨some Fortschritt.B, []⟩ }
  let Eb : Einheit Unit Unit Unit Unit Bool Unit Unit Unit Unit :=
    { Fortschritt.E_1 with
      laden := fun _ _ => some sB
      schranken := { Fortschritt.E_1.schranken with halten := fun _ => some 0 } }
  let spurB : Nat → Option (SchrittWahl Unit × SchrittSpur Unit Unit) :=
    fun t => if t % 2 = 0 then some (.kontext Fortschritt.A (), ⟨[], []⟩)
      else some (.kontext Fortschritt.B (), ⟨[], []⟩)
  let zustandB : Nat → Option (Zustand Unit Unit Unit Unit Bool Unit) := fun _ => some sB
  have taktB : ∀ t,
      Takt (Lauffolge Eb Fortschritt.hw2)
        (KeinSchritt (Lauffolge Eb Fortschritt.hw2)) t
        (zustandB t) (spurB t) (zustandB (t + 1)) := by
    intro t
    by_cases he : t % 2 = 0
    · have hsp : spurB t = some (.kontext Fortschritt.A (), (⟨[], []⟩ : SchrittSpur Unit Unit)) := by
        simp only [spurB, if_pos he]
      rw [hsp]
      exact .schritt rfl (.schritt
        (ImplSchritt.kontext (Fortschritt.hw2_crash t)
          ⟨0, Fortschritt.hw2_opp0 he, rfl, rfl⟩
          ⟨(), rfl, Or.inr ⟨rfl, rfl⟩⟩
          (Fortschritt.e1StotterAusfuehr t Fortschritt.A sB)))
    · have h1 : t % 2 = 1 := by
        rcases Nat.mod_two_eq_zero_or_one t with h0 | h1'
        · exact (he h0).elim
        · exact h1'
      have hsp : spurB t = some (.kontext Fortschritt.B (), (⟨[], []⟩ : SchrittSpur Unit Unit)) := by
        simp only [spurB, if_neg he]
      rw [hsp]
      exact .schritt rfl (.schritt
        (ImplSchritt.kontext (Fortschritt.hw2_crash t)
          ⟨1, Fortschritt.hw2_opp1 h1, rfl, rfl⟩
          ⟨(), rfl, Or.inr ⟨rfl, rfl⟩⟩
          (Fortschritt.e1StotterAusfuehr t Fortschritt.B sB)))
  let ρb : Lauf Eb := ⟨Fortschritt.s0, Fortschritt.hw2, ⟨zustandB, spurB, taktB⟩⟩
  have ownB : ∀ t', 1 ≤ t' → t' < 1 + 1 →
      ∃ s, ρb.zeit.zustand t' = some s ∧ (s.sperren ()).besitzer = some Fortschritt.B := by
    intro t' h1 h2
    have ht : t' = 1 := by omega
    subst t'
    exact ⟨sB, rfl, rfl⟩
  have hyp1 : HaltePrefix Eb ρb 1 := by
    intro l c' a n bound own
    cases l
    cases n with
    | zero =>
        intro lim _
        simp only [Kontextkosten, I.zaehle]
        exact Nat.zero_le lim
    | succ n =>
        have ha : a = 0 := by omega
        have hn : n = 0 := by omega
        subst a
        subst n
        have cb : c' = Fortschritt.B := by
          obtain ⟨s, hzs, hposs⟩ := own 0 (Nat.le_refl _) (by decide : 0 < 0 + 1)
          change some sB = some s at hzs
          obtain rfl := Option.some.inj hzs
          change (some Fortschritt.B : Option Kontext) = some c' at hposs
          exact (Option.some.inj hposs).symm
        subst c'
        have fremdB : ∀ d w spur, ρb.zeit.spur 0 = some (.kontext d w, spur) → d ≠ Fortschritt.B := by
          intro d w spur hstep
          change some (.kontext Fortschritt.A (), (⟨[], []⟩ : SchrittSpur Unit Unit)) =
            some (.kontext d w, spur) at hstep
          have hp := Option.some.inj hstep
          cases hp
          show Fortschritt.A ≠ Fortschritt.B
          decide
        have hk : Kontextkosten ρb Fortschritt.B 0 1 = 0 := by
          have hk' := kontextkosten_fremd (ρ := ρb) (c := Fortschritt.B)
            (a := 0) (k := 0) (t := 0) rfl fremdB
          change Kontextkosten ρb Fortschritt.B 0 (0 + 1) = Kontextkosten ρb Fortschritt.B 0 0 at hk'
          rw [hk']
          rfl
        change ∀ m, Eb.schranken.halten () = some m → Kontextkosten ρb Fortschritt.B 0 1 ≤ m
        intro m hm
        have hm0 : m = 0 := Option.some.inj hm.symm
        subst m
        rw [hk]
        exact Nat.zero_le 0
  have fremdA : ∀ d w spur, ρb.zeit.spur 1 = some (.kontext d w, spur) → d ≠ Fortschritt.A := by
    intro d w spur hstep
    change some (.kontext Fortschritt.B (), (⟨[], []⟩ : SchrittSpur Unit Unit)) =
      some (.kontext d w, spur) at hstep
    have hp := Option.some.inj hstep
    cases hp
    show Fortschritt.B ≠ Fortschritt.A
    decide
  have nach := H Unit Unit Unit Unit Bool Unit Unit Unit Unit
    (inferInstance : DecidableEq Unit) Eb ρb Fortschritt.A 1 fremdA hyp1
  have verletzung := nach () Fortschritt.B 1 1 (by decide : 1 + 1 ≤ 2) ownB
  have hm0 : Kontextkosten ρb Fortschritt.B 1 1 ≤ 0 := verletzung 0 rfl
  have hk1 : Kontextkosten ρb Fortschritt.B 1 1 = 1 := by
    simp only [Kontextkosten, I.zaehle, Nat.zero_add, Nat.add_zero, ρb, spurB,
      if_neg (by decide : ¬ 1 % 2 = 0), decide_true, if_true]
  rw [hk1] at hm0
  exact (by decide : ¬ 1 ≤ 0) hm0

end Gabbro.Core.Beobachtung
