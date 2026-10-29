/-
  File:      stage0/Stage0/Senke/Anweisung/Pruefung.lean
  Subject:   The test of a gate's answer against its declared range (`chkC`): inside, the code runs to its end and
             changes no slot below `s + 1`; outside, the stop 110 (G's hardware outcome at the gate).
-/
import Stage0.Senke.Anweisung.Tor

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable [Kern]

variable {D : Deklaration}

theorem bool_ne_zero {b : Bool} : Runner.IR.bool b ≠ 0 ↔ b = true := by cases b <;> decide

theorem slt_lit {w : Runner.W} {k : Int} (hk : lit32 k = true) : w.slt (BitVec.ofInt 64 k) = decide (w.toInt < k) := by
  simp only [lit32, Bool.and_eq_true, decide_eq_true_eq] at hk
  rw [BitVec.slt_eq_decide, toInt_ofInt_in (by omega) (by omega)]

/-- `d := slot s < k` with `d = s + 1`. -/
theorem sltC_ok {m : Runner.Mem} {pc fp : Runner.W} {K s : Nat} {k : Int} {Γ : Ctx} {ρ : Env D Γ} {w : Runner.W}
    (hp : PreS m pc fp K (s + 1) (sltC s k) ρ) (hk : lit32 k = true) (hs : s + 2 < K)
    (hw : m.rd64 (slot fp (BitVec.ofNat 64 s)) = some w) :
    Ok m pc fp K (s + 1) (sltC s k) (· = Runner.IR.bool (decide (w.toInt < k))) := by
  have hp' : PreS m pc fp K (s + 1) ([ci 2 ((s + 1 : Nat) : Int) s 0] ++ [ci 1 (((s + 1 : Nat) : Int) + 1) k 0,
      ci 13 ((s + 1 : Nat) : Int) ((s + 1 : Nat) : Int) (((s + 1 : Nat) : Int) + 1)]) ρ := hp
  have := hp.small
  exact ok_seq hp' (mov_ok hp'.left (by omega) (by omega) hw)
    (fun m' w' hp'' hr he => (binK_ok (r := Runner.IR.bool (w'.slt (BitVec.ofInt 64 k))) hp'' hr hk rfl (by decide)
      rfl (by omega)).mono fun x hx => by rw [hx, he, slt_lit hk]) (by omega)

/-- A test `c` leaving `v` in slot `d`, then the guard over `d`. -/
theorem test_ok {m : Runner.Mem} {pc fp : Runner.W} {K d s : Nat} {c : List II} {Γ : Ctx} {ρ : Env D Γ}
    {v : Runner.W} (hp : PreS m pc fp K d (c ++ guardC d 110 s) ρ) (ho : Ok m pc fp K d c (· = v))
    (hd : d < K) (hs : s + 8 ≤ K) :
    (v ≠ 0 → ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * (c ++ guardC d 110 s).length), fp⟩ m' ∧
      Agree fp d K m m') ∧ (v = 0 → Stops ⟨pc, fp⟩ m 110) := by
  obtain ⟨m1, s1, a1, w, hw, rfl⟩ := ho
  have hp1 := hp.next a1 (Nat.le_refl _) (by omega)
  have hlen : (guardC d 110 s).length = 5 := rfl
  refine ⟨fun hne => ⟨m1, ?_, a1⟩, fun h0 => ?_⟩
  · have sg := guard_pass hp1.code (by have := hp.small; omega) hw hne
    rw [hlen] at sg
    refine s1.trans (star_cast sg rfl ?_)
    rw [List.length_append, hlen, pc_add]
  · subst h0
    exact Stops.prefix s1 (guard_stop hp1.code (by simpa [hlen] using hp1.far) hp1.frame hd hs hp.small (by decide) hw)

/-- The lower bound. -/
theorem loC_ok {m : Runner.Mem} {pc fp : Runner.W} {K s : Nat} {lo : Int} {Γ : Ctx} {ρ : Env D Γ} {w : Runner.W}
    (hp : PreS m pc fp K (s + 1) (loC s lo) ρ) (hk : lit32 lo = true) (hs : s + 10 ≤ K)
    (hw : m.rd64 (slot fp (BitVec.ofNat 64 s)) = some w) :
    (lo ≤ w.toInt → ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * (loC s lo).length), fp⟩ m' ∧
      Agree fp (s + 1) K m m') ∧ (¬ lo ≤ w.toInt → Stops ⟨pc, fp⟩ m 110) := by
  have hp' : PreS m pc fp K (s + 1) ((sltC s lo ++ [ci 1 (((s + 1 : Nat) : Int) + 1) 0 0,
      ci 14 ((s + 1 : Nat) : Int) ((s + 1 : Nat) : Int) (((s + 1 : Nat) : Int) + 1)]) ++ guardC (s + 1) 110 (s + 2)) ρ :=
    hp
  have := hp.small
  have ho := ok_seq hp'.left (sltC_ok hp'.left.left hk (by omega) hw)
    (Pb := (· = Runner.IR.bool (Runner.IR.bool (decide (w.toInt < lo)) == BitVec.ofInt 64 0)))
    (fun m' w' hp'' hr he => (binK_ok (r := Runner.IR.bool (w' == BitVec.ofInt 64 0)) hp'' hr (by decide) rfl
      (by decide) rfl (by omega)).mono fun x hx => by rw [hx, he]) (by omega)
  obtain ⟨h1, h2⟩ := test_ok hp' ho (by omega) (by omega)
  refine ⟨fun hl => h1 ?_, fun hl => h2 ?_⟩
  · have : decide (w.toInt < lo) = false := by simp only [decide_eq_false_iff_not]; omega
    rw [this]; decide
  · have : decide (w.toInt < lo) = true := by simp only [decide_eq_true_eq]; omega
    rw [this]; decide

/-- The upper bound. -/
theorem hiC_ok {m : Runner.Mem} {pc fp : Runner.W} {K s : Nat} {hi : Int} {Γ : Ctx} {ρ : Env D Γ} {w : Runner.W}
    (hp : PreS m pc fp K (s + 1) (hiC s hi) ρ) (hk : lit32 (hi + 1) = true) (hs : s + 10 ≤ K)
    (hw : m.rd64 (slot fp (BitVec.ofNat 64 s)) = some w) :
    (w.toInt ≤ hi → ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * (hiC s hi).length), fp⟩ m' ∧
      Agree fp (s + 1) K m m') ∧ (¬ w.toInt ≤ hi → Stops ⟨pc, fp⟩ m 110) := by
  have := hp.small
  obtain ⟨h1, h2⟩ := test_ok hp (sltC_ok hp.left hk (by omega) hw) (by omega) (by omega)
  refine ⟨fun hl => h1 ?_, fun hl => h2 ?_⟩
  · rw [bool_ne_zero]; simp only [decide_eq_true_eq]; omega
  · have : decide (w.toInt < hi + 1) = false := by simp only [decide_eq_false_iff_not]; omega
    rw [this]; rfl

/-- A part of the test: nothing, or a test that passes in the range `P` and stops outside it. -/
theorem part_ok {m : Runner.Mem} {pc fp : Runner.W} {K s : Nat} {c : List II} {Γ : Ctx} {ρ : Env D Γ}
    {P : Prop} (hp : PreS m pc fp K (s + 1) c ρ)
    (h : (c = [] ∧ P) ∨ ((P → ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * c.length), fp⟩ m' ∧
      Agree fp (s + 1) K m m') ∧ (¬ P → Stops ⟨pc, fp⟩ m 110))) :
    (P → ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * c.length), fp⟩ m' ∧ Agree fp (s + 1) K m m') ∧
      (¬ P → Stops ⟨pc, fp⟩ m 110) := by
  rcases h with ⟨rfl, hP⟩ | h
  · exact ⟨fun _ => ⟨m, by simpa using Star.refl _ m, Agree.refl _ _ _ _⟩, fun h => absurd hP h⟩
  · exact h

/-- **The test of an answer**: inside `lo .. hi` on to the end, outside the stop 110. -/
theorem chkC_ok {lo hi : Int} {s : Nat} {c : List II} (h : chkC (some (.int lo hi)) s = some c)
    {m : Runner.Mem} {pc fp : Runner.W} {K : Nat} {Γ : Ctx} {ρ : Env D Γ} {w : Runner.W}
    (hp : PreS m pc fp K (s + 1) c ρ) (hK : s + 10 ≤ K) (hw : m.rd64 (slot fp (BitVec.ofNat 64 s)) = some w) :
    (lo ≤ w.toInt ∧ w.toInt ≤ hi → ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * c.length), fp⟩ m' ∧
      Agree fp (s + 1) K m m') ∧ (¬ (lo ≤ w.toInt ∧ w.toInt ≤ hi) → Stops ⟨pc, fp⟩ m 110) := by
  have hwi := BitVec.toInt_lt (x := w)
  have hwl := BitVec.le_toInt (x := w)
  simp only [Nat.reduceSub] at hwi hwl
  simp only [chkC] at h
  split at h
  · next a b ha hb =>
    simp only [Option.some.injEq] at h
    subst h
    have hroom := hp.frame.room
    have hA : (a = [] ∧ lo ≤ w.toInt) ∨ ((lo ≤ w.toInt → ∃ m', Star ⟨pc, fp⟩ m
        ⟨pc + BitVec.ofNat 64 (16 * a.length), fp⟩ m' ∧ Agree fp (s + 1) K m m') ∧
        (¬ lo ≤ w.toInt → Stops ⟨pc, fp⟩ m 110)) := by
      split at ha
      · cases ha; exact .inl ⟨rfl, by omega⟩
      · split at ha
        · cases ha; exact .inr (loC_ok hp.left (by assumption) (by omega) hw)
        · cases ha
    obtain ⟨hA1, hA2⟩ := part_ok hp.left hA
    refine ⟨fun ⟨hl, hh⟩ => ?_, fun hn => ?_⟩
    · obtain ⟨m1, s1, a1⟩ := hA1 hl
      have hp1 := hp.next a1 (Nat.le_refl _) (by omega)
      have hw1 : m1.rd64 (slot fp (BitVec.ofNat 64 s)) = some w := by
        rw [agree_rd_low a1 hroom (by omega) (by omega)]; exact hw
      have hB : (b = [] ∧ w.toInt ≤ hi) ∨ ((w.toInt ≤ hi → ∃ m', Star ⟨pc + BitVec.ofNat 64 (16 * a.length), fp⟩ m1
          ⟨pc + BitVec.ofNat 64 (16 * a.length) + BitVec.ofNat 64 (16 * b.length), fp⟩ m' ∧
          Agree fp (s + 1) K m1 m') ∧ (¬ w.toInt ≤ hi → Stops ⟨pc + BitVec.ofNat 64 (16 * a.length), fp⟩ m1 110)) := by
        split at hb
        · cases hb; exact .inl ⟨rfl, by omega⟩
        · split at hb
          · cases hb; exact .inr (hiC_ok hp1 (by assumption) (by omega) hw1)
          · cases hb
      obtain ⟨m2, s2, a2⟩ := (part_ok hp1 hB).1 hh
      exact ⟨m2, s1.trans (by rw [List.length_append, ← pc_add]; exact s2), a1.trans a2⟩
    · by_cases hl : lo ≤ w.toInt
      · obtain ⟨m1, s1, a1⟩ := hA1 hl
        have hp1 := hp.next a1 (Nat.le_refl _) (by omega)
        have hw1 : m1.rd64 (slot fp (BitVec.ofNat 64 s)) = some w := by
          rw [agree_rd_low a1 hroom (by omega) (by omega)]; exact hw
        have hh : ¬ w.toInt ≤ hi := fun hh => hn ⟨hl, hh⟩
        split at hb
        · omega
        · split at hb
          · cases hb; exact Stops.prefix s1 ((hiC_ok hp1 (by assumption) (by omega) hw1).2 hh)
          · cases hb
      · exact hA2 hl
  · cases h

end Gabbro.Stage0.Senke
