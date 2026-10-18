import Grammatik.Speichermodell.Payload.PayloadLitmus

/-
  File:      Grammatik/Speichermodell/Payload/PayloadLB.lean
  Subject:   PHASE B, ITEM 1: the litmus test LB (load buffering) is FORBIDDEN in the weak
             memory model, as an invariant proof over `LSchritt` (the machine of `Sicht.lean`).
             The model has no promises, so the causal cycle `r0 := y; x := 1 || r0 := x; y := 1`
             with both reads returning 1 is unreachable (RC11 forbids it as well).
-/

namespace Gabbro.Grammatik.Speichermodell

open Befehl LOrt Ordnung

/-- `LB`, all relaxed. Thread 0: `r0 := y; x := 1`. Thread 1: `r0 := x; y := 1`. -/
def lb : Nat → List (Befehl LOrt) :=
  faeden [[lies .y 0 .entspannt, schreib .x 1 .entspannt],
          [lies .x 0 .entspannt, schreib .y 1 .entspannt]]

theorem lb_fall {t n : Nat} {b : Befehl LOrt} (h : (lb t)[n]? = some b) :
    (t = 0 ∧ n = 0 ∧ b = lies .y 0 .entspannt) ∨ (t = 0 ∧ n = 1 ∧ b = schreib .x 1 .entspannt) ∨
    (t = 1 ∧ n = 0 ∧ b = lies .x 0 .entspannt) ∨ (t = 1 ∧ n = 1 ∧ b = schreib .y 1 .entspannt) := by
  match t, n, h with
  | 0, 0, h => simp [lb, faeden] at h; exact Or.inl ⟨rfl, rfl, h.symm⟩
  | 0, 1, h => simp [lb, faeden] at h; exact Or.inr (Or.inl ⟨rfl, rfl, h.symm⟩)
  | 1, 0, h => simp [lb, faeden] at h; exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, h.symm⟩))
  | 1, 1, h => simp [lb, faeden] at h; exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl, h.symm⟩))
  | 0, n + 2, h => simp [lb, faeden] at h
  | 1, n + 2, h => simp [lb, faeden] at h
  | t + 2, n, h => simp [lb, faeden] at h

theorem ns_pc_self (Z : LZustand LOrt) (t : Nat) (loc : LOrt) (w : Int) (o : Ordnung) (ts : Nat) :
    (Z.nachSchreib t loc w o ts).pc t = Z.pc t + 1 := by simp [LZustand.nachSchreib, aufN]

theorem ns_pc_other (Z : LZustand LOrt) {t u : Nat} (loc : LOrt) (w : Int) (o : Ordnung) (ts : Nat)
    (h : u ≠ t) : (Z.nachSchreib t loc w o ts).pc u = Z.pc u := by
  simp [LZustand.nachSchreib, aufN, h]

theorem ns_hist_self (Z : LZustand LOrt) (t : Nat) (loc : LOrt) (w : Int) (o : Ordnung) (ts : Nat) :
    (Z.nachSchreib t loc w o ts).hist loc = nachricht o (Z.sicht t) loc ts w :: Z.hist loc := by
  simp [LZustand.nachSchreib, aufO]

theorem ns_hist_other (Z : LZustand LOrt) (t : Nat) {loc loc2 : LOrt} (w : Int) (o : Ordnung)
    (ts : Nat) (h : loc2 ≠ loc) : (Z.nachSchreib t loc w o ts).hist loc2 = Z.hist loc2 := by
  simp [LZustand.nachSchreib, aufO, h]

theorem ns_reg (Z : LZustand LOrt) (t : Nat) (loc : LOrt) (w : Int) (o : Ordnung) (ts : Nat) :
    (Z.nachSchreib t loc w o ts).reg = Z.reg := rfl

theorem nl_pc_self (Z : LZustand LOrt) (t : Nat) (loc : LOrt) (r : Nat) (o : Ordnung)
    (m : Nachricht LOrt Int) : (Z.nachLies t loc r o m).pc t = Z.pc t + 1 := by
  simp [LZustand.nachLies, aufN]

theorem nl_pc_other (Z : LZustand LOrt) {t u : Nat} (loc : LOrt) (r : Nat) (o : Ordnung)
    (m : Nachricht LOrt Int) (h : u ≠ t) : (Z.nachLies t loc r o m).pc u = Z.pc u := by
  simp [LZustand.nachLies, aufN, h]

theorem nl_hist (Z : LZustand LOrt) (t : Nat) (loc : LOrt) (r : Nat) (o : Ordnung)
    (m : Nachricht LOrt Int) : (Z.nachLies t loc r o m).hist = Z.hist := rfl

theorem nl_reg_self (Z : LZustand LOrt) (t : Nat) (loc : LOrt) (o : Ordnung)
    (m : Nachricht LOrt Int) : (Z.nachLies t loc 0 o m).reg t 0 = m.wert := by
  simp [LZustand.nachLies, aufN]

theorem nl_reg_other (Z : LZustand LOrt) {t u : Nat} (loc : LOrt) (r : Nat) (o : Ordnung)
    (m : Nachricht LOrt Int) (h : u ≠ t) : (Z.nachLies t loc r o m).reg u = Z.reg u := by
  simp [LZustand.nachLies, aufN, h]

/-- The invariant of `lb`: a message of value 1 exists only after its writer's write (`a1`,
    `a2`); a thread that read 1 saw a write whose thread had already finished its read
    (`b0`, `b1`); and so the two reads never both return 1 (`g`). -/
structure LBInv (Z : LZustand LOrt) : Prop where
  a1 : ∀ m ∈ Z.hist .x, m.wert = 1 → 2 ≤ Z.pc 0
  a2 : ∀ m ∈ Z.hist .y, m.wert = 1 → 2 ≤ Z.pc 1
  b0 : 1 ≤ Z.pc 0 → Z.reg 0 0 = 1 → 2 ≤ Z.pc 1
  b1 : 1 ≤ Z.pc 1 → Z.reg 1 0 = 1 → 2 ≤ Z.pc 0
  g : ¬ (1 ≤ Z.pc 0 ∧ Z.reg 0 0 = 1 ∧ 1 ≤ Z.pc 1 ∧ Z.reg 1 0 = 1)

theorem lbInv_start : LBInv (LZustand.start LOrt) where
  a1 m hm h := by simp [LZustand.start] at hm; subst hm; simp at h
  a2 m hm h := by simp [LZustand.start] at hm; subst hm; simp at h
  b0 h := by simp [LZustand.start] at h
  b1 h := by simp [LZustand.start] at h
  g h := by simp [LZustand.start] at h

theorem lbInv_schritt {Z Z' : LZustand LOrt} (hI : LBInv Z) (hs : LSchritt lb Z Z') :
    LBInv Z' := by
  cases hs with
  | schreib t xo w o ts hb hf =>
      rcases lb_fall hb with ⟨_, _, hc⟩ | ⟨rfl, hpc, hc⟩ | ⟨_, _, hc⟩ | ⟨rfl, hpc, hc⟩
      · cases hc
      · -- thread 0 writes `x := 1`
        obtain ⟨rfl, rfl, rfl⟩ := befehl_schreib_inj hc
        have h0 : Z.pc 0 = 1 := hpc
        have P0 := ns_pc_self Z 0 .x 1 .entspannt ts
        have P1 : (Z.nachSchreib 0 .x 1 .entspannt ts).pc 1 = Z.pc 1 :=
          ns_pc_other Z .x 1 .entspannt ts (by decide)
        have R := ns_reg Z 0 .x 1 .entspannt ts
        have Hx := ns_hist_self Z 0 .x 1 .entspannt ts
        have Hy : (Z.nachSchreib 0 .x 1 .entspannt ts).hist .y = Z.hist .y :=
          ns_hist_other Z 0 1 .entspannt ts (by decide)
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · intro m hm hw
          rw [Hx] at hm
          rw [P0]
          rcases List.mem_cons.mp hm with rfl | hm
          · omega
          · have := hI.a1 m hm hw; omega
        · intro m hm hw
          rw [Hy] at hm
          rw [P1]
          exact hI.a2 m hm hw
        · intro h h'
          rw [P1]
          rw [R] at h'
          exact hI.b0 (by omega) h'
        · intro h h'
          rw [P0]
          omega
        · intro h
          rw [P0, P1, R] at h
          exact hI.g ⟨by omega, h.2.1, h.2.2.1, h.2.2.2⟩
      · cases hc
      · -- thread 1 writes `y := 1`
        obtain ⟨rfl, rfl, rfl⟩ := befehl_schreib_inj hc
        have h1 : Z.pc 1 = 1 := hpc
        have P1 := ns_pc_self Z 1 .y 1 .entspannt ts
        have P0 : (Z.nachSchreib 1 .y 1 .entspannt ts).pc 0 = Z.pc 0 :=
          ns_pc_other Z .y 1 .entspannt ts (by decide)
        have R := ns_reg Z 1 .y 1 .entspannt ts
        have Hy := ns_hist_self Z 1 .y 1 .entspannt ts
        have Hx : (Z.nachSchreib 1 .y 1 .entspannt ts).hist .x = Z.hist .x :=
          ns_hist_other Z 1 1 .entspannt ts (by decide)
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · intro m hm hw
          rw [Hx] at hm
          rw [P0]
          exact hI.a1 m hm hw
        · intro m hm hw
          rw [Hy] at hm
          rw [P1]
          rcases List.mem_cons.mp hm with rfl | hm
          · omega
          · have := hI.a2 m hm hw; omega
        · intro h h'
          rw [P1]
          omega
        · intro h h'
          rw [P0]
          rw [R] at h'
          exact hI.b1 (by omega) h'
        · intro h
          rw [P0, P1, R] at h
          exact hI.g ⟨h.1, h.2.1, by omega, h.2.2.2⟩
  | lies t xo r o m hb hl =>
      rcases lb_fall hb with ⟨rfl, hpc, hc⟩ | ⟨_, _, hc⟩ | ⟨rfl, hpc, hc⟩ | ⟨_, _, hc⟩
      · -- thread 0 reads `y`
        obtain ⟨rfl, rfl, rfl⟩ := befehl_lies_inj hc
        have h0 : Z.pc 0 = 0 := hpc
        have hm := hl.1
        have P0 := nl_pc_self Z 0 .y 0 .entspannt m
        have P1 : (Z.nachLies 0 .y 0 .entspannt m).pc 1 = Z.pc 1 :=
          nl_pc_other Z .y 0 .entspannt m (by decide)
        have R0 := nl_reg_self Z 0 .y .entspannt m
        have R1 : (Z.nachLies 0 .y 0 .entspannt m).reg 1 = Z.reg 1 :=
          nl_reg_other Z .y 0 .entspannt m (by decide)
        have H := nl_hist Z 0 .y 0 .entspannt m
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · intro m' hm' hw
          rw [H] at hm'
          have := hI.a1 m' hm' hw; omega
        · intro m' hm' hw
          rw [H] at hm'
          rw [P1]
          exact hI.a2 m' hm' hw
        · intro h h'
          rw [R0] at h'
          rw [P1]
          exact hI.a2 m hm h'
        · intro h h'
          rw [R1] at h'
          rw [P1] at h
          have := hI.b1 h h'
          omega
        · intro h
          rw [P0, P1, R0, R1] at h
          have h2 := hI.a2 m hm h.2.1
          have h3 := hI.b1 h.2.2.1 h.2.2.2
          omega
      · cases hc
      · -- thread 1 reads `x`
        obtain ⟨rfl, rfl, rfl⟩ := befehl_lies_inj hc
        have h1 : Z.pc 1 = 0 := hpc
        have hm := hl.1
        have P1 := nl_pc_self Z 1 .x 0 .entspannt m
        have P0 : (Z.nachLies 1 .x 0 .entspannt m).pc 0 = Z.pc 0 :=
          nl_pc_other Z .x 0 .entspannt m (by decide)
        have R1 := nl_reg_self Z 1 .x .entspannt m
        have R0 : (Z.nachLies 1 .x 0 .entspannt m).reg 0 = Z.reg 0 :=
          nl_reg_other Z .x 0 .entspannt m (by decide)
        have H := nl_hist Z 1 .x 0 .entspannt m
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · intro m' hm' hw
          rw [H] at hm'
          rw [P0]
          exact hI.a1 m' hm' hw
        · intro m' hm' hw
          rw [H] at hm'
          have := hI.a2 m' hm' hw; omega
        · intro h h'
          rw [R0] at h'
          rw [P0] at h
          have := hI.b0 h h'
          omega
        · intro h h'
          rw [R1] at h'
          rw [P0]
          exact hI.a1 m hm h'
        · intro h
          rw [P0, P1, R0, R1] at h
          have h2 := hI.a1 m hm h.2.2.2
          have h3 := hI.b0 h.1 h.2.1
          omega
      · cases hc

theorem lbInv_erreichbar {Z : LZustand LOrt} (h : LErreichbar (LSchritt lb) Z) : LBInv Z := by
  induction h with
  | start => exact lbInv_start
  | schritt _ hs ih => exact lbInv_schritt ih hs

/-- **LB is FORBIDDEN**: no reachable state has both threads finished with both reads
    returning 1. The model has no promises, so a read never returns a write that comes after
    the reader's own later write in a causal cycle (RC11 forbids it too). -/
theorem lb_verboten {Z : LZustand LOrt} (h : LErreichbar (LSchritt lb) Z)
    (h0 : 2 ≤ Z.pc 0) (h1 : 2 ≤ Z.pc 1) (r0 : Z.reg 0 0 = 1) : Z.reg 1 0 ≠ 1 :=
  fun r1 => (lbInv_erreichbar h).g ⟨by omega, r0, by omega, r1⟩

end Gabbro.Grammatik.Speichermodell

#print axioms Gabbro.Grammatik.Speichermodell.lb_verboten
