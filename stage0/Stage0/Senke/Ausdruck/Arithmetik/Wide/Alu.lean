/-
  File:      stage0/Stage0/Senke/Ausdruck/Arithmetik/Wide/Alu.lean
  Subject:   A generic executor for straight-line register code over frame slots.

  Multiword integer arithmetic is straight-line code of constants, moves and total word
  operations. `aluRun` is the pure effect of such code on the slot valuation of a frame;
  `alu_run` proves that the actual IR execution reaches exactly that valuation, writes only slots
  from `d` on, and leaves the code untouched. Limb arithmetic is then argued on `aluRun` alone.
-/
module
public import Stage0.Senke.Ausdruck.Quant.Frame
public import Stage0.Senke.Ausdruck.Aggregat.WideInt.KernelCode
@[expose] public section


namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem

/-- The word function of every total binary ALU opcode used by limb arithmetic. -/
def aluFn : Nat → Option (Runner.W → Runner.W → Runner.W)
  | 3 => some (fun a b => a + b)
  | 4 => some (fun a b => a - b)
  | 5 => some (fun a b => a * b)
  | 8 => some (fun a b => a &&& b)
  | 9 => some (fun a b => a ||| b)
  | 10 => some (fun a b => a ^^^ b)
  | 11 => some (fun a b => a <<< (b.toNat % 64))
  | 12 => some (fun a b => a >>> (b.toNat % 64))
  | 13 => some (fun a b => Runner.IR.bool (a.slt b))
  | 14 => some (fun a b => Runner.IR.bool (a == b))
  | 27 => some (fun a b => Runner.IR.bool (a.ult b))
  | _ => none

theorem aluFn_op {o : Nat} {f : Runner.W → Runner.W → Runner.W} (h : aluFn o = some f) :
    op o = bin (fun a b => some (f a b)) := by
  unfold aluFn at h
  split at h <;> (cases h <;> rfl)

theorem aluFn_lt {o : Nat} {f : Runner.W → Runner.W → Runner.W} (h : aluFn o = some f) :
    o < 256 := by
  unfold aluFn at h
  split at h <;> first | omega | (cases h)

/-- The instructions the executor admits, with every slot in `d .. K-1` as destination
    and every operand slot inside the frame. -/
inductive AluIns (K d : Nat) : II → Prop
  | const (a : Nat) (k : Int) : d ≤ a → a < K → lit32 k = true → AluIns K d (ci 1 a k 0)
  | mov (a b : Nat) : d ≤ a → a < K → b < K → AluIns K d (ci 2 a b 0)
  | bin (o a b c : Nat) (f : Runner.W → Runner.W → Runner.W) : aluFn o = some f →
      d ≤ a → a < K → b < K → c < K → AluIns K d (ci o a b c)

/-- The slot valuation with slot `a` replaced. -/
def slotUpd (s : Nat → Runner.W) (a : Nat) (v : Runner.W) : Nat → Runner.W :=
  fun j => if j = a then v else s j

@[simp] theorem slotUpd_same (s : Nat → Runner.W) (a : Nat) (v : Runner.W) : slotUpd s a v a = v := by
  simp [slotUpd]

theorem slotUpd_other (s : Nat → Runner.W) {a j : Nat} (v : Runner.W) (h : j ≠ a) : slotUpd s a v j = s j := by
  simp [slotUpd, h]

/-- The word an instruction computes. -/
def aluVal (i : II) (s : Nat → Runner.W) : Runner.W :=
  if i.o = 1 then BitVec.ofInt 64 i.b
  else if i.o = 2 then s i.b.toNat
  else match aluFn i.o with
    | some f => f (s i.b.toNat) (s i.c.toNat)
    | none => 0

/-- The slot valuation after one instruction. -/
def aluStep (i : II) (s : Nat → Runner.W) : Nat → Runner.W := slotUpd s i.a.toNat (aluVal i s)

def aluRun : List II → (Nat → Runner.W) → (Nat → Runner.W)
  | [], s => s
  | i :: is, s => aluRun is (aluStep i s)

@[simp] theorem aluRun_nil (s : Nat → Runner.W) : aluRun [] s = s := by rfl
@[simp] theorem aluRun_cons (i : II) (is : List II) (s : Nat → Runner.W) :
    aluRun (i :: is) s = aluRun is (aluStep i s) := by rfl

theorem aluRun_append (a b : List II) (s : Nat → Runner.W) :
    aluRun (a ++ b) s = aluRun b (aluRun a s) := by
  induction a generalizing s with
  | nil => rfl
  | cons i is ih => simp only [List.cons_append, aluRun_cons, ih]

/-- Slots below the destination bound are never written by admitted code. -/
theorem aluStep_low {K d : Nat} {i : II} (h : AluIns K d i) (s : Nat → Runner.W) {j : Nat}
    (hj : j < d) : aluStep i s j = s j := by
  cases h <;> (apply slotUpd_other; simp only [ci, Int.toNat_natCast]; omega)

theorem aluRun_low {K d : Nat} {code : List II} (h : ∀ i ∈ code, AluIns K d i)
    (s : Nat → Runner.W) {j : Nat} (hj : j < d) : aluRun code s j = s j := by
  induction code generalizing s with
  | nil => rfl
  | cons i is ih =>
    simp only [aluRun_cons]
    rw [ih (fun x hx => h x (List.mem_cons_of_mem _ hx)), aluStep_low (h i (List.mem_cons_self ..)) s hj]

variable [Kern]

/-- One admitted instruction executes and updates exactly its destination slot. -/
theorem alu_step {m : Runner.Mem} {pc fp : Runner.W} {K d : Nat} {i : II}
    (hF : FrameOK m fp K) (hK : K < 2 ^ 31) (hc : CodeAt m pc [i]) (hi : AluIns K d i)
    (s : Nat → Runner.W) (hs : ∀ j, j < K → m.rd64 (slot fp (BitVec.ofNat 64 j)) = some (s j)) :
    ∃ m1, Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * [i].length), fp⟩ m1 ∧ Agree fp d K m m1 ∧
      ∀ j, j < K → m1.rd64 (slot fp (BitVec.ofNat 64 j)) = some (aluStep i s j) := by
  have ins := hc 0 (by simp)
  simp only [List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero] at ins
  have finish : ∀ (a : Nat) (r : Runner.W), d ≤ a → a < K →
      (∀ j, j < K → j ≠ a → m.rd64 (slot fp (BitVec.ofNat 64 j)) = some (s j)) →
      ∃ m1, m.wr64 (slot fp (BitVec.ofNat 64 a)) r = some m1 ∧ Agree fp d K m m1 ∧
        (∀ j, j < K → m1.rd64 (slot fp (BitVec.ofNat 64 j)) = some (slotUpd s a r j)) := by
    intro a r ha1 ha2 hrest
    obtain ⟨hw, hrd, ag⟩ := wr_slot hF ha2 r
    refine ⟨_, hw, ag.mono ha1, fun j hj => ?_⟩
    by_cases e : j = a
    · subst e; simpa using hrd
    · rw [slotUpd_other s r e, rd_other hF.room ha2 hj (fun h => e h.symm)]; exact hs j hj
  cases hi with
  | const a k h1 h2 hk =>
    have ins' : InsAt m pc 1 (II.f a) (II.f k) (II.f 0) := ins
    obtain ⟨m1, hw, ag, rd⟩ := finish a (BitVec.ofInt 64 k) h1 h2 (fun j hj _ => hs j hj)
    refine ⟨m1, star_ins hc (by simp [ci]) ?_, ag, fun j hj => ?_⟩
    · show Run (op 1 ⟨pc, fp⟩) m ⟨pc + 16, fp⟩ m1
      simp only [op]
      refine f2_run (t := ⟨pc, fp⟩) ins' ?_
      simp only [ret1]
      refine f1_run (t := ⟨pc, fp⟩) ins' ?_
      rw [sx_lit hk, sx_nat (by omega)]
      exact run_wr64 hw
    · rw [rd j hj]; simp only [aluStep, aluVal, ci, Int.toNat_natCast, ite_true]
  | mov a b h1 h2 h3 =>
    have ins' : InsAt m pc 2 (II.f a) (II.f b) (II.f 0) := ins
    obtain ⟨m1, hw, ag, rd⟩ := finish a (s b) h1 h2 (fun j hj _ => hs j hj)
    refine ⟨m1, star_ins hc (by simp [ci]) ?_, ag, fun j hj => ?_⟩
    · show Run (op 2 ⟨pc, fp⟩) m ⟨pc + 16, fp⟩ m1
      simp only [op]
      refine f2_run (t := ⟨pc, fp⟩) ins' ?_
      rw [sx_nat (by omega)]
      simp only [ld]
      refine run_rd64 (hs b h3) ?_
      simp only [ret1]
      refine f1_run (t := ⟨pc, fp⟩) ins' ?_
      rw [sx_nat (by omega)]
      exact run_wr64 hw
    · rw [rd j hj]; simp only [aluStep, aluVal, ci, Int.toNat_natCast]; rfl
  | bin o a b c f hf h1 h2 h3 h4 =>
    have ins' : InsAt m pc o (II.f a) (II.f b) (II.f c) := ins
    obtain ⟨m1, hw, ag, rd⟩ := finish a (f (s b) (s c)) h1 h2 (fun j hj _ => hs j hj)
    refine ⟨m1, star_ins hc (by simpa [ci] using aluFn_lt hf) ?_, ag, fun j hj => ?_⟩
    · show Run (op o ⟨pc, fp⟩) m ⟨pc + 16, fp⟩ m1
      rw [aluFn_op hf]
      refine run_bin (t := ⟨pc, fp⟩) (m1 := m1) ins' (va := s b) (vb := s c) ?_ ?_ rfl ?_
      · simpa only [sx_nat (by omega : b < 2 ^ 31)] using hs b h3
      · simpa only [sx_nat (by omega : c < 2 ^ 31)] using hs c h4
      · simpa only [sx_nat (by omega : a < 2 ^ 31)] using hw
    · rw [rd j hj]
      have : o ≠ 1 ∧ o ≠ 2 := by
        constructor <;> (intro h; subst h; simp [aluFn] at hf)
      simp only [aluStep, aluVal, ci, Int.toNat_natCast, hf, this.1, this.2, ite_false]

/-- Admitted straight-line code runs to its end; every frame slot then holds `aluRun`. -/
theorem alu_run {m : Runner.Mem} {pc fp : Runner.W} {K d : Nat} {code : List II}
    (hF : FrameOK m fp K) (hK : K < 2 ^ 31) (hc : CodeAt m pc code)
    (hfar : CodeFar pc code.length fp K) (hs : ∀ i ∈ code, AluIns K d i)
    (s : Nat → Runner.W) (hv : ∀ j, j < K → m.rd64 (slot fp (BitVec.ofNat 64 j)) = some (s j)) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * code.length), fp⟩ m' ∧ Agree fp d K m m' ∧
      ∀ j, j < K → m'.rd64 (slot fp (BitVec.ofNat 64 j)) = some (aluRun code s j) := by
  induction code generalizing m pc s with
  | nil => exact ⟨m, by simpa using Star.refl (⟨pc, fp⟩ : T) m, Agree.refl _ _ _ _, by simpa using hv⟩
  | cons i is ih =>
    have c1 : CodeAt m pc [i] := by simpa using codeAt_left (a := [i]) (b := is) hc
    obtain ⟨m1, s1, a1, v1⟩ := alu_step hF hK c1 (hs i (List.mem_cons_self ..)) s hv
    have c2 : CodeAt m1 (pc + BitVec.ofNat 64 (16 * [i].length)) is := by
      have far : CodeFar pc (i :: is).length fp K := hfar
      have far1 : CodeFar pc ([i].length + is.length) fp K := by simpa [Nat.add_comm] using far
      have h2 := codeAt_right (a := [i]) (b := is) hc
      exact h2.agree a1 (codeFar_right far1)
    obtain ⟨m2, s2, a2, v2⟩ := ih (hF.agree a1) c2
      (by have far : CodeFar pc (i :: is).length fp K := hfar
          have far1 : CodeFar pc ([i].length + is.length) fp K := by simpa [Nat.add_comm] using far
          exact codeFar_right far1 |> fun h => by simpa using h)
      (fun x hx => hs x (List.mem_cons_of_mem _ hx)) _ v1
    refine ⟨m2, ?_, a1.trans a2, by simpa using v2⟩
    have e : pc + BitVec.ofNat 64 (16 * (i :: is).length) =
        pc + BitVec.ofNat 64 (16 * [i].length) + BitVec.ofNat 64 (16 * is.length) := by
      rw [pc_add]; congr 2; simp only [List.length_cons, List.length_nil]; omega
    rw [e]
    exact s1.trans s2

end Gabbro.Stage0.Senke
