import Grammatik.Code.Model.Facts
import Grammatik.Code.Model.Weak

/-
  File:      Grammatik/Code/Model/Need.lean
  Subject:   TRACK L -- WHAT A CPU MODEL MUST PROVIDE for the later step `Code -> bytes`.
             The same list for x86-64, AArch64 and RISC-V. This is a STATEMENT OF OBLIGATIONS, not an
             instance and not an ISA model.

  Two halves.

  (1) What `Code` already GUARANTEES, proved here, so that no backend has to handle the places
      where the ISAs disagree: division and remainder have a nonzero divisor (x86 traps, AArch64
      answers 0, RISC-V answers -1), `INT_MIN / -1` never happens, a shift amount is below the
      width (the ISAs mask differently), every memory access is aligned, every atomic access is on
      a word-sized cell. In each case the `Code` step is STUCK otherwise (`code_pre_*`).

  (2) What the CPU side must supply, the structure `Need`: for a CPU state type `Mach`, a relation
      `Rel` that says "this CPU state holds this `Code` memory and register file" (byte memory in
      the target byte order `Conf.big`, words of width `Conf.wbits`) and a relation `Exec` that says
      "the CPU runs the machine code of this instruction from one state to another". Then the
      obligations are exactly: every DEFINED plain `Code` step is simulated (wraparound
      arithmetic at the word width, loads and stores of aligned scalars, stack cells), every
      DEFINED terminator is simulated (fused compare-and-branch, jump, switch, return), an atomic
      load returns a value the weak-memory interface `Sees` allows (the machine-level atomics
      are the abstract operations `armw`/`cas`: lock prefix, LL/SC or AMO is the backend's
      choice), and a fence orders as `Order.toOrdnung` says. NOTHING is asked where `Code` is
      stuck. No obligation mentions condition flags, a register count, a register class, an ABI
      number or a stack layout: those are the backend's.
-/

namespace Gabbro.Code

variable [Conf]

/-! ## (1) What `Code` guarantees -/

/-- A defined division has a nonzero divisor. -/
theorem code_pre_div (op : BinOp) (hop : op = .udiv ∨ op = .urem ∨ op = .sdiv ∨ op = .srem)
    (w : Nat) (a b : BitVec w) (h : (op.ap w a b).isSome = true) : b ≠ 0 := by
  intro hb
  subst hb
  rcases hop with rfl | rfl | rfl | rfl <;> simp [BinOp.ap] at h

/-- A defined signed division or remainder is not `INT_MIN / -1`. -/
theorem code_pre_sdiv (op : BinOp) (hop : op = .sdiv ∨ op = .srem) (w : Nat) (a b : BitVec w)
    (h : (op.ap w a b).isSome = true) :
    ¬ (a.toInt = -((2 : Int) ^ (w - 1)) ∧ b.toInt = -1) := by
  intro hc
  rcases hop with rfl | rfl <;> simp [BinOp.ap, hc] at h

/-- A defined shift has an amount below the width. -/
theorem code_pre_shift (op : BinOp) (hop : op = .shl ∨ op = .lshr ∨ op = .ashr) (w : Nat)
    (a b : BitVec w) (h : (op.ap w a b).isSome = true) : b.toNat < w := by
  cases hc : decide (b.toNat < w)
  · have hn : ¬ b.toNat < w := by simpa using hc
    rcases hop with rfl | rfl | rfl <;> simp [BinOp.ap, hn] at h
  · simpa using hc

/-- A defined load or store is aligned. -/
theorem code_pre_align_load {m : Mem} {b : Nat} {o : Int} {t : Ty} {v : Val}
    (h : m.load b o t = some v) : o % (t.align : Int) = 0 := by
  unfold Mem.load at h
  cases hb : m.blks b with
  | none => simp [hb] at h
  | some blk =>
      simp only [hb] at h
      by_cases hi : Mem.inside blk.size o t
      · exact hi.2.2.2
      · simp [hi] at h

theorem code_pre_align_store {m m' : Mem} {b : Nat} {o : Int} {t : Ty} {v : Val}
    (h : m.store b o t v = some m') : o % (t.align : Int) = 0 := by
  obtain ⟨blk, _, hin, _, _⟩ := store_some h
  exact hin.2.2.2

/-! ## (2) What the CPU must provide -/

/-- **The obligations.** `Rel m rs x`: the CPU state `x` holds the `Code` memory `m` and register
    file `rs`. `Exec i x y`: the CPU runs the machine code of instruction `i` from `x` to `y`
    (`Jump t x y` for a terminator). Every field is a Prop; none is assumed here. -/
structure Need (Mach : Type) (Rel : Mem → Regs → Mach → Prop) (Exec : Instr → Mach → Mach → Prop)
    (Jump : Term → Mach → Mach → Prop) : Prop where
  /-- Every DEFINED plain `Code` step is simulated: wraparound arithmetic and comparisons at the
      explicit width, conversions, aligned scalar loads and stores, stack cells, address
      arithmetic, the abstract read-modify-write and compare-and-swap, the fence. -/
  plain : ∀ i m rs m' rs' x, stepI i m rs = some (m', rs') → Rel m rs x →
    ∃ y, Exec i x y ∧ Rel m' rs' y
  /-- An atomic load returns a value the memory-model interface allows. -/
  atomic : ∀ (S : Sees) d t p o m rs x b off, Rel m rs x →
    p.ev rs = some (.ptr b off) → atomicOk t = true →
    ∃ y v, Exec (.aload d t p o) x y ∧ S m b off t o v ∧ Rel m (rs.set d v) y
  /-- A terminator whose step is DEFINED and stays in the function (a jump, a branch, a fused
      compare-and-branch, a switch) is simulated: the CPU moves to the target block with the
      registers the step leaves (the phis of the target included). -/
  branch : ∀ (M : Modl) t m (f g : Frame) (ks : List Frame) x,
    stepTerm M t m f ks = some (.run m g ks) → Rel m f.regs x →
    ∃ y, Jump t x y ∧ Rel m g.regs y

end Gabbro.Code
