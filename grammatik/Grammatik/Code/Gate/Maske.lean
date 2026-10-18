import Grammatik.Code.Gate.Gate
import Grammatik.Code.Conc.Mask

/-
  File:      Grammatik/Code/Gate/Maske.lean
  Subject:   TRACK L -- THE INTERRUPT MASK AS A USER GATE (L6).  PLAN-HARDWARE.md section 16.7.

  `Code` has the abstract instruction `Instr.imsk d p v` (`d := old word; word := v`) and the named
  assumption `MaskHw` (`Conc/MaskNeed.lean`); the compiler lowered it with a table of its own (x86
  `pushfq; cli; popq`, aarch64 `mrs daif; msr daifset`). The proposal is that the PROGRAM declares the
  exchange as a gate, `mask via xmask;` with `xmask` a user `asm` function whose contract is the
  exchange, so no mask instruction is built into the compiler. This file shows the exchange gate IS
  `imsk`: the contract `maskSpec` has exactly one outcome (`maskSpec_eindeutig`), and it is the one
  `stepI` of `imsk` computes (`maskSpec_ist_imsk`). So `imsk` needs no instruction of its own in the
  lowering: a call of the user's gate with this contract is the same step, and `MaskHw`
  (H1-H3: the cell IS the register, an interrupt only on an unmasked core) stays the gate's named
  assumption.

  No `sorry`, no `native_decide`, no new axiom.
-/

namespace Gabbro.Code

variable [Conf]

open Lower

/-- The exchange contract on the mask word of block `mb`: read the old word, store the new one,
    answer the old one. -/
def maskSpec (mb : Nat) : GateSpec where
  pre m vs := ∃ w, vs = [w] ∧ (m.load mb 0 lw).isSome = true ∧ (m.store mb 0 lw w).isSome = true
  post m vs m' ans := ∃ w old, vs = [w] ∧ m.load mb 0 lw = some old ∧
    m.store mb 0 lw w = some m' ∧ ans = some old

/-- **The contract has exactly one outcome**: loads and stores are functions. -/
theorem maskSpec_eindeutig {mb : Nat} {m : Mem} {vs : List Val} {m1 m2 : Mem} {a1 a2 : Option Val}
    (h1 : (maskSpec mb).post m vs m1 a1) (h2 : (maskSpec mb).post m vs m2 a2) :
    m1 = m2 ∧ a1 = a2 := by
  obtain ⟨w, o, hv, hl, hs, ha⟩ := h1
  obtain ⟨w', o', hv', hl', hs', ha'⟩ := h2
  have hw : w = w' := by
    rw [hv] at hv'
    exact List.head_eq_of_cons_eq hv'
  subst hw
  rw [hl] at hl'
  cases hl'
  rw [hs] at hs'
  cases hs'
  exact ⟨rfl, by rw [ha, ha']⟩

/-- **The gate is `imsk`**: an outcome of the exchange contract is exactly what `stepI` of
    `imsk` computes on the same memory and word. -/
theorem maskSpec_ist_imsk {mb : Nat} {m m' : Mem} {rs : Regs} {d : Reg} {v : Opd} {w x : Val}
    (hv : v.ev rs = some w) (h : (maskSpec mb).post m [w] m' (some x)) :
    stepI (.imsk d (.glob mb) v) m rs = some (m', rs.set d x) := by
  obtain ⟨w', o, hvs, hl, hs, ha⟩ := h
  have hw : w' = w := by
    have := List.head_eq_of_cons_eq hvs
    exact this.symm
  subst hw
  cases ha
  exact stepI_imsk hl hv hs

/-- And back: when `stepI` of `imsk` is defined, the contract has that outcome. -/
theorem imsk_ist_maskSpec {mb : Nat} {m m' : Mem} {rs : Regs} {d : Reg} {v : Opd} {w x : Val}
    (hv : v.ev rs = some w) (hl : m.load mb 0 lw = some x) (hs : m.store mb 0 lw w = some m') :
    (maskSpec mb).post m [w] m' (some x) ∧ (maskSpec mb).pre m [w] ∧
      stepI (.imsk d (.glob mb) v) m rs = some (m', rs.set d x) :=
  ⟨⟨w, x, rfl, hl, hs, rfl⟩, ⟨w, rfl, by simp [hl], by simp [hs]⟩, stepI_imsk hl hv hs⟩

end Gabbro.Code
