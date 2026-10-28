import Grammatik.Code.Conc.LockRel

/-
  File:      Grammatik/Code/Conc/Mask.lean
  Subject:   TRACK L, PHASE L3 -- A LOCK DECLARED `masks irqs` AS `Code`: the two blocks around the ticket lock
             that switch the executing core's interrupt mask, and the runs of a thread through them.

  Machine G's lock `L` with `D.maskiert L = true` (`lock L ... masks irqs`) masks the core of its holder while it is
  held (`Zielsatz/Eigenschaften/KernMaske.lean`: the per-core mask state, the entry guard of an interrupt handler).
  The IR realises that with ONE hardware form, `Instr.imsk d p v` (`d := old word at p; word at p := v`, nonzero
  masks), on the executing core's mask word `mb`:

      maskOn  : rm := imsk(mb, 1)                    -- BEFORE the ticket is taken: the spin runs masked
      ...       the ticket lock of `Conc/Lock.lean`   (take, spin, body, release)
      maskOff : rx := imsk(mb, rm)                   -- AFTER the release: the SAVED word comes back

  The saved word makes nesting right with no static knowledge of the callers: a masking lock taken inside another
  masking section restores `1`, the outermost restores `0`. The cell `mb` is the core's architectural mask word,
  not RAM: that it behaves as the CPU's mask, and that an interrupt (and a context switch) is taken only while the
  word is zero, is the NAMED hardware assumption of `Conc/MaskNeed.lean`. The runs here are the thread-local facts;
  the invariant against machine G's mask state is in `Conc/MaskRel.lean`.
-/

namespace Gabbro.Code.Lower

variable [Conf]

open Gabbro.Grammatik (Deklaration)

variable {D : Deklaration}

/-- The word `1` is the ticket value `1`. -/
theorem wone_eq : Val.ofInt Conf.wbits 1 = tk 1 := by
  simp only [Val.ofInt, BitVec.ofInt_ofNat, tk]

/-- A set mask word is not the zero word. -/
theorem tk_one_ne : tk 1 ≠ tk 0 := by
  intro h
  have h2 : BitVec.ofNat Conf.wbits 1 = BitVec.ofNat Conf.wbits 0 := by
    simpa [tk] using h
  have h3 := ofNat_eq_iff.mp h2
  have hw : 1 < 2 ^ Conf.wbits := by
    rcases Conf.wide with h | h <;> rw [h] <;> decide
  rw [Nat.mod_eq_of_lt hw, Nat.zero_mod] at h3
  exact absurd h3 (by decide)

/-- **Mask the core**: `rm := imsk(mb, 1)` (the old word is saved in `rm`), then continue (the ticket take). -/
def maskOn (mb : Nat) (rm : Reg) (lb k : Lbl) : Block :=
  ⟨lb, [], [.imsk rm (.glob mb) (.int Conf.wbits 1)], .jmp k⟩

/-- **Restore the mask**: `rx := imsk(mb, rm)` -- the word saved before the lock comes back. -/
def maskOff (mb : Nat) (rm rx : Reg) (lb k : Lbl) : Block :=
  ⟨lb, [], [.imsk rx (.glob mb) (.reg rm)], .jmp k⟩

/-! ## 1. The instruction -/

/-- `imsk` exchanges the word at the mask cell and returns the old one. -/
theorem stepI_imsk {m m' : Mem} {rs : Regs} {d : Reg} {b : Nat} {x w : Val} {v : Opd}
    (hl : m.load b 0 lw = some x) (hv : v.ev rs = some w)
    (hs : m.store b 0 lw w = some m') :
    stepI (.imsk d (.glob b) v) m rs = some (m', rs.set d x) := by
  have h1 : (Opd.glob b).ev rs = some (.ptr b 0) := rfl
  have h2 : atomicOk (.int Conf.wbits) = true := atomicOk_lw
  have hl' : m.load b 0 (.int Conf.wbits) = some x := hl
  have hs' : m.store b 0 (.int Conf.wbits) w = some m' := hs
  simp only [stepI, h1, hv, h2, if_true, hl', hs', Option.map_some]

/-! ## 2. The runs of a thread -/

/-- **Mask**: from `maskOn` to the next block; the mask word is `1`, the register holds the old word. -/
theorem maskOn_run {mb : Nat} {rm : Reg} {M : Modl} {S : Sees} {fn : Nat} {lb k : Lbl} {bk : Block}
    (hb : M.blk fn lb = some (maskOn mb rm lb k)) (hk : M.blk fn k = some bk) (hkp : bk.phis = [])
    {m m' : Mem} {rs : Regs} {ks : List Frame} {dst : Option Reg} {x : Val}
    (hl : m.load mb 0 lw = some x) (hs : m.store mb 0 lw (tk 1) = some m') :
    Reach M S (.run m ⟨fn, lb, 0, rs, dst⟩ ks) (.run m' ⟨fn, k, 0, rs.set rm x, dst⟩ ks) :=
  reach_block_jmp (b := maskOn mb rm lb k) hb rfl hk hkp (by
    have hv : (Opd.int Conf.wbits 1).ev rs = some (tk 1) := by simp only [Opd.ev, wone_eq]
    simp only [maskOn, seqI, stepI_imsk hl hv hs])

/-- **Restore**: from `maskOff` to the next block; the mask word is the saved one. -/
theorem maskOff_run {mb : Nat} {rm rx : Reg} {M : Modl} {S : Sees} {fn : Nat} {lb k : Lbl} {bk : Block}
    (hb : M.blk fn lb = some (maskOff mb rm rx lb k)) (hk : M.blk fn k = some bk) (hkp : bk.phis = [])
    {m m' : Mem} {rs : Regs} {ks : List Frame} {dst : Option Reg} {x y : Val}
    (hrm : rs rm = some x) (hl : m.load mb 0 lw = some y)
    (hs : m.store mb 0 lw x = some m') :
    Reach M S (.run m ⟨fn, lb, 0, rs, dst⟩ ks) (.run m' ⟨fn, k, 0, rs.set rx y, dst⟩ ks) :=
  reach_block_jmp (b := maskOff mb rm rx lb k) hb rfl hk hkp (by
    have hv : (Opd.reg rm).ev rs = some x := hrm
    simp only [maskOff, seqI, stepI_imsk hl hv hs])

#print axioms Gabbro.Code.Lower.stepI_imsk
#print axioms Gabbro.Code.Lower.maskOn_run
#print axioms Gabbro.Code.Lower.maskOff_run

end Gabbro.Code.Lower
