import Runner.X86.Dec

/-! # The instruction layer: decoding an encoded instruction gives it back

`decode_enc`: for every instruction of the subset that `enc` can encode, the decoder reads exactly its bytes and
answers it, whatever follows. The handler proofs fetch through this theorem, so they hold at every address and do
not depend on where the assembler placed a handler. -/

namespace Runner.X86

theorem byte_toNat (n : Nat) : (byte n).toNat = n % 256 := by simp [byte]

theorem Reg.ofNum_num (r : Reg) : Reg.ofNum r.num = r := by cases r <;> rfl

theorem Reg.num_lt (r : Reg) : r.num < 16 := by cases r <;> decide

theorem Reg.ofNum_eq {n : Nat} {r : Reg} (h : n = r.num) : Reg.ofNum n = r := by
  rw [h, Reg.ofNum_num]

theorem Reg.num_ne_four {r : Reg} (h : r ≠ .rsp) : r.num ≠ 4 := by
  cases r <;> simp_all [Reg.num]

theorem le32_val (v : BitVec 32) :
    BitVec.ofNat 32 (v.toNat % 256 + 256 * (v.toNat / 256 % 256) + 65536 * (v.toNat / 65536 % 256) +
      16777216 * (v.toNat / 16777216 % 256)) = v := by
  have := v.isLt
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  omega

/-- Unfold encoder and decoder, decide every branch condition by `omega`, match the fields. -/
macro "dec_enc" : tactic => `(tactic| (
  simp [enc, memEnc, regEnc, le32, rex, modrm, decode, decRex, decW, decW0F, opd, bt, imm32, byte_toNat,
    Alu.opc, Alu.ext, Cond.cc, Alu.ofOpc, Alu.ofExt, Cond.ofCc, List.getElem?_cons] <;>
  simp (disch := omega) only [ite_eq_left, ite_eq_right, ↓reduceIte, Option.getD_some, Option.map_some,
    byte_toNat, le32_val, Option.some.injEq, Prod.mk.injEq,
    Ins.ld.injEq, Ins.st.injEq, Ins.mov.injEq, Ins.movi.injEq, Ins.ldsx.injEq, Ins.ldzx.injEq, Ins.zx8.injEq,
    Ins.lea.injEq, Ins.alu.injEq, Ins.alui.injEq, Ins.imul.injEq, Ins.idiv.injEq, Ins.shl.injEq, Ins.shr.injEq,
    Ins.set.injEq, Ins.jmp.injEq, Ins.jcc.injEq, Ins.jmpm.injEq, Ins.cmpxchg.injEq, Addr.mk.injEq] <;>
  and_intros <;> first | exact Reg.ofNum_eq (by omega) | omega | trivial | rfl))

set_option maxHeartbeats 2000000 in
theorem decode_enc (i : Ins) (h : i.ok = true) (rest : List B) :
    decode (enc i ++ rest) = some (i, (enc i).length) := by
  cases i with
  | ld d m | st m d | ldsx d m | ldzx d m | lea d m | cmpxchg m d =>
    have := Reg.num_lt d
    rcases m with ⟨b, _ | x, sc, disp⟩ <;> have := Reg.num_lt b <;>
      simp [Ins.ok, Addr.ok] at h
    · dec_enc
    · have := Reg.num_lt x
      have := Reg.num_ne_four h.2
      dec_enc
  | jmpm m =>
    rcases m with ⟨b, _ | x, sc, disp⟩ <;> have := Reg.num_lt b <;>
      simp [Ins.ok, Addr.ok] at h
    · dec_enc
    · have := Reg.num_lt x
      have := Reg.num_ne_four h.2
      dec_enc
  | mov d s | zx8 d s | imul d s =>
    have := Reg.num_lt d
    have := Reg.num_lt s
    dec_enc
  | movi d v | idiv d | shl d | shr d =>
    have := Reg.num_lt d
    dec_enc
  | alu o d s =>
    have := Reg.num_lt d
    have := Reg.num_lt s
    cases o <;> dec_enc
  | alui o d v =>
    have := Reg.num_lt d
    cases o <;> simp [Ins.ok] at h <;> dec_enc
  | set c d =>
    have := Reg.num_lt d
    cases c <;> dec_enc
  | jcc c v => cases c <;> dec_enc
  | jmp v | cqo | syscall | ud2 => dec_enc

end Runner.X86
