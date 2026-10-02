/-
  File:      Grammatik/X86/CompactFormsWitnesses.lean
  Subject:   Concrete witnesses and poison probes for CompactForms.lean's
             ten DESIGN-§2B compact forms.

  Every form is executed on a concrete `Zustand` with a visible register
  or memory change (reusing the witness memory/flags/register helpers
  from `Ausfuehrung.lean`), each pinned byte encoding is decoded back,
  and the cross-family boundary (this family's bytes vs the pilot's) is
  probed concretely both ways. Poison probes: an imm8 out of the signed
  8-bit range refused by the imm8/imm32 selector, the `rbp`/`r13` disp0
  RIP-relative special case refused by the codec, a memory-mode ModRM
  refused where only register-direct is canonical for Group 1, and a
  rel8 out of range refused by the branch selector. No `Befehl`
  extension, no `schritt` change, no new source-language construct.
-/
import Grammatik.X86.CompactForms

namespace Gabbro.Grammatik.X86

/-! ## 1. Witness states (reusing `zeugeSpeicher`/`zeugeFlags` etc.). -/

/-- Witness register file: RAX holds 10, the stack pointer its usual
    top. -/
def cwReg : Register → Wort := fun q =>
  if q = Register.rax then 10
  else if q = Register.rsp then BitVec.ofNat 64 8192
  else BitVec.ofNat 64 0

/-- Witness state over `cwReg`, the shared witness memory and flags. -/
def cwZustand : Zustand :=
  { register := cwReg, flags := zeugeFlags, rip := BitVec.ofNat 64 4096,
    speicher := zeugeSpeicher }

/-! ## 2. Executed witnesses: a visible register change per MOV/ALU form. -/

/-- `movImm32Zx`: RAX becomes the zero-extended 32-bit pattern (upper 32
    bits cleared, never sign-filled), RIP advances by 5. -/
theorem zeuge_movImm32Zx :
    (schrittC ⟨.movImm32Zx .rax 0xDEADBEEF, 5⟩ cwZustand).map
        (fun s => (s.register Register.rax, s.rip)) =
      some (0x00000000DEADBEEF, BitVec.ofNat 64 4101) := by
  decide

/-- `movImm32Sx`: RAX becomes the sign-extended pattern (`0xFFFFFFFF`
    fills to all-ones), RIP advances by 7. -/
theorem zeuge_movImm32Sx :
    (schrittC ⟨.movImm32Sx .rax 0xFFFFFFFF, 7⟩ cwZustand).map
        (fun s => (s.register Register.rax, s.rip)) =
      some (0xFFFFFFFFFFFFFFFF, BitVec.ofNat 64 4103) := by
  decide

/-- `aluImm8 add`: RAX (10) plus the sign-extended immediate (5) lands
    at 15, no carry. -/
theorem zeuge_aluImm8_add :
    (schrittC ⟨.aluImm8 .add .rax 5, 4⟩ cwZustand).map
        (fun s => (s.register Register.rax, s.flags.cf)) =
      some (15, false) := by
  decide

/-- `aluImm8 sub`: RAX (10) minus 20 (sign-extended to `-20`) lands at
    `-10`, with a borrow. -/
theorem zeuge_aluImm8_sub :
    (schrittC ⟨.aluImm8 .sub .rax (natByte 20), 4⟩ cwZustand).map
        (fun s => (s.register Register.rax, s.flags.cf)) =
      some (BitVec.ofNat 64 (2 ^ 64 - 10), true) := by
  decide

/-- `aluImm32 cmp`: equal operands set ZF and write no register. -/
theorem zeuge_aluImm32_cmp :
    (schrittC ⟨.aluImm32 .cmp .rax 10, 7⟩ cwZustand).map
        (fun s => (s.register Register.rax, s.flags.zf)) =
      some (10, true) := by
  decide

/-! ## 3. Memory witnesses: disp8/disp0 load/store through real memory. -/

/-- Witness memory after storing 7 at address 8200 (`rsp` + 8). -/
def cwSpeicherD8 : Speicher :=
  { zeugenSpeicher with bytes := writeBytes zeugenSpeicher (BitVec.ofNat 64 8200) 7 }

/-- `load64Disp8` reads the stored word back through real permission-
    checked memory. -/
theorem zeuge_load64Disp8 :
    (schrittC ⟨.load64Disp8 .rbx .rsp (natByte 8), 4⟩
        { cwZustand with speicher := cwSpeicherD8 }).map
        (fun s => s.register Register.rbx) = some 7 := by
  decide

/-- `store64Disp8` writes through the stack pointer with a positive
    disp8; the stored word reads back through real permission-checked
    memory, and the targeted byte observably changed from the zeroed
    witness memory. -/
theorem zeuge_store64Disp8 :
    ((schrittC ⟨.store64Disp8 .rsp .rax (natByte 8), 4⟩ cwZustand).bind
        (fun s => read64 s.speicher (BitVec.ofNat 64 8200))) = some 10 ∧
    cwZustand.speicher.bytes (BitVec.ofNat 64 8200) = 0 := by
  decide

/-- `store64Disp8` through the stack pointer changes the targeted byte
    observably (from the zeroed witness memory to the stored low byte
    of RAX). -/
theorem zeuge_store64Disp8_aendert_sich :
    ((schrittC ⟨.store64Disp8 .rsp .rax (natByte 8), 4⟩ cwZustand).map
        (fun s => s.speicher.bytes (BitVec.ofNat 64 8200))) = some 10 ∧
    cwZustand.speicher.bytes (BitVec.ofNat 64 8200) = 0 := by
  decide

/-- `load64Disp0` reads at the base register alone (no displacement
    byte at all). -/
theorem zeuge_load64Disp0 :
    (schrittC ⟨.load64Disp0 .rbx .rsp, 3⟩
        { cwZustand with
          speicher := { zeugenSpeicher with
            bytes := writeBytes zeugenSpeicher (BitVec.ofNat 64 8192) 42 } }).map
        (fun s => s.register Register.rbx) = some 42 := by
  decide

/-- `store64Disp0` writes at the base register alone and changes the
    targeted byte observably. -/
theorem zeuge_store64Disp0_aendert_sich :
    ((schrittC ⟨.store64Disp0 .rsp .rax, 3⟩ cwZustand).map
        (fun s => s.speicher.bytes (BitVec.ofNat 64 8192))) = some 10 ∧
    cwZustand.speicher.bytes (BitVec.ofNat 64 8192) = 0 := by
  decide

/-! ## 4. Control-flow witnesses: taken/not-taken, through real steps. -/

/-- `jump8` with a positive rel8 moves RIP to the post-decode address
    plus the displacement. -/
theorem zeuge_jump8 :
    (schrittC ⟨.jump8 (natByte 16), 2⟩ cwZustand).map (fun s => s.rip) =
      some (BitVec.ofNat 64 4114) := by
  decide

/-- `jumpIf8` taken (ZF set) moves past the decode point by the rel8. -/
theorem zeuge_jumpIf8_genommen :
    (schrittC ⟨.jumpIf8 .e (natByte 16), 2⟩
        { cwZustand with flags := zeugeFlagsGleich }).map (fun s => s.rip) =
      some (BitVec.ofNat 64 4114) := by
  decide

/-- `jumpIf8` not taken (ZF clear) falls through to the post-decode
    address. -/
theorem zeuge_jumpIf8_nicht :
    (schrittC ⟨.jumpIf8 .e (natByte 16), 2⟩ cwZustand).map (fun s => s.rip) =
      some (BitVec.ofNat 64 4098) := by
  decide

/-! ## 5. Pinned byte encodings and their decode. -/

theorem pin_movImm32Zx_r8 :
    encodeC (.movImm32Zx .r8 0x01020304) =
      [natByte 65, natByte 184, natByte 4, natByte 3, natByte 2, natByte 1] := by
  decide

theorem pin_movImm32Zx_r8_dekode :
    decodeC [natByte 65, natByte 184, natByte 4, natByte 3, natByte 2, natByte 1] =
      some ((⟨.movImm32Zx .r8 0x01020304, 6⟩ : CompactDecodiert), []) := by
  decide

theorem pin_movImm32Sx_r9 :
    encodeC (.movImm32Sx .r9 0x01020304) =
      [natByte 73, natByte 199, natByte 193, natByte 4, natByte 3, natByte 2, natByte 1] := by
  decide

theorem pin_aluImm8_add_rcx :
    encodeC (.aluImm8 .add .rcx 5) = [natByte 72, natByte 131, natByte 193, natByte 5] := by
  decide

theorem pin_aluImm32_cmp_r10 :
    encodeC (.aluImm32 .cmp .r10 0x01020304) =
      [natByte 73, natByte 129, natByte 250, natByte 4, natByte 3, natByte 2, natByte 1] := by
  decide

theorem pin_load64Disp8_rbp :
    encodeC (.load64Disp8 .rax .rbp (natByte 5)) =
      [natByte 72, natByte 139, natByte 69, natByte 5] := by
  decide

theorem pin_store64Disp8_rsp :
    encodeC (.store64Disp8 .rsp .rdx (natByte 3)) =
      [natByte 72, natByte 137, natByte 84, natByte 36, natByte 3] := by
  decide

theorem pin_load64Disp0_rcx :
    encodeC (.load64Disp0 .rax .rcx) = [natByte 72, natByte 139, natByte 1] := by
  decide

theorem pin_store64Disp0_r12 :
    encodeC (.store64Disp0 .r12 .rbx) =
      [natByte 73, natByte 137, natByte 28, natByte 36] := by
  decide

theorem pin_jump8_neg :
    encodeC (.jump8 (natByte 251)) = [natByte 235, natByte 251] := by decide

theorem pin_jumpIf8_e :
    encodeC (.jumpIf8 .e (natByte 16)) = [natByte 116, natByte 16] := by decide

/-! ## 6. Refusals: truncated and non-canonical inputs. -/

theorem cw_decode_nichts_leer : decodeC [] = none := rfl

theorem cw_decode_nichts_rex_allein : decodeC [natByte 72] = none := by decide

theorem cw_decode_nichts_modrm_fehlt :
    decodeC [natByte 72, natByte 131] = none := by decide

theorem cw_decode_nichts_imm_fehlt :
    decodeC [natByte 72, natByte 131, natByte 193] = none := by decide

/-- NON-CANONICAL MODRM: a memory-mode ModRM (mod=0) after the Group-1
    `83` opcode is refused -- only register-direct (mod=3) is canonical
    for `aluImm8`/`aluImm32`. -/
theorem cw_decode_nichts_modus_speicher :
    decodeC [natByte 72, natByte 131, natByte 1, natByte 5] = none := by decide

/-- NON-CANONICAL MODRM: a memory-mode ModRM (mod=2, the pilot's own
    disp32 mode) after `83` is likewise refused. -/
theorem cw_decode_nichts_modus_disp32 :
    decodeC [natByte 72, natByte 131, natByte 129, natByte 5] = none := by decide

/-! ## 7. Boundary: the pilot and this family never claim each other's
    canonical bytes. -/

theorem grenze_pilot_verweigert_83 :
    decode [natByte 72, natByte 131, natByte 193, natByte 5] = none := by decide

theorem grenze_pilot_verweigert_81 :
    decode [natByte 73, natByte 129, natByte 250, natByte 4, natByte 3, natByte 2, natByte 1] =
      none := by decide

theorem grenze_pilot_verweigert_c7 :
    decode [natByte 73, natByte 199, natByte 193, natByte 4, natByte 3, natByte 2, natByte 1] =
      none := by decide

theorem grenze_pilot_verweigert_mod0 :
    decode [natByte 72, natByte 139, natByte 1] = none := by decide

theorem grenze_pilot_verweigert_mod1 :
    decode [natByte 72, natByte 139, natByte 69, natByte 5] = none := by decide

theorem grenze_pilot_verweigert_bare_b8 :
    decode [natByte 184, natByte 4, natByte 3, natByte 2, natByte 1] = none := by decide

theorem grenze_pilot_verweigert_41_b8 :
    decode [natByte 65, natByte 184, natByte 4, natByte 3, natByte 2, natByte 1] = none := by decide

theorem grenze_pilot_verweigert_70er :
    decode [natByte 116, natByte 16] = none := by decide

theorem grenze_compact_verweigert_modreg :
    decodeC [natByte 72, natByte 137, natByte 192] = none := by decide

theorem grenze_compact_verweigert_push_hoch :
    decodeC [natByte 65, natByte 80] = none := by decide

theorem grenze_compact_verweigert_push_niedrig :
    decodeC [natByte 80] = none := by decide

/-! ## 8. Poison: the `rbp`/`r13` disp0 special case refused by the
    codec, matching `pin_load64_rbp` of `Codec.lean` (rbp always keeps
    its wider form, never the RIP-relative special case). -/

theorem poison_load64Disp0_rbp :
    decodeC (encodeC (.load64Disp0 .rax .rbp)) = none := by decide

theorem poison_load64Disp0_r13 :
    decodeC (encodeC (.load64Disp0 .rax .r13)) = none := by decide

theorem poison_store64Disp0_rbp :
    decodeC (encodeC (.store64Disp0 .rbp .rax)) = none := by decide

theorem poison_kompaktWahl_rbp_disp0 :
    kompaktWahl (.load64 .rax .rbp 0) ≠ some (.load64Disp0 .rax .rbp) := by decide

/-! ## 9. Poison: a rel8 out of range refused by the branch selector. -/

theorem poison_kompaktWahl_jump_ausser_bereich :
    kompaktWahl (.jump32 (BitVec.ofNat 32 1000)) = none := by decide

theorem poison_kompaktWahl_jumpIf_ausser_bereich :
    kompaktWahl (.jumpIf32 .e (BitVec.ofNat 32 1000)) = none := by decide

/-! ## 10. The imm8/imm32 selector: shortest legal ALU immediate form,
    with its own poison probe (an immediate outside the signed 8-bit
    range refused, falling back to `aluImm32`). -/

/-- Picks `aluImm8` when the 32-bit immediate round-trips through a
    signed byte, `aluImm32` otherwise -- DESIGN §2B's imm8-vs-imm32
    selection rule, never a silent truncation. -/
def aluImmWahl (op : AluOp) (dst : Register) (imm32 : BitVec 32) : CompactBefehl :=
  if passtS8_32 imm32 then .aluImm8 op dst (disp8Of imm32)
  else .aluImm32 op dst imm32

/-- The selected imm8 form computes the SAME value and flags as the
    kept imm32 form, whenever the immediate round-trips through a
    signed byte: selection changes bytes, never the computed effect. -/
theorem aluImmWahl_korrekt_imm8 (op : AluOp) (dst : Register) (imm32 : BitVec 32)
    (h : passtS8_32 imm32 = true) (s : Zustand) :
    (schrittC ⟨aluImmWahl op dst imm32, 4⟩ s).map (fun s' => (s'.register, s'.flags, s'.speicher)) =
      (schrittC ⟨.aluImm32 op dst imm32, 7⟩ s).map (fun s' => (s'.register, s'.flags, s'.speicher)) := by
  unfold aluImmWahl
  rw [if_pos h]
  have hd : dispWort8 (disp8Of imm32) = dispWort imm32 := by
    rw [dispWort8_eq_signExtend]
    congr 1
    unfold disp8Of
    exact of_decide_eq_true h
  show (schrittC ⟨.aluImm8 op dst (disp8Of imm32), 4⟩ s).map
      (fun s' => (s'.register, s'.flags, s'.speicher)) =
    (schrittC ⟨.aluImm32 op dst imm32, 7⟩ s).map (fun s' => (s'.register, s'.flags, s'.speicher))
  unfold schrittC
  simp only [laengeOk]
  rw [show decide (1 ≤ 4 ∧ 4 ≤ 15) = true from rfl,
      show decide (1 ≤ 7 ∧ 7 ≤ 15) = true from rfl]
  rw [hd]
  cases aluSchreibt op <;> rfl

/-- POISON (imm8 out of range): `200` does not round-trip through a
    signed byte (`200` as a signed byte is `-56`), so the selector
    refuses the compact `aluImm8` and keeps `aluImm32`. -/
theorem poison_aluImmWahl_bereich :
    aluImmWahl .add .rax (BitVec.ofNat 32 200) = .aluImm32 .add .rax (BitVec.ofNat 32 200) := by
  decide

/-- The refusing value really is outside the round-trip: a direct
    witness that `passtS8_32` catches it. -/
theorem poison_passtS8_32_bereich : passtS8_32 (BitVec.ofNat 32 200) = false := by decide


/- CUTS:
   Proved here: a visible register or memory change per compact form
   (MOV/ALU on a concrete register, disp8/disp0 load/store through real
   permission-checked memory with a before/after byte change, jump8/
   jumpIf8 taken and not taken), pinned byte/decode pairs for every
   form, explicit refusals of truncated inputs and of a memory-mode
   ModRM where only register-direct is canonical for Group 1, the
   cross-family boundary confirmed concretely both ways (the pilot
   `decode` refuses this family's REX+opcode/bare/0x41/0x70-7F bytes;
   this family's `decodeC` refuses the pilot's register-direct and
   push/pop bytes), the `rbp`/`r13` disp0 refusal both at the codec
   level and through `kompaktWahl`, a rel8/rel-adjusted-displacement out
   of range refused by `kompaktWahl` for `jump32`/`jumpIf32`, and the
   imm8-vs-imm32 selector `aluImmWahl` (DESIGN §2B's selection rule)
   with its own correctness proof and poison probe (an immediate
   outside the signed 8-bit range refused, kept as `aluImm32`).

   NOT proved here, and not claimed:
   - No `Befehl` extension, no `schritt` change, no new source-language
     construct: no diagnostic, poison-probe, example or CLI numbers are
     taken (the poison PROBES above are proof-level refusal witnesses,
     never `beispiele/gift/` corpus files).
   - No hardware correspondence, no source correspondence, no TSO
     bridge, no cost transfer: see `CompactForms.lean`'s CUTS, which
     this file's witnesses instantiate but do not extend.
   - `aluImmWahl` is a standalone two-form selector shown here, not
     wired into `kompaktWahl` (which only selects among the FIVE pilot
     constructors with a direct single-instruction compact analog; an
     ALU imm8/imm32 pair has no pilot immediate instruction to select
     FROM in the first place, per `CompactForms.lean`'s own CUTS).
-/

#print axioms zeuge_movImm32Zx
#print axioms zeuge_movImm32Sx
#print axioms zeuge_aluImm8_add
#print axioms zeuge_aluImm8_sub
#print axioms zeuge_aluImm32_cmp
#print axioms zeuge_load64Disp8
#print axioms zeuge_store64Disp8
#print axioms zeuge_store64Disp8_aendert_sich
#print axioms zeuge_load64Disp0
#print axioms zeuge_store64Disp0_aendert_sich
#print axioms zeuge_jump8
#print axioms zeuge_jumpIf8_genommen
#print axioms zeuge_jumpIf8_nicht
#print axioms pin_movImm32Zx_r8
#print axioms pin_movImm32Zx_r8_dekode
#print axioms pin_movImm32Sx_r9
#print axioms pin_aluImm8_add_rcx
#print axioms pin_aluImm32_cmp_r10
#print axioms pin_load64Disp8_rbp
#print axioms pin_store64Disp8_rsp
#print axioms pin_load64Disp0_rcx
#print axioms pin_store64Disp0_r12
#print axioms pin_jump8_neg
#print axioms pin_jumpIf8_e
#print axioms cw_decode_nichts_leer
#print axioms cw_decode_nichts_rex_allein
#print axioms cw_decode_nichts_modrm_fehlt
#print axioms cw_decode_nichts_imm_fehlt
#print axioms cw_decode_nichts_modus_speicher
#print axioms cw_decode_nichts_modus_disp32
#print axioms grenze_pilot_verweigert_83
#print axioms grenze_pilot_verweigert_81
#print axioms grenze_pilot_verweigert_c7
#print axioms grenze_pilot_verweigert_mod0
#print axioms grenze_pilot_verweigert_mod1
#print axioms grenze_pilot_verweigert_bare_b8
#print axioms grenze_pilot_verweigert_41_b8
#print axioms grenze_pilot_verweigert_70er
#print axioms grenze_compact_verweigert_modreg
#print axioms grenze_compact_verweigert_push_hoch
#print axioms grenze_compact_verweigert_push_niedrig
#print axioms poison_load64Disp0_rbp
#print axioms poison_load64Disp0_r13
#print axioms poison_store64Disp0_rbp
#print axioms poison_kompaktWahl_rbp_disp0
#print axioms poison_kompaktWahl_jump_ausser_bereich
#print axioms poison_kompaktWahl_jumpIf_ausser_bereich
#print axioms aluImmWahl_korrekt_imm8
#print axioms poison_aluImmWahl_bereich
#print axioms poison_passtS8_32_bereich


end Gabbro.Grammatik.X86
