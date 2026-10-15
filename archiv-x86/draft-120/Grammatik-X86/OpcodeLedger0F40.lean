/-
  File:      Grammatik/X86/OpcodeLedger0F40.lean
  Subject:   Opcode ledger for two-byte opcodes 0F 40-7F (64-bit mode).

  Lane 1343: one row per second opcode byte in 0F 40-7F, with the status of
  each row against the accepted Lean families. Modelled rows name the
  family decoder and carry a checked witness (the accepted round trip);
  every other row is a finding (`fehlt`). Checked part 4 pins which
  modelled rows the unified `kapDecode` chain takes: the CMOV rows (first
  arm `decodeMulDivWidth` -> `decodeExt` -> `decodeCmov`) and the
  scalar-prefix FP rows (second arm `s32Decode`); the IntVec rows and the
  unmodelled rows are refused by the whole chain.
-/
import Grammatik.X86.ControlCodec
import Grammatik.X86.ScalarFloat32HardwareForms
import Grammatik.X86.VectorIntegerHardwareForms
import Grammatik.X86.ExtendedExecution
import Grammatik.X86.HwKapsteinDecoder

namespace Gabbro.Grammatik.X86
namespace OpcodeLedger0F40

/-- Ledger status of one opcode row. -/
inductive LStatus where
  | modelliert
  | zurueckgestellt
  | verweigert
  | ungueltig64
  | fehlt
  deriving DecidableEq, Repr

/-- One ledger row: second opcode byte, mnemonic, status, modelling
    family/file, and a one-line reason for every non-`modelliert` row. -/
structure LEintrag where
  op : Nat
  mnem : String
  status : LStatus
  familie : String
  grund : String
  deriving DecidableEq, Repr

/-- The ledger: exactly one row per second byte 64-127 (0F 40-7F).
    CMOVcc 40-4F are modelled register-only via `ControlCodec.decodeCmov`
    (REX.W 0F 40+cc /r mod=3; memory sources refused by construction). -/
def ledger : List LEintrag :=
  [ ⟨64, "CMOVO", .modelliert, "ControlCodec.decodeCmov", ""⟩
  , ⟨65, "CMOVNO", .modelliert, "ControlCodec.decodeCmov", ""⟩
  , ⟨66, "CMOVB/CMOVC", .modelliert, "ControlCodec.decodeCmov", ""⟩
  , ⟨67, "CMOVAE/CMOVNC", .modelliert, "ControlCodec.decodeCmov", ""⟩
  , ⟨68, "CMOVE/CMOVZ", .modelliert, "ControlCodec.decodeCmov", ""⟩
  , ⟨69, "CMOVNE/CMOVNZ", .modelliert, "ControlCodec.decodeCmov", ""⟩
  , ⟨70, "CMOVBE/CMOVNA", .modelliert, "ControlCodec.decodeCmov", ""⟩
  , ⟨71, "CMOVA/CMOVNBE", .modelliert, "ControlCodec.decodeCmov", ""⟩
  , ⟨72, "CMOVS", .modelliert, "ControlCodec.decodeCmov", ""⟩
  , ⟨73, "CMOVNS", .modelliert, "ControlCodec.decodeCmov", ""⟩
  , ⟨74, "CMOVP/CMOVPE", .modelliert, "ControlCodec.decodeCmov", ""⟩
  , ⟨75, "CMOVNP/CMOVPO", .modelliert, "ControlCodec.decodeCmov", ""⟩
  , ⟨76, "CMOVL/CMOVNGE", .modelliert, "ControlCodec.decodeCmov", ""⟩
  , ⟨77, "CMOVNL/CMOVGE", .modelliert, "ControlCodec.decodeCmov", ""⟩
  , ⟨78, "CMOVLE/CMOVNG", .modelliert, "ControlCodec.decodeCmov", ""⟩
  , ⟨79, "CMOVNLE/CMOVG", .modelliert, "ControlCodec.decodeCmov", ""⟩
  , ⟨80, "MOVMSKPS/MOVMSKPD", .fehlt, "", "mask move to GPR: no family decodes F3/66 0F 50"⟩
  , ⟨81, "SQRTPS/SQRTSS/SQRTSD/SQRTPD", .fehlt, "", "packed and scalar square roots: s32 covers no 0F 51 row"⟩
  , ⟨82, "RSQRTPS/RSQRTSS", .fehlt, "", "approximate reciprocal sqrt: no family"⟩
  , ⟨83, "RCPPS/RCPSS", .fehlt, "", "approximate reciprocal: no family"⟩
  , ⟨84, "ANDPS/ANDPD", .fehlt, "", "packed bitwise AND: no family (scalar s32 has no logic rows)"⟩
  , ⟨85, "ANDNPS/ANDNPD", .fehlt, "", "packed AND-NOT: no family"⟩
  , ⟨86, "ORPS/ORPD", .fehlt, "", "packed bitwise OR: no family"⟩
  , ⟨87, "XORPS/XORPD", .fehlt, "", "packed bitwise XOR: no family (only packed-integer PXOR is modelled)"⟩
  , ⟨88, "ADDPS/ADDSS/ADDSD/ADDPD", .modelliert, "ScalarFloat32HardwareForms.s32Decode", "scalar SS row modelled; packed PS/PD and SD rows missing"⟩
  , ⟨89, "MULPS/MULSS/MULSD/MULPD", .modelliert, "ScalarFloat32HardwareForms.s32Decode", "scalar SS row modelled; packed PS/PD and SD rows missing"⟩
  , ⟨90, "CVTPS2PD/CVTSS2SD/CVTPD2PS/CVTSD2SS", .modelliert, "ScalarFloat32HardwareForms.s32Decode", "scalar convert rows modelled; packed converts missing"⟩
  , ⟨91, "CVTDQ2PS/CVTPS2DQ/CVTTPS2DQ", .fehlt, "", "packed int/float converts: no family"⟩
  , ⟨92, "SUBPS/SUBSS/SUBSD/SUBPD", .modelliert, "ScalarFloat32HardwareForms.s32Decode", "scalar SS row modelled; packed PS/PD and SD rows missing"⟩
  , ⟨93, "MINPS/MINSS/MINSD/MINPD", .fehlt, "", "packed and scalar minima: s32 has no MIN row"⟩
  , ⟨94, "DIVPS/DIVSS/DIVSD/DIVPD", .modelliert, "ScalarFloat32HardwareForms.s32Decode", "scalar SS row modelled; packed PS/PD and SD rows missing"⟩
  , ⟨95, "MAXPS/MAXSS/MAXSD/MAXPD", .fehlt, "", "packed and scalar maxima: s32 has no MAX row"⟩
  , ⟨96, "PUNPCKLBW", .fehlt, "", "interleave low bytes: IntVec has no unpack rows"⟩
  , ⟨97, "PUNPCKLWD", .fehlt, "", "interleave low words: no family"⟩
  , ⟨98, "PUNPCKLDQ", .fehlt, "", "interleave low dwords: no family"⟩
  , ⟨99, "PACKSSWB", .fehlt, "", "pack with signed saturation: no family"⟩
  , ⟨100, "PCMPGTB", .fehlt, "", "packed byte greater-compare: no family"⟩
  , ⟨101, "PCMPGTW", .fehlt, "", "packed word greater-compare: no family"⟩
  , ⟨102, "PCMPGTD", .fehlt, "", "packed dword greater-compare: no family"⟩
  , ⟨103, "PACKUSWB", .fehlt, "", "pack with unsigned saturation: no family"⟩
  , ⟨104, "PUNPCKHBW", .fehlt, "", "interleave high bytes: no family"⟩
  , ⟨105, "PUNPCKHWD", .fehlt, "", "interleave high words: no family"⟩
  , ⟨106, "PUNPCKHDQ", .fehlt, "", "interleave high dwords: no family"⟩
  , ⟨107, "PACKSSDW", .fehlt, "", "pack dwords with signed saturation: no family"⟩
  , ⟨108, "PUNPCKLQDQ", .fehlt, "", "interleave low quadwords: no family"⟩
  , ⟨109, "PUNPCKHQDQ", .fehlt, "", "interleave high quadwords: no family"⟩
  , ⟨110, "MOVD/MOVQ 0F 6E", .fehlt, "", "dword/qword move GPR to XMM: IntVec has no 0F 6E row"⟩
  , ⟨111, "MOVQ/MOVDQA/MOVDQU 0F 6F", .modelliert, "VectorIntegerHardwareForms.decodeIntVec", "128-bit loads modelled (66/F3 prefixes); legacy MMX MOVQ missing"⟩
  , ⟨112, "PSHUFD/PSHUFHW/PSHUFLW", .fehlt, "", "packed shuffles with imm8: no family"⟩
  , ⟨113, "Grp12 PSRLW/PSRAW/PSLLW", .fehlt, "", "word-shift group (/2 /4 /6 extensions): no family"⟩
  , ⟨114, "Grp13 PSRLD/PSRAD/PSLLD", .fehlt, "", "dword-shift group: no family"⟩
  , ⟨115, "Grp14 PSRLQ/PSLLQ", .modelliert, "VectorIntegerHardwareForms.decodeIntVec", "imm8 /6 /2 rows modelled; /3 /7 DQ and register rows missing"⟩
  , ⟨116, "PCMPEQB", .fehlt, "", "packed byte equality (memcmp workhorse): no family"⟩
  , ⟨117, "PCMPEQW", .fehlt, "", "packed word equality: no family"⟩
  , ⟨118, "PCMPEQD", .fehlt, "", "packed dword equality: no family"⟩
  , ⟨119, "EMMS", .fehlt, "", "empty MMX state: no family (rare, legacy MMX exit)"⟩
  , ⟨120, "VMREAD", .fehlt, "", "VMX read: privileged system form, no family"⟩
  , ⟨121, "VMWRITE", .fehlt, "", "VMX write: privileged system form, no family"⟩
  , ⟨122, "reserved 0F 7A", .fehlt, "", "reserved, faults #UD: no fault path modelled"⟩
  , ⟨123, "reserved 0F 7B", .fehlt, "", "reserved, faults #UD: no fault path modelled"⟩
  , ⟨124, "HADDPS/HADDPD", .fehlt, "", "horizontal add (F2/66 prefix; bare form #UD): no family"⟩
  , ⟨125, "HSUBPS/HSUBPD", .fehlt, "", "horizontal subtract (F2/66 prefix; bare form #UD): no family"⟩
  , ⟨126, "MOVD/MOVQ 0F 7E", .fehlt, "", "dword/qword move XMM to GPR or memory: no family"⟩
  , ⟨127, "MOVQ/MOVDQA/MOVDQU 0F 7F", .modelliert, "VectorIntegerHardwareForms.decodeIntVec", "128-bit stores modelled (66/F3 prefixes); legacy MMX MOVQ missing"⟩
  ]

/-! ## Checked part 1: every modelled CMOVcc row decodes through the
    named family decoder (`decodeCmov`), reusing the accepted round trip.
    The second byte is `64 + condCode`, i.e. exactly the ledger `op`. -/

theorem wit_cmov_o :
    decodeCmov (encodeCmov .o .rax .rcx) = some ((.o, .rax, .rcx), []) := by
  have h := roundtrip_cmov .o .rax .rcx []
  simpa using h

theorem wit_cmov_no :
    decodeCmov (encodeCmov .no .rax .rcx) = some ((.no, .rax, .rcx), []) := by
  have h := roundtrip_cmov .no .rax .rcx []
  simpa using h

theorem wit_cmov_b :
    decodeCmov (encodeCmov .b .rax .rcx) = some ((.b, .rax, .rcx), []) := by
  have h := roundtrip_cmov .b .rax .rcx []
  simpa using h

theorem wit_cmov_ae :
    decodeCmov (encodeCmov .ae .rax .rcx) = some ((.ae, .rax, .rcx), []) := by
  have h := roundtrip_cmov .ae .rax .rcx []
  simpa using h

theorem wit_cmov_e :
    decodeCmov (encodeCmov .e .rax .rcx) = some ((.e, .rax, .rcx), []) := by
  have h := roundtrip_cmov .e .rax .rcx []
  simpa using h

theorem wit_cmov_ne :
    decodeCmov (encodeCmov .ne .rax .rcx) = some ((.ne, .rax, .rcx), []) := by
  have h := roundtrip_cmov .ne .rax .rcx []
  simpa using h

theorem wit_cmov_be :
    decodeCmov (encodeCmov .be .rax .rcx) = some ((.be, .rax, .rcx), []) := by
  have h := roundtrip_cmov .be .rax .rcx []
  simpa using h

theorem wit_cmov_a :
    decodeCmov (encodeCmov .a .rax .rcx) = some ((.a, .rax, .rcx), []) := by
  have h := roundtrip_cmov .a .rax .rcx []
  simpa using h

theorem wit_cmov_s :
    decodeCmov (encodeCmov .s .rax .rcx) = some ((.s, .rax, .rcx), []) := by
  have h := roundtrip_cmov .s .rax .rcx []
  simpa using h

theorem wit_cmov_ns :
    decodeCmov (encodeCmov .ns .rax .rcx) = some ((.ns, .rax, .rcx), []) := by
  have h := roundtrip_cmov .ns .rax .rcx []
  simpa using h

theorem wit_cmov_p :
    decodeCmov (encodeCmov .p .rax .rcx) = some ((.p, .rax, .rcx), []) := by
  have h := roundtrip_cmov .p .rax .rcx []
  simpa using h

theorem wit_cmov_np :
    decodeCmov (encodeCmov .np .rax .rcx) = some ((.np, .rax, .rcx), []) := by
  have h := roundtrip_cmov .np .rax .rcx []
  simpa using h

theorem wit_cmov_l :
    decodeCmov (encodeCmov .l .rax .rcx) = some ((.l, .rax, .rcx), []) := by
  have h := roundtrip_cmov .l .rax .rcx []
  simpa using h

theorem wit_cmov_ge :
    decodeCmov (encodeCmov .ge .rax .rcx) = some ((.ge, .rax, .rcx), []) := by
  have h := roundtrip_cmov .ge .rax .rcx []
  simpa using h

theorem wit_cmov_le :
    decodeCmov (encodeCmov .le .rax .rcx) = some ((.le, .rax, .rcx), []) := by
  have h := roundtrip_cmov .le .rax .rcx []
  simpa using h

theorem wit_cmov_g :
    decodeCmov (encodeCmov .g .rax .rcx) = some ((.g, .rax, .rcx), []) := by
  have h := roundtrip_cmov .g .rax .rcx []
  simpa using h

/-- The CMOVcc second bytes are exactly the ledger ops 64-79. -/
theorem cmovSecond_ops :
    [cmovSecond .o, cmovSecond .no, cmovSecond .b, cmovSecond .ae,
     cmovSecond .e, cmovSecond .ne, cmovSecond .be, cmovSecond .a,
     cmovSecond .s, cmovSecond .ns, cmovSecond .p, cmovSecond .np,
     cmovSecond .l, cmovSecond .ge, cmovSecond .le, cmovSecond .g] =
    [64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79] := rfl

/-! ## Checked part 2: the modelled scalar-FP rows decode through the
    named family decoder (`s32Decode`), reusing the accepted round trips.
    Each witness is the canonical prefix form (F3 0F 58/5C/59/5E,
    F3 0F 5A); packed PS/PD and double SD rows stay `fehlt`. -/

theorem wit_s32_addss :
    s32Decode (s32EncodeAddssRR .xmm0 .xmm1) =
      some (⟨.addssRR .xmm0 .xmm1, (s32EncodeAddssRR .xmm0 .xmm1).length⟩, []) := by
  have h := s32Roundtrip_addssRR .xmm0 .xmm1 []
  simpa using h

theorem wit_s32_subss :
    s32Decode (s32EncodeSubssRR .xmm0 .xmm1) =
      some (⟨.subssRR .xmm0 .xmm1, (s32EncodeSubssRR .xmm0 .xmm1).length⟩, []) := by
  have h := s32Roundtrip_subssRR .xmm0 .xmm1 []
  simpa using h

theorem wit_s32_mulss :
    s32Decode (s32EncodeMulssRR .xmm0 .xmm1) =
      some (⟨.mulssRR .xmm0 .xmm1, (s32EncodeMulssRR .xmm0 .xmm1).length⟩, []) := by
  have h := s32Roundtrip_mulssRR .xmm0 .xmm1 []
  simpa using h

theorem wit_s32_divss :
    s32Decode (s32EncodeDivssRR .xmm0 .xmm1) =
      some (⟨.divssRR .xmm0 .xmm1, (s32EncodeDivssRR .xmm0 .xmm1).length⟩, []) := by
  have h := s32Roundtrip_divssRR .xmm0 .xmm1 []
  simpa using h

theorem wit_s32_cvtss2sd :
    s32Decode (s32EncodeCvtss2sdRR .xmm0 .xmm1) =
      some (⟨.cvtss2sdRR .xmm0 .xmm1, (s32EncodeCvtss2sdRR .xmm0 .xmm1).length⟩, []) := by
  have h := s32Roundtrip_cvtss2sdRR .xmm0 .xmm1 []
  simpa using h

/-! ## Checked part 3: the modelled vector-integer rows decode through
    the named family decoder (`decodeIntVec`), reusing the accepted round
    trips (0F 6F loads, 0F 73 imm8 shifts, 0F 7F stores). -/

theorem wit_intvec_6f :
    decodeIntVec (encodeIntVec (.movdqaLd .xmm0 .rax (BitVec.ofNat 32 0))) =
      some ((⟨.movdqaLd .xmm0 .rax (BitVec.ofNat 32 0),
        (encodeIntVec (.movdqaLd .xmm0 .rax (BitVec.ofNat 32 0))).length⟩ : IntVecDec),
        []) := by
  have h := roundtrip_movdqaLd .xmm0 .rax (BitVec.ofNat 32 0) []
  simpa using h

theorem wit_intvec_73 :
    decodeIntVec (encodeIntVec (.psllqImm .xmm0 1)) =
      some ((⟨.psllqImm .xmm0 (1 % 256), 6⟩ : IntVecDec), []) := by
  have h := roundtrip_psllqImm .xmm0 1 []
  simpa using h

theorem wit_intvec_7f :
    decodeIntVec (encodeIntVec (.movdqaSt .rax .xmm0 (BitVec.ofNat 32 0))) =
      some ((⟨.movdqaSt .rax .xmm0 (BitVec.ofNat 32 0),
        (encodeIntVec (.movdqaSt .rax .xmm0 (BitVec.ofNat 32 0))).length⟩ : IntVecDec),
        []) := by
  have h := roundtrip_movdqaSt .rax .xmm0 (BitVec.ofNat 32 0) []
  simpa using h

/-- The modelled vector second bytes are exactly the ledger ops. -/
theorem intVecSecond_ops :
    [intVecSecond (.movdqaLd .xmm0 .rax (BitVec.ofNat 32 0)),
     intVecSecond (.psllqImm .xmm0 1),
     intVecSecond (.movdqaSt .rax .xmm0 (BitVec.ofNat 32 0))] =
    [111, 115, 127] := rfl

/-! ## Checked part 4: which modelled rows the unified `kapDecode`
    chain takes (repair of review 1344).

    The first submission wrongly claimed the chain covers none of this
    region. In fact the CMOV rows enter through the first arm
    (`decodeMulDivWidth` -> `decodeExt` -> `decodeCmov`, pin
    `pin_ext_cmov`) and the scalar-prefix FP rows through the second arm
    (`s32Decode`, with `decodeMulDivWidth` refusing first). The IntVec
    rows (0F 6F/73/7F) and representative unmodelled rows are refused by
    the whole chain. Every pin below is checked; each premise is used. -/

set_option maxHeartbeats 32000000 in
/-- Every canonical CMOVcc row is taken by the unified chain's first arm. -/
theorem kap_cmov_alle (c : Bedingung) (dst src : Register) :
    kapDecode (encodeCmov c dst src) =
      some (KapDekodiert.breit (WdHwInstr.ext (ExtInstr.cmov c dst src 4)), []) := by
  have h1 : decodeExt (encodeCmov c dst src) =
      some (ExtInstr.cmov c dst src 4, []) := by
    cases c <;> cases dst <;> cases src <;> rfl
  have h2 := decodeMulDivWidth_prefers_ext _ _ _ h1
  exact kapDecode_breit _ _ _ h2

/-- The scalar ADDSS row is taken by the chain's `s32` arm. -/
theorem kap_s32_addss :
    kapDecode (s32EncodeAddssRR .xmm0 .xmm1) =
      some (KapDekodiert.s32 ⟨.addssRR .xmm0 .xmm1, (s32EncodeAddssRR .xmm0 .xmm1).length⟩, []) := by
  have h1 : decodeMulDivWidth (s32EncodeAddssRR .xmm0 .xmm1) = none := by decide
  have h2 : s32Decode (s32EncodeAddssRR .xmm0 .xmm1) =
      some (⟨.addssRR .xmm0 .xmm1, (s32EncodeAddssRR .xmm0 .xmm1).length⟩, []) := by
    have h := s32Roundtrip_addssRR .xmm0 .xmm1 []
    simpa using h
  exact kapDecode_s32 _ _ _ h1 h2

/-- The scalar SUBSS row is taken by the chain's `s32` arm. -/
theorem kap_s32_subss :
    kapDecode (s32EncodeSubssRR .xmm0 .xmm1) =
      some (KapDekodiert.s32 ⟨.subssRR .xmm0 .xmm1, (s32EncodeSubssRR .xmm0 .xmm1).length⟩, []) := by
  have h1 : decodeMulDivWidth (s32EncodeSubssRR .xmm0 .xmm1) = none := by decide
  have h2 : s32Decode (s32EncodeSubssRR .xmm0 .xmm1) =
      some (⟨.subssRR .xmm0 .xmm1, (s32EncodeSubssRR .xmm0 .xmm1).length⟩, []) := by
    have h := s32Roundtrip_subssRR .xmm0 .xmm1 []
    simpa using h
  exact kapDecode_s32 _ _ _ h1 h2

/-- The scalar MULSS row is taken by the chain's `s32` arm. -/
theorem kap_s32_mulss :
    kapDecode (s32EncodeMulssRR .xmm0 .xmm1) =
      some (KapDekodiert.s32 ⟨.mulssRR .xmm0 .xmm1, (s32EncodeMulssRR .xmm0 .xmm1).length⟩, []) := by
  have h1 : decodeMulDivWidth (s32EncodeMulssRR .xmm0 .xmm1) = none := by decide
  have h2 : s32Decode (s32EncodeMulssRR .xmm0 .xmm1) =
      some (⟨.mulssRR .xmm0 .xmm1, (s32EncodeMulssRR .xmm0 .xmm1).length⟩, []) := by
    have h := s32Roundtrip_mulssRR .xmm0 .xmm1 []
    simpa using h
  exact kapDecode_s32 _ _ _ h1 h2

/-- The scalar DIVSS row is taken by the chain's `s32` arm. -/
theorem kap_s32_divss :
    kapDecode (s32EncodeDivssRR .xmm0 .xmm1) =
      some (KapDekodiert.s32 ⟨.divssRR .xmm0 .xmm1, (s32EncodeDivssRR .xmm0 .xmm1).length⟩, []) := by
  have h1 : decodeMulDivWidth (s32EncodeDivssRR .xmm0 .xmm1) = none := by decide
  have h2 : s32Decode (s32EncodeDivssRR .xmm0 .xmm1) =
      some (⟨.divssRR .xmm0 .xmm1, (s32EncodeDivssRR .xmm0 .xmm1).length⟩, []) := by
    have h := s32Roundtrip_divssRR .xmm0 .xmm1 []
    simpa using h
  exact kapDecode_s32 _ _ _ h1 h2

/-- The scalar CVTSS2SD row is taken by the chain's `s32` arm. -/
theorem kap_s32_cvtss2sd :
    kapDecode (s32EncodeCvtss2sdRR .xmm0 .xmm1) =
      some (KapDekodiert.s32 ⟨.cvtss2sdRR .xmm0 .xmm1, (s32EncodeCvtss2sdRR .xmm0 .xmm1).length⟩, []) := by
  have h1 : decodeMulDivWidth (s32EncodeCvtss2sdRR .xmm0 .xmm1) = none := by decide
  have h2 : s32Decode (s32EncodeCvtss2sdRR .xmm0 .xmm1) =
      some (⟨.cvtss2sdRR .xmm0 .xmm1, (s32EncodeCvtss2sdRR .xmm0 .xmm1).length⟩, []) := by
    have h := s32Roundtrip_cvtss2sdRR .xmm0 .xmm1 []
    simpa using h
  exact kapDecode_s32 _ _ _ h1 h2

/-- The 0F 6F vector load is refused by the whole unified chain. -/
theorem kap_ohne_intvec_6f :
    kapDecode (encodeIntVec (.movdqaLd .xmm0 .rax (BitVec.ofNat 32 0))) = none := by
  decide

/-- The 0F 73 vector shift is refused by the whole unified chain. -/
theorem kap_ohne_intvec_73 :
    kapDecode (encodeIntVec (.psllqImm .xmm0 1)) = none := by decide

/-- The 0F 7F vector store is refused by the whole unified chain. -/
theorem kap_ohne_intvec_7f :
    kapDecode (encodeIntVec (.movdqaSt .rax .xmm0 (BitVec.ofNat 32 0))) = none := by
  decide

/-- MOVMSKPS shape (REX.W 0F 50 /r): refused by the whole chain. -/
theorem kap_nichts_movmskps :
    kapDecode [natByte 72, natByte 15, natByte 80, natByte 200] = none := by decide

/-- Bare packed ADDPS shape (0F 58 /r): refused by the whole chain. -/
theorem kap_nichts_addps :
    kapDecode [natByte 15, natByte 88, natByte 192] = none := by decide

/-- PUNPCKLBW shape (66 0F 60 /r): refused by the whole chain. -/
theorem kap_nichts_punpcklbw :
    kapDecode [natByte 102, natByte 15, natByte 96, natByte 192] = none := by decide

/-- PCMPEQB shape (66 0F 74 /r): refused by the whole chain. -/
theorem kap_nichts_pcmpeqb :
    kapDecode [natByte 102, natByte 15, natByte 116, natByte 192] = none := by decide

/-- EMMS (0F 77): refused by the whole chain. -/
theorem kap_nichts_emms :
    kapDecode [natByte 15, natByte 119] = none := by decide

/-- VMREAD shape (0F 78 /r): refused by the whole chain. -/
theorem kap_nichts_vmread :
    kapDecode [natByte 15, natByte 120, natByte 192] = none := by decide

/-! ## Summary: counts per status and exact coverage of the region. -/

/-- 24 ledger rows are modelled. -/
theorem anzahl_modelliert :
    (ledger.filter (fun e => decide (e.status = LStatus.modelliert))).length = 24 := by
  decide

/-- 40 ledger rows are missing families: the findings of this lane. -/
theorem anzahl_fehlt :
    (ledger.filter (fun e => decide (e.status = LStatus.fehlt))).length = 40 := by
  decide

/-- Nothing in this region is deferred, refused, or invalid in 64-bit mode. -/
theorem anzahl_rest_leer :
    (ledger.filter (fun e => decide (e.status = LStatus.zurueckgestellt))).length = 0 ∧
    (ledger.filter (fun e => decide (e.status = LStatus.verweigert))).length = 0 ∧
    (ledger.filter (fun e => decide (e.status = LStatus.ungueltig64))).length = 0 := by
  decide

/-- The ledger covers the region exactly once, in order. -/
theorem ledger_ops :
    ledger.map LEintrag.op = List.range' 64 64 := by
  rfl

/-- No opcode is listed twice. -/
theorem ledger_nodup : ledger.Nodup := by
  decide

/-!
CUTS:
- The opcode map (which mnemonic lives at which 0F second byte, which
  prefix selects which variant, that 0F 7A/7B are reserved and the bare
  0F 7C/7D forms fault) is a NAMED assumption: Intel SDM edition
  325462-093US (clone-local `intel-instruction-reference.pdf/txt`,
  REFERENCES.json sha256 a4a62e6a...f9168ee5). It is not checked
  provenance: no PDF text was machine-read by this lane.
- Vendor neutral (rule 17): no entry pins behaviour Intel or AMD calls
  undefined or model-specific; no AMD manual exists in the clone, so no
  AMD provenance is claimed. No entry is marked `herstellerabhaengig`
  because the region has no known Intel/AMD definition split.
- `modelliert` means only: the named family decoder accepts the
  canonical witness (proved above via accepted round trips). Whether the
  unified `kapDecode` chain takes the bytes is pinned separately in
  checked part 4: the CMOV rows (first arm) and the scalar-prefix FP rows
  (`s32` arm) are inside the chain; the IntVec rows and the unmodelled
  rows are refused by it. No full semantic/hardware correspondence is
  claimed.
- Partial rows (88/89/90/92/94 scalar-only, 111/115/127 selected
  rows-only) overstate by construction of the one-row-per-byte schema;
  the missing variants are named in `grund` and in MUSE-REPORT-1343.md.
- No refusal (`verweigert`) or invalid-64 (`ungueltig64`) facts are
  claimed; `anzahl_rest_leer` only says the lists are empty.
- No connection to `HwSchritt`, W/GX, timing, faults, or the loaded
  image is claimed.
- `ledger_nodup` and the counts are closed `decide` evaluations over the
  written list; they check the list, not the architecture.
-/
#print axioms wit_cmov_e
#print axioms wit_s32_addss
#print axioms wit_intvec_6f
#print axioms kap_cmov_alle
#print axioms kap_s32_addss
#print axioms kap_ohne_intvec_6f
#print axioms kap_nichts_emms
#print axioms anzahl_modelliert
#print axioms ledger_ops
#print axioms ledger_nodup

end OpcodeLedger0F40
end Gabbro.Grammatik.X86
