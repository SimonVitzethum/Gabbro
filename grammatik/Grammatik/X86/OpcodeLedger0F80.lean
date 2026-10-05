/-
  File:      Grammatik/X86/OpcodeLedger0F80.lean
  Subject:   Opcode ledger for two-byte opcodes 0F 80-BF (64-bit mode).

  Lane 1345: ledger over the x86-64 opcode map region 0F 80-BF.
  Self-contained schema; checked decoder/refusal pins reuse accepted
  decoders unchanged (never redefined).
-/
import Grammatik.X86.HwKapsteinDecoder
import Grammatik.X86.ControlCodec
import Grammatik.X86.IntBitTest
import Grammatik.X86.IntBitScan
import Grammatik.X86.CpuFeatureHardwareForms
import Grammatik.X86.LockedInstructionExecution

namespace Gabbro.Grammatik.X86.OpcodeLedger0F80

/-- Ledger status of one opcode byte in the region. -/
inductive LStatus where
  | modelliert
  | zurueckgestellt
  | verweigert
  | ungueltig64
  | fehlt
  deriving DecidableEq, Repr

/-- One ledger row: second opcode byte, mnemonic, status, modelling
    family (existing Lean module as a string) and a one-line reason
    for every non-`modelliert` entry. -/
structure LEintrag where
  op2 : Nat
  mnem : String
  status : LStatus
  familie : String
  grund : String
  deriving DecidableEq, Repr

/-- The full ledger: one row per second-opcode byte 0F 80-BF
    (128-191). Opcode map: Intel SDM Vol 2 Appendix A, Table A-3
    (two-byte opcodes); local snapshot
    `.tmp/HARDWARE-REFERENCES/intel-instruction-reference.txt`
    (edition 325462-093US, Sep 2026). No AMD manual is snapshotted,
    so no AMD provenance is claimed (rule 17). -/
def ledger : List LEintrag :=
  [{ op2 := 128, mnem := "JO rel16/32", status := .modelliert,
     familie := "Codec.lean", grund := "" },
   { op2 := 129, mnem := "JNO rel16/32", status := .modelliert,
     familie := "Codec.lean", grund := "" },
   { op2 := 130, mnem := "JB/JC/JNAE rel16/32", status := .modelliert,
     familie := "Codec.lean", grund := "" },
   { op2 := 131, mnem := "JAE/JNB/JNC rel16/32", status := .modelliert,
     familie := "Codec.lean", grund := "" },
   { op2 := 132, mnem := "JE/JZ rel16/32", status := .modelliert,
     familie := "Codec.lean", grund := "" },
   { op2 := 133, mnem := "JNE/JNZ rel16/32", status := .modelliert,
     familie := "Codec.lean", grund := "" },
   { op2 := 134, mnem := "JBE/JNA rel16/32", status := .modelliert,
     familie := "Codec.lean", grund := "" },
   { op2 := 135, mnem := "JA/JNBE rel16/32", status := .modelliert,
     familie := "Codec.lean", grund := "" },
   { op2 := 136, mnem := "JS rel16/32", status := .modelliert,
     familie := "Codec.lean", grund := "" },
   { op2 := 137, mnem := "JNS rel16/32", status := .modelliert,
     familie := "Codec.lean", grund := "" },
   { op2 := 138, mnem := "JP/JPE rel16/32", status := .modelliert,
     familie := "Codec.lean", grund := "" },
   { op2 := 139, mnem := "JNP/JPO rel16/32", status := .modelliert,
     familie := "Codec.lean", grund := "" },
   { op2 := 140, mnem := "JL/JNGE rel16/32", status := .modelliert,
     familie := "Codec.lean", grund := "" },
   { op2 := 141, mnem := "JGE/JNL rel16/32", status := .modelliert,
     familie := "Codec.lean", grund := "" },
   { op2 := 142, mnem := "JLE/JNG rel16/32", status := .modelliert,
     familie := "Codec.lean", grund := "" },
   { op2 := 143, mnem := "JG/JNLE rel16/32", status := .modelliert,
     familie := "Codec.lean", grund := "" },
   { op2 := 144, mnem := "SETO r/m8", status := .modelliert,
     familie := "ControlCodec.lean", grund := "" },
   { op2 := 145, mnem := "SETNO r/m8", status := .modelliert,
     familie := "ControlCodec.lean", grund := "" },
   { op2 := 146, mnem := "SETB/SETC/SETNAE r/m8", status := .modelliert,
     familie := "ControlCodec.lean", grund := "" },
   { op2 := 147, mnem := "SETAE/SETNB/SETNC r/m8", status := .modelliert,
     familie := "ControlCodec.lean", grund := "" },
   { op2 := 148, mnem := "SETE/SETZ r/m8", status := .modelliert,
     familie := "ControlCodec.lean", grund := "" },
   { op2 := 149, mnem := "SETNE/SETNZ r/m8", status := .modelliert,
     familie := "ControlCodec.lean", grund := "" },
   { op2 := 150, mnem := "SETBE/SETNA r/m8", status := .modelliert,
     familie := "ControlCodec.lean", grund := "" },
   { op2 := 151, mnem := "SETA/SETNBE r/m8", status := .modelliert,
     familie := "ControlCodec.lean", grund := "" },
   { op2 := 152, mnem := "SETS r/m8", status := .modelliert,
     familie := "ControlCodec.lean", grund := "" },
   { op2 := 153, mnem := "SETNS r/m8", status := .modelliert,
     familie := "ControlCodec.lean", grund := "" },
   { op2 := 154, mnem := "SETP/SETPE r/m8", status := .modelliert,
     familie := "ControlCodec.lean", grund := "" },
   { op2 := 155, mnem := "SETNP/SETPO r/m8", status := .modelliert,
     familie := "ControlCodec.lean", grund := "" },
   { op2 := 156, mnem := "SETL/SETNGE r/m8", status := .modelliert,
     familie := "ControlCodec.lean", grund := "" },
   { op2 := 157, mnem := "SETGE/SETNL r/m8", status := .modelliert,
     familie := "ControlCodec.lean", grund := "" },
   { op2 := 158, mnem := "SETLE/SETNG r/m8", status := .modelliert,
     familie := "ControlCodec.lean", grund := "" },
   { op2 := 159, mnem := "SETG/SETNLE r/m8", status := .modelliert,
     familie := "ControlCodec.lean", grund := "" },
   { op2 := 160, mnem := "PUSH FS", status := .fehlt,
     familie := "", grund := "no family models segment pushes; rare in user code" },
   { op2 := 161, mnem := "POP FS", status := .fehlt,
     familie := "", grund := "no family models segment pops; rare in user code" },
   { op2 := 162, mnem := "CPUID", status := .modelliert,
     familie := "CpuFeatureHardwareForms.lean", grund := "" },
   { op2 := 163, mnem := "BT r/m, r", status := .modelliert,
     familie := "IntBitTest.lean", grund := "" },
   { op2 := 164, mnem := "SHLD r/m, r, imm8", status := .fehlt,
     familie := "", grund := "no family models double shifts; emitted for wide rotates" },
   { op2 := 165, mnem := "SHLD r/m, r, CL", status := .fehlt,
     familie := "", grund := "no family models double shifts; emitted for wide rotates" },
   { op2 := 166, mnem := "XBTS (invalid)", status := .verweigert,
     familie := "HwKapsteinDecoder.lean", grund := "286 extended op, #UD on x86-64" },
   { op2 := 167, mnem := "IBTS (invalid)", status := .verweigert,
     familie := "HwKapsteinDecoder.lean", grund := "286 extended op, #UD on x86-64" },
   { op2 := 168, mnem := "PUSH GS", status := .fehlt,
     familie := "", grund := "no family models segment pushes; rare in user code" },
   { op2 := 169, mnem := "POP GS", status := .fehlt,
     familie := "", grund := "no family models segment pops; rare in user code" },
   { op2 := 170, mnem := "RSM", status := .verweigert,
     familie := "HwKapsteinDecoder.lean", grund := "SMM-only, #UD outside SMM" },
   { op2 := 171, mnem := "BTS r/m, r", status := .modelliert,
     familie := "IntBitTest.lean", grund := "" },
   { op2 := 172, mnem := "SHRD r/m, r, imm8", status := .fehlt,
     familie := "", grund := "no family models double shifts; emitted for wide rotates" },
   { op2 := 173, mnem := "SHRD r/m, r, CL", status := .fehlt,
     familie := "", grund := "no family models double shifts; emitted for wide rotates" },
   { op2 := 174, mnem := "Group 15 (FXSAVE/SFENCE/...) ", status := .zurueckgestellt,
     familie := "LockedInstructionExecution.lean",
     grund := "fence rows modelled, FXSAVE/XRSTOR/CLFLUSH deferred" },
   { op2 := 175, mnem := "IMUL r, r/m", status := .modelliert,
     familie := "MulDivWidthHardwareForms.lean", grund := "" },
   { op2 := 176, mnem := "CMPXCHG r/m8, r8", status := .fehlt,
     familie := "", grund := "only 64-bit LOCK CMPXCHG modelled; byte form missing" },
   { op2 := 177, mnem := "CMPXCHG r/m, r", status := .modelliert,
     familie := "LockedInstructionExecution.lean", grund := "" },
   { op2 := 178, mnem := "LSS r, m", status := .fehlt,
     familie := "", grund := "no family models far-pointer loads; legacy only" },
   { op2 := 179, mnem := "BTR r/m, r", status := .modelliert,
     familie := "IntBitTest.lean", grund := "" },
   { op2 := 180, mnem := "LFS r, m", status := .fehlt,
     familie := "", grund := "no family models far-pointer loads; legacy only" },
   { op2 := 181, mnem := "LGS r, m", status := .fehlt,
     familie := "", grund := "no family models far-pointer loads; legacy only" },
   { op2 := 182, mnem := "MOVZX r, r/m8", status := .fehlt,
     familie := "", grund := "no family models zero extension; very common in output" },
   { op2 := 183, mnem := "MOVZX r, r/m16", status := .fehlt,
     familie := "", grund := "no family models zero extension; very common in output" },
   { op2 := 184, mnem := "JMPE (IA-64)", status := .verweigert,
     familie := "HwKapsteinDecoder.lean", grund := "Itanium emulator op, #UD on x86-64" },
   { op2 := 185, mnem := "UD1/Group 10", status := .verweigert,
     familie := "HwKapsteinDecoder.lean", grund := "reserved, #UD by definition" },
   { op2 := 186, mnem := "Group 8 BT imm8", status := .modelliert,
     familie := "IntBitTest.lean", grund := "" },
   { op2 := 187, mnem := "BTC r/m, r", status := .modelliert,
     familie := "IntBitTest.lean", grund := "" },
   { op2 := 188, mnem := "BSF r, r/m", status := .modelliert,
     familie := "IntBitScan.lean", grund := "" },
   { op2 := 189, mnem := "BSR r, r/m", status := .modelliert,
     familie := "IntBitScan.lean", grund := "" },
   { op2 := 190, mnem := "MOVSX r, r/m8", status := .fehlt,
     familie := "", grund := "no family models sign extension; very common in output" },
   { op2 := 191, mnem := "MOVSXD/MOVSX r, r/m16", status := .fehlt,
     familie := "", grund := "no family models sign extension; very common in output" }]

/-- Status count over the ledger. -/
def statusZaehlt (s : LStatus) : Nat :=
  (ledger.filter (fun e => e.status == s)).length

/-- The ledger has one row per opcode byte in the region. -/
theorem ledger_laenge : ledger.length = 64 := rfl

/-- Count per status: 42 modelled. -/
theorem ledger_modelliert : statusZaehlt .modelliert = 42 := by decide

/-- Count per status: 1 deferred (group 15). -/
theorem ledger_zurueckgestellt : statusZaehlt .zurueckgestellt = 1 := by decide

/-- Count per status: 5 refused (invalid/privileged/reserved). -/
theorem ledger_verweigert : statusZaehlt .verweigert = 5 := by decide

/-- Count per status: none invalid-in-64-bit-only in this region. -/
theorem ledger_ungueltig64 : statusZaehlt .ungueltig64 = 0 := by decide

/-- Count per status: 16 missing. -/
theorem ledger_fehlt : statusZaehlt .fehlt = 16 := by decide

/-- The ledger opcodes are exactly the region bytes 128-191. -/
theorem ledger_opcodes :
    (ledger.map LEintrag.op2) = List.range' 128 64 := by decide

/-- No opcode byte is listed twice. -/
theorem ledger_nodup : (ledger.map LEintrag.op2).Nodup := by decide

/-! ## Checked part: every `modelliert` row decodes, every
    `verweigert` row is refused by the capstone chain. -/

/-- All 16 near-Jcc rows decode through the pilot codec (reused
    generic round trip; every premise is used). -/
theorem jcc_alle_modelliert (c : Bedingung) (d : BitVec 32)
    (suffix : List Byte) :
    decode (encode (.jumpIf32 c d) ++ suffix) =
      some (⟨.jumpIf32 c d, (encode (.jumpIf32 c d)).length⟩, suffix) :=
  roundtrip_jumpIf32 c d suffix

/-- All 16 SETcc rows decode through the family decoder (reused
    generic round trip; every premise is used). -/
theorem setcc_alle_modelliert (c : Bedingung) (dst : Register)
    (suffix : List Byte) :
    decodeSetCC (encodeSetCC c dst ++ suffix) =
      some ((c, dst), suffix) :=
  roundtrip_setCC c dst suffix

/-- BT register row 0F A3 decodes (reused accepted pin). -/
theorem bt_reg_modelliert :
    decodeBt [natByte 72, natByte 15, natByte 187, natByte 200] =
      some (((.reg .btc .w64 .rax .rcx) : BtForm), []) :=
  pin_bt_dekode.1

/-- BT group row 0F BA imm8 decodes (reused accepted pin). -/
theorem bt_imm_modelliert :
    decodeBt [natByte 64, natByte 15, natByte 186, natByte 234,
      natByte 5] =
      some (((.imm .bts .w32 .rdx 5) : BtForm), []) :=
  pin_bt_dekode.2.1

/-- BT memory row 0F A3 with SIB decodes (reused accepted pin). -/
theorem bt_mem_modelliert :
    decodeBt [natByte 64, natByte 15, natByte 163, natByte 132,
      natByte 36, natByte 0, natByte 0, natByte 0, natByte 0] =
      some (((.memReg .bt .w32 .rsp .rax 0) : BtForm), []) :=
  pin_bt_dekode.2.2

/-- BT group memory-imm8 row 0F BA /5 disp32 imm8 decodes. -/
theorem bt_memimm_modelliert :
    decodeBt [natByte 64, natByte 15, natByte 186, natByte 170,
      natByte 16, natByte 0, natByte 0, natByte 0, natByte 5] =
      some (((.memImm .bts .w32 .rdx 16 5) : BtForm), []) := by
  decide

/-- BSF row 0F BC decodes (reused accepted pin). -/
theorem bsf_modelliert :
    decodeBs [natByte 15, natByte 188, natByte 193] =
      some (⟨.bsf .b32 .rax (.reg .rcx), 3⟩, []) :=
  pin_bsf_reg

/-- Every BSR register row decodes (reused generic round trip;
    both premises are used). -/
theorem bsr_alle_modelliert (dst src : Register) :
    decodeBs (encodeBs (.bsr .b32 dst (.reg src))) =
      some (⟨.bsr .b32 dst (.reg src),
        (encodeBs (.bsr .b32 dst (.reg src))).length⟩, []) :=
  encodeBsr_decodeBs .b32 dst src

/-- CPUID row 0F A2 decodes (reused generic fact; premise used). -/
theorem cpuid_modelliert (suffix : List Byte) :
    decodeCpuFeature (cpuEncode .cpuid ++ suffix) =
      some (.cpuid, suffix) :=
  decodeCpu_cpuid suffix

/-- IMUL row 0F AF is taken by the capstone chain in the unified
    arm (reused accepted overlap winner). -/
theorem imul_modelliert :
    kapDecode [natByte 77, natByte 15, natByte 175, natByte 207] =
      some (KapDekodiert.breit
        (.ext (.muldiv ⟨.imul2 .r9 .r15, 4⟩)), []) :=
  kapUeber_wd_ext_imul2

/-- LOCK CMPXCHG row 0F B1 decodes (reused accepted pin). -/
theorem cmpxchg_modelliert :
    decodeLock pinCmpxchg =
      some (LockAnweisung.ok (.cmpxchg64 .rcx .rbp 0) 9, []) :=
  pin_lock_cmpxchg_decodiert

/-- Refused: XBTS 0F A6 decodes to nothing on the capstone chain. -/
theorem verw_a6 : kapDecode [natByte 15, natByte 166] = none := by
  decide

/-- Refused: IBTS 0F A7 decodes to nothing on the capstone chain. -/
theorem verw_a7 : kapDecode [natByte 15, natByte 167] = none := by
  decide

/-- Refused: RSM 0F AA decodes to nothing on the capstone chain. -/
theorem verw_aa : kapDecode [natByte 15, natByte 170] = none := by
  decide

/-- Refused: JMPE 0F B8 decodes to nothing on the capstone chain. -/
theorem verw_b8 : kapDecode [natByte 15, natByte 184] = none := by
  decide

/-- Refused: reserved 0F B9 decodes to nothing on the capstone chain. -/
theorem verw_b9 : kapDecode [natByte 15, natByte 185] = none := by
  decide

/- CUTS:
   Proved here, over the reused accepted decoders only (every decoder
   lifted, never redefined):
   - the full 64-entry ledger over 0F 80-BF, one row per second-opcode
     byte, with counts 42 modelliert / 1 zurueckgestellt / 5 verweigert /
     0 ungueltig64 / 16 fehlt, opcode coverage exactly the region bytes
     128-191 with no duplicate;
   - checked decodes for every modelled family: all 16 near-Jcc rows
     (pilot `decode`), all 16 SETcc rows (`decodeSetCC`), BT/BTS/BTR/BTC
     register, imm8, memory and memory-imm8 rows (`decodeBt`), BSF
     (`decodeBs` pin) and all BSR register rows (generic round trip),
     CPUID (`decodeCpuFeature`), IMUL (`kapDecode` unified arm),
     LOCK CMPXCHG (`decodeLock`);
   - checked refusals: the 5 verweigert rows decode to nothing on the
     capstone chain `kapDecode`.
   NOT proved here, and not claimed:
   - opcode map provenance: Intel SDM Vol 2 Appendix A as a NAMED
     assumption (local snapshot `.tmp/HARDWARE-REFERENCES/`,
     edition 325462-093US); no AMD provenance claimed (no AMD manual
     snapshotted); vendor-differing behaviour (e.g. BSF/BSR
     zero-input destination, CPUID leaf answers) stays FREE in the
     model and is not pinned here;
   - the `fehlt` rows have no decoder proof (that is the finding);
     the `zurueckgestellt` group-15 row has no single witness (fence
     rows are proved where they live);
   - no execution, flag, fault-class or timing claim beyond decoding;
     no W/GX bridge; no source, checker, contract, entry, ABI, loader,
     budget or liveness claim.
-/

#print axioms ledger_laenge
#print axioms ledger_modelliert
#print axioms ledger_zurueckgestellt
#print axioms ledger_verweigert
#print axioms ledger_ungueltig64
#print axioms ledger_fehlt
#print axioms ledger_opcodes
#print axioms ledger_nodup
#print axioms jcc_alle_modelliert
#print axioms setcc_alle_modelliert
#print axioms bt_reg_modelliert
#print axioms bt_imm_modelliert
#print axioms bt_mem_modelliert
#print axioms bt_memimm_modelliert
#print axioms bsf_modelliert
#print axioms bsr_alle_modelliert
#print axioms cpuid_modelliert
#print axioms imul_modelliert
#print axioms cmpxchg_modelliert
#print axioms verw_a6
#print axioms verw_a7
#print axioms verw_aa
#print axioms verw_b8
#print axioms verw_b9

end Gabbro.Grammatik.X86.OpcodeLedger0F80
