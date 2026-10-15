/-
  File:      Grammatik/X86/OpcodeLedger1Byte00.lean
  Subject:   Opcode ledger: one-byte opcodes 00-3F in 64-bit mode.

  Lane 1333: every opcode byte 0x00-0x3F from the x86-64 opcode map
  (SDM Vol 2 Appendix A, Intel edition 093; no AMD manual in this
  clone, so vendor differences stay FREE) listed exactly once with its
  status against the accepted Lean families. Checked facts use the
  capstone chain `kapDecode` (HwKapsteinDecoder) or the named family
  decoder; every refusal is a proved `none`, never a comment.
-/
import Grammatik.X86.HwKapsteinDecoder
import Grammatik.X86.IntCarryForms
import Grammatik.X86.CompactArithRax

namespace Gabbro.Grammatik.X86.Ledger00

/-- Status of one opcode row in this ledger. -/
inductive LStatus where
  | modelliert : LStatus
  | zurueckgestellt : LStatus
  | verweigert : LStatus
  | ungueltig64 : LStatus
  | fehlt : LStatus
  deriving DecidableEq, Repr

/-- One ledger row: opcode byte, mnemonic, status, modelling family
    module and a one-line reason for every non-`modelliert` entry. -/
structure LEintrag where
  opcode : Nat
  mnemonik : String
  status : LStatus
  familie : String
  grund : String
  deriving DecidableEq, Repr

/-- The ledger: all 64 opcode bytes 0x00-0x3F, each exactly once.
    Mnemonics follow SDM Vol 2 Appendix A (64-bit mode). -/
def ledger00 : List LEintrag :=
  [⟨0, "ADD r/m8, r8", .fehlt, "none",
      "no 8-bit ADD row: IntCarryForms covers only ADC/SBB byte forms"⟩,
    ⟨1, "ADD r/m64, r64", .modelliert, "Codec/decode (pilot, kapDecode .breit)",
      "REX form only; bare 32-bit form refused"⟩,
    ⟨2, "ADD r8, r/m8", .fehlt, "none", "no 8-bit ADD row"⟩,
    ⟨3, "ADD r32/64, r/m32/64", .fehlt, "none",
      "load-direction ADD unmodelled in every width"⟩,
    ⟨4, "ADD AL, imm8", .fehlt, "none", "no AL-imm ADD row"⟩,
    ⟨5, "ADD rAX, imm32", .modelliert, "CompactArithRax/decodeRax",
      "REX.W form only; bare 32-bit form refused"⟩,
    ⟨6, "PUSH ES", .ungueltig64, "none", "invalid in 64-bit mode"⟩,
    ⟨7, "POP ES", .ungueltig64, "none", "invalid in 64-bit mode"⟩,
    ⟨8, "OR r/m8, r8", .fehlt, "none", "no 8-bit OR row"⟩,
    ⟨9, "OR r/m64, r64", .modelliert, "IntegerCore/decodeCore (kapDecode .kern)",
      "REX.W reg-direct only"⟩,
    ⟨10, "OR r8, r/m8", .fehlt, "none", "no 8-bit OR row"⟩,
    ⟨11, "OR r32/64, r/m32/64", .fehlt, "none",
      "load-direction OR unmodelled in every width"⟩,
    ⟨12, "OR AL, imm8", .fehlt, "none", "no AL-imm OR row"⟩,
    ⟨13, "OR rAX, imm32", .fehlt, "none",
      "decodeRax covers only ADD/SUB/CMP rAX; OR-imm is common"⟩,
    ⟨14, "PUSH CS", .ungueltig64, "none", "invalid in 64-bit mode"⟩,
    ⟨15, "escape 0F", .zurueckgestellt, "two-byte map",
      "0F escape: the second opcode byte belongs to another region"⟩,
    ⟨16, "ADC r/m8, r8", .modelliert, "IntCarryForms/decodeCarry", ""⟩,
    ⟨17, "ADC r/m32, r32", .modelliert, "IntCarryForms/decodeCarry", ""⟩,
    ⟨18, "ADC r8, r/m8", .modelliert, "IntCarryForms/decodeCarry", ""⟩,
    ⟨19, "ADC r32, r/m32", .modelliert, "IntCarryForms/decodeCarry", ""⟩,
    ⟨20, "ADC AL, imm8", .modelliert, "IntCarryForms/decodeCarry", ""⟩,
    ⟨21, "ADC rAX, imm32", .modelliert, "IntCarryForms/decodeCarry", ""⟩,
    ⟨22, "PUSH SS", .ungueltig64, "none", "invalid in 64-bit mode"⟩,
    ⟨23, "POP SS", .ungueltig64, "none", "invalid in 64-bit mode"⟩,
    ⟨24, "SBB r/m8, r8", .modelliert, "IntCarryForms/decodeCarry", ""⟩,
    ⟨25, "SBB r/m32, r32", .modelliert, "IntCarryForms/decodeCarry", ""⟩,
    ⟨26, "SBB r8, r/m8", .modelliert, "IntCarryForms/decodeCarry", ""⟩,
    ⟨27, "SBB r32, r/m32", .modelliert, "IntCarryForms/decodeCarry", ""⟩,
    ⟨28, "SBB AL, imm8", .modelliert, "IntCarryForms/decodeCarry", ""⟩,
    ⟨29, "SBB rAX, imm32", .modelliert, "IntCarryForms/decodeCarry", ""⟩,
    ⟨30, "PUSH DS", .ungueltig64, "none", "invalid in 64-bit mode"⟩,
    ⟨31, "POP DS", .ungueltig64, "none", "invalid in 64-bit mode"⟩,
    ⟨32, "AND r/m8, r8", .fehlt, "none", "no 8-bit AND row"⟩,
    ⟨33, "AND r/m64, r64", .modelliert, "IntegerCore/decodeCore (kapDecode .kern)",
      "REX.W reg-direct only"⟩,
    ⟨34, "AND r8, r/m8", .fehlt, "none", "no 8-bit AND row"⟩,
    ⟨35, "AND r32/64, r/m32/64", .fehlt, "none",
      "load-direction AND unmodelled in every width"⟩,
    ⟨36, "AND AL, imm8", .fehlt, "none", "no AL-imm AND row"⟩,
    ⟨37, "AND rAX, imm32", .fehlt, "none",
      "decodeRax covers only ADD/SUB/CMP rAX; AND-imm is common"⟩,
    ⟨38, "ES prefix", .zurueckgestellt, "addressed-forms lane",
      "segment-override prefix: owned by the addressed-forms lane"⟩,
    ⟨39, "DAA", .ungueltig64, "none", "invalid in 64-bit mode"⟩,
    ⟨40, "SUB r/m8, r8", .fehlt, "none", "no 8-bit SUB row"⟩,
    ⟨41, "SUB r/m64, r64", .modelliert, "Codec/decode (pilot, kapDecode .breit)",
      "REX form only; bare 32-bit form refused"⟩,
    ⟨42, "SUB r8, r/m8", .fehlt, "none", "no 8-bit SUB row"⟩,
    ⟨43, "SUB r32/64, r/m32/64", .fehlt, "none",
      "load-direction SUB unmodelled in every width"⟩,
    ⟨44, "SUB AL, imm8", .fehlt, "none", "no AL-imm SUB row"⟩,
    ⟨45, "SUB rAX, imm32", .modelliert, "CompactArithRax/decodeRax",
      "REX.W form only; bare 32-bit form refused"⟩,
    ⟨46, "CS prefix", .zurueckgestellt, "addressed-forms lane",
      "segment-override prefix: owned by the addressed-forms lane"⟩,
    ⟨47, "DAS", .ungueltig64, "none", "invalid in 64-bit mode"⟩,
    ⟨48, "XOR r/m8, r8", .fehlt, "none", "no 8-bit XOR row"⟩,
    ⟨49, "XOR r/m64, r64", .modelliert, "Codec/decode (pilot, kapDecode .breit)",
      "REX form only; self-form is also the ZeroIdiomXor filter input"⟩,
    ⟨50, "XOR r8, r/m8", .fehlt, "none", "no 8-bit XOR row"⟩,
    ⟨51, "XOR r32/64, r/m32/64", .fehlt, "none",
      "load-direction XOR unmodelled; includes the 32-bit zero idiom"⟩,
    ⟨52, "XOR AL, imm8", .fehlt, "none", "no AL-imm XOR row"⟩,
    ⟨53, "XOR rAX, imm32", .fehlt, "none",
      "decodeRax covers only ADD/SUB/CMP rAX; XOR-imm is common"⟩,
    ⟨54, "SS prefix", .zurueckgestellt, "addressed-forms lane",
      "segment-override prefix: owned by the addressed-forms lane"⟩,
    ⟨55, "AAA", .ungueltig64, "none", "invalid in 64-bit mode"⟩,
    ⟨56, "CMP r/m8, r8", .fehlt, "none", "no 8-bit CMP row"⟩,
    ⟨57, "CMP r/m64, r64", .modelliert, "Codec/decode (pilot, kapDecode .breit)",
      "REX form only; bare 32-bit form refused"⟩,
    ⟨58, "CMP r8, r/m8", .fehlt, "none", "no 8-bit CMP row"⟩,
    ⟨59, "CMP r32/64, r/m32/64", .fehlt, "none",
      "load-direction CMP unmodelled; the most common compare form"⟩,
    ⟨60, "CMP AL, imm8", .fehlt, "none", "no AL-imm CMP row"⟩,
    ⟨61, "CMP rAX, imm32", .modelliert, "CompactArithRax/decodeRax",
      "REX.W form only; bare 32-bit form refused"⟩,
    ⟨62, "DS prefix", .zurueckgestellt, "addressed-forms lane",
      "segment-override prefix: owned by the addressed-forms lane"⟩,
    ⟨63, "AAS", .ungueltig64, "none", "invalid in 64-bit mode"⟩]

/-- Boolean status equality (no BEq derivation needed). -/
def passt : LStatus → LStatus → Bool
  | .modelliert, .modelliert => true
  | .zurueckgestellt, .zurueckgestellt => true
  | .verweigert, .verweigert => true
  | .ungueltig64, .ungueltig64 => true
  | .fehlt, .fehlt => true
  | _, _ => false

/-- Row count by status, as checked data. -/
def zaehle (s : LStatus) : Nat :=
  (ledger00.filter (fun e => passt e.status s)).length

theorem c_modelliert : zaehle .modelliert = 21 := by decide
theorem c_zurueckgestellt : zaehle .zurueckgestellt = 5 := by decide
theorem c_verweigert : zaehle .verweigert = 0 := by decide
theorem c_ungueltig64 : zaehle .ungueltig64 = 11 := by decide
theorem c_fehlt : zaehle .fehlt = 27 := by decide

/-- The table covers the region exactly once: no opcode twice, none skipped. -/
theorem abdeckung :
    ((List.range 64).all
      (fun n => ((ledger00.map LEintrag.opcode).count n) == 1)) = true := by
  decide

/-- Chain pin: the chain takes REX.W ADD r/m64, r64. -/
theorem kap_add_akzeptiert :
    kapDecode [natByte 72, natByte 1, natByte 192] =
      some (KapDekodiert.breit
        (WdHwInstr.ext (ExtInstr.pilot ⟨Befehl.addReg64 .rax .rax, 3⟩)),
        []) := by
  decide

/-- Chain pin: the chain takes REX.W OR r/m64, r64. -/
theorem kap_or_akzeptiert :
    kapDecode [natByte 72, natByte 9, natByte 192] =
      some (KapDekodiert.kern ⟨CoreBefehl.orReg64 .rax .rax, 3⟩, []) := by
  decide

/-- Chain pin: the chain takes REX.W AND r/m64, r64. -/
theorem kap_and_akzeptiert :
    kapDecode [natByte 72, natByte 33, natByte 192] =
      some (KapDekodiert.kern ⟨CoreBefehl.andReg64 .rax .rax, 3⟩, []) := by
  decide

/-- Chain pin: the chain takes REX.W SUB r/m64, r64. -/
theorem kap_sub_akzeptiert :
    kapDecode [natByte 72, natByte 41, natByte 192] =
      some (KapDekodiert.breit
        (WdHwInstr.ext (ExtInstr.pilot ⟨Befehl.subReg64 .rax .rax, 3⟩)),
        []) := by
  decide

/-- Chain pin: the chain takes REX.W XOR r/m64, r64. -/
theorem kap_xor_akzeptiert :
    kapDecode [natByte 72, natByte 49, natByte 192] =
      some (KapDekodiert.breit
        (WdHwInstr.ext (ExtInstr.pilot ⟨Befehl.xorReg64 .rax .rax, 3⟩)),
        []) := by
  decide

/-- Chain pin: the chain takes REX.W CMP r/m64, r64. -/
theorem kap_cmp_akzeptiert :
    kapDecode [natByte 72, natByte 57, natByte 192] =
      some (KapDekodiert.breit
        (WdHwInstr.ext (ExtInstr.pilot ⟨Befehl.cmpReg64 .rax .rax, 3⟩)),
        []) := by
  decide

/-- Family pin: ADC r/m8, r8 (0x10). -/
theorem carry_10 : (decodeCarry [natByte 16, natByte 192]).isSome = true := by
  decide

/-- Family pin: ADC r/m32, r32 (0x11). -/
theorem carry_11 : (decodeCarry [natByte 17, natByte 192]).isSome = true := by
  decide

/-- Family pin: ADC r8, r/m8 (0x12). -/
theorem carry_12 : (decodeCarry [natByte 18, natByte 192]).isSome = true := by
  decide

/-- Family pin: ADC r32, r/m32 (0x13). -/
theorem carry_13 : (decodeCarry [natByte 19, natByte 192]).isSome = true := by
  decide

/-- Family pin: ADC AL, imm8 (0x14). -/
theorem carry_14 : (decodeCarry [natByte 20, natByte 7]).isSome = true := by
  decide

/-- Family pin: ADC rAX, imm32 (0x15). -/
theorem carry_15 :
    (decodeCarry [natByte 21, natByte 1, natByte 0, natByte 0, natByte 0]).isSome
      = true := by
  decide

/-- Family pin: SBB r/m8, r8 (0x18). -/
theorem carry_18 : (decodeCarry [natByte 24, natByte 192]).isSome = true := by
  decide

/-- Family pin: SBB r/m32, r32 (0x19). -/
theorem carry_19 : (decodeCarry [natByte 25, natByte 192]).isSome = true := by
  decide

/-- Family pin: SBB r8, r/m8 (0x1A). -/
theorem carry_1a : (decodeCarry [natByte 26, natByte 192]).isSome = true := by
  decide

/-- Family pin: SBB r32, r/m32 (0x1B). -/
theorem carry_1b : (decodeCarry [natByte 27, natByte 192]).isSome = true := by
  decide

/-- Family pin: SBB AL, imm8 (0x1C). -/
theorem carry_1c : (decodeCarry [natByte 28, natByte 7]).isSome = true := by
  decide

/-- Family pin: SBB rAX, imm32 (0x1D). -/
theorem carry_1d :
    (decodeCarry [natByte 29, natByte 1, natByte 0, natByte 0, natByte 0]).isSome
      = true := by
  decide

/-- Family pin: REX.W ADD rAX, imm32 (0x05). -/
theorem rax_05 :
    (decodeRax
      [natByte 72, natByte 5, natByte 1, natByte 0, natByte 0,
        natByte 0]).isSome = true := by
  decide

/-- Family pin: REX.W SUB rAX, imm32 (0x2D). -/
theorem rax_2d :
    (decodeRax
      [natByte 72, natByte 45, natByte 1, natByte 0, natByte 0,
        natByte 0]).isSome = true := by
  decide

/-- Family pin: REX.W CMP rAX, imm32 (0x3D). -/
theorem rax_3d :
    (decodeRax
      [natByte 72, natByte 61, natByte 1, natByte 0, natByte 0,
        natByte 0]).isSome = true := by
  decide

/-- Invalid in 64-bit mode: PUSH ES (0x06) decodes to nothing. -/
theorem ung_06 : kapDecode [natByte 6] = none := by decide

/-- Invalid in 64-bit mode: POP ES (0x07) decodes to nothing. -/
theorem ung_07 : kapDecode [natByte 7] = none := by decide

/-- Invalid in 64-bit mode: PUSH CS (0x0E) decodes to nothing. -/
theorem ung_0e : kapDecode [natByte 14] = none := by decide

/-- Invalid in 64-bit mode: PUSH SS (0x16) decodes to nothing. -/
theorem ung_16 : kapDecode [natByte 22] = none := by decide

/-- Invalid in 64-bit mode: POP SS (0x17) decodes to nothing. -/
theorem ung_17 : kapDecode [natByte 23] = none := by decide

/-- Invalid in 64-bit mode: PUSH DS (0x1E) decodes to nothing. -/
theorem ung_1e : kapDecode [natByte 30] = none := by decide

/-- Invalid in 64-bit mode: POP DS (0x1F) decodes to nothing. -/
theorem ung_1f : kapDecode [natByte 31] = none := by decide

/-- Invalid in 64-bit mode: DAA (0x27) decodes to nothing. -/
theorem ung_27 : kapDecode [natByte 39] = none := by decide

/-- Invalid in 64-bit mode: DAS (0x2F) decodes to nothing. -/
theorem ung_2f : kapDecode [natByte 47] = none := by decide

/-- Invalid in 64-bit mode: AAA (0x37) decodes to nothing. -/
theorem ung_37 : kapDecode [natByte 55] = none := by decide

/-- Invalid in 64-bit mode: AAS (0x3F) decodes to nothing. -/
theorem ung_3f : kapDecode [natByte 63] = none := by decide

/-- Deferred: the bare 0F escape alone decodes to nothing. -/
theorem zur_0f : kapDecode [natByte 15] = none := by decide

/-- Deferred: the bare ES prefix alone decodes to nothing. -/
theorem zur_26 : kapDecode [natByte 38] = none := by decide

/-- Deferred: the bare CS prefix alone decodes to nothing. -/
theorem zur_2e : kapDecode [natByte 46] = none := by decide

/-- Deferred: the bare SS prefix alone decodes to nothing. -/
theorem zur_36 : kapDecode [natByte 54] = none := by decide

/-- Deferred: the bare DS prefix alone decodes to nothing. -/
theorem zur_3e : kapDecode [natByte 62] = none := by decide

/-- Gap: no family takes ADD r/m8, r8 (0x00). -/
theorem fehlt_00 : kapDecode [natByte 0, natByte 192] = none := by decide

/-- Gap: no family takes ADD r8, r/m8 (0x02). -/
theorem fehlt_02 : kapDecode [natByte 2, natByte 192] = none := by decide

/-- Gap: no family takes ADD r32, r/m32 (0x03). -/
theorem fehlt_03 : kapDecode [natByte 3, natByte 192] = none := by decide

/-- Gap: no family takes ADD AL, imm8 (0x04). -/
theorem fehlt_04 : kapDecode [natByte 4, natByte 7] = none := by decide

/-- Gap: no family takes OR r/m8, r8 (0x08). -/
theorem fehlt_08 : kapDecode [natByte 8, natByte 192] = none := by decide

/-- Gap: no family takes OR r8, r/m8 (0x0A). -/
theorem fehlt_0a : kapDecode [natByte 10, natByte 192] = none := by decide

/-- Gap: no family takes OR r32, r/m32 (0x0B). -/
theorem fehlt_0b : kapDecode [natByte 11, natByte 192] = none := by decide

/-- Gap: no family takes OR AL, imm8 (0x0C). -/
theorem fehlt_0c : kapDecode [natByte 12, natByte 7] = none := by decide

/-- Gap: no family takes OR rAX, imm32 (0x0D). -/
theorem fehlt_0d :
    kapDecode [natByte 13, natByte 1, natByte 0, natByte 0, natByte 0] = none := by
  decide

/-- Gap: no family takes AND r/m8, r8 (0x20). -/
theorem fehlt_20 : kapDecode [natByte 32, natByte 192] = none := by decide

/-- Gap: no family takes AND r8, r/m8 (0x22). -/
theorem fehlt_22 : kapDecode [natByte 34, natByte 192] = none := by decide

/-- Gap: no family takes AND r32, r/m32 (0x23). -/
theorem fehlt_23 : kapDecode [natByte 35, natByte 192] = none := by decide

/-- Gap: no family takes AND AL, imm8 (0x24). -/
theorem fehlt_24 : kapDecode [natByte 36, natByte 7] = none := by decide

/-- Gap: no family takes AND rAX, imm32 (0x25). -/
theorem fehlt_25 :
    kapDecode [natByte 37, natByte 1, natByte 0, natByte 0, natByte 0] = none := by
  decide

/-- Gap: no family takes SUB r/m8, r8 (0x28). -/
theorem fehlt_28 : kapDecode [natByte 40, natByte 192] = none := by decide

/-- Gap: no family takes SUB r8, r/m8 (0x2A). -/
theorem fehlt_2a : kapDecode [natByte 42, natByte 192] = none := by decide

/-- Gap: no family takes SUB r32, r/m32 (0x2B). -/
theorem fehlt_2b : kapDecode [natByte 43, natByte 192] = none := by decide

/-- Gap: no family takes SUB AL, imm8 (0x2C). -/
theorem fehlt_2c : kapDecode [natByte 44, natByte 7] = none := by decide

/-- Gap: no family takes XOR r/m8, r8 (0x30). -/
theorem fehlt_30 : kapDecode [natByte 48, natByte 192] = none := by decide

/-- Gap: no family takes XOR r8, r/m8 (0x32). -/
theorem fehlt_32 : kapDecode [natByte 50, natByte 192] = none := by decide

/-- Gap: no family takes XOR r32, r/m32 (0x33). -/
theorem fehlt_33 : kapDecode [natByte 51, natByte 192] = none := by decide

/-- Gap: no family takes XOR AL, imm8 (0x34). -/
theorem fehlt_34 : kapDecode [natByte 52, natByte 7] = none := by decide

/-- Gap: no family takes XOR rAX, imm32 (0x35). -/
theorem fehlt_35 :
    kapDecode [natByte 53, natByte 1, natByte 0, natByte 0, natByte 0] = none := by
  decide

/-- Gap: no family takes CMP r/m8, r8 (0x38). -/
theorem fehlt_38 : kapDecode [natByte 56, natByte 192] = none := by decide

/-- Gap: no family takes CMP r8, r/m8 (0x3A). -/
theorem fehlt_3a : kapDecode [natByte 58, natByte 192] = none := by decide

/-- Gap: no family takes CMP r32, r/m32 (0x3B). -/
theorem fehlt_3b : kapDecode [natByte 59, natByte 192] = none := by decide

/-- Gap: no family takes CMP AL, imm8 (0x3C). -/
theorem fehlt_3c : kapDecode [natByte 60, natByte 7] = none := by decide

/-! CUTS:
  - Checked part complete for this region: 6 chain pins, 15 family
    pins, 11 invalid-form refusals, 5 deferred-prefix refusals,
    27 checked gap refusals, 5 count theorems, exact-once coverage.
  - The `fehlt` refusals are proved against the `kapDecode` chain only.
    Standalone family decoders outside the chain (decodeCarry,
    decodeRax, decodeZero) were inspected by reading their dispatch
    tables, not by a checked sweep.
  - `verweigert` is honestly zero: no valid in-scope form in 00-3F is
    deliberately refused; gaps are `fehlt`, invalid forms `ungueltig64`.
  - Opcode map is a NAMED assumption (Intel SDM edition 093, checked
    against the supplied PDF/TXT extracts, never as proved fact).
  - No AMD manual in this clone: no vendor-difference claim. No
    `herstellerabhaengig` row occurs in 00-3F.
  - No silicon correspondence beyond self-consistency is claimed.
-/

#print axioms c_modelliert
#print axioms c_fehlt
#print axioms abdeckung
#print axioms kap_add_akzeptiert
#print axioms kap_or_akzeptiert
#print axioms kap_and_akzeptiert
#print axioms kap_sub_akzeptiert
#print axioms kap_xor_akzeptiert
#print axioms kap_cmp_akzeptiert
