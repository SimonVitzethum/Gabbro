/-
  File:      Grammatik/X86/OpcodeLedger1Byte80.lean
  Subject:   Opcode ledger over one-byte opcodes 0x80-0xBF in 64-bit mode.

  Lane 1337: every opcode byte in 0x80-0xBF with every legal
  prefix/ModRM.reg extension, classified against the capstone
  decoder chain `kapDecode` (HwKapsteinDecoder). Statuses:
  modelled (chain decodes the witness to the named family),
  deferred (an accepted family models it, chain unwired),
  refused (valid but excluded by machine design), invalid-in-64
  (architecturally #UD/reserved), missing (no family models it).
  Provenance: Intel SDM 325462-093US (clone-local text).
-/
import Grammatik.X86.HwKapsteinDecoder
import Grammatik.X86.IntCarryForms
import Grammatik.X86.XchgOrderNeed
import Grammatik.X86.AddressEncoding

namespace Gabbro.Grammatik.X86.OpcodeLedger80

/-- Prefix class of a ledger key (canonical witness byte first). -/
inductive LPraefix | ohne | rexW | rexB | lock | ops16
  deriving DecidableEq, Repr

/-- Ledger status per the lane task. -/
inductive LStatus | modelliert | zurueckgestellt | verweigert | ungueltig64 | fehlt
  deriving DecidableEq, Repr

/-- One ledger row: key, mnemonic, status, modelling family module,
    one-line reason, expected `kapFam` tag (255 = chain refuses)
    and the canonical witness bytes. -/
structure LEintrag where
  praefix : LPraefix
  op : Nat
  erw : Option Nat
  mnemonik : String
  status : LStatus
  familie : String
  grund : String
  tag : Nat
  zeuge : List Byte
  deriving DecidableEq, Repr

/-- Family tag of a `kapDecode` answer: 0 breit, 5 kompakt, 6 kern,
    7 avx2, 255 refusal (s32/mxcsr/lock arms take no 80-BF bytes). -/
def kapFam (bs : List Byte) : Nat :=
  match kapDecode bs with
  | some (.breit _, _) => 0
  | some (.kompakt _, _) => 5
  | some (.kern _, _) => 6
  | some (.avx2 _, _) => 7
  | _ => 255

/-- One-line row constructor. -/
def L (p : LPraefix) (op : Nat) (erw : Option Nat) (mn : String)
    (s : LStatus) (fam : String) (gr : String) (tag : Nat)
    (z : List Byte) : LEintrag :=
  ⟨p, op, erw, mn, s, fam, gr, tag, z⟩

/-- Skeleton rows: the four convert forms (98/99 bare and REX.W). -/
def ledger80 : List LEintrag :=
  [L .ohne 152 none "CWDE" .modelliert "MulDivWidthHardwareForms"
    "" 0 [natByte 152],
   L .rexW 152 none "CDQE" .modelliert "MulDivWidthHardwareForms"
    "" 0 [natByte 72, natByte 152],
   L .ohne 128 (some 0) "ADD Eb,Ib" .fehlt "keine"
    "pervasive 8-bit ALU-imm form, no family models it" 255
    [natByte 128, natByte 192, natByte 5],
   L .ohne 128 (some 1) "OR Eb,Ib" .fehlt "keine"
    "pervasive 8-bit ALU-imm form, no family models it" 255
    [natByte 128, natByte 200, natByte 5],
   L .ohne 128 (some 2) "ADC Eb,Ib" .zurueckgestellt "IntCarryForms"
    "family models it (pin_carry_128_e2), chain unwired" 255
    [natByte 128, natByte 208, natByte 5],
   L .ohne 128 (some 3) "SBB Eb,Ib" .zurueckgestellt "IntCarryForms"
    "family models it (pin_carry_128_e3), chain unwired" 255
    [natByte 128, natByte 216, natByte 5],
   L .ohne 128 (some 4) "AND Eb,Ib" .fehlt "keine"
    "pervasive 8-bit ALU-imm form, no family models it" 255
    [natByte 128, natByte 224, natByte 5],
   L .ohne 128 (some 5) "SUB Eb,Ib" .fehlt "keine"
    "pervasive 8-bit ALU-imm form, no family models it" 255
    [natByte 128, natByte 232, natByte 5],
   L .ohne 128 (some 6) "XOR Eb,Ib" .fehlt "keine"
    "pervasive 8-bit ALU-imm form, no family models it" 255
    [natByte 128, natByte 240, natByte 5],
   L .ohne 128 (some 7) "CMP Eb,Ib" .fehlt "keine"
    "pervasive 8-bit ALU-imm form, no family models it" 255
    [natByte 128, natByte 248, natByte 5],
   L .ohne 129 (some 0) "ADD Ev,Iz" .fehlt "keine"
    "pervasive 32-bit ALU-imm form, no family models it" 255
    [natByte 129, natByte 192, natByte 5, natByte 0, natByte 0, natByte 0],
   L .ohne 129 (some 1) "OR Ev,Iz" .fehlt "keine"
    "pervasive 32-bit ALU-imm form, no family models it" 255
    [natByte 129, natByte 200, natByte 5, natByte 0, natByte 0, natByte 0],
   L .ohne 129 (some 2) "ADC Ev,Iz" .zurueckgestellt "IntCarryForms"
    "family models it (pin_carry_129_e2), chain unwired" 255
    [natByte 129, natByte 208, natByte 5, natByte 0, natByte 0, natByte 0],
   L .ohne 129 (some 3) "SBB Ev,Iz" .zurueckgestellt "IntCarryForms"
    "family models it (pin_carry_129_e3), chain unwired" 255
    [natByte 129, natByte 216, natByte 5, natByte 0, natByte 0, natByte 0],
   L .ohne 129 (some 4) "AND Ev,Iz" .fehlt "keine"
    "pervasive 32-bit ALU-imm form, no family models it" 255
    [natByte 129, natByte 224, natByte 5, natByte 0, natByte 0, natByte 0],
   L .ohne 129 (some 5) "SUB Ev,Iz" .fehlt "keine"
    "pervasive 32-bit ALU-imm form, no family models it" 255
    [natByte 129, natByte 232, natByte 5, natByte 0, natByte 0, natByte 0],
   L .ohne 129 (some 6) "XOR Ev,Iz" .fehlt "keine"
    "pervasive 32-bit ALU-imm form, no family models it" 255
    [natByte 129, natByte 240, natByte 5, natByte 0, natByte 0, natByte 0],
   L .ohne 129 (some 7) "CMP Ev,Iz" .fehlt "keine"
    "pervasive 32-bit ALU-imm form, no family models it" 255
    [natByte 129, natByte 248, natByte 5, natByte 0, natByte 0, natByte 0],
   L .ohne 130 (some 0) "ADD Eb,Ib (82 alias)" .ungueltig64 "keine"
    "SDM Vol 3B 25: opcode 82H causes #UD in 64-bit mode" 255
    [natByte 130, natByte 192, natByte 5],
   L .ohne 130 (some 1) "OR Eb,Ib (82 alias)" .ungueltig64 "keine"
    "SDM Vol 3B 25: opcode 82H causes #UD in 64-bit mode" 255
    [natByte 130, natByte 200, natByte 5],
   L .ohne 130 (some 2) "ADC Eb,Ib (82 alias)" .ungueltig64 "keine"
    "SDM Vol 3B 25: opcode 82H causes #UD in 64-bit mode" 255
    [natByte 130, natByte 208, natByte 5],
   L .ohne 130 (some 3) "SBB Eb,Ib (82 alias)" .ungueltig64 "keine"
    "SDM Vol 3B 25: opcode 82H causes #UD in 64-bit mode" 255
    [natByte 130, natByte 216, natByte 5],
   L .ohne 130 (some 4) "AND Eb,Ib (82 alias)" .ungueltig64 "keine"
    "SDM Vol 3B 25: opcode 82H causes #UD in 64-bit mode" 255
    [natByte 130, natByte 224, natByte 5],
   L .ohne 130 (some 5) "SUB Eb,Ib (82 alias)" .ungueltig64 "keine"
    "SDM Vol 3B 25: opcode 82H causes #UD in 64-bit mode" 255
    [natByte 130, natByte 232, natByte 5],
   L .ohne 130 (some 6) "XOR Eb,Ib (82 alias)" .ungueltig64 "keine"
    "SDM Vol 3B 25: opcode 82H causes #UD in 64-bit mode" 255
    [natByte 130, natByte 240, natByte 5],
   L .ohne 130 (some 7) "CMP Eb,Ib (82 alias)" .ungueltig64 "keine"
    "SDM Vol 3B 25: opcode 82H causes #UD in 64-bit mode" 255
    [natByte 130, natByte 248, natByte 5],
   L .ohne 131 (some 0) "ADD Ev,Ib" .fehlt "keine"
    "pervasive sign-extended ALU-imm8 form, no family models it" 255
    [natByte 131, natByte 192, natByte 5],
   L .ohne 131 (some 1) "OR Ev,Ib" .fehlt "keine"
    "pervasive sign-extended ALU-imm8 form, no family models it" 255
    [natByte 131, natByte 200, natByte 5],
   L .ohne 131 (some 2) "ADC Ev,Ib" .zurueckgestellt "IntCarryForms"
    "family models it (pin_carry_131_e2), chain unwired" 255
    [natByte 131, natByte 208, natByte 5],
   L .ohne 131 (some 3) "SBB Ev,Ib" .zurueckgestellt "IntCarryForms"
    "family models it (pin_carry_131_e3), chain unwired" 255
    [natByte 131, natByte 216, natByte 5],
   L .ohne 131 (some 4) "AND Ev,Ib" .fehlt "keine"
    "pervasive sign-extended ALU-imm8 form, no family models it" 255
    [natByte 131, natByte 224, natByte 5],
   L .ohne 131 (some 5) "SUB Ev,Ib" .fehlt "keine"
    "pervasive sign-extended ALU-imm8 form, no family models it" 255
    [natByte 131, natByte 232, natByte 5],
   L .ohne 131 (some 6) "XOR Ev,Ib" .fehlt "keine"
    "pervasive sign-extended ALU-imm8 form, no family models it" 255
    [natByte 131, natByte 240, natByte 5],
   L .ohne 131 (some 7) "CMP Ev,Ib" .fehlt "keine"
    "pervasive sign-extended ALU-imm8 form, no family models it" 255
    [natByte 131, natByte 248, natByte 5],
   L .rexW 128 (some 0) "ADD Eb,Ib" .fehlt "keine"
    "REX.W ignored on byte op; no family models it" 255
    [natByte 72, natByte 128, natByte 192, natByte 5],
   L .rexW 128 (some 1) "OR Eb,Ib" .fehlt "keine"
    "REX.W ignored on byte op; no family models it" 255
    [natByte 72, natByte 128, natByte 200, natByte 5],
   L .rexW 128 (some 2) "ADC Eb,Ib" .zurueckgestellt "IntCarryForms"
    "family models it (pin_carry_w128_e2), chain unwired" 255
    [natByte 72, natByte 128, natByte 208, natByte 5],
   L .rexW 128 (some 3) "SBB Eb,Ib" .zurueckgestellt "IntCarryForms"
    "family models it (pin_carry_w128_e3), chain unwired" 255
    [natByte 72, natByte 128, natByte 216, natByte 5],
   L .rexW 128 (some 4) "AND Eb,Ib" .fehlt "keine"
    "REX.W ignored on byte op; no family models it" 255
    [natByte 72, natByte 128, natByte 224, natByte 5],
   L .rexW 128 (some 5) "SUB Eb,Ib" .fehlt "keine"
    "REX.W ignored on byte op; no family models it" 255
    [natByte 72, natByte 128, natByte 232, natByte 5],
   L .rexW 128 (some 6) "XOR Eb,Ib" .fehlt "keine"
    "REX.W ignored on byte op; no family models it" 255
    [natByte 72, natByte 128, natByte 240, natByte 5],
   L .rexW 128 (some 7) "CMP Eb,Ib" .fehlt "keine"
    "REX.W ignored on byte op; no family models it" 255
    [natByte 72, natByte 128, natByte 248, natByte 5],
   L .rexW 129 (some 0) "ADD Gv,Ev" .modelliert "CompactForms"
    "register-direct aluImm32 only; memory ALU unmodelled" 5
    [natByte 72, natByte 129, natByte 192, natByte 5, natByte 0, natByte 0, natByte 0],
   L .rexW 129 (some 1) "OR Gv,Ev" .modelliert "CompactForms"
    "register-direct aluImm32 only; memory ALU unmodelled" 5
    [natByte 72, natByte 129, natByte 200, natByte 5, natByte 0, natByte 0, natByte 0],
   L .rexW 129 (some 2) "ADC Gv,Ev" .zurueckgestellt "IntCarryForms"
    "family models it (pin_carry_w129_e2), chain unwired" 255
    [natByte 72, natByte 129, natByte 208, natByte 5, natByte 0, natByte 0, natByte 0],
   L .rexW 129 (some 3) "SBB Gv,Ev" .zurueckgestellt "IntCarryForms"
    "family models it (pin_carry_w129_e3), chain unwired" 255
    [natByte 72, natByte 129, natByte 216, natByte 5, natByte 0, natByte 0, natByte 0],
   L .rexW 129 (some 4) "AND Gv,Ev" .modelliert "CompactForms"
    "register-direct aluImm32 only; memory ALU unmodelled" 5
    [natByte 72, natByte 129, natByte 224, natByte 5, natByte 0, natByte 0, natByte 0],
   L .rexW 129 (some 5) "SUB Gv,Ev" .modelliert "CompactForms"
    "register-direct aluImm32 only; memory ALU unmodelled" 5
    [natByte 72, natByte 129, natByte 232, natByte 5, natByte 0, natByte 0, natByte 0],
   L .rexW 129 (some 6) "XOR Gv,Ev" .modelliert "CompactForms"
    "register-direct aluImm32 only; memory ALU unmodelled" 5
    [natByte 72, natByte 129, natByte 240, natByte 5, natByte 0, natByte 0, natByte 0],
   L .rexW 129 (some 7) "CMP Gv,Ev" .modelliert "CompactForms"
    "register-direct aluImm32 only; memory ALU unmodelled" 5
    [natByte 72, natByte 129, natByte 248, natByte 5, natByte 0, natByte 0, natByte 0],
   L .rexW 130 (some 0) "ADD Eb,Ib (82 alias)" .ungueltig64 "keine"
    "SDM Vol 3B 25: opcode 82H causes #UD in 64-bit mode" 255
    [natByte 72, natByte 130, natByte 192, natByte 5],
   L .rexW 130 (some 1) "OR Eb,Ib (82 alias)" .ungueltig64 "keine"
    "SDM Vol 3B 25: opcode 82H causes #UD in 64-bit mode" 255
    [natByte 72, natByte 130, natByte 200, natByte 5],
   L .rexW 130 (some 2) "ADC Eb,Ib (82 alias)" .ungueltig64 "keine"
    "SDM Vol 3B 25: opcode 82H causes #UD in 64-bit mode" 255
    [natByte 72, natByte 130, natByte 208, natByte 5],
   L .rexW 130 (some 3) "SBB Eb,Ib (82 alias)" .ungueltig64 "keine"
    "SDM Vol 3B 25: opcode 82H causes #UD in 64-bit mode" 255
    [natByte 72, natByte 130, natByte 216, natByte 5],
   L .rexW 130 (some 4) "AND Eb,Ib (82 alias)" .ungueltig64 "keine"
    "SDM Vol 3B 25: opcode 82H causes #UD in 64-bit mode" 255
    [natByte 72, natByte 130, natByte 224, natByte 5],
   L .rexW 130 (some 5) "SUB Eb,Ib (82 alias)" .ungueltig64 "keine"
    "SDM Vol 3B 25: opcode 82H causes #UD in 64-bit mode" 255
    [natByte 72, natByte 130, natByte 232, natByte 5],
   L .rexW 130 (some 6) "XOR Eb,Ib (82 alias)" .ungueltig64 "keine"
    "SDM Vol 3B 25: opcode 82H causes #UD in 64-bit mode" 255
    [natByte 72, natByte 130, natByte 240, natByte 5],
   L .rexW 130 (some 7) "CMP Eb,Ib (82 alias)" .ungueltig64 "keine"
    "SDM Vol 3B 25: opcode 82H causes #UD in 64-bit mode" 255
    [natByte 72, natByte 130, natByte 248, natByte 5],
   L .rexW 131 (some 0) "ADD Gv,Ib" .modelliert "CompactForms"
    "register-direct aluImm8 only; memory ALU unmodelled" 5
    [natByte 72, natByte 131, natByte 192, natByte 5],
   L .rexW 131 (some 1) "OR Gv,Ib" .modelliert "CompactForms"
    "register-direct aluImm8 only; memory ALU unmodelled" 5
    [natByte 72, natByte 131, natByte 200, natByte 5],
   L .rexW 131 (some 2) "ADC Gv,Ib" .zurueckgestellt "IntCarryForms"
    "family models it (pin_carry_w131_e2), chain unwired" 255
    [natByte 72, natByte 131, natByte 208, natByte 5],
   L .rexW 131 (some 3) "SBB Gv,Ib" .zurueckgestellt "IntCarryForms"
    "family models it (pin_carry_w131_e3), chain unwired" 255
    [natByte 72, natByte 131, natByte 216, natByte 5],
   L .rexW 131 (some 4) "AND Gv,Ib" .modelliert "CompactForms"
    "register-direct aluImm8 only; memory ALU unmodelled" 5
    [natByte 72, natByte 131, natByte 224, natByte 5],
   L .rexW 131 (some 5) "SUB Gv,Ib" .modelliert "CompactForms"
    "register-direct aluImm8 only; memory ALU unmodelled" 5
    [natByte 72, natByte 131, natByte 232, natByte 5],
   L .rexW 131 (some 6) "XOR Gv,Ib" .modelliert "CompactForms"
    "register-direct aluImm8 only; memory ALU unmodelled" 5
    [natByte 72, natByte 131, natByte 240, natByte 5],
   L .rexW 131 (some 7) "CMP Gv,Ib" .modelliert "CompactForms"
    "register-direct aluImm8 only; memory ALU unmodelled" 5
    [natByte 72, natByte 131, natByte 248, natByte 5]]

theorem t152o : kapFam [natByte 152] = 0 := by decide
theorem t152w : kapFam [natByte 72, natByte 152] = 0 := by decide
theorem t128o0 : kapDecode [natByte 128, natByte 192, natByte 5] = none := by decide
theorem t128o1 : kapDecode [natByte 128, natByte 200, natByte 5] = none := by decide
theorem t128o2 : kapDecode [natByte 128, natByte 208, natByte 5] = none := by decide
theorem t128o3 : kapDecode [natByte 128, natByte 216, natByte 5] = none := by decide
theorem t128o4 : kapDecode [natByte 128, natByte 224, natByte 5] = none := by decide
theorem t128o5 : kapDecode [natByte 128, natByte 232, natByte 5] = none := by decide
theorem t128o6 : kapDecode [natByte 128, natByte 240, natByte 5] = none := by decide
theorem t128o7 : kapDecode [natByte 128, natByte 248, natByte 5] = none := by decide
theorem t129o0 : kapDecode [natByte 129, natByte 192, natByte 5, natByte 0, natByte 0, natByte 0] = none := by decide
theorem t129o1 : kapDecode [natByte 129, natByte 200, natByte 5, natByte 0, natByte 0, natByte 0] = none := by decide
theorem t129o2 : kapDecode [natByte 129, natByte 208, natByte 5, natByte 0, natByte 0, natByte 0] = none := by decide
theorem t129o3 : kapDecode [natByte 129, natByte 216, natByte 5, natByte 0, natByte 0, natByte 0] = none := by decide
theorem t129o4 : kapDecode [natByte 129, natByte 224, natByte 5, natByte 0, natByte 0, natByte 0] = none := by decide
theorem t129o5 : kapDecode [natByte 129, natByte 232, natByte 5, natByte 0, natByte 0, natByte 0] = none := by decide
theorem t129o6 : kapDecode [natByte 129, natByte 240, natByte 5, natByte 0, natByte 0, natByte 0] = none := by decide
theorem t129o7 : kapDecode [natByte 129, natByte 248, natByte 5, natByte 0, natByte 0, natByte 0] = none := by decide
theorem t130o0 : kapDecode [natByte 130, natByte 192, natByte 5] = none := by decide
theorem t130o1 : kapDecode [natByte 130, natByte 200, natByte 5] = none := by decide
theorem t130o2 : kapDecode [natByte 130, natByte 208, natByte 5] = none := by decide
theorem t130o3 : kapDecode [natByte 130, natByte 216, natByte 5] = none := by decide
theorem t130o4 : kapDecode [natByte 130, natByte 224, natByte 5] = none := by decide
theorem t130o5 : kapDecode [natByte 130, natByte 232, natByte 5] = none := by decide
theorem t130o6 : kapDecode [natByte 130, natByte 240, natByte 5] = none := by decide
theorem t130o7 : kapDecode [natByte 130, natByte 248, natByte 5] = none := by decide
theorem t131o0 : kapDecode [natByte 131, natByte 192, natByte 5] = none := by decide
theorem t131o1 : kapDecode [natByte 131, natByte 200, natByte 5] = none := by decide
theorem t131o2 : kapDecode [natByte 131, natByte 208, natByte 5] = none := by decide
theorem t131o3 : kapDecode [natByte 131, natByte 216, natByte 5] = none := by decide
theorem t131o4 : kapDecode [natByte 131, natByte 224, natByte 5] = none := by decide
theorem t131o5 : kapDecode [natByte 131, natByte 232, natByte 5] = none := by decide
theorem t131o6 : kapDecode [natByte 131, natByte 240, natByte 5] = none := by decide
theorem t131o7 : kapDecode [natByte 131, natByte 248, natByte 5] = none := by decide
theorem t128w0 : kapDecode [natByte 72, natByte 128, natByte 192, natByte 5] = none := by decide
theorem t128w1 : kapDecode [natByte 72, natByte 128, natByte 200, natByte 5] = none := by decide
theorem t128w2 : kapDecode [natByte 72, natByte 128, natByte 208, natByte 5] = none := by decide
theorem t128w3 : kapDecode [natByte 72, natByte 128, natByte 216, natByte 5] = none := by decide
theorem t128w4 : kapDecode [natByte 72, natByte 128, natByte 224, natByte 5] = none := by decide
theorem t128w5 : kapDecode [natByte 72, natByte 128, natByte 232, natByte 5] = none := by decide
theorem t128w6 : kapDecode [natByte 72, natByte 128, natByte 240, natByte 5] = none := by decide
theorem t128w7 : kapDecode [natByte 72, natByte 128, natByte 248, natByte 5] = none := by decide
theorem t129w0 : kapFam [natByte 72, natByte 129, natByte 192, natByte 5, natByte 0, natByte 0, natByte 0] = 5 := by decide
theorem t129w1 : kapFam [natByte 72, natByte 129, natByte 200, natByte 5, natByte 0, natByte 0, natByte 0] = 5 := by decide
theorem t129w2 : kapDecode [natByte 72, natByte 129, natByte 208, natByte 5, natByte 0, natByte 0, natByte 0] = none := by decide
theorem t129w3 : kapDecode [natByte 72, natByte 129, natByte 216, natByte 5, natByte 0, natByte 0, natByte 0] = none := by decide
theorem t129w4 : kapFam [natByte 72, natByte 129, natByte 224, natByte 5, natByte 0, natByte 0, natByte 0] = 5 := by decide
theorem t129w5 : kapFam [natByte 72, natByte 129, natByte 232, natByte 5, natByte 0, natByte 0, natByte 0] = 5 := by decide
theorem t129w6 : kapFam [natByte 72, natByte 129, natByte 240, natByte 5, natByte 0, natByte 0, natByte 0] = 5 := by decide
theorem t129w7 : kapFam [natByte 72, natByte 129, natByte 248, natByte 5, natByte 0, natByte 0, natByte 0] = 5 := by decide
theorem t130w0 : kapDecode [natByte 72, natByte 130, natByte 192, natByte 5] = none := by decide
theorem t130w1 : kapDecode [natByte 72, natByte 130, natByte 200, natByte 5] = none := by decide
theorem t130w2 : kapDecode [natByte 72, natByte 130, natByte 208, natByte 5] = none := by decide
theorem t130w3 : kapDecode [natByte 72, natByte 130, natByte 216, natByte 5] = none := by decide
theorem t130w4 : kapDecode [natByte 72, natByte 130, natByte 224, natByte 5] = none := by decide
theorem t130w5 : kapDecode [natByte 72, natByte 130, natByte 232, natByte 5] = none := by decide
theorem t130w6 : kapDecode [natByte 72, natByte 130, natByte 240, natByte 5] = none := by decide
theorem t130w7 : kapDecode [natByte 72, natByte 130, natByte 248, natByte 5] = none := by decide
theorem t131w0 : kapFam [natByte 72, natByte 131, natByte 192, natByte 5] = 5 := by decide
theorem t131w1 : kapFam [natByte 72, natByte 131, natByte 200, natByte 5] = 5 := by decide
theorem t131w2 : kapDecode [natByte 72, natByte 131, natByte 208, natByte 5] = none := by decide
theorem t131w3 : kapDecode [natByte 72, natByte 131, natByte 216, natByte 5] = none := by decide
theorem t131w4 : kapFam [natByte 72, natByte 131, natByte 224, natByte 5] = 5 := by decide
theorem t131w5 : kapFam [natByte 72, natByte 131, natByte 232, natByte 5] = 5 := by decide
theorem t131w6 : kapFam [natByte 72, natByte 131, natByte 240, natByte 5] = 5 := by decide
theorem t131w7 : kapFam [natByte 72, natByte 131, natByte 248, natByte 5] = 5 := by decide

/-! CUTS (skeleton): rows 98/99 only; 236 keys outstanding. -/
#print axioms t152o
#print axioms t152w
