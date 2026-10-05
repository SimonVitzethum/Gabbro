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
    [natByte 72, natByte 131, natByte 248, natByte 5],
   L .ohne 140 (some 0) "MOV Ev,Sreg-ES" .verweigert "keine"
    "no segment-register state in the model; refused by design" 255
    [natByte 140, natByte 192],
   L .ohne 140 (some 1) "MOV Ev,Sreg-CS" .verweigert "keine"
    "no segment-register state in the model; refused by design" 255
    [natByte 140, natByte 200],
   L .ohne 140 (some 2) "MOV Ev,Sreg-SS" .verweigert "keine"
    "no segment-register state in the model; refused by design" 255
    [natByte 140, natByte 208],
   L .ohne 140 (some 3) "MOV Ev,Sreg-DS" .verweigert "keine"
    "no segment-register state in the model; refused by design" 255
    [natByte 140, natByte 216],
   L .ohne 140 (some 4) "MOV Ev,Sreg-FS" .verweigert "keine"
    "no segment-register state in the model; refused by design" 255
    [natByte 140, natByte 224],
   L .ohne 140 (some 5) "MOV Ev,Sreg-GS" .verweigert "keine"
    "no segment-register state in the model; refused by design" 255
    [natByte 140, natByte 232],
   L .ohne 140 (some 6) "MOV Ev,sreg-reserved" .ungueltig64 "keine"
    "Table B-8 sreg3 110 reserved: do not use" 255
    [natByte 140, natByte 240],
   L .ohne 140 (some 7) "MOV Ev,sreg-reserved" .ungueltig64 "keine"
    "Table B-8 sreg3 111 reserved: do not use" 255
    [natByte 140, natByte 248],
   L .ohne 142 (some 0) "MOV Sreg-ES,Ev" .verweigert "keine"
    "no segment-register state in the model; refused by design" 255
    [natByte 142, natByte 192],
   L .ohne 142 (some 1) "MOV Sreg-CS,Ev" .verweigert "keine"
    "no segment-register state in the model; refused by design" 255
    [natByte 142, natByte 200],
   L .ohne 142 (some 2) "MOV Sreg-SS,Ev" .verweigert "keine"
    "no segment-register state in the model; refused by design" 255
    [natByte 142, natByte 208],
   L .ohne 142 (some 3) "MOV Sreg-DS,Ev" .verweigert "keine"
    "no segment-register state in the model; refused by design" 255
    [natByte 142, natByte 216],
   L .ohne 142 (some 4) "MOV Sreg-FS,Ev" .verweigert "keine"
    "no segment-register state in the model; refused by design" 255
    [natByte 142, natByte 224],
   L .ohne 142 (some 5) "MOV Sreg-GS,Ev" .verweigert "keine"
    "no segment-register state in the model; refused by design" 255
    [natByte 142, natByte 232],
   L .ohne 142 (some 6) "MOV sreg-reserved,Ev" .ungueltig64 "keine"
    "Table B-8 sreg3 110 reserved: do not use" 255
    [natByte 142, natByte 240],
   L .ohne 142 (some 7) "MOV sreg-reserved,Ev" .ungueltig64 "keine"
    "Table B-8 sreg3 111 reserved: do not use" 255
    [natByte 142, natByte 248],
   L .ohne 143 (some 0) "POP Ev" .fehlt "keine"
    "common: callee-saved restores and stack cleanup; no family" 255
    [natByte 143, natByte 192],
   L .ohne 143 (some 1) "POP (reserved ext)" .ungueltig64 "keine"
    "Appendix A Group 1A defines only /0 POP; POP lists 8F /0 only" 255
    [natByte 143, natByte 200],
   L .ohne 143 (some 2) "POP (reserved ext)" .ungueltig64 "keine"
    "Appendix A Group 1A defines only /0 POP; POP lists 8F /0 only" 255
    [natByte 143, natByte 208],
   L .ohne 143 (some 3) "POP (reserved ext)" .ungueltig64 "keine"
    "Appendix A Group 1A defines only /0 POP; POP lists 8F /0 only" 255
    [natByte 143, natByte 216],
   L .ohne 143 (some 4) "POP (reserved ext)" .ungueltig64 "keine"
    "Appendix A Group 1A defines only /0 POP; POP lists 8F /0 only" 255
    [natByte 143, natByte 224],
   L .ohne 143 (some 5) "POP (reserved ext)" .ungueltig64 "keine"
    "Appendix A Group 1A defines only /0 POP; POP lists 8F /0 only" 255
    [natByte 143, natByte 232],
   L .ohne 143 (some 6) "POP (reserved ext)" .ungueltig64 "keine"
    "Appendix A Group 1A defines only /0 POP; POP lists 8F /0 only" 255
    [natByte 143, natByte 240],
   L .ohne 143 (some 7) "POP (reserved ext)" .ungueltig64 "keine"
    "Appendix A Group 1A defines only /0 POP; POP lists 8F /0 only" 255
    [natByte 143, natByte 248],
   L .rexW 140 (some 0) "MOV Ev,Sreg-ES" .verweigert "keine"
    "no segment-register state in the model; refused by design" 255
    [natByte 72, natByte 140, natByte 192],
   L .rexW 140 (some 1) "MOV Ev,Sreg-CS" .verweigert "keine"
    "no segment-register state in the model; refused by design" 255
    [natByte 72, natByte 140, natByte 200],
   L .rexW 140 (some 2) "MOV Ev,Sreg-SS" .verweigert "keine"
    "no segment-register state in the model; refused by design" 255
    [natByte 72, natByte 140, natByte 208],
   L .rexW 140 (some 3) "MOV Ev,Sreg-DS" .verweigert "keine"
    "no segment-register state in the model; refused by design" 255
    [natByte 72, natByte 140, natByte 216],
   L .rexW 140 (some 4) "MOV Ev,Sreg-FS" .verweigert "keine"
    "no segment-register state in the model; refused by design" 255
    [natByte 72, natByte 140, natByte 224],
   L .rexW 140 (some 5) "MOV Ev,Sreg-GS" .verweigert "keine"
    "no segment-register state in the model; refused by design" 255
    [natByte 72, natByte 140, natByte 232],
   L .rexW 140 (some 6) "MOV Ev,sreg-reserved" .ungueltig64 "keine"
    "Table B-8 sreg3 110 reserved: do not use" 255
    [natByte 72, natByte 140, natByte 240],
   L .rexW 140 (some 7) "MOV Ev,sreg-reserved" .ungueltig64 "keine"
    "Table B-8 sreg3 111 reserved: do not use" 255
    [natByte 72, natByte 140, natByte 248],
   L .rexW 142 (some 0) "MOV Sreg-ES,Ev" .verweigert "keine"
    "no segment-register state in the model; refused by design" 255
    [natByte 72, natByte 142, natByte 192],
   L .rexW 142 (some 1) "MOV Sreg-CS,Ev" .verweigert "keine"
    "no segment-register state in the model; refused by design" 255
    [natByte 72, natByte 142, natByte 200],
   L .rexW 142 (some 2) "MOV Sreg-SS,Ev" .verweigert "keine"
    "no segment-register state in the model; refused by design" 255
    [natByte 72, natByte 142, natByte 208],
   L .rexW 142 (some 3) "MOV Sreg-DS,Ev" .verweigert "keine"
    "no segment-register state in the model; refused by design" 255
    [natByte 72, natByte 142, natByte 216],
   L .rexW 142 (some 4) "MOV Sreg-FS,Ev" .verweigert "keine"
    "no segment-register state in the model; refused by design" 255
    [natByte 72, natByte 142, natByte 224],
   L .rexW 142 (some 5) "MOV Sreg-GS,Ev" .verweigert "keine"
    "no segment-register state in the model; refused by design" 255
    [natByte 72, natByte 142, natByte 232],
   L .rexW 142 (some 6) "MOV sreg-reserved,Ev" .ungueltig64 "keine"
    "Table B-8 sreg3 110 reserved: do not use" 255
    [natByte 72, natByte 142, natByte 240],
   L .rexW 142 (some 7) "MOV sreg-reserved,Ev" .ungueltig64 "keine"
    "Table B-8 sreg3 111 reserved: do not use" 255
    [natByte 72, natByte 142, natByte 248],
   L .rexW 143 (some 0) "POP Ev" .fehlt "keine"
    "common: callee-saved restores and stack cleanup; no family" 255
    [natByte 72, natByte 143, natByte 192],
   L .rexW 143 (some 1) "POP (reserved ext)" .ungueltig64 "keine"
    "Appendix A Group 1A defines only /0 POP; POP lists 8F /0 only" 255
    [natByte 72, natByte 143, natByte 200],
   L .rexW 143 (some 2) "POP (reserved ext)" .ungueltig64 "keine"
    "Appendix A Group 1A defines only /0 POP; POP lists 8F /0 only" 255
    [natByte 72, natByte 143, natByte 208],
   L .rexW 143 (some 3) "POP (reserved ext)" .ungueltig64 "keine"
    "Appendix A Group 1A defines only /0 POP; POP lists 8F /0 only" 255
    [natByte 72, natByte 143, natByte 216],
   L .rexW 143 (some 4) "POP (reserved ext)" .ungueltig64 "keine"
    "Appendix A Group 1A defines only /0 POP; POP lists 8F /0 only" 255
    [natByte 72, natByte 143, natByte 224],
   L .rexW 143 (some 5) "POP (reserved ext)" .ungueltig64 "keine"
    "Appendix A Group 1A defines only /0 POP; POP lists 8F /0 only" 255
    [natByte 72, natByte 143, natByte 232],
   L .rexW 143 (some 6) "POP (reserved ext)" .ungueltig64 "keine"
    "Appendix A Group 1A defines only /0 POP; POP lists 8F /0 only" 255
    [natByte 72, natByte 143, natByte 240],
   L .rexW 143 (some 7) "POP (reserved ext)" .ungueltig64 "keine"
    "Appendix A Group 1A defines only /0 POP; POP lists 8F /0 only" 255
    [natByte 72, natByte 143, natByte 248],
   L .ohne 132 none "TEST Eb,Gb" .fehlt "keine"
    "pervasive: TEST r/m8,r8 (e.g. test-bit idioms); no family" 255
    [natByte 132, natByte 192],
   L .ohne 133 none "TEST Ev,Gv" .fehlt "keine"
    "pervasive: test eax,eax after calls; no family takes bare 85" 255
    [natByte 133, natByte 192],
   L .ohne 134 none "XCHG Eb,Gb" .fehlt "keine"
    "occasional: byte atomic_exchange; no family takes bare 86" 255
    [natByte 134, natByte 192],
   L .ohne 135 none "XCHG Ev,Gv" .fehlt "keine"
    "common: atomic_exchange word forms; no family takes bare 87" 255
    [natByte 135, natByte 192],
   L .ohne 136 none "MOV Eb,Gb" .fehlt "keine"
    "pervasive 8-bit MOV; no family models it" 255
    [natByte 136, natByte 192],
   L .ohne 137 none "MOV Ev,Gv" .fehlt "keine"
    "pervasive 32-bit MOV; no family models it" 255
    [natByte 137, natByte 192],
   L .ohne 138 none "MOV Gb,Eb" .fehlt "keine"
    "pervasive 8-bit loads; no family models them" 255
    [natByte 138, natByte 192],
   L .ohne 139 none "MOV Gv,Ev" .fehlt "keine"
    "pervasive 32-bit loads; no family models them" 255
    [natByte 139, natByte 192],
   L .ohne 141 none "LEA Gv,M" .fehlt "keine"
    "pervasive: every address computation; no family takes bare 8D" 255
    [natByte 141, natByte 1],
   L .ohne 144 none "NOP" .fehlt "keine"
    "pervasive: alignment NOPs; no family models 90" 255
    [natByte 144],
   L .ohne 145 none "XCHG rCX,rAX" .fehlt "keine"
    "rare: register XCHG outside atomics; no family" 255
    [natByte 145],
   L .ohne 146 none "XCHG rDX,rAX" .fehlt "keine"
    "rare: register XCHG outside atomics; no family" 255
    [natByte 146],
   L .ohne 147 none "XCHG rBX,rAX" .fehlt "keine"
    "rare: register XCHG outside atomics; no family" 255
    [natByte 147],
   L .ohne 148 none "XCHG rSP,rAX" .fehlt "keine"
    "rare: register XCHG outside atomics; no family" 255
    [natByte 148],
   L .ohne 149 none "XCHG rBP,rAX" .fehlt "keine"
    "rare: register XCHG outside atomics; no family" 255
    [natByte 149],
   L .ohne 150 none "XCHG rSI,rAX" .fehlt "keine"
    "rare: register XCHG outside atomics; no family" 255
    [natByte 150],
   L .ohne 151 none "XCHG rDI,rAX" .fehlt "keine"
    "rare: register XCHG outside atomics; no family" 255
    [natByte 151],
   L .ohne 153 none "CWD" .modelliert "MulDivWidthHardwareForms"
    "" 0 [natByte 153],
   L .ohne 154 none "CALLF ptr16:32" .ungueltig64 "keine"
    "CALL entry: 9A Invalid in 64-bit mode" 255
    [natByte 154, natByte 0, natByte 0, natByte 0, natByte 0, natByte 0, natByte 0],
   L .ohne 155 none "WAIT/FWAIT" .verweigert "keine"
    "no wait/FPU-bus semantics in the model; refused by design" 255
    [natByte 155],
   L .ohne 156 none "PUSHF" .fehlt "keine"
    "occasional: inline-asm CPUID fences push RFLAGS; no family" 255
    [natByte 156],
   L .ohne 157 none "POPF" .fehlt "keine"
    "occasional: inline-asm CPUID fences pop RFLAGS; no family" 255
    [natByte 157],
   L .ohne 158 none "SAHF" .fehlt "keine"
    "rare; herstellerabhaengig: CPUID LAHF_SAHF_64-gated; no family" 255
    [natByte 158],
   L .ohne 159 none "LAHF" .fehlt "keine"
    "rare; herstellerabhaengig: CPUID LAHF_SAHF_64-gated; no family" 255
    [natByte 159],
   L .rexW 132 none "TEST Eb,Gb" .fehlt "keine"
    "REX.W ignored on byte op; no family models it" 255
    [natByte 72, natByte 132, natByte 192],
   L .rexW 133 none "TEST Ev,Gv" .modelliert "IntegerCore"
    "register-direct TEST only; memory TEST unmodelled" 6
    [natByte 72, natByte 133, natByte 192],
   L .rexW 134 none "XCHG Eb,Gb" .fehlt "keine"
    "REX.W byte XCHG; no family (XchgOrderNeed is 87-only)" 255
    [natByte 72, natByte 134, natByte 192],
   L .rexW 135 none "XCHG Ev,Gv" .zurueckgestellt "XchgOrderNeed"
    "family models it (pin_xchg_reg), chain unwired" 255
    [natByte 72, natByte 135, natByte 192],
   L .rexW 136 none "MOV Eb,Gb" .fehlt "keine"
    "REX.W ignored on byte op; no family models it" 255
    [natByte 72, natByte 136, natByte 192],
   L .rexW 137 none "MOV Ev,Gv" .modelliert "Codec/Ausfuehrung"
    "all ModRM.mod classes covered (reg pilot; disp0/8 kompakt; disp32 pilot)" 0
    [natByte 72, natByte 137, natByte 192],
   L .rexW 138 none "MOV Gb,Eb" .fehlt "keine"
    "REX.W ignored on byte op; no family models it" 255
    [natByte 72, natByte 138, natByte 192],
   L .rexW 139 none "MOV Gv,Ev" .modelliert "CompactForms"
    "memory-deref forms covered (disp0/8 kompakt, disp32 pilot); reg-reg missing" 5
    [natByte 72, natByte 139, natByte 1],
   L .rexW 141 none "LEA Gv,M" .zurueckgestellt "AddressEncoding"
    "family models it (pin_lea), chain unwired" 255
    [natByte 72, natByte 141, natByte 0],
   L .rexW 144 none "NOP" .fehlt "keine"
    "REX.W NOP used as alignment padding; no family models 90" 255
    [natByte 72, natByte 144],
   L .rexW 145 none "XCHG rCX,rAX" .fehlt "keine"
    "rare: 64-bit register XCHG; no family" 255
    [natByte 72, natByte 145],
   L .rexW 146 none "XCHG rDX,rAX" .fehlt "keine"
    "rare: 64-bit register XCHG; no family" 255
    [natByte 72, natByte 146],
   L .rexW 147 none "XCHG rBX,rAX" .fehlt "keine"
    "rare: 64-bit register XCHG; no family" 255
    [natByte 72, natByte 147],
   L .rexW 148 none "XCHG rSP,rAX" .fehlt "keine"
    "rare: 64-bit register XCHG; no family" 255
    [natByte 72, natByte 148],
   L .rexW 149 none "XCHG rBP,rAX" .fehlt "keine"
    "rare: 64-bit register XCHG; no family" 255
    [natByte 72, natByte 149],
   L .rexW 150 none "XCHG rSI,rAX" .fehlt "keine"
    "rare: 64-bit register XCHG; no family" 255
    [natByte 72, natByte 150],
   L .rexW 151 none "XCHG rDI,rAX" .fehlt "keine"
    "rare: 64-bit register XCHG; no family" 255
    [natByte 72, natByte 151],
   L .rexW 153 none "CQO" .modelliert "MulDivWidthHardwareForms"
    "" 0 [natByte 72, natByte 153],
   L .rexW 154 none "CALLF ptr16:32" .ungueltig64 "keine"
    "CALL entry: 9A Invalid in 64-bit mode, REX.W changes nothing" 255
    [natByte 72, natByte 154, natByte 0, natByte 0, natByte 0, natByte 0, natByte 0, natByte 0],
   L .rexW 155 none "WAIT/FWAIT" .verweigert "keine"
    "no wait/FPU-bus semantics in the model; refused by design" 255
    [natByte 72, natByte 155],
   L .rexW 156 none "PUSHFQ" .fehlt "keine"
    "occasional: inline-asm CPUID fences push RFLAGS; no family" 255
    [natByte 72, natByte 156],
   L .rexW 157 none "POPFQ" .fehlt "keine"
    "occasional: inline-asm CPUID fences pop RFLAGS; no family" 255
    [natByte 72, natByte 157],
   L .rexW 158 none "SAHF" .fehlt "keine"
    "rare; herstellerabhaengig: CPUID LAHF_SAHF_64-gated; no family" 255
    [natByte 72, natByte 158],
   L .rexW 159 none "LAHF" .fehlt "keine"
    "rare; herstellerabhaengig: CPUID LAHF_SAHF_64-gated; no family" 255
    [natByte 72, natByte 159],
   L .lock 134 none "LOCK XCHG m8,r8" .fehlt "keine"
    "common: seq-cst byte stores; LOCK family takes no XCHG row (t134Lreg: reg form #UD)" 255
    [natByte 240, natByte 134, natByte 1],
   L .lock 135 none "LOCK XCHG m,r" .fehlt "keine"
    "common: seq-cst stores and atomic_exchange; LOCK family takes no XCHG row (t135Lreg: reg form #UD)" 255
    [natByte 240, natByte 135, natByte 1],
   L .ops16 152 none "CBW" .verweigert "keine"
    "no 16-bit operand width in the model; refused by design" 255
    [natByte 102, natByte 152],
   L .ops16 153 none "CWD-16" .verweigert "keine"
    "no 16-bit operand width in the model; refused by design" 255
    [natByte 102, natByte 153]]

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
theorem t140o0 : kapDecode [natByte 140, natByte 192] = none := by decide
theorem t140o1 : kapDecode [natByte 140, natByte 200] = none := by decide
theorem t140o2 : kapDecode [natByte 140, natByte 208] = none := by decide
theorem t140o3 : kapDecode [natByte 140, natByte 216] = none := by decide
theorem t140o4 : kapDecode [natByte 140, natByte 224] = none := by decide
theorem t140o5 : kapDecode [natByte 140, natByte 232] = none := by decide
theorem t140o6 : kapDecode [natByte 140, natByte 240] = none := by decide
theorem t140o7 : kapDecode [natByte 140, natByte 248] = none := by decide
theorem t142o0 : kapDecode [natByte 142, natByte 192] = none := by decide
theorem t142o1 : kapDecode [natByte 142, natByte 200] = none := by decide
theorem t142o2 : kapDecode [natByte 142, natByte 208] = none := by decide
theorem t142o3 : kapDecode [natByte 142, natByte 216] = none := by decide
theorem t142o4 : kapDecode [natByte 142, natByte 224] = none := by decide
theorem t142o5 : kapDecode [natByte 142, natByte 232] = none := by decide
theorem t142o6 : kapDecode [natByte 142, natByte 240] = none := by decide
theorem t142o7 : kapDecode [natByte 142, natByte 248] = none := by decide
theorem t143o0 : kapDecode [natByte 143, natByte 192] = none := by decide
theorem t143o1 : kapDecode [natByte 143, natByte 200] = none := by decide
theorem t143o2 : kapDecode [natByte 143, natByte 208] = none := by decide
theorem t143o3 : kapDecode [natByte 143, natByte 216] = none := by decide
theorem t143o4 : kapDecode [natByte 143, natByte 224] = none := by decide
theorem t143o5 : kapDecode [natByte 143, natByte 232] = none := by decide
theorem t143o6 : kapDecode [natByte 143, natByte 240] = none := by decide
theorem t143o7 : kapDecode [natByte 143, natByte 248] = none := by decide
theorem t140w0 : kapDecode [natByte 72, natByte 140, natByte 192] = none := by decide
theorem t140w1 : kapDecode [natByte 72, natByte 140, natByte 200] = none := by decide
theorem t140w2 : kapDecode [natByte 72, natByte 140, natByte 208] = none := by decide
theorem t140w3 : kapDecode [natByte 72, natByte 140, natByte 216] = none := by decide
theorem t140w4 : kapDecode [natByte 72, natByte 140, natByte 224] = none := by decide
theorem t140w5 : kapDecode [natByte 72, natByte 140, natByte 232] = none := by decide
theorem t140w6 : kapDecode [natByte 72, natByte 140, natByte 240] = none := by decide
theorem t140w7 : kapDecode [natByte 72, natByte 140, natByte 248] = none := by decide
theorem t142w0 : kapDecode [natByte 72, natByte 142, natByte 192] = none := by decide
theorem t142w1 : kapDecode [natByte 72, natByte 142, natByte 200] = none := by decide
theorem t142w2 : kapDecode [natByte 72, natByte 142, natByte 208] = none := by decide
theorem t142w3 : kapDecode [natByte 72, natByte 142, natByte 216] = none := by decide
theorem t142w4 : kapDecode [natByte 72, natByte 142, natByte 224] = none := by decide
theorem t142w5 : kapDecode [natByte 72, natByte 142, natByte 232] = none := by decide
theorem t142w6 : kapDecode [natByte 72, natByte 142, natByte 240] = none := by decide
theorem t142w7 : kapDecode [natByte 72, natByte 142, natByte 248] = none := by decide
theorem t143w0 : kapDecode [natByte 72, natByte 143, natByte 192] = none := by decide
theorem t143w1 : kapDecode [natByte 72, natByte 143, natByte 200] = none := by decide
theorem t143w2 : kapDecode [natByte 72, natByte 143, natByte 208] = none := by decide
theorem t143w3 : kapDecode [natByte 72, natByte 143, natByte 216] = none := by decide
theorem t143w4 : kapDecode [natByte 72, natByte 143, natByte 224] = none := by decide
theorem t143w5 : kapDecode [natByte 72, natByte 143, natByte 232] = none := by decide
theorem t143w6 : kapDecode [natByte 72, natByte 143, natByte 240] = none := by decide
theorem t143w7 : kapDecode [natByte 72, natByte 143, natByte 248] = none := by decide
theorem t132o : kapDecode [natByte 132, natByte 192] = none := by decide
theorem t133o : kapDecode [natByte 133, natByte 192] = none := by decide
theorem t134o : kapDecode [natByte 134, natByte 192] = none := by decide
theorem t135o : kapDecode [natByte 135, natByte 192] = none := by decide
theorem t136o : kapDecode [natByte 136, natByte 192] = none := by decide
theorem t137o : kapDecode [natByte 137, natByte 192] = none := by decide
theorem t138o : kapDecode [natByte 138, natByte 192] = none := by decide
theorem t139o : kapDecode [natByte 139, natByte 192] = none := by decide
theorem t141o : kapDecode [natByte 141, natByte 1] = none := by decide
theorem t144o : kapDecode [natByte 144] = none := by decide
theorem t145o : kapDecode [natByte 145] = none := by decide
theorem t146o : kapDecode [natByte 146] = none := by decide
theorem t147o : kapDecode [natByte 147] = none := by decide
theorem t148o : kapDecode [natByte 148] = none := by decide
theorem t149o : kapDecode [natByte 149] = none := by decide
theorem t150o : kapDecode [natByte 150] = none := by decide
theorem t151o : kapDecode [natByte 151] = none := by decide
theorem t153o : kapFam [natByte 153] = 0 := by decide
theorem t154o : kapDecode [natByte 154, natByte 0, natByte 0, natByte 0, natByte 0, natByte 0, natByte 0] = none := by decide
theorem t155o : kapDecode [natByte 155] = none := by decide
theorem t156o : kapDecode [natByte 156] = none := by decide
theorem t157o : kapDecode [natByte 157] = none := by decide
theorem t158o : kapDecode [natByte 158] = none := by decide
theorem t159o : kapDecode [natByte 159] = none := by decide
theorem t132w : kapDecode [natByte 72, natByte 132, natByte 192] = none := by decide
theorem t133w : kapFam [natByte 72, natByte 133, natByte 192] = 6 := by decide
theorem t134w : kapDecode [natByte 72, natByte 134, natByte 192] = none := by decide
theorem t135w : kapDecode [natByte 72, natByte 135, natByte 192] = none := by decide
theorem t136w : kapDecode [natByte 72, natByte 136, natByte 192] = none := by decide
theorem t137w : kapFam [natByte 72, natByte 137, natByte 192] = 0 := by decide
theorem t138w : kapDecode [natByte 72, natByte 138, natByte 192] = none := by decide
theorem t139w : kapFam [natByte 72, natByte 139, natByte 1] = 5 := by decide
theorem t141w : kapDecode [natByte 72, natByte 141, natByte 0] = none := by decide
theorem t144w : kapDecode [natByte 72, natByte 144] = none := by decide
theorem t145w : kapDecode [natByte 72, natByte 145] = none := by decide
theorem t146w : kapDecode [natByte 72, natByte 146] = none := by decide
theorem t147w : kapDecode [natByte 72, natByte 147] = none := by decide
theorem t148w : kapDecode [natByte 72, natByte 148] = none := by decide
theorem t149w : kapDecode [natByte 72, natByte 149] = none := by decide
theorem t150w : kapDecode [natByte 72, natByte 150] = none := by decide
theorem t151w : kapDecode [natByte 72, natByte 151] = none := by decide
theorem t153w : kapFam [natByte 72, natByte 153] = 0 := by decide
theorem t154w : kapDecode [natByte 72, natByte 154, natByte 0, natByte 0, natByte 0, natByte 0, natByte 0, natByte 0] = none := by decide
theorem t155w : kapDecode [natByte 72, natByte 155] = none := by decide
theorem t156w : kapDecode [natByte 72, natByte 156] = none := by decide
theorem t157w : kapDecode [natByte 72, natByte 157] = none := by decide
theorem t158w : kapDecode [natByte 72, natByte 158] = none := by decide
theorem t159w : kapDecode [natByte 72, natByte 159] = none := by decide
theorem t134L : kapDecode [natByte 240, natByte 134, natByte 1] = none := by decide
theorem t135L : kapDecode [natByte 240, natByte 135, natByte 1] = none := by decide
theorem t134Lreg : kapDecode [natByte 240, natByte 134, natByte 192] = none := by decide
theorem t135Lreg : kapDecode [natByte 240, natByte 135, natByte 192] = none := by decide
theorem t152s : kapDecode [natByte 102, natByte 152] = none := by decide
theorem t153s : kapDecode [natByte 102, natByte 153] = none := by decide

/-! CUTS (skeleton): rows 98/99 only; 236 keys outstanding. -/
#print axioms t152o
#print axioms t152w
