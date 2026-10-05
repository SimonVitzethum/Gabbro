/-
  File:      Grammatik/X86/OpcodeLedger0FC0.lean
  Subject:   Opcode ledger for two-byte opcodes 0F C0-FF plus escapes
             0F 38 / 0F 3A (lane 1347).

  Region ledger, own namespace, self-contained schema (no other ledger
  lane is depended on). Every row carries the opcode byte(s), the
  ModRM.reg extension where the map refines one, the required legacy
  prefix, the mnemonic, the status, the modeling family/file (a string
  naming the existing Lean module) and a one-line reason for every
  non-`modelliert` row.

  Opcode map provenance: Intel SDM combined Vols 1-4, edition
  325462-093US September 2026, local snapshot
  `.tmp/HARDWARE-REFERENCES/intel-instruction-reference.txt`
  (sha256 `a4a62e6...f9168ee5` per `REFERENCES.json`, verified
  2026-10-02), Appendix A Table A-3 (two-byte map), Table A-4
  (three-byte map 0F 38), Group tables 9/10/11. No AMD manual is in
  the clone: vendor differences stay FREE per rule 17, and no AMD
  provenance is claimed.
-/
import Grammatik.X86.Hw.Kapstein.HwKapsteinDecoder
import Grammatik.X86.Befehle.Vektor.VectorCodec
import Grammatik.X86.Hw.Grundlage.ExtendedExecution

namespace Gabbro.Grammatik.X86.Ledger0FC0

/-- Ledger status of one opcode-map row. -/
inductive LStatus where
  | modelliert
  | zurueckgestellt
  | verweigert
  | ungueltig64
  | fehlt
  deriving DecidableEq, Repr

/-- One opcode-map row: second opcode byte `op` (192-255 for
    0F C0-FF, 56/58 for the 0F 38/0F 3A escape groups), the
    ModRM.reg extension `erw` where the map refines one, the
    required legacy prefix `prae`, the display bytes, the mnemonic,
    the status, the modeling family (existing Lean module name) and
    the one-line reason for every non-`modelliert` row. -/
structure LEintrag where
  op : Nat
  erw : Option Nat
  prae : String
  bytes : List Nat
  mnem : String
  status : LStatus
  familie : String
  grund : String
  deriving DecidableEq, Repr

/-- Rows 0F C0-CF: XADD, CMPcc, MOVNTI, PINSRW/PEXTRW, SHUF,
    Group 9 and BSWAP. -/
def ledgerTeilC : List LEintrag :=
  [ { op := 192, erw := none, prae := "-", bytes := [15, 192],
      mnem := "XADD Eb,Gb", status := .fehlt, familie := "-",
      grund := "8-bit XADD: LockedInstructionExecution covers only the 64-bit C1 row." }
  , { op := 192, erw := none, prae := "F0+REX.W", bytes := [240, 72, 15, 192],
      mnem := "LOCK XADD Eb,Gb", status := .fehlt, familie := "-",
      grund := "Valid silicon; the locked family models only r/m64 (C1)." }
  , { op := 193, erw := none, prae := "-", bytes := [15, 193],
      mnem := "XADD Ev,Gv", status := .fehlt, familie := "-",
      grund := "Lock-less XADD is valid but unmodeled; decodeLock needs F0." }
  , { op := 193, erw := none, prae := "F0+REX.W", bytes := [240, 72, 15, 193, 133, 0, 0, 0, 0],
      mnem := "LOCK XADD Ev,Gv", status := .modelliert,
      familie := "LockedInstructionExecution",
      grund := "Checked below (kapKette_lock)." }
  , { op := 193, erw := none, prae := "F0+REX.W-reg", bytes := [240, 72, 15, 193, 192],
      mnem := "LOCK XADD Gv,Gv", status := .modelliert,
      familie := "LockedInstructionExecution",
      grund := "Parses to the lockAufRegister UD marker (pin below)." }
  , { op := 193, erw := none, prae := "F0-noREX", bytes := [240, 15, 193, 133, 0, 0, 0, 0],
      mnem := "LOCK XADD Ev,Gv", status := .verweigert,
      familie := "LockedInstructionExecution",
      grund := "Non-canonical REX: the locked rows require REX.W; proved below." }
  , { op := 194, erw := none, prae := "-", bytes := [15, 194],
      mnem := "CMPPS", status := .fehlt, familie := "-",
      grund := "No family models packed/single/double compares (s32 lacks CMPSS)." }
  , { op := 194, erw := none, prae := "66", bytes := [102, 15, 194],
      mnem := "CMPPD", status := .fehlt, familie := "-",
      grund := "No family models packed double compares." }
  , { op := 194, erw := none, prae := "F3", bytes := [243, 15, 194],
      mnem := "CMPSS", status := .fehlt, familie := "-",
      grund := "Very common in scalar FP code (NaN-aware compare); unmodeled." }
  , { op := 194, erw := none, prae := "F2", bytes := [242, 15, 194],
      mnem := "CMPSD", status := .fehlt, familie := "-",
      grund := "No family models scalar double compares." }
  , { op := 195, erw := none, prae := "-", bytes := [15, 195],
      mnem := "MOVNTI My,Gy", status := .fehlt, familie := "-",
      grund := "Non-temporal store: no family models it." }
  , { op := 196, erw := none, prae := "-", bytes := [15, 196],
      mnem := "PINSRW", status := .fehlt, familie := "-",
      grund := "No family models word insert." }
  , { op := 196, erw := none, prae := "66", bytes := [102, 15, 196],
      mnem := "VPINSRW", status := .fehlt, familie := "-",
      grund := "No family models word insert." }
  , { op := 197, erw := none, prae := "-", bytes := [15, 197],
      mnem := "PEXTRW", status := .fehlt, familie := "-",
      grund := "No family models word extract." }
  , { op := 197, erw := none, prae := "66", bytes := [102, 15, 197],
      mnem := "VPEXTRW", status := .fehlt, familie := "-",
      grund := "No family models word extract." }
  , { op := 198, erw := none, prae := "-", bytes := [15, 198],
      mnem := "SHUFPS", status := .fehlt, familie := "-",
      grund := "Common in FP shuffle code; no family models it." }
  , { op := 198, erw := none, prae := "66", bytes := [102, 15, 198],
      mnem := "SHUFPD", status := .fehlt, familie := "-",
      grund := "No family models packed double shuffle." }
  , { op := 199, erw := some 0, prae := "-", bytes := [15, 199, 192],
      mnem := "Grp9/0 (reserved)", status := .verweigert, familie := "-",
      grund := "Blank in the map: reserved, must not be used; proved below." }
  , { op := 199, erw := some 1, prae := "-", bytes := [15, 199, 200],
      mnem := "CMPXCHG8B/16B", status := .fehlt, familie := "-",
      grund := "decodeLock covers only 0F B1 CMPXCHG; the m64/m128 row is open." }
  , { op := 199, erw := some 2, prae := "-", bytes := [15, 199, 208],
      mnem := "Grp9/2 (reserved)", status := .verweigert, familie := "-",
      grund := "Blank in the map: reserved, must not be used; proved below." }
  , { op := 199, erw := some 3, prae := "-", bytes := [15, 199, 216],
      mnem := "XRSTORS", status := .fehlt, familie := "-",
      grund := "Supervisor XSAVE row; no family models it." }
  , { op := 199, erw := some 4, prae := "-", bytes := [15, 199, 224],
      mnem := "XSAVEC", status := .fehlt, familie := "-",
      grund := "Supervisor XSAVE row; no family models it." }
  , { op := 199, erw := some 5, prae := "-", bytes := [15, 199, 232],
      mnem := "XSAVES", status := .fehlt, familie := "-",
      grund := "Supervisor XSAVE row; no family models it." }
  , { op := 199, erw := some 6, prae := "NP/66/F3", bytes := [15, 199, 240],
      mnem := "VMPTRLD/VMCLEAR/VMXON", status := .fehlt, familie := "-",
      grund := "VMX supervisor rows; no family models them." }
  , { op := 199, erw := some 6, prae := "NFx-mod11", bytes := [15, 199, 248],
      mnem := "RDRAND", status := .zurueckgestellt, familie := "-",
      grund := "Probabilistic silicon (Spec NOT CLAIMED); needs a scope decision first." }
  , { op := 199, erw := some 6, prae := "F3-mod11", bytes := [243, 15, 199, 248],
      mnem := "SENDUIPI", status := .fehlt, familie := "-",
      grund := "UINTR supervisor row; no family models it." }
  , { op := 199, erw := some 7, prae := "NP-mem", bytes := [15, 199, 184],
      mnem := "VMPTRST", status := .fehlt, familie := "-",
      grund := "VMX supervisor row; no family models it." }
  , { op := 199, erw := some 7, prae := "NFx-mod11", bytes := [15, 199, 252],
      mnem := "RDSEED", status := .zurueckgestellt, familie := "-",
      grund := "Probabilistic silicon (Spec NOT CLAIMED); needs a scope decision first." }
  , { op := 199, erw := some 7, prae := "F3-mod11", bytes := [243, 15, 199, 252],
      mnem := "RDPID", status := .fehlt, familie := "-",
      grund := "TSC_AUX read; no family models it." }
  , { op := 200, erw := none, prae := "-", bytes := [15, 200],
      mnem := "BSWAP EAX", status := .fehlt, familie := "-",
      grund := "ByteSwap.lean has only value helpers; no decoder covers BSWAP." }
  , { op := 201, erw := none, prae := "-", bytes := [15, 201],
      mnem := "BSWAP ECX", status := .fehlt, familie := "-",
      grund := "ByteSwap.lean has only value helpers; no decoder covers BSWAP." }
  , { op := 202, erw := none, prae := "-", bytes := [15, 202],
      mnem := "BSWAP EDX", status := .fehlt, familie := "-",
      grund := "ByteSwap.lean has only value helpers; no decoder covers BSWAP." }
  , { op := 203, erw := none, prae := "-", bytes := [15, 203],
      mnem := "BSWAP EBX", status := .fehlt, familie := "-",
      grund := "ByteSwap.lean has only value helpers; no decoder covers BSWAP." }
  , { op := 204, erw := none, prae := "-", bytes := [15, 204],
      mnem := "BSWAP ESP", status := .fehlt, familie := "-",
      grund := "ByteSwap.lean has only value helpers; no decoder covers BSWAP." }
  , { op := 205, erw := none, prae := "-", bytes := [15, 205],
      mnem := "BSWAP EBP", status := .fehlt, familie := "-",
      grund := "ByteSwap.lean has only value helpers; no decoder covers BSWAP." }
  , { op := 206, erw := none, prae := "-", bytes := [15, 206],
      mnem := "BSWAP ESI", status := .fehlt, familie := "-",
      grund := "ByteSwap.lean has only value helpers; no decoder covers BSWAP." }
  , { op := 207, erw := none, prae := "-", bytes := [15, 207],
      mnem := "BSWAP EDI", status := .fehlt, familie := "-",
      grund := "ByteSwap.lean has only value helpers; no decoder covers BSWAP." } ]

/-- Rows 0F D0-DF: shifts, PADDQ, PMULLW, MOVQ forms, PMOVMSKB
    and the unsigned-saturation ALU rows. -/
def ledgerTeilD : List LEintrag :=
  [ { op := 208, erw := none, prae := "-", bytes := [15, 208],
      mnem := "(reserved)", status := .verweigert, familie := "-",
      grund := "Blank in the map (no-prefix D0 is reserved); proved below." }
  , { op := 208, erw := none, prae := "66", bytes := [102, 15, 208],
      mnem := "ADDSUBPD", status := .fehlt, familie := "-",
      grund := "No family models add/sub packed double." }
  , { op := 208, erw := none, prae := "F2", bytes := [242, 15, 208],
      mnem := "ADDSUBPS", status := .fehlt, familie := "-",
      grund := "No family models add/sub packed single." }
  , { op := 209, erw := none, prae := "-", bytes := [15, 209],
      mnem := "PSRLW", status := .fehlt, familie := "-",
      grund := "No family models packed word shift right." }
  , { op := 209, erw := none, prae := "66", bytes := [102, 15, 209],
      mnem := "VPSRLW", status := .fehlt, familie := "-",
      grund := "No family models packed word shift right." }
  , { op := 210, erw := none, prae := "-", bytes := [15, 210],
      mnem := "PSRLD", status := .fehlt, familie := "-",
      grund := "No family models packed dword shift right." }
  , { op := 210, erw := none, prae := "66", bytes := [102, 15, 210],
      mnem := "VPSRLD", status := .fehlt, familie := "-",
      grund := "No family models packed dword shift right." }
  , { op := 211, erw := none, prae := "-", bytes := [15, 211],
      mnem := "PSRLQ", status := .fehlt, familie := "-",
      grund := "No family models packed qword shift right." }
  , { op := 211, erw := none, prae := "66", bytes := [102, 15, 211],
      mnem := "VPSRLQ", status := .fehlt, familie := "-",
      grund := "No family models packed qword shift right." }
  , { op := 212, erw := none, prae := "-", bytes := [15, 212],
      mnem := "PADDQ", status := .fehlt, familie := "-",
      grund := "MMX PADDQ (no prefix): the 66 row is modeled, this one is not." }
  , { op := 212, erw := none, prae := "66", bytes := [102, 15, 212],
      mnem := "VPADDQ", status := .modelliert, familie := "VectorCodec",
      grund := "Checked below (decodeVector roundtrip)." }
  , { op := 213, erw := none, prae := "-", bytes := [15, 213],
      mnem := "PMULLW", status := .fehlt, familie := "-",
      grund := "No family models packed word multiply-low." }
  , { op := 213, erw := none, prae := "66", bytes := [102, 15, 213],
      mnem := "VPMULLW", status := .fehlt, familie := "-",
      grund := "No family models packed word multiply-low." }
  , { op := 214, erw := none, prae := "-", bytes := [15, 214],
      mnem := "(reserved)", status := .verweigert, familie := "-",
      grund := "Blank in the map (no-prefix D6 is reserved); proved below." }
  , { op := 214, erw := none, prae := "66", bytes := [102, 15, 214],
      mnem := "MOVQ", status := .fehlt, familie := "-",
      grund := "No family models the 64-bit qword move." }
  , { op := 214, erw := none, prae := "F3", bytes := [243, 15, 214],
      mnem := "MOVQ2DQ", status := .fehlt, familie := "-",
      grund := "No family models the MMX-to-XMM move." }
  , { op := 214, erw := none, prae := "F2", bytes := [242, 15, 214],
      mnem := "MOVDQ2Q", status := .fehlt, familie := "-",
      grund := "No family models the XMM-to-MMX move." }
  , { op := 215, erw := none, prae := "-", bytes := [15, 215],
      mnem := "PMOVMSKB", status := .fehlt, familie := "-",
      grund := "Common in string/table code; no family models it." }
  , { op := 215, erw := none, prae := "66", bytes := [102, 15, 215],
      mnem := "VPMOVMSKB", status := .fehlt, familie := "-",
      grund := "Common in string/table code; no family models it." }
  , { op := 216, erw := none, prae := "-", bytes := [15, 216],
      mnem := "PSUBUSB", status := .fehlt, familie := "-",
      grund := "No family models saturating byte subtract." }
  , { op := 216, erw := none, prae := "66", bytes := [102, 15, 216],
      mnem := "VPSUBUSB", status := .fehlt, familie := "-",
      grund := "No family models saturating byte subtract." }
  , { op := 217, erw := none, prae := "-", bytes := [15, 217],
      mnem := "PSUBUSW", status := .fehlt, familie := "-",
      grund := "No family models saturating word subtract." }
  , { op := 217, erw := none, prae := "66", bytes := [102, 15, 217],
      mnem := "VPSUBUSW", status := .fehlt, familie := "-",
      grund := "No family models saturating word subtract." }
  , { op := 218, erw := none, prae := "-", bytes := [15, 218],
      mnem := "PMINUB", status := .fehlt, familie := "-",
      grund := "No family models packed byte minimum." }
  , { op := 218, erw := none, prae := "66", bytes := [102, 15, 218],
      mnem := "VPMINUB", status := .fehlt, familie := "-",
      grund := "No family models packed byte minimum." }
  , { op := 219, erw := none, prae := "-", bytes := [15, 219],
      mnem := "PAND", status := .fehlt, familie := "-",
      grund := "No family models packed AND (only the 66 PXOR/PADDQ rows exist)." }
  , { op := 219, erw := none, prae := "66", bytes := [102, 15, 219],
      mnem := "VPAND", status := .fehlt, familie := "-",
      grund := "No family models packed AND." }
  , { op := 220, erw := none, prae := "-", bytes := [15, 220],
      mnem := "PADDUSB", status := .fehlt, familie := "-",
      grund := "No family models saturating byte add." }
  , { op := 220, erw := none, prae := "66", bytes := [102, 15, 220],
      mnem := "VPADDUSB", status := .fehlt, familie := "-",
      grund := "No family models saturating byte add." }
  , { op := 221, erw := none, prae := "-", bytes := [15, 221],
      mnem := "PADDUSW", status := .fehlt, familie := "-",
      grund := "No family models saturating word add." }
  , { op := 221, erw := none, prae := "66", bytes := [102, 15, 221],
      mnem := "VPADDUSW", status := .fehlt, familie := "-",
      grund := "No family models saturating word add." }
  , { op := 222, erw := none, prae := "-", bytes := [15, 222],
      mnem := "PMAXUB", status := .fehlt, familie := "-",
      grund := "No family models packed byte maximum." }
  , { op := 222, erw := none, prae := "66", bytes := [102, 15, 222],
      mnem := "VPMAXUB", status := .fehlt, familie := "-",
      grund := "No family models packed byte maximum." }
  , { op := 223, erw := none, prae := "-", bytes := [15, 223],
      mnem := "PANDN", status := .fehlt, familie := "-",
      grund := "No family models packed AND-NOT." }
  , { op := 223, erw := none, prae := "66", bytes := [102, 15, 223],
      mnem := "VPANDN", status := .fehlt, familie := "-",
      grund := "No family models packed AND-NOT." } ]

/-- Rows 0F E0-EF: averages, shifts, multiplies, converts,
    MOVNTQ and the signed-saturation ALU rows plus PXOR. -/
def ledgerTeilE : List LEintrag :=
  [ { op := 224, erw := none, prae := "-", bytes := [15, 224],
      mnem := "PAVGB", status := .fehlt, familie := "-",
      grund := "No family models packed byte average." }
  , { op := 224, erw := none, prae := "66", bytes := [102, 15, 224],
      mnem := "VPAVGB", status := .fehlt, familie := "-",
      grund := "No family models packed byte average." }
  , { op := 225, erw := none, prae := "-", bytes := [15, 225],
      mnem := "PSRAW", status := .fehlt, familie := "-",
      grund := "No family models packed word shift arithmetic right." }
  , { op := 225, erw := none, prae := "66", bytes := [102, 15, 225],
      mnem := "VPSRAW", status := .fehlt, familie := "-",
      grund := "No family models packed word shift arithmetic right." }
  , { op := 226, erw := none, prae := "-", bytes := [15, 226],
      mnem := "PSRAD", status := .fehlt, familie := "-",
      grund := "No family models packed dword shift arithmetic right." }
  , { op := 226, erw := none, prae := "66", bytes := [102, 15, 226],
      mnem := "VPSRAD", status := .fehlt, familie := "-",
      grund := "No family models packed dword shift arithmetic right." }
  , { op := 227, erw := none, prae := "-", bytes := [15, 227],
      mnem := "PAVGW", status := .fehlt, familie := "-",
      grund := "No family models packed word average." }
  , { op := 227, erw := none, prae := "66", bytes := [102, 15, 227],
      mnem := "VPAVGW", status := .fehlt, familie := "-",
      grund := "No family models packed word average." }
  , { op := 228, erw := none, prae := "-", bytes := [15, 228],
      mnem := "PMULHUW", status := .fehlt, familie := "-",
      grund := "No family models packed unsigned multiply-high." }
  , { op := 228, erw := none, prae := "66", bytes := [102, 15, 228],
      mnem := "VPMULHUW", status := .fehlt, familie := "-",
      grund := "No family models packed unsigned multiply-high." }
  , { op := 229, erw := none, prae := "-", bytes := [15, 229],
      mnem := "PMULHW", status := .fehlt, familie := "-",
      grund := "No family models packed signed multiply-high." }
  , { op := 229, erw := none, prae := "66", bytes := [102, 15, 229],
      mnem := "VPMULHW", status := .fehlt, familie := "-",
      grund := "No family models packed signed multiply-high." }
  , { op := 230, erw := none, prae := "-", bytes := [15, 230],
      mnem := "(reserved)", status := .verweigert, familie := "-",
      grund := "Blank in the map (no-prefix E6 is reserved); proved below." }
  , { op := 230, erw := none, prae := "66", bytes := [102, 15, 230],
      mnem := "VCVTTPD2DQ", status := .fehlt, familie := "-",
      grund := "No family models packed double-to-dword convert." }
  , { op := 230, erw := none, prae := "F3", bytes := [243, 15, 230],
      mnem := "VCVTDQ2PD", status := .fehlt, familie := "-",
      grund := "No family models packed dword-to-double convert." }
  , { op := 230, erw := none, prae := "F2", bytes := [242, 15, 230],
      mnem := "VCVTPD2DQ", status := .fehlt, familie := "-",
      grund := "No family models packed double-to-dword convert." }
  , { op := 231, erw := none, prae := "-", bytes := [15, 231],
      mnem := "MOVNTQ", status := .fehlt, familie := "-",
      grund := "Non-temporal qword store: no family models it." }
  , { op := 231, erw := none, prae := "66", bytes := [102, 15, 231],
      mnem := "VMOVNTDQ", status := .fehlt, familie := "-",
      grund := "Non-temporal store: no family models it." }
  , { op := 232, erw := none, prae := "-", bytes := [15, 232],
      mnem := "PSUBSB", status := .fehlt, familie := "-",
      grund := "No family models saturating signed byte subtract." }
  , { op := 232, erw := none, prae := "66", bytes := [102, 15, 232],
      mnem := "VPSUBSB", status := .fehlt, familie := "-",
      grund := "No family models saturating signed byte subtract." }
  , { op := 233, erw := none, prae := "-", bytes := [15, 233],
      mnem := "PSUBSW", status := .fehlt, familie := "-",
      grund := "No family models saturating signed word subtract." }
  , { op := 233, erw := none, prae := "66", bytes := [102, 15, 233],
      mnem := "VPSUBSW", status := .fehlt, familie := "-",
      grund := "No family models saturating signed word subtract." }
  , { op := 234, erw := none, prae := "-", bytes := [15, 234],
      mnem := "PMINSW", status := .fehlt, familie := "-",
      grund := "No family models packed signed word minimum." }
  , { op := 234, erw := none, prae := "66", bytes := [102, 15, 234],
      mnem := "VPMINSW", status := .fehlt, familie := "-",
      grund := "No family models packed signed word minimum." }
  , { op := 235, erw := none, prae := "-", bytes := [15, 235],
      mnem := "POR", status := .fehlt, familie := "-",
      grund := "No family models packed OR (only the 66 PXOR/PADDQ rows exist)." }
  , { op := 235, erw := none, prae := "66", bytes := [102, 15, 235],
      mnem := "VPOR", status := .fehlt, familie := "-",
      grund := "No family models packed OR." }
  , { op := 236, erw := none, prae := "-", bytes := [15, 236],
      mnem := "PADDSB", status := .fehlt, familie := "-",
      grund := "No family models saturating signed byte add." }
  , { op := 236, erw := none, prae := "66", bytes := [102, 15, 236],
      mnem := "VPADDSB", status := .fehlt, familie := "-",
      grund := "No family models saturating signed byte add." }
  , { op := 237, erw := none, prae := "-", bytes := [15, 237],
      mnem := "PADDSW", status := .fehlt, familie := "-",
      grund := "No family models saturating signed word add." }
  , { op := 237, erw := none, prae := "66", bytes := [102, 15, 237],
      mnem := "VPADDSW", status := .fehlt, familie := "-",
      grund := "No family models saturating signed word add." }
  , { op := 238, erw := none, prae := "-", bytes := [15, 238],
      mnem := "PMAXSW", status := .fehlt, familie := "-",
      grund := "No family models packed signed word maximum." }
  , { op := 238, erw := none, prae := "66", bytes := [102, 15, 238],
      mnem := "VPMAXSW", status := .fehlt, familie := "-",
      grund := "No family models packed signed word maximum." }
  , { op := 239, erw := none, prae := "-", bytes := [15, 239],
      mnem := "PXOR", status := .fehlt, familie := "-",
      grund := "MMX PXOR (no prefix): the 66 row is modeled, this one is not." }
  , { op := 239, erw := none, prae := "66", bytes := [102, 15, 239],
      mnem := "VPXOR", status := .modelliert, familie := "VectorCodec",
      grund := "Checked below (kapDecode chain)." } ]

/-- Rows 0F F0-FF: LDDQU, left shifts, multiply-add, mask move,
    the wraparound ALU rows, UD0, plus the 0F 38 / 0F 3A groups. -/
def ledgerTeilF : List LEintrag :=
  [ { op := 240, erw := none, prae := "-", bytes := [15, 240],
      mnem := "(reserved)", status := .verweigert, familie := "-",
      grund := "Blank in the map (MOVBE lives at 0F 38 F0); proved below." }
  , { op := 240, erw := none, prae := "F2", bytes := [242, 15, 240],
      mnem := "LDDQU", status := .fehlt, familie := "-",
      grund := "No family models the unaligned load." }
  , { op := 241, erw := none, prae := "-", bytes := [15, 241],
      mnem := "PSLLW", status := .fehlt, familie := "-",
      grund := "No family models packed word shift left." }
  , { op := 241, erw := none, prae := "66", bytes := [102, 15, 241],
      mnem := "VPSLLW", status := .fehlt, familie := "-",
      grund := "No family models packed word shift left." }
  , { op := 242, erw := none, prae := "-", bytes := [15, 242],
      mnem := "PSLLD", status := .fehlt, familie := "-",
      grund := "No family models packed dword shift left." }
  , { op := 242, erw := none, prae := "66", bytes := [102, 15, 242],
      mnem := "VPSLLD", status := .fehlt, familie := "-",
      grund := "No family models packed dword shift left." }
  , { op := 243, erw := none, prae := "-", bytes := [15, 243],
      mnem := "PSLLQ", status := .fehlt, familie := "-",
      grund := "No family models packed qword shift left." }
  , { op := 243, erw := none, prae := "66", bytes := [102, 15, 243],
      mnem := "VPSLLQ", status := .fehlt, familie := "-",
      grund := "No family models packed qword shift left." }
  , { op := 244, erw := none, prae := "-", bytes := [15, 244],
      mnem := "PMULUDQ", status := .fehlt, familie := "-",
      grund := "No family models packed unsigned dword multiply." }
  , { op := 244, erw := none, prae := "66", bytes := [102, 15, 244],
      mnem := "VPMULUDQ", status := .fehlt, familie := "-",
      grund := "No family models packed unsigned dword multiply." }
  , { op := 245, erw := none, prae := "-", bytes := [15, 245],
      mnem := "PMADDWD", status := .fehlt, familie := "-",
      grund := "No family models packed multiply-add." }
  , { op := 245, erw := none, prae := "66", bytes := [102, 15, 245],
      mnem := "VPMADDWD", status := .fehlt, familie := "-",
      grund := "No family models packed multiply-add." }
  , { op := 246, erw := none, prae := "-", bytes := [15, 246],
      mnem := "PSADBW", status := .fehlt, familie := "-",
      grund := "No family models packed sum of absolute differences." }
  , { op := 246, erw := none, prae := "66", bytes := [102, 15, 246],
      mnem := "VPSADBW", status := .fehlt, familie := "-",
      grund := "No family models packed sum of absolute differences." }
  , { op := 247, erw := none, prae := "-", bytes := [15, 247],
      mnem := "MASKMOVQ", status := .fehlt, familie := "-",
      grund := "No family models the masked store." }
  , { op := 247, erw := none, prae := "66", bytes := [102, 15, 247],
      mnem := "VMASKMOVDQU", status := .fehlt, familie := "-",
      grund := "No family models the masked store." }
  , { op := 248, erw := none, prae := "-", bytes := [15, 248],
      mnem := "PSUBB", status := .fehlt, familie := "-",
      grund := "Very common in vectorized loops; no family models it." }
  , { op := 248, erw := none, prae := "66", bytes := [102, 15, 248],
      mnem := "VPSUBB", status := .fehlt, familie := "-",
      grund := "Very common in vectorized loops; no family models it." }
  , { op := 249, erw := none, prae := "-", bytes := [15, 249],
      mnem := "PSUBW", status := .fehlt, familie := "-",
      grund := "Very common in vectorized loops; no family models it." }
  , { op := 249, erw := none, prae := "66", bytes := [102, 15, 249],
      mnem := "VPSUBW", status := .fehlt, familie := "-",
      grund := "Very common in vectorized loops; no family models it." }
  , { op := 250, erw := none, prae := "-", bytes := [15, 250],
      mnem := "PSUBD", status := .fehlt, familie := "-",
      grund := "Very common in vectorized loops; no family models it." }
  , { op := 250, erw := none, prae := "66", bytes := [102, 15, 250],
      mnem := "VPSUBD", status := .fehlt, familie := "-",
      grund := "Very common in vectorized loops; no family models it." }
  , { op := 251, erw := none, prae := "-", bytes := [15, 251],
      mnem := "PSUBQ", status := .fehlt, familie := "-",
      grund := "No family models packed qword subtract." }
  , { op := 251, erw := none, prae := "66", bytes := [102, 15, 251],
      mnem := "VPSUBQ", status := .fehlt, familie := "-",
      grund := "No family models packed qword subtract." }
  , { op := 252, erw := none, prae := "-", bytes := [15, 252],
      mnem := "PADDB", status := .fehlt, familie := "-",
      grund := "Very common in vectorized loops; no family models it." }
  , { op := 252, erw := none, prae := "66", bytes := [102, 15, 252],
      mnem := "VPADDB", status := .fehlt, familie := "-",
      grund := "Very common in vectorized loops; no family models it." }
  , { op := 253, erw := none, prae := "-", bytes := [15, 253],
      mnem := "PADDW", status := .fehlt, familie := "-",
      grund := "Very common in vectorized loops; no family models it." }
  , { op := 253, erw := none, prae := "66", bytes := [102, 15, 253],
      mnem := "VPADDW", status := .fehlt, familie := "-",
      grund := "Very common in vectorized loops; no family models it." }
  , { op := 254, erw := none, prae := "-", bytes := [15, 254],
      mnem := "PADDD", status := .fehlt, familie := "-",
      grund := "Very common in vectorized loops; no family models it." }
  , { op := 254, erw := none, prae := "66", bytes := [102, 15, 254],
      mnem := "VPADDD", status := .fehlt, familie := "-",
      grund := "Very common in vectorized loops; no family models it." }
  , { op := 255, erw := none, prae := "-", bytes := [15, 255],
      mnem := "UD0", status := .verweigert, familie := "-",
      grund := "Guaranteed-invalid (UD0); the chain refuses it, proved below." }
  , { op := 56, erw := none, prae := "66-mostly", bytes := [15, 56],
      mnem := "0F 38 escape", status := .fehlt, familie := "-",
      grund := "SSSE3/SSE4/AES space (PHADD, MOVBE F0/F1, AESENC...); no family decodes it." }
  , { op := 58, erw := none, prae := "66/imm8", bytes := [15, 58],
      mnem := "0F 3A escape", status := .fehlt, familie := "-",
      grund := "SSE4/AES space (PALIGNR, PCLMULQDQ 0F 3A 44...); no family decodes it." } ]

/-- The ledger rows (filled in pieces below). -/
def ledger0FC0 : List LEintrag :=
  ledgerTeilC ++ ledgerTeilD ++ ledgerTeilE ++ ledgerTeilF

/-! ## 1. Coverage: every byte 0F C0-FF occurs, both escapes
    occur, no key occurs twice. -/

/-- Ledger key: opcode byte, extension, required prefix. -/
def ledgerSchluessel (e : LEintrag) : Nat × Option Nat × String :=
  (e.op, e.erw, e.prae)

/-- Status predicates (plain matches, no `BEq` on strings needed). -/
def istModelliert (e : LEintrag) : Bool :=
  match e.status with | .modelliert => true | _ => false

def istZurueckgestellt (e : LEintrag) : Bool :=
  match e.status with | .zurueckgestellt => true | _ => false

def istVerweigert (e : LEintrag) : Bool :=
  match e.status with | .verweigert => true | _ => false

def istUngueltig64 (e : LEintrag) : Bool :=
  match e.status with | .ungueltig64 => true | _ => false

def istFehlt (e : LEintrag) : Bool :=
  match e.status with | .fehlt => true | _ => false

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- No opcode/prefix/extension key is listed twice. -/
theorem ledger_nodup :
    (ledger0FC0.map ledgerSchluessel).Nodup = true := by
  decide

/-- Every second byte C0-FF occurs in at least one row. -/
theorem ledger_c0ff_vollstaendig :
    ((List.range 64).map (· + 192)).all
      (fun n => ledger0FC0.any (fun e => e.op == n)) = true := by
  decide

/-- Both three-byte escapes occur as group rows. -/
theorem ledger_escapes_vorhanden :
    (ledger0FC0.any (fun e => e.op == 56) &&
      ledger0FC0.any (fun e => e.op == 58)) = true := by
  decide

/-- Status counts (139 rows: 4 modelled, 8 refused, 2 deferred,
    0 invalid-in-64-bit, 125 missing). -/
theorem ledger_anz_modelliert :
    (ledger0FC0.filter istModelliert).length = 4 := by
  decide

theorem ledger_anz_verweigert :
    (ledger0FC0.filter istVerweigert).length = 8 := by
  decide

theorem ledger_anz_zurueckgestellt :
    (ledger0FC0.filter istZurueckgestellt).length = 2 := by
  decide

theorem ledger_anz_ungueltig64 :
    (ledger0FC0.filter istUngueltig64).length = 0 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem ledger_anz_fehlt :
    (ledger0FC0.filter istFehlt).length = 125 := by
  decide

/-! ## 2. Checked part: the four `modelliert` rows decode. -/

/-- 0F C1 LOCK+REX.W XADD: the chain takes the accepted LOCK
    witness in the LOCK arm (reuses `kapKette_lock`). -/
theorem ledger0FC1_kette :
    kapDecode kapW_lock =
      some (KapDekodiert.lock
        (LockAnweisung.ok (.xadd64 .rax .rbp 0) 9), []) :=
  kapKette_lock

/-- 0F C1 LOCK with a register destination: the family decoder
    parses the architectural UD marker (reuses the accepted pin). -/
theorem ledger0FC1_regUd :
    decodeLock pinRegUd =
      some (LockAnweisung.ud .lockAufRegister 5, []) :=
  pin_lock_reg_ud_decodiert

/-- 0F D4 with a 66 prefix: the family decoder takes PADDQ
    (accepted round trip, empty suffix). -/
theorem ledger0FD4_vec :
    decodeVector (encodeVector (.paddqRR .xmm0 .xmm1)) =
      some ((⟨.paddqRR .xmm0 .xmm1, 5⟩ : VectorDec), []) := by
  have h := roundtrip_paddq .xmm0 .xmm1 []
  simpa using h

/-- 0F EF with a 66 prefix: the chain takes PXOR in the width arm
    (accepted `decodeExt` pin lifted through the dispatcher). -/
theorem ledger0FEF_kette :
    kapDecode (encodeVector (.pxorRR .xmm0 .xmm1)) =
      some (KapDekodiert.breit
        (.ext (.vec (⟨.pxorRR .xmm0 .xmm1, 5⟩ : VectorDec))), []) :=
  kapDecode_breit _ _ _ (decodeMulDivWidth_prefers_ext _ _ _ pin_ext_vec_pxor)

/-! ## 3. Checked part: the eight `verweigert` rows refuse. -/

/-- Group 9 /0 is reserved: the chain refuses it. -/
theorem ledger_weist_c7r0_zurueck :
    kapDecode [natByte 15, natByte 199, natByte 192] = none := by
  decide

/-- Group 9 /2 is reserved: the chain refuses it. -/
theorem ledger_weist_c7r2_zurueck :
    kapDecode [natByte 15, natByte 199, natByte 208] = none := by
  decide

/-- Bare 0F D0 is reserved: the chain refuses it. -/
theorem ledger_weist_d0_zurueck :
    kapDecode [natByte 15, natByte 208] = none := by
  decide

/-- Bare 0F D6 is reserved: the chain refuses it. -/
theorem ledger_weist_d6_zurueck :
    kapDecode [natByte 15, natByte 214] = none := by
  decide

/-- Bare 0F E6 is reserved: the chain refuses it. -/
theorem ledger_weist_e6_zurueck :
    kapDecode [natByte 15, natByte 230] = none := by
  decide

/-- Bare 0F F0 is reserved (MOVBE lives at 0F 38 F0):
    the chain refuses it. -/
theorem ledger_weist_f0_zurueck :
    kapDecode [natByte 15, natByte 240] = none := by
  decide

/-- 0F FF is UD0 (guaranteed-invalid): the chain refuses it. -/
theorem ledger_weist_ff_zurueck :
    kapDecode [natByte 15, natByte 255] = none := by
  decide

/-- LOCK XADD without REX.W is non-canonical: the chain refuses it
    (the locked rows require REX.W). -/
theorem ledger_weist_c1ohneRex_zurueck :
    kapDecode [natByte 240, natByte 15, natByte 193, natByte 133,
      natByte 0, natByte 0, natByte 0, natByte 0] = none := by
  decide

#print axioms ledger_nodup
#print axioms ledger_c0ff_vollstaendig
#print axioms ledger_escapes_vorhanden
#print axioms ledger_anz_modelliert
#print axioms ledger_anz_verweigert
#print axioms ledger_anz_zurueckgestellt
#print axioms ledger_anz_ungueltig64
#print axioms ledger_anz_fehlt
#print axioms ledger0FC1_kette
#print axioms ledger0FC1_regUd
#print axioms ledger0FD4_vec
#print axioms ledger0FEF_kette
#print axioms ledger_weist_c7r0_zurueck
#print axioms ledger_weist_c7r2_zurueck
#print axioms ledger_weist_d0_zurueck
#print axioms ledger_weist_d6_zurueck
#print axioms ledger_weist_e6_zurueck
#print axioms ledger_weist_f0_zurueck
#print axioms ledger_weist_ff_zurueck
#print axioms ledger_weist_c1ohneRex_zurueck

/-
CUTS:
- The opcode map transcription is a NAMED assumption: any
  mistranscribed row is the lane author's error, not checked
  provenance (the snapshot is not machine-read by any guardian).
- Vendor differences (Intel vs AMD) stay FREE; no AMD manual exists
  in the clone, so no AMD provenance is claimed anywhere here.
- VEX/EVEX forms of the listed SIMD rows belong to the AVX piece,
  supervisor/system forms (VMX, XSAVE, RDPID, SENDUIPI) to their own
  pieces; both are named in row reasons, never modeled here.
- RDRAND/RDSEED are `zurueckgestellt`: probabilistic silicon needs a
  scope decision (Spec NOT CLAIMED) before any model row is written.
- No `_zeuge` companion is owed: no theorem here has a premise
  quantifying over program syntax, and the task names no ZEUGE target.
  The ledger rows themselves are data, and every decoder claim links
  an accepted pin or round trip, never a fresh syntax obligation.
- The 125 `fehlt` rows are findings, not gaps in this file: each is
  listed with the nearest module (or none) in its reason.
-/
