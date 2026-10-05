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
    "" 0 [natByte 72, natByte 152]]

theorem t152o : kapFam [natByte 152] = 0 := by decide
theorem t152w : kapFam [natByte 72, natByte 152] = 0 := by decide

/-! CUTS (skeleton): rows 98/99 only; 236 keys outstanding. -/
#print axioms t152o
#print axioms t152w
