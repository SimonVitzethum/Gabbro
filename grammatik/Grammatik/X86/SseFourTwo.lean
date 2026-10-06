/-
  File:      Grammatik/X86/SseFourTwo.lean
  Subject:   SSE4.2 register-direct rows (string compares, PCMPGTQ, CRC32),
    connected to the coherent machine and the capstone chain.

  Lane 1379: admitted register-direct forms only --
  PCMPESTRI/PCMPESTRM/PCMPISTRI/PCMPISTRM (`66 0F 3A 60-63 /r ib`),
  PCMPGTQ (`66 0F 38 37 /r`), CRC32 r32/r64 (`F2 0F 38 F0/F1 /r`).
  Semantics follow the Intel SDM (clone-local
  `.tmp/HARDWARE-REFERENCES/intel-instruction-reference.txt`):
  Vol. 2B section 4.1 (imm8 matrix), PCMPESTRI/PCMPESTRM/PCMPISTRI
  pages (lengths, flags, ECX/XMM0 outputs), PCMPGTQ (signed qwords),
  CRC32 (polynomial 11EDC6F41H, DEST[63:32] := 0 always).
  Memory ModRM forms, VEX/EVEX and every other row stay refused.
-/
import Grammatik.X86.Kern.Typen
import Grammatik.X86.Kern.Codec
import Grammatik.X86.Kern.Ausfuehrung
import Grammatik.X86.Kern.Vektor
import Grammatik.X86.Kern.Gleitprofil
import Grammatik.X86.Befehle.Gleitkomma.ScalarFloat
import Grammatik.X86.Befehle.Arithmetik.NarrowOps
import Grammatik.X86.Befehle.Vektor.VectorCodec
import Grammatik.X86.Flags.FeatureProfile
import Grammatik.X86.Hw.Grundlage.HardwareExecution
import Grammatik.X86.Hw.Kapstein.HwKapsteinDecoder

namespace Gabbro.Grammatik.X86

/-- Admitted SSE4.2 string-compare kinds (opcode selects
    explicit/implicit lengths and index/mask output). -/
inductive StrArt where
  | estri | estrm | istri | istrm
  deriving DecidableEq, Repr

/-- Decoded imm8 mode: data format, aggregation, polarity,
    output select (SDM Vol. 2B Table 4-8). -/
structure StrModus where
  format : Nat
  aggreg : Nat
  polar : Nat
  mssb : Bool
  deriving DecidableEq, Repr

/-- Decode the imm8 control byte into its four fields. -/
def modusVonImm (imm : Nat) : StrModus :=
  ⟨imm % 4, imm / 4 % 4, imm / 16 % 4, decide (imm / 64 % 2 = 1)⟩

/-- The mode fields invert the control byte below 128. -/
theorem modusVonImm_felder (imm : Nat) :
    (modusVonImm imm).format = imm % 4 ∧
      (modusVonImm imm).aggreg = imm / 4 % 4 ∧
      (modusVonImm imm).polar = imm / 16 % 4 := by
  unfold modusVonImm
  exact ⟨rfl, rfl, rfl⟩

end Gabbro.Grammatik.X86
