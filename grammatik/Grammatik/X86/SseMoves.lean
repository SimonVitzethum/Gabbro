/-
  File:      Grammatik/X86/SseMoves.lean
  Subject:   SSE/SSE2 moves, loads, stores and unpack connected to the
             coherent machine.

  Lane 1355: covers the ledger-1341 `fehlt` rows 0F 10/11/28/29
  (MOVUPS/MOVUPD/MOVAPS/MOVAPD), the MOVSS/MOVSD stores (loads already
  decode), MOVLPS/MOVHPS/MOVLHPS/MOVHLPS (0F 12/13/16/17), UNPCKL/UNPCKH
  PS/PD (0F 14/15) and the non-temporal stores (0F 2B/C3, 66 0F 2B/E7).
  MOVDQA/MOVDQU stay with lane 686 (`VectorIntegerHardwareForms`,
  never redefined here). Decoder plus encoder with round trip, pure
  XMM semantics reusing the accepted `Vektor` functions, a
  `HwAdapter` plug over the coherent machine in the style of
  `HwMulDivWidth`, and a reached two-core witness. No hardware
  correspondence beyond self-consistency (see CUTS).
-/
import Grammatik.X86.Kern.Typen
import Grammatik.X86.Kern.Codec
import Grammatik.X86.Kern.Vektor
import Grammatik.X86.Speicher.Speicher
import Grammatik.X86.TSO.Kern.TSO
import Grammatik.X86.Befehle.Gleitkomma.ScalarFloat
import Grammatik.X86.Hw.Grundlage.HardwareExecution

namespace Gabbro.Grammatik.X86

/-- SSE/SSE2 move and unpack rows of this lane. Register operands are
    XMM; memory operands reuse base-plus-displacement addressing over
    the GPR file. MOVDQA/MOVDQU are NOT here (lane 686 owns them). -/
inductive SseMoveOp where
  | movupsLd (dst : XmmReg) (base : Register) (disp : BitVec 32)
  | movupsSt (base : Register) (src : XmmReg) (disp : BitVec 32)
  | movapsLd (dst : XmmReg) (base : Register) (disp : BitVec 32)
  | movapsSt (base : Register) (src : XmmReg) (disp : BitVec 32)
  | movupdLd (dst : XmmReg) (base : Register) (disp : BitVec 32)
  | movupdSt (base : Register) (src : XmmReg) (disp : BitVec 32)
  | movapdLd (dst : XmmReg) (base : Register) (disp : BitVec 32)
  | movapdSt (base : Register) (src : XmmReg) (disp : BitVec 32)
  | movssSt (base : Register) (src : XmmReg) (disp : BitVec 32)
  | movsdSt (base : Register) (src : XmmReg) (disp : BitVec 32)
  | movlpsLd (dst : XmmReg) (base : Register) (disp : BitVec 32)
  | movlpsSt (base : Register) (src : XmmReg) (disp : BitVec 32)
  | movhpsLd (dst : XmmReg) (base : Register) (disp : BitVec 32)
  | movhpsSt (base : Register) (src : XmmReg) (disp : BitVec 32)
  | movlhpsRR (dst src : XmmReg)
  | movhlpsRR (dst src : XmmReg)
  | unpcklpsRR (dst src : XmmReg)
  | unpckhpsRR (dst src : XmmReg)
  | unpcklpdRR (dst src : XmmReg)
  | unpckhpdRR (dst src : XmmReg)
  | movntpsSt (base : Register) (src : XmmReg) (disp : BitVec 32)
  | movntpdSt (base : Register) (src : XmmReg) (disp : BitVec 32)
  | movntdqSt (base : Register) (src : XmmReg) (disp : BitVec 32)
  | movntiSt (base : Register) (src : Register) (disp : BitVec 32)
  deriving DecidableEq, Repr

end Gabbro.Grammatik.X86
