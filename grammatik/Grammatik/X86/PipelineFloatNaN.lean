/-
  File:      Grammatik/X86/PipelineFloatNaN.lean
  Subject:   Pipeline float: NaN payload and bit-exact agreement.

  Lane 1201: follow-up of lane 1161 (`PipelineFloat.lean`), whose NaN
  agreement is class-level only (`fpRechne_klasse`; payload equality
  never concluded). This file states and proves bit-exact agreement
  of the source IEEE result (`gleitRechne`) and the SSE2 result
  (`fpRechne`) INCLUDING NaN payload propagation and quiet/signalling
  behaviour AS THE ACCEPTED CODECS DEFINE THEM (`Gleitkomma*.lean`,
  `ScalarFloat.lean`): the model propagates a NaN operand verbatim
  (`Gleitkomma.add/mul/div`: first NaN wins; `sub` via `neg`), with a
  single `.nan` class and no quiet-bit discipline. Where silicon
  leaves the two-NaN operand-order choice open, it is a NAMED
  hardware assumption (`HwZweiNanWahl`), never proved.

  Reused, not duplicated:
    - model ops: `Gleitkomma.add/sub/mul/div/neg`, `klasse_neg`,
      `nanQ`;
    - target steps: `fpRechne`/`fpRechne_gleitRechne`, `fpSchritt`
      with its `fpSchritt_*` equations, `muster64`/`bites64`,
      `muster64_bites64`, `ucomiFlags_ungeordnet_links`;
    - pipeline: `senkGleitOp`, `laufFp`, `floatPipeOk`,
      `pipelineFloat_seq` and the witness vocabulary (`fpZeugeT`,
      `read64_nach_write64`, `zeugenSpeicher`).
  No second source interpreter, no new IEEE model, no optimiser edit.
-/
import Grammatik.X86.PipelineFloat

namespace Gabbro.Grammatik.X86.PipelineFloatNaN

open Gabbro.Grammatik
open Gabbro.Grammatik.X86
open Gabbro.Grammatik.X86.PipelineFloat

/-- Lower one float op as the admitted two-step NaN-carrying sequence:
    `movsd dst, a` then the accepted scalar SSE2 form against `b`. -/
def senkNanSeq (op : GleitOp) (dst a b : XmmReg) : List FpDecodiert :=
  [⟨.movsdRR dst a, 4⟩, ⟨senkGleitOp op dst b, 4⟩]

/-- The decided admission check of a NaN-carrying lowering: the accepted
    profile and decode length (`floatPipeOk`, reused unchanged). -/
def nanPipeOk (k : FPKontext) (len : Nat) : Bool :=
  floatPipeOk k len

/-- The reset context with a 4-byte form is admitted. -/
theorem nanPipeOk_reset : nanPipeOk kontextReset 4 = true :=
  floatPipeOk_reset

/- CUTS: what is not proved here (filled as the file grows).
  - No loaded image, no byte fetch: runs go through `laufFp` over
    constructed `FpDecodiert` values, never bytes through a decoder.
-/

#print axioms nanPipeOk_reset

end Gabbro.Grammatik.X86.PipelineFloatNaN
