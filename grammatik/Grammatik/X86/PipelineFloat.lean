/-
  File:      Grammatik/X86/PipelineFloat.lean
  Subject:   Pipeline: IEEE float expressions (source `gleit` block nodes to
              accepted scalar SSE2 forms).

  Lane 1161: lower the source IEEE model (`Gleitkomma`, `gleitRechne`,
  `gleitAusInt`, `gleitRoh`, `gleitLt`/`gleitLe`) to the ACCEPTED scalar
  SSE2 forms (`ScalarFloat.fpSchritt`/`fpRechne`, `ScalarFloatCodec`,
  `ScalarFloat32HardwareForms`, `FpControlHardwareForms`) under the MXCSR
  control-state premise (round-to-nearest, no fast-math, no contraction).

  Reused, not duplicated:
    - machine words: `Gleitprofil.muster64`/`bites64`/`fadd64`/…,
      `mxcsrGueltig`, `kontextReset`;
    - target steps: `ScalarFloat.fpSchritt` with its `fpSchritt_*`
      equations, `fpRechne_gleitRechne`, `fpRechne_klasse`,
      `ucomiFlags_*`, `cvtsiErg`, `cvttPaket_gleicht_gleitRoh`;
    - source observations: `FloatSourceObservations.eval_fllt_ist_gleitLt`;
    - joint state: `fpZeugeT`/`fpZeugeT1`/`fpZeugeT2` and their step
      lemmas for the `_zeuge`.
  No second source interpreter, no new IEEE model, no optimiser edit.
-/
import Grammatik.X86.ScalarFloat

namespace Gabbro.Grammatik.X86.PipelineFloat

open Gabbro.Grammatik
open Gabbro.Grammatik.X86

/-- Lower one source float op to its accepted scalar SSE2 register form:
    one source op = one machine op (no contraction, no fast-math). -/
def senkGleitOp : GleitOp → XmmReg → XmmReg → FpBefehl
  | .add, dst, src => .addsdRR dst src
  | .sub, dst, src => .subsdRR dst src
  | .mul, dst, src => .mulsdRR dst src
  | .div, dst, src => .divsdRR dst src

/-- Run a decoded scalar-FP list; `none` is an explicit refusal. -/
def laufFp : List FpDecodiert → FpZustand → Option FpZustand
  | [], t => some t
  | d :: ds, t =>
    match fpSchritt d t with
    | none => none
    | some t' => laufFp ds t'

end Gabbro.Grammatik.X86.PipelineFloat
