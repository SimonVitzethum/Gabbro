module
public import Runner.IR.Step
public import Runner.Basis.FloatingCodec
public import Runner.Basis.FloatingCast
@[expose] public section

/-! The existing native request Run producers, below portable composition and
    instruction sequencing. This module is a pure move, with unchanged rules. -/

namespace Runner.IR

/-- The answer of the memory to a request; `none` for a system call (not answered here). -/
def memAns (m : Mem) : Op → Option (Ans × Mem)
  | .rd 1 a => some ((m.rd8 a).map (fun v => (v.setWidth 64, 0)), m)
  | .rd 4 a => some ((m.rd32 a).map (fun v => (v.setWidth 64, 0)), m)
  | .rd _ a => some ((m.rd64 a).map (fun v => (v, 0)), m)
  | .wr a v => some (match m.wr64 a v with | some m' => (some (0, 0), m') | none => (none, m))
  | .cas a e n => some (match m.cas a e n with | some (o, m') => (some (o, 0), m') | none => (none, m))
  | .sys _ => none
  | .fp _ _ _ => none

/-- **The kernel**: which answer and which memory a system call may leave. Any relation; what a program may rely
    on is the named assumption at its gates (`Stage0/Senke/Tor`). -/
class Kern where
  ans : Req → Mem → Ans → Mem → Prop

variable [Kern]

inductive Run : Res T → Mem → T → Mem → Prop
  | next {t : T} {m : Mem} : Run (.next t) m t m
  | ask {o : Op} {k : Ans → Res T} {m m' m'' : Mem} {a : Ans} {t : T} :
      memAns m o = some (a, m') → Run (k a) m' t m'' → Run (.ask o k) m t m''
  | sys {q : Req} {k : Ans → Res T} {m m' m'' : Mem} {a : Ans} {t : T} :
      Kern.ans q m a m' → Run (k a) m' t m'' → Run (.ask (.sys q) k) m t m''
  | fp {kind : NativeFPOp} {a b result : W} {k : Ans → Res T} {m m' : Mem} {t : T} :
      NativeFPEval kind a b result → Run (k (some (result, 0))) m t m' →
      Run (.ask (.fp kind a b) k) m t m'

/-- Derive a normalized primitive request from its native CPU result. -/
theorem Run.native_fp {kind : NativeFPOp} {a b result : W} {continuation : W → Res T}
    {m m' : Mem} {t : T} (heval : NativeFPEval kind a b result)
    (hk : Run (continuation result) m t m') : Run (Runner.fp kind a b continuation) m t m' := by
  unfold Runner.fp
  have normalized : NativeFPEval kind (kind.inputs a b).1 (kind.inputs a b).2 result := by
    simpa only [NativeFPEval, nativeFP_inputs] using heval
  refine .fp normalized ?_
  simpa only [opt_some, NativeFPEval.resultWord heval] using hk

/-- The actual low-half branch of the portable unsigned conversion consumes
    the original unsigned result certificate, not a new CPU callback. -/
theorem Run.fp_fromUInt64_low {format : FPFormat} {value result : W}
    {continuation : W → Res T} {m m' : Mem} {t : T} (low : value.msb = false)
    (heval : NativeFPEval (.fromUInt64 format) value 0 result)
    (hk : Run (continuation result) m t m') : Run (fpFromUInt64 format value continuation) m t m' := by
  have signed : NativeFPEval (.fromInt64 format) value 0 result := by
    cases format
    · simpa only [NativeFPEval, nativeFP, uint64_toFloat32_nonnegative value low] using heval
    · simpa only [NativeFPEval, nativeFP, uint64_toFloat_nonnegative value low] using heval
  simpa only [fpFromUInt64, low, Bool.false_eq_true, ↓reduceIte] using Run.native_fp signed hk

end Runner.IR
