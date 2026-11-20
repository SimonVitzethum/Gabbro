module
public import Runner.IR.NativeRun
public import NativeFloat.Hardware
@[expose] public section

namespace Runner

/-! The named hardware contract supplies the numerical identity. These adapters
    compose the existing native request relation, including every permitted
    result representation; they introduce no execution rule or evaluator. -/

theorem nativeFromUInt64_high [RootNativeFloat.Hardware] {format : FPFormat} {value half result : W}
    (high : value.msb = true)
    (converted : NativeFPEval (.fromInt64 format) (uint64StickyHalf value) 0 half)
    (expected : NativeFPEval (.fromUInt64 format) value 0 result) :
    NativeFPEval (.add format) half half result := by
  cases format with
  | f32 =>
    change half = (half.setWidth 32).setWidth 64 ∧
      readFloat32 half = (Int64.ofBitVec (uint64StickyHalf value)).hwToFloat32 at converted
    change result = (result.setWidth 32).setWidth 64 ∧
      readFloat32 result = (UInt64.ofBitVec value).hwToFloat32 at expected
    change result = (result.setWidth 32).setWidth 64 ∧
      readFloat32 result = Float32.hwAdd (readFloat32 half) (readFloat32 half)
    refine ⟨expected.1, ?_⟩
    rw [expected.2, converted.2]
    exact RootNativeFloat.uint64_toFloat32_high value high
  | f64 =>
    change readFloat half = (Int64.ofBitVec (uint64StickyHalf value)).hwToFloat at converted
    change readFloat result = (UInt64.ofBitVec value).hwToFloat at expected
    change readFloat result = Float.hwAdd (readFloat half) (readFloat half)
    rw [expected, converted]
    exact RootNativeFloat.uint64_toFloat_high value high

namespace IR
variable [Kern]

/-- The high-half path answers a signed conversion and an addition. Its final
    word is the original unsigned certificate, without a NaN-bit inverse. -/
theorem Run.fp_fromUInt64_high {format : FPFormat} {value result : W}
    {continuation : W → Res T} {m m' : Mem} {t : T} (high : value.msb = true)
    (heval : NativeFPEval (.fromUInt64 format) value 0 result)
    (hk : Run (continuation result) m t m') :
    Run (fpFromUInt64 format value continuation) m t m' := by
  let half := nativeFPBits (.fromInt64 format) (uint64StickyHalf value) 0
  have converted : NativeFPEval (.fromInt64 format) (uint64StickyHalf value) 0 half :=
    nativeFPBits_eval _ _ _
  have doubled : NativeFPEval (.add format) half half result :=
    nativeFromUInt64_high high converted heval
  have actual : Run (Runner.fp (.fromInt64 format) (uint64StickyHalf value) 0
      fun rounded => Runner.fp (.add format) rounded rounded continuation) m t m' :=
    Run.native_fp (continuation := fun rounded =>
      Runner.fp (.add format) rounded rounded continuation)
      converted (Run.native_fp doubled hk)
  simpa only [fpFromUInt64, high, ↓reduceIte] using
    actual

/-- The complete portable request sequence covers every UInt64 input and uses
    only the existing native primitive and continuation Run constructors. -/
theorem Run.fp_fromUInt64 {format : FPFormat} {value result : W}
    {continuation : W → Res T} {m m' : Mem} {t : T}
    (heval : NativeFPEval (.fromUInt64 format) value 0 result)
    (hk : Run (continuation result) m t m') :
    Run (fpFromUInt64 format value continuation) m t m' := by
  cases high : value.msb with
  | false => exact Run.fp_fromUInt64_low high heval hk
  | true => exact Run.fp_fromUInt64_high high heval hk

end IR
end Runner
