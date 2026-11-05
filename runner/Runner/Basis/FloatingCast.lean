module
public import Runner.Basis.FloatingSequence
public import NativeFloat.Hardware
@[expose] public section

namespace Runner

/-! The low-half identity is projected from the named hardware contract.
    No toolchain floating model is unfolded by this request adapter. -/

theorem nativeFromUInt64_low [RootNativeFloat.Hardware]
    {format : FPFormat} {value result : W} (h : value.msb = false)
    (hr : NativeFPEval (.fromInt64 format) value 0 result) :
    NativeFPEval (.fromUInt64 format) value 0 result := by
  cases format
  · simpa only [NativeFPEval, nativeFP, RootNativeFloat.uint64_toFloat32_nonnegative value h] using hr
  · simpa only [NativeFPEval, nativeFP, RootNativeFloat.uint64_toFloat_nonnegative value h] using hr

end Runner
