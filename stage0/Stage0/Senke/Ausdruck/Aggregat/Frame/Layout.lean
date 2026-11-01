/- Function-local frame placement; the external call/result ABI remains canonical. -/
module
public import Stage0.Senke.Ausdruck
@[expose] public section


namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik

/-- Only checked source-derived sizes enter placement. No caller supplies an offset. -/
structure FrameLayout where
  params : List Ty
  result : Option Ty
  reasons : Nat
  snapshotWords : Nat
  counterDepth : Nat

namespace FrameLayout

def parameterWords (layout : FrameLayout) : Nat := contextWords layout.params

def returnSpan (layout : FrameLayout) : Nat := returnWords layout.result layout.reasons

def snapshotBase (_ : FrameLayout) : Nat := FB

def ensReserved (layout : FrameLayout) : Nat := layout.snapshotWords

def ensParams (layout : FrameLayout) : Nat := FB + layout.ensReserved

def canonicalResult (layout : FrameLayout) : Nat := FB + layout.parameterWords

def canonicalStatus (layout : FrameLayout) : Nat := layout.canonicalResult + layout.returnSpan

def internalResult (layout : FrameLayout) : Nat := layout.ensParams + layout.parameterWords

def internalStatus (layout : FrameLayout) : Nat := layout.internalResult + layout.returnSpan

def bodyReserved (layout : FrameLayout) : Nat :=
  layout.snapshotWords + layout.parameterWords + layout.returnSpan + 1 + 2 * layout.counterDepth

def bodyParams (layout : FrameLayout) : Nat := FB + layout.bodyReserved

/-- The full snapshot prefix ends before the preserved ensures environment. -/
theorem snapshots_end (layout : FrameLayout) :
    layout.snapshotBase + layout.snapshotWords = layout.ensParams := rfl

/-- Both return channels retain their canonical offsets under local snapshot reservation. -/
theorem internal_offsets (layout : FrameLayout) :
    layout.internalResult = layout.canonicalResult + layout.snapshotWords ∧
    layout.internalStatus = layout.canonicalStatus + layout.snapshotWords := by
  simp only [internalResult, internalStatus, ensParams, ensReserved, canonicalResult, canonicalStatus]
  omega

/-- Lexical body variables start after the complete internal result/status and all counters. -/
theorem body_after_status (layout : FrameLayout) :
    layout.bodyParams = layout.internalStatus + 1 + 2 * layout.counterDepth := by
  simp only [bodyParams, bodyReserved, internalStatus, internalResult, ensParams, ensReserved]
  omega

/-- Snapshot/ensures storage is below the body's variable write frontier. -/
theorem protected_prefix (layout : FrameLayout) :
    layout.ensParams ≤ layout.internalResult ∧ layout.internalStatus < layout.bodyParams := by
  have := body_after_status layout
  simp only [internalResult] at *
  omega

/-- An empty snapshot prefix recovers the existing complete-value frame protocol. -/
theorem without_snapshots (layout : FrameLayout) (empty : layout.snapshotWords = 0) :
    layout.ensReserved = 0 ∧ layout.ensParams = FB ∧
    layout.internalResult = layout.canonicalResult ∧
    layout.internalStatus = layout.canonicalStatus ∧
    layout.bodyReserved = layout.parameterWords + layout.returnSpan + 1 + 2 * layout.counterDepth := by
  simp [ensReserved, ensParams, internalResult, internalStatus, canonicalResult,
    canonicalStatus, bodyReserved, empty]

/-- Distinct original parameters, snapshots, multiword result and nested counters coexist. -/
theorem layout_zeuge :
    let layout : FrameLayout := ⟨[.arr (.int 0 255) 3], some (.arr (.int 0 255) 2), 3, 5, 2⟩
    layout.ensParams = 9 ∧ layout.internalResult = 12 ∧ layout.internalStatus = 14 ∧
      layout.canonicalResult = 7 ∧ layout.canonicalStatus = 9 ∧ layout.bodyParams = 19 := by
  decide +kernel

end FrameLayout
end Gabbro.Stage0.Senke
