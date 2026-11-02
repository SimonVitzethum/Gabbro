module
public import Grammatik.Parser.Elab.Generic.PointerTypes
public import Grammatik.Parser.Elab.Generic.Signatures
@[expose] public section
namespace Gabbro.Grammatik.Parser.Generic
open Uebersetze UebersetzeAllg

/-- Compute each parameter's pointer signature with the existing elaborator, then check the
    actual function with the very same SigPasst decision used by ordinary function pointers.
    These signatures are compile-time obligations; no pointer value or indirect call is emitted. -/
def checkStaticConformance (consts : List (String × Int))
    (aliases : List (String × (Int × Int))) (unit : UProg)
    (requirements : List (STyp × String)) : Except String Unit := do
  for (expected, target) in requirements do
    let raw ← match expected with
      | .raw raw => pure raw
      | _ => throw "static function parameter requires a function-pointer type"
    let (_, pointer) ← elabZeigerTyp consts aliases unit.tabs unit.locks unit.globs
      unit.whys unit.sums unit.ptrKeys (unit.fns.length) 0 raw
    let actual ← fnIdx unit.fns target
    if !sigPasstB (fun lock => (lockAt unit lock).rank)
        (mkSig unit (fnAt unit actual)) (mkSig unit pointer) then
      throw ("static-function-signature-mismatch: " ++ target)

/-- The successful Boolean gate is the canonical conformance relation, including effects,
    results, reason channels, held locks and lock floors. -/
theorem staticSignature_conforms (unit : UProg) (actual expected : UFn)
    (h : sigPasstB (fun lock => (lockAt unit lock).rank)
      (mkSig unit actual) (mkSig unit expected) = true) :
    SigPasst (fun lock => (lockAt unit lock).rank)
      (mkSig unit actual) (mkSig unit expected) := sigPasstB_ok h

end Gabbro.Grammatik.Parser.Generic
