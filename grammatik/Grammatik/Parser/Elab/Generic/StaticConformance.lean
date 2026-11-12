module
public import Grammatik.Parser.Elab.Generic.PointerTypes
public import Grammatik.Parser.Elab.Generic.Signatures
@[expose] public section
namespace Gabbro.Grammatik.Parser.Generic
open Uebersetze UebersetzeAllg

def staticSignatureFits (unit : UProg) (actual expected : UFn) : Except String Unit :=
  if sigPasstB (fun lock => (lockAt unit lock).rank)
      (mkSig unit actual) (mkSig unit expected) && vertragPasstB actual expected then .ok ()
  else .error ("static-function-signature-mismatch: " ++ actual.name)

/-- Compute each parameter's pointer signature with the existing elaborator, then check the
    actual function with the very same SigPasst decision used by ordinary function pointers.
    These signatures are compile-time obligations; no pointer value or indirect call is emitted. -/
def checkStaticConformance (consts : List (String × Int))
    (aliases : List (String × (Int × Int))) (unit : UProg)
    (requirements : List (STyp × String)) (named : List (String × Ty) := [])
    (specs : List (String × List String × SExpr) := [])
    (specTypen : List (String × List STyp) := []) : Except String Unit := do
  for (expected, target) in requirements do
    let raw ← match expected with
      | .raw raw => pure raw
      | _ => throw "static function parameter requires a function-pointer type"
    let (_, pointer) ← elabZeigerTyp consts aliases unit.tabs unit.locks unit.globs
      unit.whys unit.sums unit.ptrKeys (unit.fns.length) 0 raw unit.spaces named unit.eigner specs specTypen
    let actual ← fnIdx unit.fns target
    staticSignatureFits unit (fnAt unit actual) pointer

/-- The successful Boolean gate is the canonical conformance relation, including effects,
    results, reason channels, held locks and lock floors; contracts use the shared inclusion gate. -/
theorem staticSignatureFits_ok (unit : UProg) (actual expected : UFn)
    (h : staticSignatureFits unit actual expected = .ok ()) :
    SigPasst (fun lock => (lockAt unit lock).rank)
      (mkSig unit actual) (mkSig unit expected) := by
  cases hb : sigPasstB (fun lock => (lockAt unit lock).rank)
      (mkSig unit actual) (mkSig unit expected) with
  | false => simp [staticSignatureFits, hb] at h
  | true =>
    cases hc : vertragPasstB actual expected with
    | false => simp [staticSignatureFits, hb, hc] at h
    | true => exact sigPasstB_ok hb

end Gabbro.Grammatik.Parser.Generic
