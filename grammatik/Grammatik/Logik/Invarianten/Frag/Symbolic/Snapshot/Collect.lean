module

public import Grammatik.Logik.Invarianten.Frag.Symbolic.Snapshot.Base

@[expose] public section

namespace Gabbro.Grammatik.Invarianten.Frag.Symbolic.Snapshot

/-- Allocation only: the encoder separately certifies the actual index. A
    nonconstant index is refused there, without enumerating its type range. -/
def literalIndex : Expr D Γ Λ τ → Option Int
  | .lit number => some number
  | .widen _ _ body => literalIndex body
  | .add left right => do return (← literalIndex left) + (← literalIndex right)
  | .sub left right => do return (← literalIndex left) - (← literalIndex right)
  | .neg body => do return -(← literalIndex body)
  | _ => none

def observations : Expr D Γ Λ τ → List (Observation D)
  | .oldG name _ => [.glob name]
  | .oldS table field index _ =>
      (match literalIndex index with | some offset => [.slot table field offset] | none => []) ++ observations index
  | .widen _ _ body | .neg body | .not body | .strLen body
    | .some body | .istSome body | .strWeit _ body | .prodGet body _
    | .intBuiltin1 _ body => observations body
  | .add left right | .sub left right | .mul left right
    | .lt left right | .le left right | .eq left right
    | .and left right | .or left right | .strCat left right
    | .strEq left right | .strLt left right | .intBuiltin2 _ left right =>
      observations left ++ observations right
  | .slot _ _ index _ | .thru _ _ _ _ index _ => observations index
  | .eng body _ _ fallback => observations body ++ observations fallback
  | .wenn test yes no => observations test ++ observations yes ++ observations no
  | .forallSlots _ body _ | .existsSlots _ body _ | .count _ body => observations body
  | _ => []

def names (expression : Expr D Γ Λ τ) : List (Observation D) := (observations expression).eraseDups

end Gabbro.Grammatik.Invarianten.Frag.Symbolic.Snapshot
