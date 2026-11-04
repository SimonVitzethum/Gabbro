/- Native arithmetic is evaluated once before the retained-result guard. -/
module
public import Stage0.Senke.Gleit.Native.Retained
public import Stage0.Senke.Anweisung.Faelle.Hilfen
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR

/-- The stable result is below every guard temporary. A successful continuation
    already has its value in the canonical binder slot; no FP operation repeats. -/
def nativeFloatBindL (d : Nat) (lo hi : Int × Int)
    (producer : Nat → Option (List II × Nat))
    (rest : Unit → Option (List II × Nat)) : Option (List II × Nat) := do
  let ce ← producer d
  let cc ← floatRetainedRangeL d (d + 1) lo hi
  let cr ← rest ()
  pure (ce.1 ++ floatNarrowC (d + 1) cc.1 (stopC 107 d) [] cr.1,
    max ce.2 (max cc.2 (max (d + 8) cr.2)))

/-- All four source arithmetic operations share the same single-evaluation
    binder as computed integer conversion. -/
def floatArithmeticBlockL (op : GleitOp) (d : Nat) (lo hi : Int × Int)
    (left right : Nat → Option (List II × Nat))
    (rest : Unit → Option (List II × Nat)) : Option (List II × Nat) :=
  nativeFloatBindL d lo hi (fun j => floatWordsL op j left right) rest

theorem floatArithmeticBlockL_eq (op : GleitOp)
    (d : Nat) (lo hi : Int × Int) (left right : Nat → Option (List II × Nat))
    (rest : Unit → Option (List II × Nat)) :
    floatArithmeticBlockL op d lo hi left right rest = (do
      let ce ← floatWordsL op d left right
      let cc ← floatRetainedRangeL d (d + 1) lo hi
      let cr ← rest ()
      pure (ce.1 ++ floatNarrowC (d + 1) cc.1 (stopC 107 d) [] cr.1,
        max ce.2 (max cc.2 (max (d + 8) cr.2)))) := rfl

end Gabbro.Stage0.Senke
