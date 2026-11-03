/- Long-string acceptance and model witnesses; execution belongs to lead validation. -/
module
public import Stage0.Senke.Ausdruck.Aggregat.Proben
public import Stage0.Senke.Ausdruck.Aggregat.Frame.String.Values
@[expose] public section

namespace Gabbro.Stage0.Senke.StringSpanProbe
open Gabbro.Grammatik Runner.IR AggregateProbe

/-- Capacities exceed the packed representation; embedded zero and 255 remain bytes. -/
def left : Expr D [] [] (.str 12) := .strLit
  [⟨97, by decide, by decide⟩, ⟨0, by decide, by decide⟩, ⟨255, by decide, by decide⟩,
   ⟨98, by decide, by decide⟩, ⟨99, by decide, by decide⟩, ⟨100, by decide, by decide⟩,
   ⟨101, by decide, by decide⟩, ⟨102, by decide, by decide⟩] (by decide)

def right : Expr D [] [] (.str 11) := .strLit
  [⟨103, by decide, by decide⟩, ⟨104, by decide, by decide⟩, ⟨105, by decide, by decide⟩,
   ⟨106, by decide, by decide⟩, ⟨107, by decide, by decide⟩] (by decide)

def prefix : Expr D [] [] (.str 9) := .strLit
  [⟨97, by decide, by decide⟩, ⟨0, by decide, by decide⟩] (by decide)

def zeroTail : Expr D [] [] (.str 10) := .strLit
  [⟨97, by decide, by decide⟩, ⟨0, by decide, by decide⟩, ⟨0, by decide, by decide⟩] (by decide)

def emptyLong : Expr D [] [] (.str 8) := .strLit [] (by decide)

def combined : Expr D [] [] (.str 23) := .strCat left right

/-- Both long operands, either operand order, empty strings, and packed/long mixtures. -/
theorem accepted_zeuge :
    (lowE layout combined 4).isSome = true ∧
    (lowE layout (.strCat right left) 4).isSome = true ∧
    (lowE layout (.strCat left emptyLong) 4).isSome = true ∧
    (lowE layout (.strCat emptyLong right) 4).isSome = true ∧
    (lowE layout (.strCat letter letter) 4).isSome = true ∧
    (lowE layout (.strCat empty left) 4).isSome = true ∧
    (lowE layout (.strCat right letter) 4).isSome = true ∧
    (lowE layout (.strLt left right) 4).isSome = true ∧
    (lowE layout (.strLt right left) 4).isSome = true ∧
    (lowE layout (.strLt prefix left) 4).isSome = true ∧
    (lowE layout (.strLt left prefix) 4).isSome = true ∧
    (lowE layout (.strLt left left) 4).isSome = true ∧
    (lowE layout (.strLt prefix zeroTail) 4).isSome = true ∧
    (lowE layout (.strLt emptyLong zero) 4).isSome = true ∧
    (lowE layout (.strLt zero emptyLong) 4).isSome = true ∧
    (lowE layout (.strLt letter right) 4).isSome = true ∧
    (lowE layout (.strLt right letter) 4).isSome = true := by decide +kernel

/-- Appending preserves all thirteen bytes and leaves no capacity padding in the value. -/
theorem concatenate_meaning_zeuge :
    (eval world combined world .nil).1 =
      (eval world left world .nil).1 ++ (eval world right world .nil).1 ∧
    (eval world combined world .nil).1.length = 13 ∧
    (eval world (.strCat empty left) world .nil).1 = (eval world left world .nil).1 ∧
    (eval world (.strCat right emptyLong) world .nil).1 = (eval world right world .nil).1 := by
  decide +kernel

/-- Compare both ways, distinguish a proper prefix from a present zero byte, and
    compare long strings whose runtime lengths differ from their declared capacities. -/
theorem order_meaning_zeuge :
    eval world (.strLt left right) world .nil = true ∧
    eval world (.strLt right left) world .nil = false ∧
    eval world (.strLt left left) world .nil = false ∧
    eval world (.strLt prefix left) world .nil = true ∧
    eval world (.strLt left prefix) world .nil = false ∧
    eval world (.strLt prefix zeroTail) world .nil = true ∧
    eval world (.strLt zeroTail prefix) world .nil = false ∧
    eval world (.strLt left combined) world .nil = true ∧
    eval world (.strLt combined left) world .nil = false ∧
    eval world (.strLt emptyLong zero) world .nil = true ∧
    eval world (.strLt zero emptyLong) world .nil = false := by decide +kernel

/-- The accepted concatenation uses the same generic theorem as arbitrary expressions. -/
theorem concatenation_correct [Kern] {m : Runner.Mem} {pc fp : Runner.W} {K top : Nat} {c : List II}
    (lower : lowE layout combined 4 = some (c, top)) (fits : top ≤ K)
    (pre : Pre layout m pc fp K 4 c (Env.nil : Env D []) (fun m => WeltAt m layout world))
    (placed : LayIn layout) :
    ValueOk layout m pc fp K 4 c (.str 23) (eval world combined world .nil) :=
  lowE_ok world world (fun _ h => h) placed combined 4 c top lower fits m pc .nil pre

#print axioms bytesLt_keys
#print axioms stringScan_value
#print axioms strCatExpr_ok
#print axioms strLtExpr_ok

end Gabbro.Stage0.Senke.StringSpanProbe
