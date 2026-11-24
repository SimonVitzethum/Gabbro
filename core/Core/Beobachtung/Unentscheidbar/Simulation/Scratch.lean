module

public import Core.Ast.Aggregate.Types.Model

@[expose] public section

namespace Scratch

open Gabbro.Core.Ast

example (t : Ty .value) : True := by
  induction t using Ty.rec <;> trivial

example (t : Ty .value) : True := by
  let k : Kind := .value
  induction (show Ty k from t) <;> trivial

example : ∀ (k : Kind) (t : Ty k), True := by
  intro k t
  cases k
  induction t <;> trivial

def smallDecode : Nat → Option Nat
  | 0 => none
  | n + 1 =>
    let p := n.unpair
    let payload := p.2
    have hp : payload < n + 1 := lt_of_le_of_lt (Nat.unpair_right_le n) (Nat.lt_succ_self n)
    have ha : payload.unpair.1 < n + 1 := lt_of_le_of_lt (Nat.unpair_left_le payload) hp
    have hb : payload.unpair.2 < n + 1 := lt_of_le_of_lt (Nat.unpair_right_le payload) hp
    if p.1 = 0 then some (smallDecode payload.unpair.1).getD 0
    else if p.1 = 1 then some (smallDecode payload.unpair.2).getD 0
    else some payload
termination_by n => n
decreasing_by assumption

end Scratch
