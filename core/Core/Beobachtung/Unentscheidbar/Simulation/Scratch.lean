module

public import Core.Beobachtung.Unentscheidbar.Modell

@[expose] public section

namespace Scratch

open Gabbro.Core.Ast

theorem tyTrue : ∀ t : Ty .value, True
  | .int _ _ => trivial
  | .bool => trivial
  | .array el _ => tyTrue el
  | .productEnd => trivial
  | .product h t => tyTrue h; tyTrue t
  | .record _ _ lay => tyTrue lay
  | .recordSchema _ _ lay => tyTrue lay
  | .sumEnd => trivial
  | .sum h t => tyTrue h; tyTrue t
  | .variant _ _ _ lay => tyTrue lay
  | .variantSchema _ _ _ lay => tyTrue lay
  | .text _ => trivial
  | .carrierSchema _ _ lay _ => tyTrue lay
  | .effectGroupSchema _ => trivial
  | .address _ => trivial
  | .ownedRegion => trivial
  | .regionView el => tyTrue el
  | .ptr _ _ ref => tyTrue ref

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
