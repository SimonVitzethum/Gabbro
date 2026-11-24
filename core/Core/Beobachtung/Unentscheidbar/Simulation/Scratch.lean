module

public import Core.Beobachtung.Unentscheidbar.Modell

@[expose] public section

namespace Scratch

open Gabbro.Core.Ast

theorem tyTrue : ∀ t : Ty .value, True
  | .int _ _ => trivial
  | .bool => trivial
  | .array el _ => by have _ := tyTrue el; trivial
  | .productEnd => trivial
  | .product h t => by have _ := tyTrue h; have _ := tyTrue t; trivial
  | .record _ _ lay => by have _ := tyTrue lay; trivial
  | .recordSchema _ _ lay => by have _ := tyTrue lay; trivial
  | .sumEnd => trivial
  | .sum h t => by have _ := tyTrue h; have _ := tyTrue t; trivial
  | .variant _ _ _ lay => by have _ := tyTrue lay; trivial
  | .variantSchema _ _ _ lay => by have _ := tyTrue lay; trivial
  | .text _ => trivial
  | .carrierSchema _ _ lay _ => by have _ := tyTrue lay; trivial
  | .effectGroupSchema _ => trivial
  | .address _ => trivial
  | .ownedRegion => trivial
  | .regionView el => by have _ := tyTrue el; trivial
  | .ptr _ _ ref => by have _ := tyTrue ref; trivial

def smallDecode : Nat → Option Nat
  | 0 => none
  | n + 1 =>
    have hp : (n.unpair).2 < n.succ :=
      lt_of_le_of_lt (Nat.unpair_right_le n) (Nat.lt_succ_self n)
    have ha : (n.unpair).2.unpair.1 < n.succ :=
      lt_of_le_of_lt (Nat.unpair_left_le (n.unpair).2) hp
    have hb : (n.unpair).2.unpair.2 < n.succ :=
      lt_of_le_of_lt (Nat.unpair_right_le (n.unpair).2) hp
    if (n.unpair).1 = 0 then smallDecode (n.unpair).2.unpair.1
    else if (n.unpair).1 = 1 then smallDecode (n.unpair).2.unpair.2
    else some (n.unpair).2
termination_by n => n
decreasing_by assumption

end Scratch
