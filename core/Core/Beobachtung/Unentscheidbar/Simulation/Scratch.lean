module

public import Core.Beobachtung.Unentscheidbar.Modell

@[expose] public section

namespace Scratch

def smallDecode : Nat → Option Nat
  | 0 => none
  | n + 1 =>
    have hp : (n.unpair).2 < n.succ := Nat.lt_succ_of_le (Nat.unpair_right_le n)
    have ha : (n.unpair).2.unpair.1 < n.succ :=
      lt_of_le_of_lt (Nat.unpair_left_le (n.unpair).2) hp
    have hb : (n.unpair).2.unpair.2 < n.succ :=
      lt_of_le_of_lt (Nat.unpair_right_le (n.unpair).2) hp
    if (n.unpair).1 = 0 then smallDecode (n.unpair).2.unpair.1
    else if (n.unpair).1 = 1 then smallDecode (n.unpair).2.unpair.2
    else some (n.unpair).2
termination_by x => x
decreasing_by all_goals assumption

end Scratch
