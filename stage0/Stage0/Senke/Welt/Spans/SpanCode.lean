/- Canonical full-span transport code, below expression emission and proofs. -/
module
public import Stage0.Senke.Welt.Lay
public import Runner.IR.Rahmen
public import Stage0.Senke.Ausdruck.Quant.TransportCode
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR
variable {D : Deklaration}
/-- Full canonical storage read; frame layout uses exactly the declared width. -/
def globalValueC (L : Lay D) (g : D.Glob) (dst : Nat) : Option (List II × Nat) :=
  if L.ga g + 8 * valueWords (D.gtyp g) < 2 ^ 31 then
    some (loadSpan (valueWords (D.gtyp g)) dst (L.ga g), dst + valueWords (D.gtyp g))
  else none

/-- Evaluate the child once, then store every word into the typed global span. -/
def globalStoreC (L : Lay D) (g : D.Glob) (dst : Nat) (child : List II × Nat) :
    Option (List II × Nat) :=
  if L.ga g + 8 * valueWords (D.gtyp g) < 2 ^ 31 then
    some (child.1 ++ storeSpan (valueWords (D.gtyp g)) (dst + valueWords (D.gtyp g)) dst (L.ga g),
      max child.2 (dst + valueWords (D.gtyp g) + 1))
  else none

theorem globalStoreC_top {L : Lay D} {g : D.Glob} {dst top : Nat} {child : List II × Nat} {code : List II}
    (made : globalStoreC L g dst child = some (code, top)) :
    child.2 ≤ top ∧ dst + valueWords (D.gtyp g) < top := by
  unfold globalStoreC at made
  split at made
  · cases made
    exact ⟨Nat.le_max_left _ _, Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_right _ _)⟩
  · cases made

end Gabbro.Stage0.Senke
