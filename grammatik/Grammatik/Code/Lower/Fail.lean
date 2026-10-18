import Grammatik.Code.Lower.Rep

/-
  File:      Grammatik/Code/Lower/Fail.lean
  Subject:   TRACK L, PHASE L1 -- THE ANSWER WORD OF A FUNCTION WITH A FAILURE CHANNEL.

  A function that may answer a REASON (`D.gruende f = n > 0`, `return` of a value or `return why r`) answers
  ONE word in `Code` (a call has one result): with `L = n + 1`, a reason `r` is the word `r + 1`, a value
  `v` of the range `lo .. hi` is `L * (v - lo)`, a function without a value is `0`. The case number is the
  word modulo `L` (`0` is the value, `i + 1` the reason `i`) and the value is the word divided by `L`, plus
  `lo`: the same packing as a tagged value (`Lower/Sum.lean`), with the value as case `0`. The word is
  carried at `Ar.wid 0 (L * S)` bits, `S` the number of values the answer may take (at least `1`).

  NAMED CUT: a function with a failure channel answers `void` or an integer range; `bool`, a pointer, an
  option, a reason or a tagged value as the value of such a function is refused by name (`failOk`).
-/

namespace Gabbro.Code.Lower

open Gabbro.Grammatik (ErgVal Zahl Deklaration)

variable {D : Deklaration}

/-- The number of values a function's answer may take (`1` for none). -/
def failS : Option GTy → Int
  | some (.int lo hi) => hi - lo + 1
  | _ => 1

/-- The words of a function with `n` reasons and answer type `eo` are below this bound. -/
def failTop (n : Nat) (eo : Option GTy) : Int := ((n + 1 : Nat) : Int) * failS eo

variable [Conf]

/-- The width of the answer word. -/
def retW (n : Nat) (eo : Option GTy) : Nat := Ar.wid 0 (failTop n eo)

/-- The failure channel is in the fragment: the word fits, the answer is void or an integer range. -/
def failOk (n : Nat) (eo : Option GTy) : Bool :=
  decide (Ar.Fits 0 (failTop n eo) 128) &&
    (match eo with | none => true | some (.int _ _) => true | some _ => false)

/-- The word of a value answer. -/
def okZ (n : Nat) : (eo : Option GTy) → ErgVal D eo → Int
  | none, _ => 0
  | some (.int lo _), v => ((n + 1 : Nat) : Int) * ((v : Zahl lo _).n - lo)
  | some _, _ => 0

end Gabbro.Code.Lower
