/-
  File:      stage0/Stage0/Senke/Sperre/Code.lean
  Subject:   Building blocks of the lock code (`Ticket/Code.lean`): `addC` adds to a word by `cas`, again until it
             holds; `futexC` builds the request block of a `futex` call and makes it.
-/
module
public import Stage0.Senke.Ausdruck
public import Stage0.Senke.Stopp
@[expose] public section


namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR

variable {D : Deklaration}

/-- `w := w + d` for the word at `a` by `cas`, again until it holds (scratch from `u`): 7 instructions. -/
def addC (a u : Nat) (d : Int) : List II :=
  [ci 1 u a 0, ci 15 ((u + 1 : Nat) : Int) u 0, ci 1 ((u + 3 : Nat) : Int) d 0,
    ci 3 ((u + 2 : Nat) : Int) ((u + 1 : Nat) : Int) ((u + 3 : Nat) : Int),
    ci 22 ((u + 4 : Nat) : Int) u ((u + 1 : Nat) : Int),
    ci 14 ((u + 4 : Nat) : Int) ((u + 4 : Nat) : Int) ((u + 1 : Nat) : Int),
    ci 19 ((u + 4 : Nat) : Int) (-96) 0]

/-- `futex (a, op, v)` with `v` from slot `v`, the request block from `q`: 8 instructions. -/
def futexC (a op : Nat) (v q : Nat) (vConst : Option Int) : List II :=
  [ci 1 q 202 0, ci 1 ((q + 1 : Nat) : Int) a 0, ci 1 ((q + 2 : Nat) : Int) op 0,
    (match vConst with
     | some k => ci 1 ((q + 3 : Nat) : Int) k 0
     | none => ci 2 ((q + 3 : Nat) : Int) v 0),
    ci 1 ((q + 4 : Nat) : Int) 0 0, ci 1 ((q + 5 : Nat) : Int) 0 0, ci 1 ((q + 6 : Nat) : Int) 0 0,
    ci 23 ((q + 7 : Nat) : Int) q 0]

end Gabbro.Stage0.Senke
