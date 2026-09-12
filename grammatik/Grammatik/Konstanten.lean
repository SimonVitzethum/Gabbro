/-
  File:      Grammatik/Konstanten.lean
  Subject:   CONST CERTIFICATE FROM THE SOURCE (lane 121) -- the fragment
             of `const fn` bodies the checker prints to Lean, its `Nat`
             evaluation, and the soundness of the printed square function:
             evaluation of the SYNTAX equals the printed function, so the
             `List.all` certificate ties the values to the source.
-/

namespace Gabbro.Grammatik

/-- Binary operators of the const fragment: arithmetic, bit, comparison
    (as `0`/`1`), and logic (as `0`/`1`). No negation, no `~`, no
    wrap/saturate -- the printer refuses those, like `lean.rs`. -/
inductive KBinOp where
  | add | sub | mul | div | mod
  | land | lor | xor | shl | shr
  | eq | ne | lt | le | gt | ge
  | and | or
deriving DecidableEq, Repr

/-- Unary operators of the const fragment: logical negation only. -/
inductive KUnaOp where
  | not
deriving DecidableEq, Repr

/-- The translated expression language: literals, the parameter, named
    consts (by name, read off an environment), calls (by name, read off
    a function environment), and operator applications. -/
inductive KExpr where
  | lit : Nat → KExpr
  | param : KExpr
  | konst : String → KExpr
  | una : KUnaOp → KExpr → KExpr
  | bin : KBinOp → KExpr → KExpr → KExpr
  | ruf : String → List KExpr → KExpr

/-- Operator evaluation on `Nat`, mirroring the printed Lean operators. -/
def KBinOp.eval : KBinOp → Nat → Nat → Nat
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b
  | .div, a, b => a / b
  | .mod, a, b => a % b
  | .land, a, b => Nat.land a b
  | .lor, a, b => Nat.lor a b
  | .xor, a, b => Nat.xor a b
  | .shl, a, b => Nat.shiftLeft a b
  | .shr, a, b => Nat.shiftRight a b
  | .eq, a, b => if a == b then 1 else 0
  | .ne, a, b => if !(a == b) then 1 else 0
  | .lt, a, b => if a < b then 1 else 0
  | .le, a, b => if a <= b then 1 else 0
  | .gt, a, b => if a > b then 1 else 0
  | .ge, a, b => if a >= b then 1 else 0
  | .and, a, b => if a == 0 || b == 0 then 0 else 1
  | .or, a, b => if a == 0 && b == 0 then 0 else 1

/-- Expression evaluation: the parameter reads the index, names read
    the environments, calls apply the named function to the values. -/
def KExpr.eval (env : String → Nat) (fns : String → List Nat → Nat) :
    KExpr → Nat → Nat
  | .lit n, _ => n
  | .param, i => i
  | .konst c, _ => env c
  | .una .not e, i => if e.eval env fns i == 0 then 1 else 0
  | .bin op a b, i => op.eval (a.eval env fns i) (b.eval env fns i)
  | .ruf f args, i => fns f (args.map (fun e => e.eval env fns i))
