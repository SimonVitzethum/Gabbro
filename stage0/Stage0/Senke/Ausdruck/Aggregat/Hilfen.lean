/-
  File:      stage0/Stage0/Senke/Ausdruck/Aggregat/Hilfen.lean
  Subject:   The code pieces of the expression lowering (`Ausdruck.lean`): integer range tests, constants, binary
             operations, comparisons, float words, slot and array access, quantifiers. Split out of `Ausdruck.lean`
             unchanged.
-/
module
public import Stage0.Senke.Ausdruck.Aggregat.Hilfena
public import Lean.Meta.Tactic.Simp.RegisterCommand
public import Grammatik.Kern.Semantik.Semantik
public import Runner.IR.Rahmen
public import Stage0.Senke.Welt.Lay
public import Stage0.Senke.Welt.Rahmen
public import Stage0.Senke.Welt.Spans.CellCode
public import Stage0.Senke.Ausdruck.Aggregat.Wert
public import Stage0.Senke.Ausdruck.Aggregat.Frame.Code
public import Stage0.Senke.Ausdruck.Aggregat.Frame.CompareCode
public import Stage0.Senke.Ausdruck.Aggregat.Frame.StringGetCode
public import Stage0.Senke.Ausdruck.Aggregat.Frame.StringTakeCode
public import Stage0.Senke.Ausdruck.Aggregat.Frame.StringExpandCode
public import Stage0.Senke.Ausdruck.Aggregat.Frame.StringEqMixedCode
public import Stage0.Senke.Ausdruck.Aggregat.Kopie
public import Stage0.Senke.Ausdruck.Aggregat.Layout
public import Stage0.Senke.Ausdruck.Aggregat.Encoding
public import Stage0.Senke.Ausdruck.Quant.TransportCode
public meta import Lean.Meta.Tactic.Simp.Attr
@[expose] public section


namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR

variable {D : Deklaration} {L : Lay D}
    before its raw word is compared with an unsigned operand. -/
def mixedCmpC (leftSigned equal : Bool) (d : Nat) : List II :=
  [ci 1 (d + 2) 0 0,
   ci 13 (d + 2) ((if leftSigned then d else d + 1) : Nat) (d + 2),
   ci (if equal then 14 else 27) (d + 3) d (d + 1)] ++
  if leftSigned && !equal then [ci 9 d (d + 2) (d + 3)]
  else [ci 1 (d + 4) 1 0, ci 10 (d + 4) (d + 2) (d + 4), ci 8 d (d + 3) (d + 4)]

/-- Compare each complete scalar domain, with a sign guard when no common raw
    interpretation exists. Both operand programs are evaluated exactly once. -/
def scalarCompareL (equal : Bool) (d : Nat) (l1 h1 l2 h2 : Int)
    (a b : Option (List II × Nat)) : Option (List II × Nat) := do
  let a ← a
  let b ← b
  match scalarOrder l1 h1 l2 h2 with
  | some o => pure (bin2 (if equal then 14 else o) d a b)
  | none =>
    if scalarFits l1 h1 && scalarFits l2 h2 then
      pure (a.1 ++ b.1 ++ mixedCmpC (inW l1 h1) equal d, max (max a.2 b.2) (d + 5))
    else none

/-- One raw interval predicate. Its flag is in `d+1`; the input in `d` is preserved. -/
def engTest (o d : Nat) (lo hi : Int) : List II × Nat :=
  ((wordConstant (d + 1) lo).1 ++ [ci o (d + 1) d (d + 1)] ++
    (wordConstant (d + 2) hi).1 ++
    [ci o (d + 2) (d + 2) d, ci 9 (d + 1) (d + 1) (d + 2)],
   max (wordConstant (d + 1) lo).2 (wordConstant (d + 2) hi).2)

/-- Normalize a scalar interval test in the input's interpretation. Disjoint
    intervals produce a true outside flag after the input has been evaluated. -/
def intervalTestL (d : Nat) (lo hi lo' hi' : Int) : Option (List II × Nat) :=
  if scalarFits lo hi && scalarFits lo' hi' then
    if hi < lo' ∨ hi' < lo then some ([ci 1 (d + 1) 1 0], d + 2)
    else do
      let o ← scalarOrder lo hi lo hi
      pure (engTest o d (max lo lo') (min hi hi'))
  else none

/-- Evaluate the input once, test it, and evaluate the fallback only outside. -/
def engC (d : Nat) (ce ct cb : List II) : List II :=
  ce ++ ct ++ [ci 19 (d + 1) ((16 * (cb.length + 1) : Nat) : Int) 0] ++ cb

def engL (d : Nat) (lo hi lo' hi' : Int) (ce cb : Option (List II × Nat)) : Option (List II × Nat) := do
  let ce ← ce
  let cb ← cb
  let ct ← intervalTestL d lo hi lo' hi'
  if 16 * (cb.1.length + 1) < 2 ^ 31 then
    some (engC d ce.1 ct.1 cb.1, max ce.2 (max ct.2 cb.2))
  else none

/-- Signed magnitude key: strip the sign, multiply by `1 - 2 * sign`.
    The two supplied operand codes evaluate the same pure expression at `d` and `d+3`. -/
def floatKeyL (d : Nat) (a b : Option (List II × Nat)) : Option (List II × Nat) := do
  let a ← a
  let b ← b
  pure (bin2 5 d
    (bin2 12 d (bin2 11 d a ([ci 1 (d+1) 1 0], d+2)) ([ci 1 (d+1) 1 0], d+2))
    (bin2 4 (d+1) ([ci 1 (d+1) 1 0], d+2)
      (bin2 5 (d+2) ([ci 1 (d+2) 2 0], d+3)
        (bin2 13 (d+3) b ([ci 1 (d+4) 0 0], d+5)))))

/-- Compare two signed keys; non-strict order negates the reverse strict order. -/
def floatCmpL (le : Bool) (d : Nat) (a b : Option (List II × Nat)) : Option (List II × Nat) := do
  let a ← a
  let b ← b
  let c := bin2 13 d a b
  pure (if le then bin2 10 d c ([ci 1 (d+1) 1 0], d+2) else c)

/-- Apply the same key transformation to both pure operands. -/
def floatExprL (le : Bool) (d : Nat) (a b : Nat → Option (List II × Nat)) : Option (List II × Nat) :=
  floatCmpL le d (floatKeyL d (a d) (a (d+3)))
    (floatKeyL (d+1) (b (d+1)) (b (d+4)))

/-- A constant ordering key, including its sign in two's complement. -/
def floatConstL (x : GFloat) (d : Nat) : List II × Nat :=
  konstWL 4 (BitVec.ofInt 64 (floatKey x)).toNat d

/-- Outside the inclusive interval: `x < lo || hi < x`. -/
def floatRangeL (d : Nat) (lo hi : Int × Int) (e : Nat → Option (List II × Nat)) : Option (List II × Nat) := do
  let a ← floatKeyL d (e d) (e (d+3))
  let b ← floatKeyL (d+2) (e (d+2)) (e (d+5))
  pure (bin2 9 d (bin2 13 d a (floatConstL (bruch lo) (d+1)))
    (bin2 13 (d+1) (floatConstL (bruch hi) (d+1)) b))

/-- The range of an integer expression lies in 64 bits. -/
def inWE {Λ : List (Res D)} {Γ : Ctx} {lo hi : Int} (_ : Expr D Γ Λ (.int lo hi)) : Bool := inW lo hi
def inUE {Λ : List (Res D)} {Γ : Ctx} {lo hi : Int} (_ : Expr D Γ Λ (.int lo hi)) : Bool := inU lo hi


/-- A shift count below 64. -/
def lt64 {Λ : List (Res D)} {Γ : Ctx} {lo hi : Int} (_ : Expr D Γ Λ (.int lo hi)) : Bool := decide (hi < 64)

/-- The least value of an integer expression lies above `-2^63`. -/
def nichtMin {Λ : List (Res D)} {Γ : Ctx} {lo hi : Int} (_ : Expr D Γ Λ (.int lo hi)) : Bool := decide (-2 ^ 63 < lo)

/-- The address of an element of column `f` of table `t`, its index computed by `ci'` into slot `d`:
    `col + 8 · i` into slot `d`. -/
def slotA (L : Lay D) (t : D.Tab) (f : D.Feld t) (d : Nat) (ci' : List II × Nat) : Option (List II × Nat) :=
  if lit32 (L.col t f) then
    some (ci'.1 ++ [ci 1 (d + 1) 8 0, ci 5 d d (d + 1), ci 1 (d + 1) (L.col t f) 0, ci 3 d d (d + 1)],
      max ci'.2 (d + 2))
  else none

/-- World reads still use a single load until their storage consumer is migrated.
    Admission therefore requires the entire canonical value to occupy one word. -/
def aggregateFits (τ : Ty) : Bool := decide (valueWords τ = 1) && wordCompatB τ

/-- An element of column `f` of table `t`: its address (`slotA`), the word there. -/
def slotC (L : Lay D) (t : D.Tab) (f : D.Feld t) (d : Nat) (ci' : List II × Nat) : Option (List II × Nat) :=
  if aggregateFits (D.typ t f) then
    (slotA L t f d ci').map fun a => (a.1 ++ [ci 15 d d 0], a.2)
  else none

/-- Pack the payload word in `d`: subtract its lower bound, multiply by 256, add the tag. -/
def packSum (d : Nat) (lo : Int) (tag : Nat) (ce : List II × Nat) : List II × Nat :=
  bin2 3 d (bin2 5 d (bin2 4 d ce (wordConstant (d + 1) lo))
    ([ci 1 (d + 1) 256 0], d + 2)) ([ci 1 (d + 1) tag 0], d + 2)

/-- Read a little-endian byte span, one aligned world word per byte. The index code is
    repeated without changing the world. `j` is the byte offset into the span. -/
def readBytesL (L : Lay D) (t : D.Tab) (f : D.Feld t) (idx : Nat → Option (List II × Nat)) :
    Nat → Nat → Nat → Option (List II × Nat)
  | _, 0, d => some ([ci 1 d 0 0], d + 1)
  | j, n + 1, d => do
    let ci' ← idx d
    let head ← slotC L t f d (bin2 3 d ci' ([ci 1 (d + 1) j 0], d + 2))
    let tail ← readBytesL L t f idx (j + 1) n (d + 1)
    pure (bin2 3 d head (bin2 5 (d + 1) tail ([ci 1 (d + 2) 256 0], d + 3)))

/-- Borrow the binder's canonical slot, retaining its previous word above the result. -/
def quantBindC (s d : Nat) (k : Int) (cb : List II) : List II :=
  [ci 2 (d + 1) s 0, ci 1 s k 0] ++ cb ++ [ci 2 s (d + 1) 0, ci 2 d (d + 2) 0]

/-- Finite Boolean fold. Every iteration reuses the same scratch slots. -/
def quantC (all : Bool) (s d : Nat) (cb : List II) : Nat → Nat → List II
  | _, 0 => [ci 1 d (if all then 1 else 0) 0]
  | j, n + 1 => quantC all s d cb (j + 1) n ++ quantBindC s (d + 1) j cb ++
      [ci (if all then 8 else 9) d d (d + 1)]

/-- The code-size bound is checked before materialising the finite fold. -/
def quantL (all : Bool) (s d : Nat) (count : Int) (body : Option (List II × Nat)) : Option (List II × Nat) :=
  if count.toNat = 0 then some ([ci 1 d (if all then 1 else 0) 0], d + 1)
  else do
    let cb ← body
    if count.toNat < 2 ^ 31 ∧ 1 + count.toNat * (cb.1.length + 5) < 2 ^ 31 then
      some (quantC all s d cb.1 0 count.toNat, max cb.2 (d + 4))
    else none

/-- Equality of two recomputable words, with room for both operands. -/
def reachEqL (d : Nat) (a b : Option (List II × Nat)) : Option (List II × Nat) := do
  let ca ← a
  let cb ← b
  pure ((bin2 14 d ca cb).1, max ca.2 (max cb.2 (d + 2)))

/-- Follow an optional-index column. Failed links are tested before the next access.
    Recomputing pure operands avoids keeping a live index across condition code. -/
def reachL (L : Lay D) (t : D.Tab) (f : D.Feld t) (d : Nat) :
    Nat → Option (List II × Nat) → Option (List II × Nat) → Option (List II × Nat)
  | 0, a, b => reachEqL d a b
  | n + 1, a, b =>
    let next := a.bind (slotC L t f d)
    wennL d (reachEqL d a b) (some ([ci 1 d 1 0], d + 1))
      (wennL d (reachEqL d next (some ([ci 1 (d + 1) (-1) 0], d + 2)))
        (some ([ci 1 d 0 0], d + 1)) (reachL L t f d n next b))

/-- Check a conservative bound before constructing the bounded chain code. -/
def reachesL (L : Lay D) (t : D.Tab) (f : D.Feld t) (d : Nat)
    (a b : Option (List II × Nat)) : Option (List II × Nat) := do
  let ca ← a
  let cb ← b
  let n := (D.count t).toNat
  if n < 2 ^ 31 ∧ 16 * (n + 1) * (ca.1.length + cb.1.length + 20 + 6 * (n + 1)) < 2 ^ 31 then
    reachL L t f d n (some ca) (some cb)
  else none

/-- General array selection reserves the entire array before evaluating the
    index and uses the shared physical span transport for the selected value. -/
def arrGetL (τ : Ty) (n d : Nat) (a b : Option (List II × Nat)) : Option (List II × Nat) :=
  if 0 < n ∧ 8 * valueWords τ < 2 ^ 31 then do
    let ca ← a
    let cb ← b
    let ptr := d + valueWords (.arr τ n)
    pure (ca.1 ++ cb.1 ++ selectFrameSpan (valueWords τ) d d ptr (ptr + 1),
      max (max ca.2 cb.2) (ptr + 2))
  else none

/-- Replacing element `i` of an array of more than one element evaluates the array at `d`, the new element and
    the index in the consecutive spans above it, and stores the complete element through the frame pointer. -/
def arrSetL (τ : Ty) (n d : Nat) (a v i : Option (List II × Nat)) : Option (List II × Nat) :=
  if 0 < n ∧ 8 * valueWords τ < 2 ^ 31 then do
    let ca ← a
    let cv ← v
    let ci ← i
    let src := d + valueWords (.arr τ n)
    let ptr := src + valueWords τ
    pure (ca.1 ++ cv.1 ++ ci.1 ++ storeFrameSpan (valueWords τ) d src ptr (ptr + 1),
      max (max (max ca.2 cv.2) ci.2) (ptr + 2))
  else none

end Gabbro.Stage0.Senke
