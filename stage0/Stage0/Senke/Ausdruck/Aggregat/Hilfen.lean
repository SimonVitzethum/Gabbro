/-
  File:      stage0/Stage0/Senke/Ausdruck/Aggregat/Hilfen.lean
  Subject:   The code pieces of the expression lowering (`Ausdruck.lean`): integer range tests, constants, binary
             operations, comparisons, float words, slot and array access, quantifiers. Split out of `Ausdruck.lean`
             unchanged.
-/
module
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
@[expose] public section


namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR

/-- Constructor equations for expression lowering; kept separate from generated recursive equations. -/
register_simp_attr lowE_eqs

variable {D : Deklaration} {L : Lay D}


/-- A range of integers that 64 bits hold. -/
def inW (lo hi : Int) : Bool := decide (-2 ^ 63 ≤ lo) && decide (hi < 2 ^ 63)

/-- An unsigned scalar occupies one word; mixed signed/unsigned intervals are not admitted. -/
def inU (lo hi : Int) : Bool := decide (0 ≤ lo) && decide (hi < 2 ^ 64)

/-- Exact scalar interval in either signed or unsigned interpretation. -/
def scalarFits (lo hi : Int) : Bool := inW lo hi || inU lo hi

/-- Select the interpretation in which both complete scalar intervals fit. -/
def scalarOrder (l1 h1 l2 h2 : Int) : Option Nat :=
  if inW l1 h1 && inW l2 h2 then some 13
  else if inU l1 h1 && inU l2 h2 then some 27 else none

def lit32 (n : Int) : Bool := decide (-2 ^ 31 ≤ n) && decide (n < 2 ^ 31)

def ci (o : Nat) (a b c : Int) : II := ⟨o, a, b, c⟩

/-- `if c then a else b` as a value into slot `d`: the condition, `brz` over the `then` code and its jump. -/
def wennC (d : Nat) (cc ca cb : List II) : List II :=
  cc ++ [ci 19 d ((16 * (ca.length + 2) : Nat) : Int) 0] ++ ca ++ [ci 18 ((16 * (cb.length + 1) : Nat) : Int) 0 0] ++ cb

/-- The code of `if c then a else b` from the codes of its parts. -/
def wennL (d : Nat) (cc ca cb : Option (List II × Nat)) : Option (List II × Nat) := do
  let cc ← cc
  let ca ← ca
  let cb ← cb
  if 16 * (ca.1.length + cb.1.length + 2) < 2 ^ 31 then
    some (wennC d cc.1 ca.1 cb.1, max cc.2 (max ca.2 cb.2))
  else none

/-- `d := op d (d+1)` after `a` into `d` and `b` into `d+1`. -/
def bin2 (o : Nat) (d : Nat) (ca : List II × Nat) (cb : List II × Nat) : List II × Nat :=
  (ca.1 ++ cb.1 ++ [ci o d d (d + 1)], max ca.2 cb.2)

/-- A word operation whose operands have already been lowered; reserve its two operand slots explicitly. -/
def wordL (o d : Nat) (a b : Option (List II × Nat)) : Option (List II × Nat) := do
  let a ← a
  let b ← b
  pure ((bin2 o d a b).1, max (max a.2 b.2) (d + 2))

/-- A word operation against a small constant. -/
def wordK (o d : Nat) (a : Option (List II × Nat)) (k : Int) : Option (List II × Nat) :=
  wordL o d a (some ([ci 1 (d + 1) k 0], d + 2))

/-- A short string's byte at zero, or zero at every other signed index. -/
def strGetL (d : Nat) (s i : Option (List II × Nat)) : Option (List II × Nat) :=
  wennL d (wordK 14 d i 0) (wordK 8 d s 255) (some ([ci 1 d 0 0], d + 1))

/-- The raw magnitude field, without the sign bit. -/
def floatMag (a : GFloat) : Nat := a.bexp * 4503599627370496 + a.frac

/-- The mathematical ordering key; both signed zeros have key zero. -/
def floatKey (a : GFloat) : Int := if a.sign then -(floatMag a : Int) else floatMag a

/-- Build an arbitrary word from base-65536 digits, using only signed immediate fields. -/
def konstWL : Nat → Nat → Nat → List II × Nat
  | 0, _, d => ([ci 1 d 0 0], d + 1)
  | k + 1, n, d =>
    bin2 3 d (bin2 5 d (konstWL k (n / 65536) d)
      ([ci 1 (d + 1) 65536 0], d + 2))
      ([ci 1 (d + 1) (n % 65536) 0], d + 2)

/-- Materialize one canonical word, retaining the single-instruction scalar path. -/
def wordConst (w : Runner.W) (d : Nat) : List II × Nat :=
  if lit32 w.toInt then ([ci 1 d w.toInt 0], d + 1) else konstWL 4 w.toNat d

/-- Materialize any complete encoded value. Increasing destination order permits
    each word generator to reuse the following, not-yet-live word as scratch. -/
def constWords : List Runner.W → Nat → List II × Nat
  | [], d => ([], d)
  | w :: ws, d =>
    let head := wordConst w d
    let tail := constWords ws (d + 1)
    (head.1 ++ tail.1, max head.2 tail.2)

theorem wordConst_top (w : Runner.W) (d : Nat) : d < (wordConst w d).2 := by
  unfold wordConst
  split
  · simp
  · simp only [konstWL, bin2]; omega

theorem wordConst_bound (w : Runner.W) (d : Nat) : (wordConst w d).2 ≤ d + 2 := by
  unfold wordConst
  split
  · simp
  · simp only [konstWL, bin2]; omega

theorem constWords_bound (words : List Runner.W) (d : Nat) :
    (constWords words d).2 ≤ d + words.length + 1 := by
  induction words generalizing d with
  | nil => simp [constWords]
  | cons w ws ih =>
    have head := wordConst_bound w d
    have tail := ih (d + 1)
    simp only [constWords, List.length_cons]
    omega

theorem constWords_span (words : List Runner.W) (d : Nat) :
    d + words.length ≤ (constWords words d).2 := by
  induction words generalizing d with
  | nil => exact Nat.le_refl _
  | cons w ws ih =>
    have tail := ih (d + 1)
    simp only [constWords, List.length_cons]
    omega

/-- Fill new integer limbs using the preceding canonical source limb's sign.
    Nonnegative source intervals need no runtime sign test. -/
def integerExtensionL (lo : Int) (extra base : Nat) : Option (List II × Nat) :=
  let zeros := constWords (List.replicate extra 0) base
  if lo < 0 then
    wennL base (some ([ci 1 (base + 1) 0 0, ci 13 base (base - 1 : Nat) (base + 1)], base + 2))
      (some (constWords (List.replicate extra (BitVec.ofInt 64 (-1))) base)) (some zeros)
  else some zeros

/-- Reuse a complete integer prefix and extend its sign when its declared
    destination needs more limbs. The sign flag occupies the first new limb,
    which is dead until the selected constant extension writes it. -/
def resizeIntegerL (lo hi lo' hi' : Int) (d : Nat)
    (child : Option (List II × Nat)) : Option (List II × Nat) := do
  let child ← child
  let source := integerWords lo hi
  let target := integerWords lo' hi'
  if target ≤ source then
    pure (child.1, max child.2 (d + target))
  else
    let extension ← integerExtensionL lo (target - source) (d + source)
    pure (child.1 ++ extension.1, max child.2 extension.2)

/-- One scalar word, retaining the single-instruction path for small constants. -/
def wordConstant (d : Nat) (n : Int) : List II × Nat :=
  if lit32 n then ([ci 1 d n 0], d + 1)
  else konstWL 4 (BitVec.ofInt 64 n).toNat d

/-- Compare previously evaluated scalar operands, guarding the signed operand
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
