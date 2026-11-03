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
public import Stage0.Senke.Ausdruck.Aggregat.Werte.Encoding
public import Stage0.Senke.Ausdruck.Quant.TransportCode
public meta import Lean.Meta.Tactic.Simp.Attr
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


end Gabbro.Stage0.Senke
