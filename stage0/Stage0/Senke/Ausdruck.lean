/-
  File:      stage0/Stage0/Senke/Ausdruck.lean
  Subject:   The lowering of stage 0 (`PLAN-SELF-HOSTING.md` §2.1.4), part 1: expressions of machine G into `S0IR`.

  A variable of the context `Γ` lives in a frame slot, counted from the bottom of `Γ` after the frame's first
  slots (`vslot`, `FB`), so a `bind` adds the slot `frei Γ` and keeps the others. An integer is its 64-bit two's complement, a Boolean 0 or 1
  (`Enc`). `lowE L e d` computes `e` into slot `d`, using the slots above `d` as scratch; it answers the code and the
  first slot it does not touch. A form outside the fragment, an integer type outside 64 bits where the lowering
  compares, or a literal outside 32 bits is refused (`none`); wide integers and the other forms follow.

  A float occupies its IEEE-754 binary64 bit pattern. Its encoding also requires well-formed exponent and
  fraction fields; finiteness and the declared range are already properties of G's value type.

  A function pointer is the code address `L.fa f`. The layout is explicit in every value and storage encoding;
  `FunSpec.addr` ties those words to the callee code addresses. This reuses the IR's slot-based call target
  without a second dispatch mechanism. Function references outside the literal range are refused.

  Empty arrays use zero; singleton arrays reuse their element word recursively. Strings with maximum zero
  or one use zero for empty and 256 + byte otherwise. Larger aggregates are refused at constructors and reads,
  including variables, globals and table cells. No allocation, layout or call-ABI change is needed.
-/
import Lean.Meta.Tactic.Simp.RegisterCommand
import Grammatik.Kern.Semantik.Semantik
import Runner.IR.Rahmen
import Stage0.Senke.Welt.Lay
import Stage0.Senke.Ausdruck.Aggregat.Wert
import Stage0.Senke.Ausdruck.Aggregat.Kopie

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR

/-- Constructor equations for expression lowering; kept separate from generated recursive equations. -/
register_simp_attr lowE_eqs

variable {D : Deklaration} {L : Lay D}

/-- The position of a variable, counted from the head of the context. -/
def Var.idx : {Γ : Ctx} → {τ : Ty} → Var Γ τ → Nat
  | _, _, .here => 0
  | _, _, .there x => Var.idx x + 1

/-- The first slots of every frame: 0 the return `pc` and 1 the caller's `fp` (both written by `call`), 2 the
    remaining call depth (G's `fuel`; a call with depth 0 stops with `abstieg`),
    and 3 is reserved for an entry snapshot. The variables follow. -/
def FB : Nat := 4

/-- The first free slot of a frame whose variables are `Γ`. -/
def frei (Γ : Ctx) (reserved : Nat := 0) : Nat := FB + reserved + Γ.length

/-- The frame slot of a variable: counted from the bottom of the context, after the frame's first slots. -/
def vslot {Γ : Ctx} {τ : Ty} (x : Var Γ τ) (reserved : Nat := 0) : Nat :=
  FB + reserved + (Γ.length - 1 - Var.idx x)

/-- Reserve a prefix after the ABI header consistently for bindings and scratch. -/
theorem frei_reserved (Γ : Ctx) (reserved : Nat) :
    FB + reserved ≤ frei Γ reserved := by simp [frei]

theorem vslot_reserved {Γ : Ctx} {τ : Ty} (x : Var Γ τ) (reserved : Nat) :
    FB + reserved ≤ vslot x reserved := by simp [vslot]

/-- Extending the context allocates exactly its first free unreserved word. -/
theorem vslot_here_reserved (Γ : Ctx) (τ : Ty) (reserved : Nat) :
    vslot (Var.here : Var (τ :: Γ) τ) reserved = frei Γ reserved := by
  simp [vslot, frei, Var.idx]

/-- A range of integers that 64 bits hold. -/
def inW (lo hi : Int) : Bool := decide (-2 ^ 63 ≤ lo) && decide (hi < 2 ^ 63)

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

/-- Test whether the word in `d` lies outside the signed interval; the flag is in `d+1`. -/
def engTest (d : Nat) (lo hi : Int) : List II :=
  [ci 1 (d + 1) lo 0, ci 13 (d + 1) d (d + 1), ci 1 (d + 2) hi 0,
   ci 13 (d + 2) (d + 2) d, ci 9 (d + 1) (d + 1) (d + 2)]

/-- Evaluate once, test the interval and skip the fallback when the value already fits. -/
def engC (d : Nat) (lo hi : Int) (ce cb : List II) : List II :=
  ce ++ engTest d lo hi ++ [ci 19 (d + 1) ((16 * (cb.length + 1) : Nat) : Int) 0] ++ cb

/-- Bounds must fit the signed literal fields; all compared values must fit a signed word. -/
def engL (d : Nat) (lo hi lo' hi' : Int) (ce cb : Option (List II × Nat)) : Option (List II × Nat) := do
  if inW lo hi && lit32 lo' && lit32 hi' then
    let ce ← ce
    let cb ← cb
    if 16 * (cb.1.length + 1) < 2 ^ 31 then
      some (engC d lo' hi' ce.1 cb.1, max ce.2 (max cb.2 (d + 3)))
    else none
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

/-- The aggregate representations admitted by frames and reads, recursively through singleton arrays.
    Empty arrays need no representation for their element type. Other scalar fragments keep their own checks. -/
def aggregateFits : Ty → Bool
  | .arr τ n => if n = 0 then true else decide (n = 1) && aggregateFits τ
  | .str n => decide (n ≤ 1)
  | _ => true

/-- An element of column `f` of table `t`: its address (`slotA`), the word there. -/
def slotC (L : Lay D) (t : D.Tab) (f : D.Feld t) (d : Nat) (ci' : List II × Nat) : Option (List II × Nat) :=
  if aggregateFits (D.typ t f) then
    (slotA L t f d ci').map fun a => (a.1 ++ [ci 15 d d 0], a.2)
  else none

/-- A sum fits one word: eight tag bits and a 56-bit unsigned payload offset. -/
def sumFits (cs : List (Option (Int × Int))) : Bool :=
  decide (cs.length ≤ 256) && cs.all (fun c => match c with
    | none => true
    | some (lo, hi) => decide (hi - lo < 2 ^ 56))

/-- The payload's distance from the lower bound; a bare arm has offset zero. -/
def sumOff : (c : Option (Int × Int)) → Nutzlast c → Nat
  | none, _ => 0
  | some (lo, _), v => (v.n - lo).toNat

/-- The representation shared by frames, tables and globals. -/
def sumN {cs : List (Option (Int × Int))} (v : Wert D (.sum cs)) : Nat :=
  v.1.val + 256 * sumOff (cs.get v.1) v.2

/-- Pack the payload word in `d`: subtract its lower bound, multiply by 256, add the tag. -/
def packSum (d : Nat) (lo : Int) (tag : Nat) (ce : List II × Nat) : List II × Nat :=
  bin2 3 d (bin2 5 d (bin2 4 d ce ([ci 1 (d + 1) lo 0], d + 2))
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

mutual
/-- The code computing `e` into slot `d`, and the first slot from which on nothing is touched. -/
def lowE (L : Lay D) {Λ : List (Res D)} {Γ : Ctx} {τ : Ty} (e : Expr D Γ Λ τ) (d : Nat) (reserved : Nat := 0) : Option (List II × Nat) :=
  match Γ, τ, e, d with
  | _, _, .lit n, d => if lit32 n then some ([ci 1 d n 0], d + 1) else none
  | _, _, .tru, d => some ([ci 1 d 1 0], d + 1)
  | _, _, .fls, d => some ([ci 1 d 0 0], d + 1)
  | _, τ, .var x, d => if aggregateFits τ then some (copyWords 1 d (vslot x reserved), d + 1) else none
  | _, _, .widen _ _ e, d => lowE L (reserved := reserved) e d
  | _, _, .add a b, d => do let ca ← lowE L (reserved := reserved) a d; let cb ← lowE L (reserved := reserved) b (d + 1); pure (bin2 3 d ca cb)
  | _, _, .sub a b, d => do let ca ← lowE L (reserved := reserved) a d; let cb ← lowE L (reserved := reserved) b (d + 1); pure (bin2 4 d ca cb)
  | _, _, .mul a b, d => do let ca ← lowE L (reserved := reserved) a d; let cb ← lowE L (reserved := reserved) b (d + 1); pure (bin2 5 d ca cb)
  | _, _, .neg a, d => do let ca ← lowE L (reserved := reserved) a (d + 1); pure (bin2 4 d ([ci 1 d 0 0], d + 1) ca)
  | _, _, .not a, d => do let ca ← lowE L (reserved := reserved) a d; pure (bin2 10 d ca ([ci 1 (d + 1) 1 0], d + 2))
  | _, _, @Expr.le _ _ _ l1 h1 l2 h2 a b, d =>
    if inW l1 h1 && inW l2 h2 then do
      let cb ← lowE L (reserved := reserved) b d; let ca ← lowE L (reserved := reserved) a (d + 1)
      pure (bin2 10 d (bin2 13 d cb ca) ([ci 1 (d + 1) 1 0], d + 2))
    else none
  | _, _, @Expr.lt _ _ _ l1 h1 l2 h2 a b, d =>
    if inW l1 h1 && inW l2 h2 then do
      let ca ← lowE L (reserved := reserved) a d; let cb ← lowE L (reserved := reserved) b (d + 1); pure (bin2 13 d ca cb)
    else none
  | _, _, @Expr.eq _ _ _ l1 h1 l2 h2 a b, d =>
    if inW l1 h1 && inW l2 h2 then do
      let ca ← lowE L (reserved := reserved) a d; let cb ← lowE L (reserved := reserved) b (d + 1); pure (bin2 14 d ca cb)
    else none
  | _, _, .fllt a b, d => floatExprL false d (lowE L (reserved := reserved) a) (lowE L (reserved := reserved) b)
  | _, _, .flle a b, d => floatExprL true d (lowE L (reserved := reserved) b) (lowE L (reserved := reserved) a)
  | _, _, .and a b, d => do let ca ← lowE L (reserved := reserved) a d; let cb ← lowE L (reserved := reserved) b (d + 1); pure (bin2 8 d ca cb)
  | _, _, .or a b, d => do let ca ← lowE L (reserved := reserved) a d; let cb ← lowE L (reserved := reserved) b (d + 1); pure (bin2 9 d ca cb)
  | _, _, .div _ _ a b, d =>
    if inWE a && inWE b then do let ca ← lowE L (reserved := reserved) a d; let cb ← lowE L (reserved := reserved) b (d + 1); pure (bin2 6 d ca cb) else none
  | _, _, .rem _ _ a b, d =>
    if inWE a && inWE b then do let ca ← lowE L (reserved := reserved) a d; let cb ← lowE L (reserved := reserved) b (d + 1); pure (bin2 7 d ca cb) else none
  | _, _, .sdiv _ a b, d =>
    if inWE a && inWE b && nichtMin a then do
      let ca ← lowE L (reserved := reserved) a d; let cb ← lowE L (reserved := reserved) b (d + 1); pure (bin2 6 d ca cb)
    else none
  | _, _, .srem _ a b, d =>
    if inWE a && inWE b && nichtMin a then do
      let ca ← lowE L (reserved := reserved) a d; let cb ← lowE L (reserved := reserved) b (d + 1); pure (bin2 7 d ca cb)
    else none
  | _, _, .band _ _ a b, d =>
    if inWE a && inWE b then do let ca ← lowE L (reserved := reserved) a d; let cb ← lowE L (reserved := reserved) b (d + 1); pure (bin2 8 d ca cb) else none
  | _, _, .bor _ _ _ _ _ a b, d =>
    if inWE a && inWE b then do let ca ← lowE L (reserved := reserved) a d; let cb ← lowE L (reserved := reserved) b (d + 1); pure (bin2 9 d ca cb) else none
  | _, _, .bxor _ _ _ _ _ a b, d =>
    if inWE a && inWE b then do let ca ← lowE L (reserved := reserved) a d; let cb ← lowE L (reserved := reserved) b (d + 1); pure (bin2 10 d ca cb) else none
  | _, _, .shl _ _ _ _ _ a b, d =>
    if inWE b && lt64 b then do let ca ← lowE L (reserved := reserved) a d; let cb ← lowE L (reserved := reserved) b (d + 1); pure (bin2 11 d ca cb) else none
  | _, _, .shr _ _ _ _ _ a b, d =>
    if inWE a && inWE b && lt64 b then do
      let ca ← lowE L (reserved := reserved) a d; let cb ← lowE L (reserved := reserved) b (d + 1); pure (bin2 12 d ca cb)
    else none
  | _, _, .arrNil, d => some ([ci 1 d 0 0], d + 1)
  | _, _, @Expr.arrCons _ _ _ _ n a _, d => if n = 0 then lowE L (reserved := reserved) a d else none
  | _, _, @Expr.arrGet _ _ _ _ n a _, d => if n = 1 then lowE L (reserved := reserved) a d else none
  | _, _, @Expr.arrSet _ _ _ _ n _ _ v, d => if n = 1 then lowE L (reserved := reserved) v d else none
  | _, _, @Expr.strLit _ n _ _ bs _, d =>
    if n ≤ 1 then some ([ci 1 d (strN bs) 0], d + 1) else none
  | _, _, @Expr.strLen _ _ _ n s, d =>
    if n ≤ 1 then wordK 12 d (lowE L (reserved := reserved) s d) 8 else none
  | _, _, @Expr.strCat _ _ _ n m s t, d =>
    if n + m ≤ 1 then (if n = 0 then lowE L (reserved := reserved) t d else lowE L (reserved := reserved) s d) else none
  | _, _, @Expr.strGet _ _ _ n lo hi s i, d =>
    if n ≤ 1 ∧ inW lo hi = true then strGetL d (lowE L (reserved := reserved) s d) (lowE L (reserved := reserved) i d) else none
  | _, _, @Expr.strEq _ _ _ n m s t, d =>
    if n ≤ 1 ∧ m ≤ 1 then wordL 14 d (lowE L (reserved := reserved) s d) (lowE L (reserved := reserved) t (d + 1)) else none
  | _, _, @Expr.strLt _ _ _ n m s t, d =>
    if n ≤ 1 ∧ m ≤ 1 then wordL 13 d (lowE L (reserved := reserved) s d) (lowE L (reserved := reserved) t (d + 1)) else none
  | _, _, @Expr.strWeit _ _ _ n m s, d =>
    if n ≤ 1 ∧ m ≤ 1 then (if m = 0 then some ([ci 1 d 0 0], d + 1) else lowE L (reserved := reserved) s d) else none
  | _, _, .none _, d => some ([ci 1 d (-1) 0], d + 1)
  | _, _, .some e, d => lowE L (reserved := reserved) e d
  | _, _, @Expr.istSome _ _ _ n e, d =>
    if decide (n ≤ 2 ^ 63) then do
      let ce ← lowE L (reserved := reserved) e d
      pure (bin2 10 d (bin2 14 d ce ([ci 1 (d + 1) (-1) 0], d + 2)) ([ci 1 (d + 1) 1 0], d + 2))
    else none
  | _, _, .case cs i nutz, d => if sumFits cs then lowN L (reserved := reserved) i.val nutz d else none
  | _, _, .why n r, d => if decide (n < 2 ^ 31) then some ([ci 1 d (r.val : Int) 0], d + 1) else none
  | _, _, .fnref f _ _, d => if lit32 (L.fa f) then some ([ci 1 d (L.fa f) 0], d + 1) else none
  | _, _, .ptrOf .., d => some ([ci 1 d 0 0], d + 1)
  | _, _, .glob g _, d => if lit32 (L.ga g) && aggregateFits (D.gtyp g) then some ([ci 1 d (L.ga g) 0, ci 15 d d 0], d + 1) else none
  | _, _, .slot t f i _, d => do let ci' ← lowE L (reserved := reserved) i d; slotC L t f d ci'
  | _, _, .thru _ t _ f i _, d => do let ci' ← lowE L (reserved := reserved) i d; slotC L t f d ci'
  | _, _, @Expr.eng _ _ _ lo hi e lo' hi' b, d => engL d lo hi lo' hi' (lowE L (reserved := reserved) e d) (lowE L (reserved := reserved) b d)
  | _, _, .getBytes t f _ n i _ _ _, d =>
    if n ≤ 8 then readBytesL L t f (lowE L (reserved := reserved) i) 0 n d else none
  | Γ, _, .forallSlots t body _, d => quantL true (frei Γ reserved) d (D.count t) (lowE L (reserved := reserved) body (d + 3))
  | Γ, _, .existsSlots t body _, d => quantL false (frei Γ reserved) d (D.count t) (lowE L (reserved := reserved) body (d + 3))
  | _, _, .reaches t f _ a b _, d => reachesL L t f d (lowE L (reserved := reserved) a d) (lowE L (reserved := reserved) b (d + 1))
  | _, _, .refEq a b, d => wordL 14 d (lowE L (reserved := reserved) a d) (lowE L (reserved := reserved) b (d + 1))
  | _, _, .slotRef r t _ _ f _, d => do let cr ← lowE L (reserved := reserved) r d; slotC L t f d cr
  | _, _, .wenn c a b, d => wennL d (lowE L (reserved := reserved) c d) (lowE L (reserved := reserved) a d) (lowE L (reserved := reserved) b d)
  | _, _, _, _ => none


/-- Lower a tagged payload through the same expression recursion. -/
def lowN (L : Lay D) {Λ : List (Res D)} {Γ : Ctx} (tag : Nat) {c : Option (Int × Int)} (e : NutzlastExpr D Γ Λ c) (d : Nat) (reserved : Nat := 0) : Option (List II × Nat) :=
  match c, e, d with
  | _, .empty, d => some ([ci 1 d tag 0], d + 1)
  | some (lo, _), .num e, d => if lit32 lo then do
      let ce ← lowE L (reserved := reserved) e d
      pure (packSum d lo tag ce)
    else none
end

/-! ## Values in words -/

/-- The number of an option: `-1` for absent, the index otherwise. -/
def optN {n : Int} : Option (Zahl 0 (n - 1)) → Int
  | Option.none => -1
  | Option.some k => k.n

/-- `w` is the word of the value `v` of type `τ`. -/
def Enc (L : Lay D) : (τ : Ty) → Wert D τ → Runner.W → Prop
  | .int _ _, v, w => w = BitVec.ofInt 64 v.n
  | .bool, v, w => w = (if wahr? (D := D) v = true then 1 else 0)
  | .opt _, v, w => w = BitVec.ofInt 64 (optN v)
  | .why _, v, w => w = BitVec.ofNat 64 (Fin.val (n := _) v)
  | .ref n, v, w => w = BitVec.ofNat 64 v.zelle ∧ v.zelle < 2 ^ 64 ∧
      ∃ t, D.tabNr n = some t ∧ D.offen t = true ∧ (v.zelle : Int) < L.count t
  | .fnptr _, v, w => w = BitVec.ofNat 64 (L.fa v.1)
  | .sum cs, v, w => sumFits cs = true ∧ w = BitVec.ofNat 64 (sumN v)
  | .arr τ n, v, w => match n with
    | 0 => w = 0
    | 1 => Enc L τ (v ⟨0, by decide⟩) w
    | _ => False
  | .str n, v, w => n ≤ 1 ∧ w = BitVec.ofNat 64 (strN v.1)
  | .fl _ _, v, w => Gleitkomma.wf Gleitkomma.f64 v.x ∧
      w = BitVec.ofNat 64 (Gleitkomma.zuBits Gleitkomma.f64 v.x)
  | .ptr _ _, _, _ => True
  | _, _, _ => False

/-- The variables of `ρ` are in their slots of the frame at `fp`. -/
def EnvAt (L : Lay D) (m : Runner.Mem) (fp : Runner.W) {Γ : Ctx} (ρ : Env D Γ) (reserved : Nat := 0) : Prop :=
  ∀ (τ : Ty) (x : Var Γ τ), ∃ w, m.rd64 (slot fp (BitVec.ofNat 64 (vslot x reserved))) = some w ∧ Enc L τ (ρ.get x) w

end Gabbro.Stage0.Senke
