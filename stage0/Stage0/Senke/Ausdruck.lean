/-
  File:      stage0/Stage0/Senke/Ausdruck.lean
  Subject:   The lowering of stage 0 (`PLAN-SELF-HOSTING.md` §2.1.4), part 1: expressions of machine G into `S0IR`.

  A variable of the context `Γ` lives in a frame slot, counted from the bottom of `Γ` after the frame's first
  slots (`vslot`, `FB`), so a `bind` adds the slot `frei Γ` and keeps the others. An integer is its 64-bit two's complement, a Boolean 0 or 1
  (`Enc`). `lowE L e d` computes `e` into slot `d`, using the slots above `d` as scratch; it answers the code and the
  first slot it does not touch. A form outside the fragment, an integer type outside 64 bits where the lowering
  compares, or a literal outside signed/unsigned 64 bits is refused (`none`); wide integers and the other forms follow.

  A float occupies its IEEE-754 binary64 bit pattern. Its encoding also requires well-formed exponent and
  fraction fields; finiteness and the declared range are already properties of G's value type.

  A function pointer is the code address `L.fa f`. The layout is explicit in every value and storage encoding;
  `FunSpec.addr` ties those words to the callee code addresses. This reuses the IR's slot-based call target
  without a second dispatch mechanism. Function references outside the literal range are refused.

  Empty arrays use zero; singleton arrays reuse their element word recursively. Strings with maximum zero
  or one use zero for empty and 256 + byte otherwise. Larger aggregates are refused at constructors and reads,
  including variables, globals and table cells. No allocation, layout or call-ABI change is needed.

  C13 arithmetic shares complete-value wide kernels and masks wrapping results to the declared width.
  Count borrows and restores the ordinary quantifier binder slot. Scans, popcount, rotations and byte swaps
  compose the same wide kernels; their generic proofs identify the named Zahl functions.
-/
module
public import Lean.Meta.Tactic.Simp.RegisterCommand
public import Grammatik.Kern.Semantik.Semantik
public import Runner.IR.Rahmen
public import Stage0.Senke.Welt.Lay
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
public import Stage0.Senke.Welt.Rahmen
public import Stage0.Senke.Ausdruck.Aggregat.Hilfen
public import Stage0.Senke.Ausdruck.Aggregat.WideInt.Place
public import Stage0.Senke.Ausdruck.Aggregat.WideInt.BuiltinCode
public import Stage0.Senke.Ausdruck.Quant.TransportCode
public import Stage0.Senke.Ausdruck.Quant.CountCode
@[expose] public section


namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR

variable {D : Deklaration} {L : Lay D}

mutual
/-- The code computing
 `e` into slot `d`, and the first slot from which on nothing is touched. -/
def lowE (L : Lay D) {Λ : List (Res D)} {Γ : Ctx} {τ : Ty} (e : Expr D Γ Λ τ) (d : Nat) (reserved : Nat := 0) : Option (List II × Nat) :=
  match Γ, τ, e, d with
  | _, _, .lit n, d => if lit32 n then some ([ci 1 d n 0], d + 1) else
      some (constWords (encodeWords L (.int n n) ⟨n, by omega, by omega⟩) d)
  | _, _, .tru, d => some ([ci 1 d 1 0], d + 1)
  | _, _, .fls, d => some ([ci 1 d 0 0], d + 1)
  | _, τ, .var x, d => some (copyWords (valueWords τ) d (vslot x reserved), d + valueWords τ)
  | _, _, .widen (lo := lo) (hi := hi) (lo' := lo') (hi' := hi') _ _ e, d =>
    resizeIntegerL lo hi lo' hi' d (lowE L (reserved := reserved) e d)
  | _, _, @Expr.add _ _ _ l1 h1 l2 h2 a b, d =>
    if valueWords (.int (l1 + l2) (h1 + h2)) = 1 then
      do let ca ← lowE L (reserved := reserved) a d; let cb ← lowE L (reserved := reserved) b (d + 1); pure (bin2 3 d ca cb)
    else wideAddL l1 h1 l2 h2 (l1 + l2) (h1 + h2) d (lowE L (reserved := reserved) a) (lowE L (reserved := reserved) b)
  | _, _, @Expr.sub _ _ _ l1 h1 l2 h2 a b, d =>
    if valueWords (.int (l1 - h2) (h1 - l2)) = 1 then
      do let ca ← lowE L (reserved := reserved) a d; let cb ← lowE L (reserved := reserved) b (d + 1); pure (bin2 4 d ca cb)
    else wideSubL l1 h1 l2 h2 (l1 - h2) (h1 - l2) d (lowE L (reserved := reserved) a) (lowE L (reserved := reserved) b)
  | _, _, @Expr.mul _ _ _ l1 h1 l2 h2 a b, d =>
    if valueWords (.int (imin (imin (l1*l2) (l1*h2)) (imin (h1*l2) (h1*h2)))
      (imax (imax (l1*l2) (l1*h2)) (imax (h1*l2) (h1*h2)))) = 1 then
      do let ca ← lowE L (reserved := reserved) a d; let cb ← lowE L (reserved := reserved) b (d + 1); pure (bin2 5 d ca cb)
    else wideMulL l1 h1 l2 h2 (imin (imin (l1*l2) (l1*h2)) (imin (h1*l2) (h1*h2)))
      (imax (imax (l1*l2) (l1*h2)) (imax (h1*l2) (h1*h2))) d (lowE L (reserved := reserved) a) (lowE L (reserved := reserved) b)
  | _, _, @Expr.neg _ _ _ lo hi a, d =>
    if valueWords (.int (-hi) (-lo)) = 1 then do let ca ← lowE L (reserved := reserved) a (d + 1); pure (bin2 4 d ([ci 1 d 0 0], d + 1) ca)
    else wideNegL lo hi (-hi) (-lo) d (lowE L (reserved := reserved) a)
  | _, _, .not a, d => do let ca ← lowE L (reserved := reserved) a d; pure (bin2 10 d ca ([ci 1 (d + 1) 1 0], d + 2))
  | _, _, @Expr.le _ _ _ l1 h1 l2 h2 a b, d =>
    if scalarFits l1 h1 && scalarFits l2 h2 then do
      let c ← scalarCompareL false d l2 h2 l1 h1
        (lowE L (reserved := reserved) b d) (lowE L (reserved := reserved) a (d + 1))
      pure (bin2 10 d c ([ci 1 (d + 1) 1 0], d + 2))
    else wideLeL l1 h1 l2 h2 d (lowE L (reserved := reserved) a) (lowE L (reserved := reserved) b)
  | _, _, @Expr.lt _ _ _ l1 h1 l2 h2 a b, d =>
    if scalarFits l1 h1 && scalarFits l2 h2 then
      scalarCompareL false d l1 h1 l2 h2 (lowE L (reserved := reserved) a d) (lowE L (reserved := reserved) b (d + 1))
    else wideLtL l1 h1 l2 h2 d (lowE L (reserved := reserved) a) (lowE L (reserved := reserved) b)
  | _, _, @Expr.eq _ _ _ l1 h1 l2 h2 a b, d =>
    if scalarFits l1 h1 && scalarFits l2 h2 then
      scalarCompareL true d l1 h1 l2 h2 (lowE L (reserved := reserved) a d) (lowE L (reserved := reserved) b (d + 1))
    else wideEqL l1 h1 l2 h2 d (lowE L (reserved := reserved) a) (lowE L (reserved := reserved) b)
  | _, _, .fllt a b, d => floatExprL false d (lowE L (reserved := reserved) a) (lowE L (reserved := reserved) b)
  | _, _, .flle a b, d => floatExprL true d (lowE L (reserved := reserved) b) (lowE L (reserved := reserved) a)
  | _, _, .and a b, d => do let ca ← lowE L (reserved := reserved) a d; let cb ← lowE L (reserved := reserved) b (d + 1); pure (bin2 8 d ca cb)
  | _, _, .or a b, d => do let ca ← lowE L (reserved := reserved) a d; let cb ← lowE L (reserved := reserved) b (d + 1); pure (bin2 9 d ca cb)
  | _, _, .div (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) _ _ a b, d =>
    if inUE a && inUE b then do let ca ← lowE L (reserved := reserved) a d; let cb ← lowE L (reserved := reserved) b (d + 1); pure (bin2 25 d ca cb)
    else wideDivL l1 h1 l2 h2 0 h1 d (lowE L (reserved := reserved) a) (lowE L (reserved := reserved) b)
  | _, _, .rem (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) _ _ a b, d =>
    if inUE a && inUE b then do let ca ← lowE L (reserved := reserved) a d; let cb ← lowE L (reserved := reserved) b (d + 1); pure (bin2 26 d ca cb)
    else wideRemL l1 h1 l2 h2 0 (h2 - 1) d (lowE L (reserved := reserved) a) (lowE L (reserved := reserved) b)
  | _, _, .sdiv (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) _ a b, d =>
    if inWE a && inWE b && nichtMin a then do
      let ca ← lowE L (reserved := reserved) a d; let cb ← lowE L (reserved := reserved) b (d + 1); pure (bin2 6 d ca cb)
    else wideSdivL l1 h1 l2 h2 (-(betragMax l1 h1)) (betragMax l1 h1) d
      (lowE L (reserved := reserved) a) (lowE L (reserved := reserved) b)
  | _, _, .srem (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) _ a b, d =>
    if inWE a && inWE b && nichtMin a then do
      let ca ← lowE L (reserved := reserved) a d; let cb ← lowE L (reserved := reserved) b (d + 1); pure (bin2 7 d ca cb)
    else wideSremL l1 h1 l2 h2 (-(betragMax l2 h2 - 1)) (betragMax l2 h2 - 1) d
      (lowE L (reserved := reserved) a) (lowE L (reserved := reserved) b)
  | _, _, .band (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) _ _ a b, d =>
    if inUE a && inUE b then do let ca ← lowE L (reserved := reserved) a d; let cb ← lowE L (reserved := reserved) b (d + 1); pure (bin2 8 d ca cb)
    else wideBitL 8 l1 h1 l2 h2 0 h1 d (lowE L (reserved := reserved) a) (lowE L (reserved := reserved) b)
  | _, _, .bor (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) w _ _ _ _ a b, d =>
    if inUE a && inUE b then resizeIntegerL 0 (2 ^ 64 - 1) 0 (2 ^ w - 1) d
      (do let ca ← lowE L (reserved := reserved) a d; let cb ← lowE L (reserved := reserved) b (d + 1); pure (bin2 9 d ca cb))
    else wideBitL 9 l1 h1 l2 h2 0 (2 ^ w - 1) d (lowE L (reserved := reserved) a) (lowE L (reserved := reserved) b)
  | _, _, .bxor (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) w _ _ _ _ a b, d =>
    if inUE a && inUE b then resizeIntegerL 0 (2 ^ 64 - 1) 0 (2 ^ w - 1) d
      (do let ca ← lowE L (reserved := reserved) a d; let cb ← lowE L (reserved := reserved) b (d + 1); pure (bin2 10 d ca cb))
    else wideBitL 10 l1 h1 l2 h2 0 (2 ^ w - 1) d (lowE L (reserved := reserved) a) (lowE L (reserved := reserved) b)
  | _, _, .shl (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) _ _ _ _ _ a b, d =>
    if decide (valueWords (.int 0 (h1 * 2 ^ h2.toNat)) = 1) && inWE b && lt64 b then
      do let ca ← lowE L (reserved := reserved) a d; let cb ← lowE L (reserved := reserved) b (d + 1); pure (bin2 11 d ca cb)
    else wideShlL l1 h1 l2 h2 0 (h1 * 2 ^ h2.toNat) d (lowE L (reserved := reserved) a) (lowE L (reserved := reserved) b)
  | _, _, .shr (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) _ _ _ _ _ a b, d =>
    if inUE a && inUE b && lt64 b then do
      let ca ← lowE L (reserved := reserved) a d; let cb ← lowE L (reserved := reserved) b (d + 1); pure (bin2 12 d ca cb)
    else wideShrL l1 h1 l2 h2 0 h1 d (lowE L (reserved := reserved) a) (lowE L (reserved := reserved) b)
  | _, _, .arrNil, d => some ([ci 1 d 0 0], d + 1)
  | _, _, @Expr.arrCons _ _ _ τ n a rest, d =>
    if n = 0 then lowE L (reserved := reserved) a d else do
      let head ← lowE L (reserved := reserved) a d
      let tail ← lowE L (reserved := reserved) rest (d + valueWords τ)
      pure (head.1 ++ tail.1, max (max head.2 tail.2) (d + valueWords (.arr τ (n + 1))))
  | _, _, @Expr.arrGet _ _ _ τ n a i, d => if n = 1 then lowE L (reserved := reserved) a d else
    arrGetL τ n d (lowE L (reserved := reserved) a d)
      (lowE L (reserved := reserved) i (d + valueWords (.arr τ n)))
  | _, _, @Expr.arrSet _ _ _ τ n a i v, d => if n = 1 then lowE L (reserved := reserved) v d else
    arrSetL τ n d (lowE L (reserved := reserved) a d)
      (lowE L (reserved := reserved) v (d + valueWords (.arr τ n)))
      (lowE L (reserved := reserved) i (d + valueWords (.arr τ n) + valueWords τ))
  | _, _, @Expr.strLit _ n _ _ bs hb, d =>
    some (constWords (encodeWords L (.str n) ⟨bs, hb⟩) d)
  | _, _, @Expr.strLen _ _ _ n s, d =>
    if n ≤ 1 then wordK 12 d (lowE L (reserved := reserved) s d) 8 else
      (lowE L (reserved := reserved) s d).map fun p => (p.1, max p.2 (d + valueWords (.str n)))
  | _, _, @Expr.strCat _ _ _ n m s t, d =>
    if n + m ≤ 1 then (if n = 0 then lowE L (reserved := reserved) t d else lowE L (reserved := reserved) s d) else none
  | _, _, @Expr.strGet _ _ _ n lo hi s i, d =>
    if n ≤ 1 ∧ inW lo hi = true then strGetL d (lowE L (reserved := reserved) s d) (lowE L (reserved := reserved) i d)
    else if scalarFits lo hi = true then
      strGetWideL n d (lowE L (reserved := reserved) s d) (lowE L (reserved := reserved) i (d + n + 2))
    else none
  | _, _, @Expr.strEq _ _ _ n m s t, d =>
    if n ≤ 1 ∧ m ≤ 1 then wordL 14 d (lowE L (reserved := reserved) s d) (lowE L (reserved := reserved) t (d + 1))
    else if n ≤ 1 ∨ m ≤ 1 then
      strEqMixedL n m d (lowE L (reserved := reserved) s d) (lowE L (reserved := reserved) t (d + valueWords (.str n)))
    else strEqLongL n m d (lowE L (reserved := reserved) s d) (lowE L (reserved := reserved) t (d + (n + 1)))
  | _, _, @Expr.strLt _ _ _ n m s t, d =>
    if n ≤ 1 ∧ m ≤ 1 then wordL 13 d (lowE L (reserved := reserved) s d) (lowE L (reserved := reserved) t (d + 1)) else none
  | _, _, @Expr.strWeit _ _ _ n m s, d =>
    if n ≤ 1 ∧ m ≤ 1 then (if m = 0 then some ([ci 1 d 0 0], d + 1) else lowE L (reserved := reserved) s d)
    else if 2 ≤ n ∧ n ≤ m then
      (lowE L (reserved := reserved) s d).map fun a =>
        (a.1 ++ (constWords (List.replicate (m - n) 0) (d + n + 1)).1,
          max a.2 (max (constWords (List.replicate (m - n) 0) (d + n + 1)).2 (d + m + 1)))
    else if n ≤ 1 then
      strExpandL n m d (lowE L (reserved := reserved) s d) (constWords (List.replicate (m - 1) 0) (d + 2))
    else strTakeL n m d (lowE L (reserved := reserved) s d)
  | _, _, .none n, d => some (constWords (encodeWords L (.opt n) none) d)
  | _, _, @Expr.some _ _ _ n e, d =>
    if n ≤ 2 ^ 63 then lowE L (reserved := reserved) e d else do
      let child ← lowE L (reserved := reserved) e (d + 1)
      pure ([ci 1 d 1 0] ++ child.1, max child.2 (d + valueWords (.opt n)))
  | _, _, @Expr.istSome _ _ _ n e, d =>
    if decide (n ≤ 2 ^ 63) then do
      let ce ← lowE L (reserved := reserved) e d
      pure (bin2 10 d (bin2 14 d ce ([ci 1 (d + 1) (-1) 0], d + 2)) ([ci 1 (d + 1) 1 0], d + 2))
    else none
  | _, _, .case cs i nutz, d => if sumFits cs then lowN L (reserved := reserved) i.val nutz d else none
  | _, _, .why n r, d => some (constWords (encodeWords L (.why n) r) d)
  | _, _, .fnref f _ _, d => if lit32 (L.fa f) then some ([ci 1 d (L.fa f) 0], d + 1) else none
  | _, _, .ptrOf .., d => some ([ci 1 d 0 0], d + 1)
  | _, _, .glob g _, d => globalValueC L g d
  | _, _, .slot t f i _, d => do
    let ci' ← lowE L (reserved := reserved) i (d + valueWords (D.typ t f)); slotValueC L t f d ci'
  | _, _, .thru _ t _ f i _, d => do
    let ci' ← lowE L (reserved := reserved) i (d + valueWords (D.typ t f)); slotValueC L t f d ci'
  | _, _, @Expr.eng _ _ _ lo hi e lo' hi' b, d =>
    if scalarFits lo hi && scalarFits lo' hi' then
      engL d lo hi lo' hi' (lowE L (reserved := reserved) e d) (lowE L (reserved := reserved) b d)
    else wideEngL lo hi lo' hi' d (lowE L (reserved := reserved) e) (lowE L (reserved := reserved) b)
  | _, _, .getBytes t f _ n i _ _ _, d =>
    if n ≤ 8 then readBytesL L t f (lowE L (reserved := reserved) i) 0 n d else none
  | Γ, _, .forallSlots t body _, d => quantL true (frei Γ reserved) d (D.count t) (lowE L (reserved := reserved) body (d + 3))
  | Γ, _, .existsSlots t body _, d => quantL false (frei Γ reserved) d (D.count t) (lowE L (reserved := reserved) body (d + 3))
  | Γ, _, .count n body, d => countL (frei Γ reserved) d n (lowE L (reserved := reserved) body (d + 3))
  | _, _, .reaches t f _ a b _, d => reachesL L t f d (lowE L (reserved := reserved) a d) (lowE L (reserved := reserved) b (d + 1))
  | _, _, .refEq a b, d => wordL 14 d (lowE L (reserved := reserved) a d) (lowE L (reserved := reserved) b (d + 1))
  | _, _, .slotRef r t _ _ f _, d => do
    let cr ← lowE L (reserved := reserved) r (d + valueWords (D.typ t f)); slotValueC L t f d cr
  | _, _, .wenn c a b, d => wennL d (lowE L (reserved := reserved) c d) (lowE L (reserved := reserved) a d) (lowE L (reserved := reserved) b d)
  | _, _, .intBuiltin1 op a, d => BitBuiltin.unary op (lowE L (reserved := reserved) a) d
  | _, _, .intBuiltin2 op a b, d => intBuiltin2L op d
      (lowE L (reserved := reserved) a) (lowE L (reserved := reserved) b)
  | _, _, .oldG .., _ | _, _, .oldS .., _ => none


/-- Lower a tagged payload through the same expression recursion. -/
def lowN (L : Lay D) {Λ : List (Res D)} {Γ : Ctx} (tag : Nat) {c : Option (Int × Int)} (e : NutzlastExpr D Γ Λ c) (d : Nat) (reserved : Nat := 0) : Option (List II × Nat) :=
  match c, e, d with
  | _, .empty, d => some ([ci 1 d tag 0], d + 1)
  | some (lo, _), .num e, d => do
      let ce ← lowE L (reserved := reserved) e d
      pure (packSum d lo tag ce)
end

/-! ## Values in words -/

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
  | .ptr _, _, w => w = 0
  | _, _, _ => False

/-- The variables of `ρ` are in their slots of the frame at `fp`. -/
def EnvAt (L : Lay D) (m : Runner.Mem) (fp : Runner.W) {Γ : Ctx} (ρ : Env D Γ) (reserved : Nat := 0) : Prop :=
  ∀ (τ : Ty) (x : Var Γ τ), ValueAt L m fp (vslot x reserved) τ (ρ.get x)

end Gabbro.Stage0.Senke
