/-
  File:      stage0/Stage0/Senke/Ausdruck.lean
  Subject:   The lowering of stage 0 (`PLAN-SELF-HOSTING.md` §2.1.4), part 1: expressions of machine G into `S0IR`.

  Lexical values occupy complete canonical frame spans, shared with parameters,
  returns and world cells. lowE computes the whole value at d and reports a scratch
  ceiling; every accepted path is connected to lowE_ok. Scalars use the first
  canonical word through Enc only where WordCompatible permits that view.

  Packed sums retain their eight-bit tag and 56-bit integer offset. Other sums
  materialize a separate tag, the selected payload's complete encoding and zero
  padding up to the largest payload span. Float/reference validity follows the
  selected payload recursively. Strings, products, arrays and wide integers use
  the same encoding and transport as all other aggregate values.

  Byte reads capture the start once and emit the <=8-byte kernel per canonical limb.
  Float values retain their binary64 representation; function pointers contain
  the checked layout's code address, never a numerical source pointer conversion.

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
public import Stage0.Senke.Ausdruck.Aggregat.Frame.String.Code
public import Stage0.Senke.Ausdruck.Aggregat.Frame.CompareCode
public import Stage0.Senke.Ausdruck.Aggregat.Frame.StringGetCode
public import Stage0.Senke.Ausdruck.Aggregat.Frame.StringTakeCode
public import Stage0.Senke.Ausdruck.Aggregat.Frame.StringExpandCode
public import Stage0.Senke.Ausdruck.Aggregat.Frame.StringEqMixedCode
public import Stage0.Senke.Ausdruck.Aggregat.Kopie
public import Stage0.Senke.Ausdruck.Aggregat.Layout
public import Stage0.Senke.Ausdruck.Aggregat.Werte.Encoding
public import Stage0.Senke.Welt.Rahmen
public import Stage0.Senke.Ausdruck.FrameCache
public import Stage0.Senke.Ausdruck.Aggregat.Hilfen
public import Stage0.Senke.Ausdruck.Aggregat.Stored.Code
public import Stage0.Senke.Ausdruck.Aggregat.Prod.ProdArgs
public import Stage0.Senke.Ausdruck.Aggregat.Werte.Sum.Code
public import Stage0.Senke.Ausdruck.Aggregat.WideInt.Place
public import Stage0.Senke.Ausdruck.Aggregat.WideInt.BuiltinCode
public import Stage0.Senke.Ausdruck.Quant.TransportCode
public import Stage0.Senke.Ausdruck.Quant.CountCode
public import Stage0.Senke.Ausdruck.Wort.BytesCode
@[expose] public section


namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR

variable {D : Deklaration} {L : Lay D}

mutual
/-- Compute `e` into slot `d`, returning the first untouched slot. Ordinary G evaluation
    uses its current world as the old world. `currentOld = false` is the ensures fallback:
    it refuses old reads that must instead go through the checked entry-snapshot emitter. -/
@[specialize lookup] def lowEWith (lookup : FrameLookup) (L : Lay D) {Λ : List (Res D)} {Γ : Ctx} {τ : Ty} (e : Expr D Γ Λ τ) (d : Nat) (reserved : Nat := 0) (currentOld : Bool := true) (frame : FrameCache Γ) : Option (List II × Nat) :=
  match Γ, τ, e, d with
  | _, _, .lit n, d => if lit32 n then some ([ci 1 d n 0], d + 1) else
      some (constWords (encodeWords L (.int n n) ⟨n, by omega, by omega⟩) d)
  | _, _, .tru, d => some ([ci 1 d 1 0], d + 1)
  | _, _, .fls, d => some ([ci 1 d 0 0], d + 1)
  | _, τ, .var x, d => some (copyWords (valueWords τ) d (lookup.slot frame x reserved), d + valueWords τ)
  | _, _, .widen (lo := lo) (hi := hi) (lo' := lo') (hi' := hi') _ _ e, d =>
    resizeIntegerL lo hi lo' hi' d (lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) e d)
  | _, _, @Expr.add _ _ _ l1 h1 l2 h2 a b, d =>
    if valueWords (.int (l1 + l2) (h1 + h2)) = 1 then
      do let ca ← lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) a d; let cb ← lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) b (d + 1); pure (bin2 3 d ca cb)
    else wideAddL l1 h1 l2 h2 (l1 + l2) (h1 + h2) d (lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) a) (lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) b)
  | _, _, @Expr.sub _ _ _ l1 h1 l2 h2 a b, d =>
    if valueWords (.int (l1 - h2) (h1 - l2)) = 1 then
      do let ca ← lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) a d; let cb ← lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) b (d + 1); pure (bin2 4 d ca cb)
    else wideSubL l1 h1 l2 h2 (l1 - h2) (h1 - l2) d (lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) a) (lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) b)
  | _, _, @Expr.mul _ _ _ l1 h1 l2 h2 a b, d =>
    if valueWords (.int (imin (imin (l1*l2) (l1*h2)) (imin (h1*l2) (h1*h2)))
      (imax (imax (l1*l2) (l1*h2)) (imax (h1*l2) (h1*h2)))) = 1 then
      do let ca ← lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) a d; let cb ← lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) b (d + 1); pure (bin2 5 d ca cb)
    else wideMulL l1 h1 l2 h2 (imin (imin (l1*l2) (l1*h2)) (imin (h1*l2) (h1*h2)))
      (imax (imax (l1*l2) (l1*h2)) (imax (h1*l2) (h1*h2))) d (lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) a) (lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) b)
  | _, _, @Expr.neg _ _ _ lo hi a, d =>
    if valueWords (.int (-hi) (-lo)) = 1 then do let ca ← lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) a (d + 1); pure (bin2 4 d ([ci 1 d 0 0], d + 1) ca)
    else wideNegL lo hi (-hi) (-lo) d (lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) a)
  | _, _, .not a, d => do let ca ← lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) a d; pure (bin2 10 d ca ([ci 1 (d + 1) 1 0], d + 2))
  | _, _, @Expr.le _ _ _ l1 h1 l2 h2 a b, d =>
    if scalarFits l1 h1 && scalarFits l2 h2 then do
      let c ← scalarCompareL false d l2 h2 l1 h1
        (lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) b d) (lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) a (d + 1))
      pure (bin2 10 d c ([ci 1 (d + 1) 1 0], d + 2))
    else wideLeL l1 h1 l2 h2 d (lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) a) (lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) b)
  | _, _, @Expr.lt _ _ _ l1 h1 l2 h2 a b, d =>
    if scalarFits l1 h1 && scalarFits l2 h2 then
      scalarCompareL false d l1 h1 l2 h2 (lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) a d) (lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) b (d + 1))
    else wideLtL l1 h1 l2 h2 d (lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) a) (lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) b)
  | _, _, @Expr.eq _ _ _ l1 h1 l2 h2 a b, d =>
    if scalarFits l1 h1 && scalarFits l2 h2 then
      scalarCompareL true d l1 h1 l2 h2 (lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) a d) (lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) b (d + 1))
    else wideEqL l1 h1 l2 h2 d (lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) a) (lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) b)
  | _, _, .fllt a b, d => floatExprL false d (lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) a) (lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) b)
  | _, _, .flle a b, d => floatExprL true d (lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) b) (lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) a)
  | _, _, .and a b, d => do let ca ← lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) a d; let cb ← lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) b (d + 1); pure (bin2 8 d ca cb)
  | _, _, .or a b, d => do let ca ← lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) a d; let cb ← lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) b (d + 1); pure (bin2 9 d ca cb)
  | _, _, .div (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) _ _ a b, d =>
    if inUE a && inUE b then do let ca ← lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) a d; let cb ← lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) b (d + 1); pure (bin2 25 d ca cb)
    else wideDivL l1 h1 l2 h2 0 h1 d (lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) a) (lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) b)
  | _, _, .rem (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) _ _ a b, d =>
    if inUE a && inUE b then do let ca ← lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) a d; let cb ← lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) b (d + 1); pure (bin2 26 d ca cb)
    else wideRemL l1 h1 l2 h2 0 (h2 - 1) d (lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) a) (lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) b)
  | _, _, .sdiv (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) _ a b, d =>
    if inWE a && inWE b && nichtMin a then do
      let ca ← lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) a d; let cb ← lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) b (d + 1); pure (bin2 6 d ca cb)
    else wideSdivL l1 h1 l2 h2 (-(betragMax l1 h1)) (betragMax l1 h1) d
      (lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) a) (lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) b)
  | _, _, .srem (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) _ a b, d =>
    if inWE a && inWE b && nichtMin a then do
      let ca ← lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) a d; let cb ← lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) b (d + 1); pure (bin2 7 d ca cb)
    else wideSremL l1 h1 l2 h2 (-(betragMax l2 h2 - 1)) (betragMax l2 h2 - 1) d
      (lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) a) (lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) b)
  | _, _, .band (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) _ _ a b, d =>
    if inUE a && inUE b then do let ca ← lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) a d; let cb ← lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) b (d + 1); pure (bin2 8 d ca cb)
    else wideBitL 8 l1 h1 l2 h2 0 h1 d (lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) a) (lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) b)
  | _, _, .bor (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) w _ _ _ _ a b, d =>
    if inUE a && inUE b then resizeIntegerL 0 (2 ^ 64 - 1) 0 (2 ^ w - 1) d
      (do let ca ← lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) a d; let cb ← lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) b (d + 1); pure (bin2 9 d ca cb))
    else wideBitL 9 l1 h1 l2 h2 0 (2 ^ w - 1) d (lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) a) (lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) b)
  | _, _, .bxor (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) w _ _ _ _ a b, d =>
    if inUE a && inUE b then resizeIntegerL 0 (2 ^ 64 - 1) 0 (2 ^ w - 1) d
      (do let ca ← lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) a d; let cb ← lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) b (d + 1); pure (bin2 10 d ca cb))
    else wideBitL 10 l1 h1 l2 h2 0 (2 ^ w - 1) d (lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) a) (lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) b)
  | _, _, .shl (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) _ _ _ _ _ a b, d =>
    if decide (valueWords (.int 0 (h1 * 2 ^ h2.toNat)) = 1) && inWE b && lt64 b then
      do let ca ← lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) a d; let cb ← lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) b (d + 1); pure (bin2 11 d ca cb)
    else wideShlL l1 h1 l2 h2 0 (h1 * 2 ^ h2.toNat) d (lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) a) (lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) b)
  | _, _, .shr (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) _ _ _ _ _ a b, d =>
    if inUE a && inUE b && lt64 b then do
      let ca ← lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) a d; let cb ← lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) b (d + 1); pure (bin2 12 d ca cb)
    else wideShrL l1 h1 l2 h2 0 h1 d (lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) a) (lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) b)
  | _, _, .arrNil, d => some ([ci 1 d 0 0], d + 1)
  | _, _, @Expr.arrCons _ _ _ τ n a rest, d =>
    if n = 0 then lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) a d else do
      let head ← lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) a d
      let tail ← lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) rest (d + valueWords τ)
      pure (head.1 ++ tail.1, max (max head.2 tail.2) (d + valueWords (.arr τ (n + 1))))
  | _, _, @Expr.arrGet _ _ _ τ n a i, d => if storedExpr a then
      arrReadL τ n d (lowStorageWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) a (d + valueWords τ))
        (lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) i (d + valueWords τ + 1))
    else if n = 1 then lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) a d else
    arrGetL τ n d (lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) a d)
      (lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) i (d + valueWords (.arr τ n)))
  | _, _, @Expr.arrSet _ _ _ τ n a i v, d => if n = 1 then lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) v d else
    arrSetL τ n d (lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) a d)
      (lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) v (d + valueWords (.arr τ n)))
      (lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) i (d + valueWords (.arr τ n) + valueWords τ))
  | _, _, @Expr.strLit _ n _ _ bs hb, d =>
    some (constWords (encodeWords L (.str n) ⟨bs, hb⟩) d)
  | _, _, @Expr.strLen _ _ _ n s, d =>
    if n ≤ 1 then wordK 12 d (lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) s d) 8 else
      (lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) s d).map fun p => (p.1, max p.2 (d + valueWords (.str n)))
  | _, _, @Expr.strCat _ _ _ n m s t, d =>
    if n + m ≤ 1 then (if n = 0 then lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) t d else lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) s d) else
      strCatSpanL n m d (lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) s (d + (n + m + 1)))
        (lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) t (d + (n + m + 1) + (stringCapacity n + 1)))
  | _, _, @Expr.strGet _ _ _ n lo hi s i, d =>
    if n ≤ 1 ∧ inW lo hi = true then strGetL d (lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) s d) (lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) i d)
    else if scalarFits lo hi = true then
      strGetWideL n d (lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) s d) (lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) i (d + n + 2))
    else none
  | _, _, @Expr.strEq _ _ _ n m s t, d =>
    if n ≤ 1 ∧ m ≤ 1 then wordL 14 d (lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) s d) (lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) t (d + 1))
    else if n ≤ 1 ∨ m ≤ 1 then
      strEqMixedL n m d (lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) s d) (lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) t (d + valueWords (.str n)))
    else strEqLongL n m d (lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) s d) (lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) t (d + (n + 1)))
  | _, _, @Expr.strLt _ _ _ n m s t, d =>
    if n ≤ 1 ∧ m ≤ 1 then wordL 13 d (lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) s d) (lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) t (d + 1)) else
      strLtSpanL n m d (lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) s (d + 1))
        (lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) t (d + 1 + (stringCapacity n + 1)))
  | _, _, @Expr.strWeit _ _ _ n m s, d =>
    if n ≤ 1 ∧ m ≤ 1 then (if m = 0 then some ([ci 1 d 0 0], d + 1) else lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) s d)
    else if 2 ≤ n ∧ n ≤ m then
      (lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) s d).map fun a =>
        (a.1 ++ (constWords (List.replicate (m - n) 0) (d + n + 1)).1,
          max a.2 (max (constWords (List.replicate (m - n) 0) (d + n + 1)).2 (d + m + 1)))
    else if n ≤ 1 then
      strExpandL n m d (lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) s d) (constWords (List.replicate (m - 1) 0) (d + 2))
    else strTakeL n m d (lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) s d)
  | _, _, .none n, d => some (constWords (encodeWords L (.opt n) none) d)
  | _, _, @Expr.some _ _ _ n e, d =>
    if n ≤ 2 ^ 63 then lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) e d else do
      let child ← lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) e (d + 1)
      pure ([ci 1 d 1 0] ++ child.1, max child.2 (d + valueWords (.opt n)))
  | _, _, @Expr.istSome _ _ _ n e, d =>
    if decide (n ≤ 2 ^ 63) then do
      let ce ← lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) e d
      pure (bin2 10 d (bin2 14 d ce ([ci 1 (d + 1) (-1) 0], d + 2)) ([ci 1 (d + 1) 1 0], d + 2))
    else lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) e d
  | _, _, .case cs i nutz, d =>
    if sumFits cs then lowNWith (frame := FrameCache.ofCtx _) (currentOld := currentOld) specLookup L (reserved := reserved) i.val nutz d else
      sumSpanL cs i d (lowPayloadWith (frame := FrameCache.ofCtx _) (currentOld := currentOld) specLookup L (reserved := reserved) nutz
        (d + integerWords 0 (cs.length - 1)))
  | _, _, .why n r, d => some (constWords (encodeWords L (.why n) r) d)
  | _, _, .fnref f _ _, d => if lit32 (L.fa f) then some ([ci 1 d (L.fa f) 0], d + 1) else none
  | _, _, .ptrOf .., d => some ([ci 1 d 0 0], d + 1)
  | _, _, .glob g _, d => globalValueC L g d
  | _, _, .slot t f i _, d => do
    let ci' ← lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) i (d + valueWords (D.typ t f)); slotValueC L t f d ci'
  | _, _, .thru _ t _ f i _, d => do
    let ci' ← lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) i (d + valueWords (D.typ t f)); slotValueC L t f d ci'
  | _, _, .thruOwn _ t _ f i _ _ _ _ _ _, d => do
    let ci' ← lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) i (d + valueWords (D.typ t f)); slotValueC L t f d ci'
  | _, _, @Expr.eng _ _ _ lo hi e lo' hi' b, d =>
    if scalarFits lo hi && scalarFits lo' hi' then
      engL d lo hi lo' hi' (lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) e d) (lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) b d)
    else wideEngL lo hi lo' hi' d (lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) e) (lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) b)
  | _, _, .getBytes t f _ n i _ _ _, d =>
    readBytesWideL L t f (lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) i) n d
  | Γ, _, .forallSlots t body _, d => quantL true (lookup.free frame reserved) d (D.count t) (lowEWith (frame := lookup.push frame _) (currentOld := currentOld) lookup L (reserved := reserved) body (d + 3))
  | Γ, _, .existsSlots t body _, d => quantL false (lookup.free frame reserved) d (D.count t) (lowEWith (frame := lookup.push frame _) (currentOld := currentOld) lookup L (reserved := reserved) body (d + 3))
  | Γ, _, .count n body, d => countL (lookup.free frame reserved) d n (lowEWith (frame := lookup.push frame _) (currentOld := currentOld) lookup L (reserved := reserved) body (d + 3))
  | _, _, .prod _ args, d => prodL d (lowProdArgsWith (frame := FrameCache.ofCtx _) (currentOld := currentOld) specLookup L (reserved := reserved) args d)
  | _, _, .prodGet (r := name) v i, d => prodGetL (name := name) i d (lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) v d)
  | _, _, .prodSet (r := name) (fs := fields) v i e, d => prodSetL (name := name) i d (lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) v d) (lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) e (d + valueWords (.prod name fields)))
  | _, _, .reaches t f _ a b _, d => reachesL L t f d (lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) a d) (lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) b (d + 1))
  | _, _, .refEq a b, d => wordL 14 d (lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) a d) (lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) b (d + 1))
  | _, _, .slotRef r t _ _ f _, d => do
    let cr ← lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) r (d + valueWords (D.typ t f)); slotValueC L t f d cr
  | _, _, .wenn c a b, d => wennL d (lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) c d) (lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) a d) (lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) b d)
  | _, _, .intBuiltin1 op a, d => BitBuiltin.unary op (lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) a) d
  | _, _, .intBuiltin2 op a b, d => intBuiltin2L op d
      (lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) a) (lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) b)
  | _, _, .oldG g _, d => if currentOld then globalValueC L g d else none
  | _, _, .oldS t f i _, d => if currentOld then do
      let index ← lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) i (d + valueWords (D.typ t f))
      slotValueC L t f d index
    else none
termination_by structural e

/-- Compute only the physical address of a stored value. This traversal is used
    exclusively by aggregate reads; ordinary value lowering keeps its copy semantics. -/
@[specialize lookup] def lowStorageWith (lookup : FrameLookup) (L : Lay D) {Λ : List (Res D)} {Γ : Ctx} {τ : Ty}
    (e : Expr D Γ Λ τ) (d : Nat) (reserved : Nat := 0) (currentOld : Bool := true) (frame : FrameCache Γ) :
    Option (List II × Nat) :=
  match e with
  | .var x => some ([ci 17 d (lookup.slot frame x reserved) 0], d + 1)
  | .glob g _ => if L.ga g < 2 ^ 31 then some ([ci 1 d (L.ga g) 0], d + 1) else none
  | .slot t f i _ | .thru _ t _ f i _ | .thruOwn _ t _ f i _ _ _ _ _ _ => do
    let index ← lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) i d
    cellAddressC L t f d index
  | .slotRef r t _ _ f _ => do
    let index ← lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) r d
    cellAddressC L t f d index
  | _ => none
termination_by structural e

/-- Traverse a complete sum payload directly in the canonical expression family. The caller
    owns its tag and padding; an absent payload emits no words at the supplied payload base. -/
@[specialize lookup] def lowPayloadWith (lookup : FrameLookup) (L : Lay D) {Λ : List (Res D)} {Γ : Ctx} {c : Option Ty}
    (e : NutzlastExpr D Γ Λ c) (d : Nat) (reserved : Nat := 0) (currentOld : Bool := true) (frame : FrameCache Γ) :
    Option (List II × Nat) :=
  match c, e with
  | _, .empty => some ([], d)
  | _, .val child => lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) child d
termination_by structural e

/-- Lower a tagged payload through the same expression recursion. -/
@[specialize lookup] def lowNWith (lookup : FrameLookup) (L : Lay D) {Λ : List (Res D)} {Γ : Ctx} (tag : Nat) {c : Option Ty} (e : NutzlastExpr D Γ Λ c) (d : Nat) (reserved : Nat := 0) (currentOld : Bool := true) (frame : FrameCache Γ) : Option (List II × Nat) :=
  match c, e with
  | _, .empty => some ([ci 1 d tag 0], d + 1)
  | some (.int lo _), .val e => do
      let ce ← lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) e d
      pure (packSum d lo tag ce)
  | _, .val _ => none
termination_by structural e

/-- Traverse the actual argument spine in the expression's mutual recursion. -/
@[specialize lookup] def lowProdArgsWith (lookup : FrameLookup) (L : Lay D) {Λ : List (Res D)} {Γ : Ctx} {fs : List Ty}
    (args : Args D Γ Λ fs) (d : Nat) (reserved : Nat := 0) (currentOld : Bool := true) (frame : FrameCache Γ) : Option (List II × Nat) :=
  match fs, args with
  | _, .nil => some ([], d)
  | _, @Args.cons _ _ _ τ _ e rest => do
    let head ← lowEWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) e d
    let tail ← lowProdArgsWith (frame := frame) (currentOld := currentOld) lookup L (reserved := reserved) rest (d + valueWords τ)
    pure (head.1 ++ tail.1, max head.2 tail.2)
termination_by structural args
end

/-- The specification uses canonical context lookup. Its constructor equations
    remain definitionally equal to the original complete-value traversal. -/
@[inline] def lowE (L : Lay D) {Λ : List (Res D)} {Γ : Ctx} {τ : Ty}
    (e : Expr D Γ Λ τ) (d : Nat) (reserved : Nat := 0) (currentOld : Bool := true) :
    Option (List II × Nat) :=
  lowEWith specLookup L e d reserved currentOld (FrameCache.ofCtx Γ)

/-- Storage addresses use the same canonical frame lookup as expression values. -/
@[inline] def lowStorage (L : Lay D) {Λ : List (Res D)} {Γ : Ctx} {τ : Ty}
    (e : Expr D Γ Λ τ) (d : Nat) (reserved : Nat := 0) (currentOld : Bool := true) :
    Option (List II × Nat) :=
  lowStorageWith specLookup L e d reserved currentOld (FrameCache.ofCtx Γ)

@[inline] def lowPayload (L : Lay D) {Λ : List (Res D)} {Γ : Ctx} {c : Option Ty}
    (e : NutzlastExpr D Γ Λ c) (d : Nat) (reserved : Nat := 0) (currentOld : Bool := true) :
    Option (List II × Nat) :=
  lowPayloadWith specLookup L e d reserved currentOld (FrameCache.ofCtx Γ)

@[inline] def lowN (L : Lay D) {Λ : List (Res D)} {Γ : Ctx} (tag : Nat) {c : Option Ty}
    (e : NutzlastExpr D Γ Λ c) (d : Nat) (reserved : Nat := 0) (currentOld : Bool := true) :
    Option (List II × Nat) :=
  lowNWith specLookup L tag e d reserved currentOld (FrameCache.ofCtx Γ)

@[inline] def lowProdArgs (L : Lay D) {Λ : List (Res D)} {Γ : Ctx} {fs : List Ty}
    (args : Args D Γ Λ fs) (d : Nat) (reserved : Nat := 0) (currentOld : Bool := true) :
    Option (List II × Nat) :=
  lowProdArgsWith specLookup L args d reserved currentOld (FrameCache.ofCtx Γ)

/-- The structural compiler traversal is the parameterized product traversal. -/
theorem lowProdArgs_eq_prodArgsL {Λ : List (Res D)} {Γ : Ctx} {reserved : Nat} {currentOld : Bool} :
    ∀ {fs} (args : Args D Γ Λ fs) d,
    lowProdArgs (currentOld := currentOld) L (reserved := reserved) args d = prodArgsL (lowE (currentOld := currentOld) L (reserved := reserved)) args d
  | _, .nil, _ => rfl
  | _, @Args.cons _ _ _ τ fs e rest, d => by
    change (do
      let head ← lowE (currentOld := currentOld) L (reserved := reserved) e d
      let tail ← lowProdArgs (currentOld := currentOld) L (reserved := reserved) rest (d + valueWords τ)
      pure (head.1 ++ tail.1, max head.2 tail.2)) = _
    rw [lowProdArgs_eq_prodArgsL rest]
    rfl

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
  | .fl _ _, v, w => w = v.x.hwToBits.toBitVec
  | .ptr _, _, w => w = 0
  | _, _, _ => False

/-- The variables of `ρ` are in their slots of the frame at `fp`. -/
def EnvAt (L : Lay D) (m : Runner.Mem) (fp : Runner.W) {Γ : Ctx} (ρ : Env D Γ) (reserved : Nat := 0) : Prop :=
  ∀ (τ : Ty) (x : Var Γ τ), ValueAt L m fp (vslot x reserved) τ (ρ.get x)

end Gabbro.Stage0.Senke
