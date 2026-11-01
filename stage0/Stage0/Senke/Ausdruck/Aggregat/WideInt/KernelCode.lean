/-
  File:      stage0/Stage0/Senke/Ausdruck/Aggregat/WideInt/KernelCode.lean
  Subject:   The code of the multiword integer kernels, below every proof.

  Straight-line limb code over frame slots: carry chains (`wideAddC`), products (`wideMulC`), bit operations
  (`wideBitC`), comparisons (`wideLtC`, `wideEqC`), negation, shifts by a runtime count, unsigned and signed
  division, in-place extension and the narrowing test. The execution theorems of these programs live next to
  their limb arithmetic in `Arithmetik/Wide/*`; the definitions are here so that the expression lowering
  (`lowE`) can emit them without importing any of those proofs.
-/
import Stage0.Senke.Ausdruck.Aggregat.Hilfen

namespace Gabbro.Stage0.Senke
open Runner.IR

/-- Instructions over natural slot numbers. -/
abbrev cn (o a b c : Nat) : II := ci o a b c

/-- One limb: `tb := B ^ m`, `A := A + tb + c`, the new carry from both partial additions. -/
def addLimbC (A B m c t : Nat) : List II :=
  [cn 10 t B m, cn 3 (t + 1) A t, cn 27 (t + 2) (t + 1) A, cn 3 (t + 3) (t + 1) c,
   cn 27 (t + 4) (t + 3) (t + 1), cn 2 A (t + 3) 0, cn 9 c (t + 2) (t + 4)]

def addChain : Nat → Nat → Nat → Nat → Nat → Nat → List II
  | 0, _, _, _, _, _ => []
  | n + 1, a, b, m, c, t => addLimbC a b m c t ++ addChain n (a + 1) (b + 1) m c t

/-- Add (`mask = 0`, `carry = 0`) or subtract (`mask = -1`, `carry = 1`). -/
def wideAddC (k a : Nat) (mask carry : Int) : List II :=
  [ci 1 (a + 2 * k : Nat) mask 0, ci 1 (a + 2 * k + 1 : Nat) carry 0] ++
    addChain k a (a + k) (a + 2 * k) (a + 2 * k + 1) (a + 2 * k + 2)

def bitChain (o : Nat) : Nat → Nat → Nat → List II
  | 0, _, _ => []
  | n + 1, A, B => cn o A A B :: bitChain o n (A + 1) (B + 1)

def wideBitC (o k a : Nat) : List II := bitChain o k a (a + k)

/-- Read the sign bit of the top limb into slot `a`. -/
def signTail (n a : Nat) : List II :=
  [ci 1 (a + 2 * (n + 1) : Nat) 63 0, cn 12 a (a + n) (a + 2 * (n + 1))]

def wideLtC (n a : Nat) : List II := wideAddC (n + 1) a (-1) 1 ++ signTail n a

/-- OR the limbs `j .. j+n-1` into limb zero. -/
def orChain : Nat → Nat → Nat → List II
  | 0, _, _ => []
  | n + 1, a, j => cn 9 a a (a + j) :: orChain n a (j + 1)

def eqTail (n a : Nat) : List II :=
  [ci 1 (a + 2 * (n + 1) : Nat) 0 0, cn 14 a a (a + 2 * (n + 1))]

def wideEqC (n a : Nat) : List II := wideAddC (n + 1) a (-1) 1 ++ orChain n a 1 ++ eqTail n a

def flagC (c Tk : Nat) : List II :=
  [cn 12 (c + 4) Tk (c + 3), cn 4 (c + 4) (c + 1) (c + 4), cn 4 (c + 5) c (c + 4)]

def selP (src M T a j : Nat) : List II :=
  [cn 10 T (a + j) src, cn 8 T T M, cn 10 (a + j) (a + j) T]

def seqC (P : Nat → List II) : List Nat → List II
  | [] => []
  | j :: l => P j ++ seqC P l

def selSeq (R T MS TA n : Nat) : List II :=
  seqC (fun j => selP (T + j) MS TA R j) (List.range n).reverse

def bitP (oM oX src Rr O W T T2 a j : Nat) : List II :=
  [cn oM T (a + j) Rr, cn oX T2 src O, cn oX T2 T2 W, cn 9 (a + j) T T2]

def shl1P (p O W TB TA TB2 j : Nat) : List II :=
  if j = 0 then [cn 11 TA p O, cn 9 p TA TB] else bitP 11 12 (p + (j - 1)) O O W TA TB2 p j

def shl1C (p n O W TB TA TB2 : Nat) : List II :=
  seqC (shl1P p O W TB TA TB2) (List.range n).reverse

def dvStep (k a c : Nat) : List II :=
  [cn 12 (c + 4) (a + (k - 1)) (c + 3)] ++
  shl1C (a + k) (k + 1) (c + 1) (c + 2) (c + 4) (c + 6) (c + 7) ++
  copyWords (k + 1) (a + 2 * k + 1) (a + k) ++
  wideAddC (k + 1) (a + 2 * k + 1) (-1) 1 ++
  flagC c (a + 2 * k + 1 + k) ++
  selSeq (a + k) (a + 2 * k + 1) (c + 5) (c + 6) (k + 1) ++
  shl1C a k (c + 1) (c + 2) (c + 4) (c + 6) (c + 7)

def dvLoop (k a c : Nat) : Nat → List II
  | 0 => []
  | n + 1 => dvLoop k a c n ++ dvStep k a c

def zeroSlotsC : Nat → Nat → List II
  | 0, _ => []
  | n + 1, r => ci 1 (r : Nat) 0 0 :: zeroSlotsC n (r + 1)

def dvPre (k a : Nat) : List II :=
  copyWords k (a + 3 * k + 2) (a + k) ++ [ci 1 (a + 4 * k + 2 : Nat) 0 0] ++ zeroSlotsC (k + 1) (a + k) ++
    [ci 1 (a + 4 * k + 10 : Nat) 0 0, ci 1 (a + 4 * k + 11 : Nat) 1 0, ci 1 (a + 4 * k + 12 : Nat) 62 0,
     ci 1 (a + 4 * k + 13 : Nat) 63 0]

def wideDivC (k a : Nat) : List II := dvPre k a ++ dvLoop k a (a + 4 * k + 10) (64 * k)

def wideLitFrom (a : Nat) (v : Int) : Nat → Nat → List II
  | _, 0 => []
  | j0, n + 1 => (wordConstant (a + j0) (v / 2 ^ (64 * j0))).1 ++ wideLitFrom a v (j0 + 1) n

def wideLitC (k a : Nat) (v : Int) : List II := wideLitFrom a v 0 k

def wideOutC (k a : Nat) (lo hi : Int) : List II :=
  [ci 1 (a + k : Nat) 0 0, ci 1 (a + k + 1 : Nat) 63 0, cn 12 (a + k + 2) (a + (k - 1)) (a + k + 1),
   cn 4 (a + k + 2) (a + k) (a + k + 2)] ++
  copyWords k (a + k + 4) a ++ [ci 2 (a + k + 4 + k : Nat) (a + k + 2 : Nat) 0] ++
  wideLitC (k + 1) (a + k + 4 + (k + 1)) lo ++ wideLtC k (a + k + 4) ++
  wideLitC (k + 1) (a + k + 4 + (2 * (k + 1) + 7)) hi ++
  copyWords k (a + k + 4 + (2 * (k + 1) + 7) + (k + 1)) a ++
  [ci 2 (a + k + 4 + (2 * (k + 1) + 7) + (k + 1) + k : Nat) (a + k + 2 : Nat) 0] ++
  wideLtC k (a + k + 4 + (2 * (k + 1) + 7)) ++
  [cn 9 (a + k + 3) (a + k + 4) (a + k + 4 + (2 * (k + 1) + 7))]

def extendPre (signed : Bool) (j k a : Nat) : List II :=
  if signed then
    [ci 1 (a + k : Nat) 0 0, ci 1 (a + k + 1 : Nat) 63 0,
     cn 12 (a + k + 2) (a + (j - 1)) (a + k + 1), cn 4 (a + k + 2) (a + k) (a + k + 2)]
  else [ci 1 (a + k + 2 : Nat) 0 0]

def wideExtendC (signed : Bool) (j k a : Nat) : List II :=
  extendPre signed j k a ++ seqC (fun i => [ci 2 (a + i : Nat) (a + k + 2 : Nat) 0]) (List.range' j (k - j))

/-- Low product and high word (into `t` and `t+11`), scratch `t .. t+15`. -/
def mulHiC (X Y t : Nat) : List II :=
  [cn 5 t X Y, ci 1 (t + 1 : Nat) 32 0, ci 1 (t + 2 : Nat) 1 0,
   cn 11 (t + 3) (t + 2) (t + 1), cn 4 (t + 3) (t + 3) (t + 2),
   cn 12 (t + 4) X (t + 1), cn 8 (t + 5) X (t + 3), cn 12 (t + 6) Y (t + 1), cn 8 (t + 7) Y (t + 3),
   cn 5 (t + 8) (t + 5) (t + 7), cn 5 (t + 9) (t + 4) (t + 7),
   cn 5 (t + 10) (t + 5) (t + 6), cn 5 (t + 11) (t + 4) (t + 6),
   cn 12 (t + 12) (t + 8) (t + 1), cn 8 (t + 13) (t + 9) (t + 3), cn 3 (t + 12) (t + 12) (t + 13),
   cn 8 (t + 13) (t + 10) (t + 3), cn 3 (t + 12) (t + 12) (t + 13),
   cn 12 (t + 13) (t + 12) (t + 1), cn 12 (t + 14) (t + 9) (t + 1), cn 12 (t + 15) (t + 10) (t + 1),
   cn 3 (t + 11) (t + 11) (t + 14), cn 3 (t + 11) (t + 11) (t + 15), cn 3 (t + 11) (t + 11) (t + 13)]

/-- Add the product (low word in `t`, high word in `t+11`) and the carry into the digit. -/
def mulAccC (R c t : Nat) : List II :=
  [cn 3 (t + 1) R t, cn 27 (t + 2) (t + 1) t, cn 3 (t + 3) (t + 1) c, cn 27 (t + 4) (t + 3) (t + 1),
   cn 2 R (t + 3) 0, cn 3 c (t + 11) (t + 2), cn 3 c c (t + 4)]

def mulLimbC (X Y R c t : Nat) : List II := mulHiC X Y t ++ mulAccC R c t

def mulRow : Nat → Nat → Nat → Nat → Nat → Nat → List II
  | 0, _, _, _, _, _ => []
  | n + 1, X, Y, R, c, t => mulLimbC X Y R c t ++ mulRow n X (Y + 1) (R + 1) c t

def mulRowC (n X Y R c t : Nat) : List II := ci 1 (c : Nat) 0 0 :: mulRow n X Y R c t

/-- Rows `i .. k-1`: row `i` has `k - i` digits. -/
def mulRows (k a : Nat) : Nat → Nat → List II
  | 0, _ => []
  | m + 1, i => mulRowC (m + 1) (a + i) (a + k) (a + 2 * k + i) (a + 3 * k) (a + 3 * k + 1) ++
      mulRows k a m (i + 1)

def wideMulC (k a : Nat) : List II :=
  zeroSlotsC k (a + 2 * k) ++ mulRows k a k 0 ++ copyWords k a (a + 2 * k)

def wideNegC (k a : Nat) : List II :=
  copyWords k (a + k) a ++ zeroSlotsC k a ++ wideAddC k a (-1) 1

def bitC (k a oM oX : Nat) (srcB : Nat → Nat) (l : List Nat) : List II :=
  seqC (fun j => bitP oM oX (srcB j) (a + k + 2) (a + k + 4) (a + k + 3) (a + k + 7) (a + k + 8) a j) l

def shPre (k a : Nat) : List II :=
  [ci 1 (a + k + 8 : Nat) 6 0, cn 12 (a + k + 1) (a + k) (a + k + 8), ci 1 (a + k + 7 : Nat) 63 0,
   cn 8 (a + k + 2) (a + k) (a + k + 7), cn 4 (a + k + 3) (a + k + 7) (a + k + 2),
   ci 1 (a + k + 4 : Nat) 1 0, ci 1 (a + k + 5 : Nat) 0 0]

def shlSrc (k a c j : Nat) : Nat := if c ≤ j then a + (j - c) else a + k + 5

def shlOrder (k : Nat) : List Nat := (List.range k).reverse

def shlSrcB (k a j : Nat) : Nat := if j = 0 then a + k + 5 else a + (j - 1)

def stgPre (k a idx : Nat) : List II :=
  [ci 1 (a + k + 9 : Nat) idx 0, cn 12 (a + k + 7) (a + k + 1) (a + k + 9),
   cn 8 (a + k + 7) (a + k + 7) (a + k + 4), cn 4 (a + k + 6) (a + k + 5) (a + k + 7)]

def stgC (k a idx : Nat) (src : Nat → Nat) (l : List Nat) : List II :=
  stgPre k a idx ++ seqC (fun j => selP (src j) (a + k + 6) (a + k + 7) a j) l

def stagesC (k a : Nat) (src : Nat → Nat → Nat) (l : List Nat) : Nat → List II
  | 0 => []
  | S + 1 => stagesC k a src l S ++ stgC k a S (src (2 ^ S)) l

def wideShlC (k S a : Nat) : List II :=
  shPre k a ++ stagesC k a (shlSrc k a) (shlOrder k) S ++ bitC k a 11 12 (shlSrcB k a) (shlOrder k)

def shrSrc (k a c j : Nat) : Nat := if j + c < k then a + (j + c) else a + k + 5

def shrOrder (k : Nat) : List Nat := List.range k

def shrSrcB (k a j : Nat) : Nat := if j + 1 < k then a + (j + 1) else a + k + 5

def wideShrC (k S a : Nat) : List II :=
  shPre k a ++ stagesC k a (shrSrc k a) (shrOrder k) S ++ bitC k a 12 11 (shrSrcB k a) (shrOrder k)

def condNegC (k p c F MS TA Z : Nat) : List II :=
  copyWords k c p ++ wideNegC k c ++ [cn 4 MS Z F] ++ selSeq p c MS TA k

def sdSign (k a : Nat) : List II :=
  [ci 1 (a + 4 * k + 18 + 2 : Nat) 63 0, ci 1 (a + 4 * k + 18 + 5 : Nat) 0 0,
   cn 12 (a + 4 * k + 18) (a + (k - 1)) (a + 4 * k + 18 + 2),
   cn 12 (a + 4 * k + 18 + 1) (a + k + (k - 1)) (a + 4 * k + 18 + 2)]

def wideSdivC (k a : Nat) : List II :=
  sdSign k a ++
  condNegC k a (a + 2 * k) (a + 4 * k + 18) (a + 4 * k + 18 + 3) (a + 4 * k + 18 + 4) (a + 4 * k + 18 + 5) ++
  condNegC k (a + k) (a + 2 * k) (a + 4 * k + 18 + 1) (a + 4 * k + 18 + 3) (a + 4 * k + 18 + 4)
    (a + 4 * k + 18 + 5) ++
  [cn 10 (a + 4 * k + 18 + 6) (a + 4 * k + 18) (a + 4 * k + 18 + 1)] ++
  wideDivC k a ++
  condNegC k a (a + 2 * k) (a + 4 * k + 18 + 6) (a + 4 * k + 18 + 3) (a + 4 * k + 18 + 4)
    (a + 4 * k + 18 + 5) ++
  condNegC k (a + k) (a + 2 * k) (a + 4 * k + 18) (a + 4 * k + 18 + 3) (a + 4 * k + 18 + 4)
    (a + 4 * k + 18 + 5)

end Gabbro.Stage0.Senke
