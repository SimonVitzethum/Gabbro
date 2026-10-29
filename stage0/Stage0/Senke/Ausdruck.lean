/-
  File:      stage0/Stage0/Senke/Ausdruck.lean
  Subject:   The lowering of stage 0 (`PLAN-SELF-HOSTING.md` §2.1.4), part 1: expressions of machine G into `S0IR`.

  A variable of the context `Γ` lives in a frame slot, counted from the bottom of `Γ` after the frame's first
  slots (`vslot`, `FB`), so a `bind` adds the slot `frei Γ` and keeps the others. An integer is its 64-bit two's complement, a Boolean 0 or 1
  (`Enc`). `lowE L e d` computes `e` into slot `d`, using the slots above `d` as scratch; it answers the code and the
  first slot it does not touch. A form outside the fragment, an integer type outside 64 bits where the lowering
  compares, or a literal outside 32 bits is refused (`none`); wide integers and the other forms follow.

  A function pointer is the code address `L.fa f`. The layout is explicit in every value and storage encoding;
  `FunSpec.addr` ties those words to the callee code addresses. This reuses the IR's slot-based call target
  without a second dispatch mechanism. Function references outside the literal range are refused.
-/
import Lean.Meta.Tactic.Simp.RegisterCommand
import Grammatik.Kern.Semantik.Semantik
import Runner.IR.Rahmen
import Stage0.Senke.Welt.Lay

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
    remaining call depth (G's `fuel`; a call with depth 0 stops with `abstieg`). The variables follow. -/
def FB : Nat := 3

/-- The first free slot of a frame whose variables are `Γ`. -/
def frei (Γ : Ctx) : Nat := FB + Γ.length

/-- The frame slot of a variable: counted from the bottom of the context, after the frame's first slots. -/
def vslot {Γ : Ctx} {τ : Ty} (x : Var Γ τ) : Nat := FB + (Γ.length - 1 - Var.idx x)

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

/-- `d := op d (d+1)` after `a` into `d` and `b` into `d+1`. -/
def bin2 (o : Nat) (d : Nat) (ca : List II × Nat) (cb : List II × Nat) : List II × Nat :=
  (ca.1 ++ cb.1 ++ [ci o d d (d + 1)], max ca.2 cb.2)

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

/-- An element of column `f` of table `t`: its address (`slotA`), the word there. -/
def slotC (L : Lay D) (t : D.Tab) (f : D.Feld t) (d : Nat) (ci' : List II × Nat) : Option (List II × Nat) :=
  (slotA L t f d ci').map fun a => (a.1 ++ [ci 15 d d 0], a.2)

/-- The code computing `e` into slot `d`, and the first slot from which on nothing is touched. -/
def lowE (L : Lay D) {Λ : List (Res D)} : {Γ : Ctx} → {τ : Ty} → Expr D Γ Λ τ → Nat → Option (List II × Nat)
  | _, _, .lit n, d => if lit32 n then some ([ci 1 d n 0], d + 1) else none
  | _, _, .tru, d => some ([ci 1 d 1 0], d + 1)
  | _, _, .fls, d => some ([ci 1 d 0 0], d + 1)
  | _, _, .var x, d => some ([ci 2 d (vslot x) 0], d + 1)
  | _, _, .widen _ _ e, d => lowE L e d
  | _, _, .add a b, d => do let ca ← lowE L a d; let cb ← lowE L b (d + 1); pure (bin2 3 d ca cb)
  | _, _, .sub a b, d => do let ca ← lowE L a d; let cb ← lowE L b (d + 1); pure (bin2 4 d ca cb)
  | _, _, .mul a b, d => do let ca ← lowE L a d; let cb ← lowE L b (d + 1); pure (bin2 5 d ca cb)
  | _, _, .neg a, d => do let ca ← lowE L a (d + 1); pure (bin2 4 d ([ci 1 d 0 0], d + 1) ca)
  | _, _, .not a, d => do let ca ← lowE L a d; pure (bin2 10 d ca ([ci 1 (d + 1) 1 0], d + 2))
  | _, _, @Expr.le _ _ _ l1 h1 l2 h2 a b, d =>
    if inW l1 h1 && inW l2 h2 then do
      let cb ← lowE L b d; let ca ← lowE L a (d + 1)
      pure (bin2 10 d (bin2 13 d cb ca) ([ci 1 (d + 1) 1 0], d + 2))
    else none
  | _, _, @Expr.lt _ _ _ l1 h1 l2 h2 a b, d =>
    if inW l1 h1 && inW l2 h2 then do
      let ca ← lowE L a d; let cb ← lowE L b (d + 1); pure (bin2 13 d ca cb)
    else none
  | _, _, @Expr.eq _ _ _ l1 h1 l2 h2 a b, d =>
    if inW l1 h1 && inW l2 h2 then do
      let ca ← lowE L a d; let cb ← lowE L b (d + 1); pure (bin2 14 d ca cb)
    else none
  | _, _, .and a b, d => do let ca ← lowE L a d; let cb ← lowE L b (d + 1); pure (bin2 8 d ca cb)
  | _, _, .or a b, d => do let ca ← lowE L a d; let cb ← lowE L b (d + 1); pure (bin2 9 d ca cb)
  | _, _, .div _ _ a b, d =>
    if inWE a && inWE b then do let ca ← lowE L a d; let cb ← lowE L b (d + 1); pure (bin2 6 d ca cb) else none
  | _, _, .rem _ _ a b, d =>
    if inWE a && inWE b then do let ca ← lowE L a d; let cb ← lowE L b (d + 1); pure (bin2 7 d ca cb) else none
  | _, _, .sdiv _ a b, d =>
    if inWE a && inWE b && nichtMin a then do
      let ca ← lowE L a d; let cb ← lowE L b (d + 1); pure (bin2 6 d ca cb)
    else none
  | _, _, .srem _ a b, d =>
    if inWE a && inWE b && nichtMin a then do
      let ca ← lowE L a d; let cb ← lowE L b (d + 1); pure (bin2 7 d ca cb)
    else none
  | _, _, .band _ _ a b, d =>
    if inWE a && inWE b then do let ca ← lowE L a d; let cb ← lowE L b (d + 1); pure (bin2 8 d ca cb) else none
  | _, _, .bor _ _ _ _ _ a b, d =>
    if inWE a && inWE b then do let ca ← lowE L a d; let cb ← lowE L b (d + 1); pure (bin2 9 d ca cb) else none
  | _, _, .bxor _ _ _ _ _ a b, d =>
    if inWE a && inWE b then do let ca ← lowE L a d; let cb ← lowE L b (d + 1); pure (bin2 10 d ca cb) else none
  | _, _, .shl _ _ _ _ _ a b, d =>
    if inWE b && lt64 b then do let ca ← lowE L a d; let cb ← lowE L b (d + 1); pure (bin2 11 d ca cb) else none
  | _, _, .shr _ _ _ _ _ a b, d =>
    if inWE a && inWE b && lt64 b then do
      let ca ← lowE L a d; let cb ← lowE L b (d + 1); pure (bin2 12 d ca cb)
    else none
  | _, _, .none _, d => some ([ci 1 d (-1) 0], d + 1)
  | _, _, .some e, d => lowE L e d
  | _, _, @Expr.istSome _ _ _ n e, d =>
    if decide (n ≤ 2 ^ 63) then do
      let ce ← lowE L e d
      pure (bin2 10 d (bin2 14 d ce ([ci 1 (d + 1) (-1) 0], d + 2)) ([ci 1 (d + 1) 1 0], d + 2))
    else none
  | _, _, .why n r, d => if decide (n < 2 ^ 31) then some ([ci 1 d (r.val : Int) 0], d + 1) else none
  | _, _, .fnref f _ _, d => if lit32 (L.fa f) then some ([ci 1 d (L.fa f) 0], d + 1) else none
  | _, _, .ptrOf .., d => some ([ci 1 d 0 0], d + 1)
  | _, _, .glob g _, d => if lit32 (L.ga g) then some ([ci 1 d (L.ga g) 0, ci 15 d d 0], d + 1) else none
  | _, _, .slot t f i _, d => do let ci' ← lowE L i d; slotC L t f d ci'
  | _, _, .thru _ t _ f i _, d => do let ci' ← lowE L i d; slotC L t f d ci'
  | _, _, .wenn c a b, d => wennL d (lowE L c d) (lowE L a d) (lowE L b d)
  | _, _, _, _ => none

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
  | .fnptr _, v, w => w = BitVec.ofNat 64 (L.fa v.1)
  | .ptr _ _, _, _ => True
  | _, _, _ => False

/-- The variables of `ρ` are in their slots of the frame at `fp`. -/
def EnvAt (L : Lay D) (m : Runner.Mem) (fp : Runner.W) {Γ : Ctx} (ρ : Env D Γ) : Prop :=
  ∀ (τ : Ty) (x : Var Γ τ), ∃ w, m.rd64 (slot fp (BitVec.ofNat 64 (vslot x))) = some w ∧ Enc L τ (ρ.get x) w

end Gabbro.Stage0.Senke
