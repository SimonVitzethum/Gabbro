/-
  File:      stage0/Stage0/Senke/Anweisung.lean
  Subject:   The lowering of stage 0, part 2: statements and blocks of machine G into `S0IR`.

  The first free slot of a context `Γ` is `frei Γ`: an expression of a statement is computed there; a `bind`
  computes its value there, which is then the new variable's slot. `assignVar x e` moves the value into `x`'s slot;
  `ite c t e` tests `c` with `brz` and jumps over the other branch; a call (`call`, `bindCall`) places the
  callee's frame at the first free slot (`callC`). `lo` is the lowest slot an assignment may write (a function's
  body keeps its parameters for `ensures`); `A f` is the code address of `f`. Accepted so far: `assignVar`, `ite`,
  `call`, and the blocks `nil`, `cons`, `bind`, `bindCall`; everything else is refused (`none`). The answer's
  number is an upper bound of the slots the code writes.
-/
import Stage0.Senke.Ausdruck

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR

variable {D : Deklaration} {V : Vertrag D}

/-- The arguments of a call into the callee's parameter slots from `p` (the callee frame's first variable slot);
    the head goes highest. The last argument is computed first, so a later one's scratch slots lie above every
    argument already in place. -/
def lowA {Λ : List (Res D)} : {Γ : Ctx} → {τs : List Ty} → Args D Γ Λ τs → Nat → Option (List II × Nat)
  | _, _, .nil, p => some ([], p)
  | _, _ :: τs, .cons e rest, p => do
    let cr ← lowA rest p
    let ce ← lowE e (p + τs.length)
    pure (cr.1 ++ ce.1, max cr.2 ce.2)

/-- A call of `f` with its frame at slot `F` of the caller: the arguments (`ca`), the depth one less, the
    address of `f`, `call`. -/
def callTail (A : D.Fn → Nat) (f : D.Fn) (F : Nat) : List II :=
  [ci 1 ((F + FB + (D.params f).length : Nat) : Int) 1 0,
   ci 4 ((F + 2 : Nat) : Int) 2 ((F + FB + (D.params f).length : Nat) : Int),
   ci 1 ((F + FB + (D.params f).length : Nat) : Int) (A f) 0,
   ci 20 ((F + FB + (D.params f).length : Nat) : Int) F 0]

def callC (A : D.Fn → Nat) (f : D.Fn) (F : Nat) (ca : List II) : List II := ca ++ callTail A f F

def callTop (f : D.Fn) (F t : Nat) : Nat := max t (F + FB + (D.params f).length + 1)

mutual
def lowS (A : D.Fn → Nat) (lo : Nat) : {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} → Stmt D V l Γ Λ Λ' →
    Option (List II × Nat)
  | _, Γ, _, _, .assignVar x e =>
    if lo ≤ vslot x then do
      let ce ← lowE e (frei Γ)
      pure (ce.1 ++ [ci 2 (vslot x) (frei Γ) 0], ce.2)
    else none
  | _, Γ, _, _, .ite c t e => do
    let cc ← lowE c (frei Γ)
    let ct ← lowB A lo t
    let ce ← lowB A lo e
    pure (cc.1 ++ [ci 19 (frei Γ) (16 * (ct.1.length + 2)) 0] ++ ct.1 ++ [ci 18 (16 * (ce.1.length + 1)) 0 0] ++ ce.1,
      max cc.2 (max ct.2 ce.2))
  | _, Γ, _, _, .call f args _ _ => do
    let ca ← lowA args (frei Γ + FB)
    pure (callC A f (frei Γ) ca.1, callTop f (frei Γ) ca.2)
  | _, _, _, _, _ => none

def lowB (A : D.Fn → Nat) (lo : Nat) : {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} → Block D V l Γ Λ Λ' →
    Option (List II × Nat)
  | _, Γ, _, _, .nil => some ([], frei Γ)
  | _, _, _, _, .cons s rest => do
    let cs ← lowS A lo s
    let cr ← lowB A lo rest
    pure (cs.1 ++ cr.1, max cs.2 cr.2)
  | _, Γ, _, _, .bind e rest => do
    let ce ← lowE e (frei Γ)
    let cr ← lowB A lo rest
    pure (ce.1 ++ cr.1, max ce.2 cr.2)
  | _, Γ, _, _, .bindCall f args _ _ _ rest => do
    let ca ← lowA args (frei Γ + FB)
    let cr ← lowB A lo rest
    pure (callC A f (frei Γ) ca.1 ++ [ci 2 (frei Γ) (frei Γ + 2) 0] ++ cr.1, max (callTop f (frei Γ) ca.2) cr.2)
  | _, _, _, _, _ => none
end

end Gabbro.Stage0.Senke
