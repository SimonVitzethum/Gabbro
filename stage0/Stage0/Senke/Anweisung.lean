/-
  File:      stage0/Stage0/Senke/Anweisung.lean
  Subject:   The lowering of stage 0, part 2: statements and blocks of machine G into `S0IR`.

  The first free slot of a context `Γ` is `frei Γ`: an expression of a statement is computed there; a `bind`
  computes its value there, which is then the new variable's slot. `assignVar x e` moves the value into `x`'s slot;
  `ite c t e` tests `c` with `brz` and jumps over the other branch. Accepted so far: `assignVar`, `ite`, and the
  blocks `nil`, `cons`, `bind`; everything else is refused (`none`). The answer's number is an upper bound of the
  slots the code writes.
-/
import Stage0.Senke.Ausdruck

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR

variable {D : Deklaration} {V : Vertrag D}

mutual
def lowS : {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} → Stmt D V l Γ Λ Λ' → Option (List II × Nat)
  | _, Γ, _, _, .assignVar x e => do
    let ce ← lowE e (frei Γ)
    pure (ce.1 ++ [ci 2 (vslot x) (frei Γ) 0], ce.2)
  | _, Γ, _, _, .ite c t e => do
    let cc ← lowE c (frei Γ)
    let ct ← lowB t
    let ce ← lowB e
    pure (cc.1 ++ [ci 19 (frei Γ) (16 * (ct.1.length + 2)) 0] ++ ct.1 ++ [ci 18 (16 * (ce.1.length + 1)) 0 0] ++ ce.1,
      max cc.2 (max ct.2 ce.2))
  | _, _, _, _, _ => none

def lowB : {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} → Block D V l Γ Λ Λ' → Option (List II × Nat)
  | _, Γ, _, _, .nil => some ([], (frei Γ))
  | _, _, _, _, .cons s rest => do
    let cs ← lowS s
    let cr ← lowB rest
    pure (cs.1 ++ cr.1, max cs.2 cr.2)
  | _, Γ, _, _, .bind e rest => do
    let ce ← lowE e (frei Γ)
    let cr ← lowB rest
    pure (ce.1 ++ cr.1, max ce.2 cr.2)
  | _, _, _, _, _ => none
end

end Gabbro.Stage0.Senke
