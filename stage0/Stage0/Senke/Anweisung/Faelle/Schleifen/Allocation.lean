/- Compute simultaneous counter demand from the complete source syntax. Sequential and
   alternative branches reuse slots; only a nested forever increases the live depth.
   Each level reserves a counter and an immutable decrement word below lexical locals. -/
import Stage0.Senke.Anweisung.Faelle.Schleifen.Code

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik
variable {D : Deklaration}

mutual
def counterDepthS {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} : Stmt D V l Γ Λ Λ' → Nat
  | .assignSlot _ _ _ _ _ _ => 0
  | .assignThru _ _ _ _ _ _ _ _ => 0
  | .assignSlotRef _ _ _ _ _ _ _ _ => 0
  | .assignGlob _ _ _ _ => 0
  | .putBytes _ _ _ _ _ _ _ _ _ _ => 0
  | .assignVar _ _ => 0
  | .shift _ _ _ _ _ _ _ _ _ _ => 0
  | .ite _ t e => max (counterDepthB t) (counterDepthB e)
  | .onOption _ p a => max (counterDepthB p) (counterDepthB a)
  | .onTag _ arms => counterDepthA arms
  | .onWhy _ arms => counterDepthG arms
  | .call _ _ _ _ => 0
  | .callInd _ _ _ _ => 0
  | .locks _ _ body => counterDepthB body
  | .breaking _ body => counterDepthB body
  | .traverse _ _ body => counterDepthB body
  | .retry _ _ body ueber => max (counterDepthB body) (counterDepthB ueber)
  | .forever _ _ body => 1 + counterDepthB body
  | .axiomCall _ _ _ _ _ _ _ => 0
  | .regWrite _ _ _ => 0
  | .transition .. => 0
  | .publish _ _ _ _ _ _ => 0
  | .advances .. => 0
  | .retires .. => 0
  | .ret _ _ => 0
  | .retWhy .. => 0
  | .leave _ => 0
  | .next _ => 0

def counterDepthB {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} : Block D V l Γ Λ Λ' → Nat
  | .nil => 0
  | .cons s rest => max (counterDepthS s) (counterDepthB rest)
  | .bind _ rest => counterDepthB rest
  | .bindCall _ _ _ _ _ rest => counterDepthB rest
  | .bindCallInd _ _ _ _ _ rest => counterDepthB rest
  | .bindCallElse _ _ _ _ _ err rest => max (counterDepthE err) (counterDepthB rest)
  | .bindAxiom _ _ _ _ _ _ _ rest => counterDepthB rest
  | .bindAxiomElse _ _ _ _ _ _ _ _ err rest => max (counterDepthE err) (counterDepthB rest)
  | .regRead _ _ rest => counterDepthB rest
  | .regReadElse _ _ _ sonst rest => max (counterDepthE sonst) (counterDepthB rest)
  | .awaits _ _ _ _ _ rest => counterDepthB rest
  | .exchange _ _ _ _ rest => counterDepthB rest
  | .narrow _ _ _ sonst rest => max (counterDepthE sonst) (counterDepthB rest)
  | .check _ sonst rest => max (counterDepthE sonst) (counterDepthB rest)
  | .float _ _ _ _ _ rest => counterDepthB rest
  | .floatLit _ _ _ rest => counterDepthB rest
  | .floatOf _ _ _ rest => counterDepthB rest
  | .floatNarrow _ _ _ sonst rest => max (counterDepthE sonst) (counterDepthB rest)

def counterDepthE {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} : Endblock D V l Γ Λ → Nat
  | .ret _ _ => 0
  | .retWhy .. => 0
  | .leave _ => 0
  | .next _ => 0
  | .cons s rest => max (counterDepthS s) (counterDepthE rest)
  | .bind _ rest => counterDepthE rest
  | .bindCall _ _ _ _ _ rest => counterDepthE rest
  | .bindCallElse _ _ _ _ _ err rest => max (counterDepthE err) (counterDepthE rest)
  | .bindAxiom _ _ _ _ _ _ _ rest => counterDepthE rest
  | .bindAxiomElse _ _ _ _ _ _ _ _ err rest => max (counterDepthE err) (counterDepthE rest)
  | .regRead _ _ rest => counterDepthE rest
  | .regReadElse _ _ _ sonst rest => max (counterDepthE sonst) (counterDepthE rest)
  | .awaits _ _ _ _ _ rest => counterDepthE rest
  | .bindCallInd _ _ _ _ _ rest => counterDepthE rest
  | .narrow _ _ _ sonst rest => max (counterDepthE sonst) (counterDepthE rest)
  | .exchange _ _ _ _ rest => counterDepthE rest
  | .ite _ t e => max (counterDepthE e) (counterDepthE t)

def counterDepthA {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {cs : List (Option (Int × Int))} : Arms D V l Γ Λ Λ' cs → Nat
  | .nil => 0
  | .cons b rest => max (counterDepthB b) (counterDepthA rest)

def counterDepthG {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {n : Nat} : GrundArms D V l Γ Λ Λ' n → Nat
  | .nil => 0
  | .cons b rest => max (counterDepthB b) (counterDepthG rest)
end

/-- Assign a loop from its remaining nesting depth. A child has smaller remaining
    depth and therefore a higher pair; sequential loops reuse the same pair.
    The reservation includes the original parameters and both ABI return words. -/
def counterPair (reserved remaining : Nat) : Nat × Nat :=
  let counter := FB + reserved - 2 * (remaining + 1)
  (counter, counter + 1)

/-- Every assigned pair lies above the ABI and below the relocated environment. -/
theorem counterPair_bounds (abi depth remaining : Nat) (h : remaining < depth) :
    FB + abi ≤ (counterPair (abi + 2 * depth) remaining).1 ∧
    (counterPair (abi + 2 * depth) remaining).1 + 1 =
      (counterPair (abi + 2 * depth) remaining).2 ∧
    (counterPair (abi + 2 * depth) remaining).2 < FB + (abi + 2 * depth) := by
  dsimp [counterPair, FB]
  omega

/-- A nested loop cannot overwrite either word of its enclosing loop's pair. -/
theorem counterPair_nested (abi depth outer inner : Nat)
    (ho : outer < depth) (hi : inner < outer) :
    (counterPair (abi + 2 * depth) outer).2 <
      (counterPair (abi + 2 * depth) inner).1 := by
  dsimp [counterPair, FB]
  omega

theorem counterPair_zeuge :
    counterPair (3 + 2 + 2 * 2) 1 = (9, 10) ∧
    counterPair (3 + 2 + 2 * 2) 0 = (11, 12) ∧
    FB + (3 + 2 + 2 * 2) = 13 := by decide

end Gabbro.Stage0.Senke
