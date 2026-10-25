/-
  File:      Grammatik/Gen/Fein/Zellen.lean
  Subject:   THE FINE CELLS: the syntactic cells of a program, read off its terms.

    * a CONSTRUCTOR cell (`art = 0`): the constructor of a node, its loop context `l` (the index of `Stmt`, `Block`,
      `Endblock`, `Arms`, `GrundArms`; `false` for the expression families) and the type classes of its expression
      children (`Ty.kopf`, in order);
    * a PAIR cell (`art = 1`): the constructor of a node, its loop context, a child position, and the family and
      constructor of the child there (two directly nested constructs).

  The constructor cell is the lowering cell of `Adaequanz/Ueberdeckung.lean` (Track L, `lowerS_ok`: the lowering of a
  node is correct when the template for its constructor, lowering context and child classes is). The traversal is
  GENERATED from the constructor list of the model (the children named as the model names them, families numbered as
  in `Adaequanz/Gabbro/Signatur.lean`); a new constructor makes its matches non-exhaustive and stops the build.
-/
import Grammatik.Gen.Abdeckung.Satz.ZellenVoll

namespace Gabbro.Grammatik.Gen.Fein

open Gabbro.Grammatik

/-- A fine cell: kind (0 constructor, 1 pair), family, constructor, loop context, data (the child type classes; for a
    pair: position, child family, child constructor). -/
structure FZelle where
  art : Nat
  fam : Nat
  kon : Nat
  l : Bool
  daten : List Nat
  deriving DecidableEq, Hashable, Repr

/-- The class of a type: its head constructor. -/
def _root_.Gabbro.Grammatik.Ty.kopf : Ty → Nat
  | .int .. => 0
  | .bool => 1
  | .opt .. => 2
  | .sum .. => 3
  | .why .. => 4
  | .never => 5
  | .fl .. => 6
  | .fnptr .. => 7
  | .ptr .. => 8
  | .ref .. => 9
  | .arr .. => 10
  | .str .. => 11

variable {D : Deklaration}

/-- The type class of an expression. -/
def tk {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} (_ : Expr D Γ Λ τ) : Nat := τ.kopf

/-- The constructor of a node (its index in the family, the order of `Adaequanz/Gabbro/Signatur.lean`; the region forms of
    2026-10-24 are appended after the existing numbers, so that the cached witness runs keep their cell names). -/
def kE {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} : Expr D Γ Λ τ → Nat
  | .lit .. => 0
  | .tru .. => 1
  | .fls .. => 2
  | .var .. => 3
  | .glob .. => 4
  | .slot .. => 5
  | .thru .. => 6
  | .ptrOf .. => 7
  | .fnref .. => 8
  | .oldG .. => 9
  | .oldS .. => 10
  | .widen .. => 11
  | .add .. => 12
  | .sub .. => 13
  | .neg .. => 14
  | .mul .. => 15
  | .div .. => 16
  | .rem .. => 17
  | .sdiv .. => 18
  | .srem .. => 19
  | .getBytes .. => 20
  | .band .. => 21
  | .bor .. => 22
  | .bxor .. => 23
  | .shl .. => 24
  | .shr .. => 25
  | .lt .. => 26
  | .le .. => 27
  | .eq .. => 28
  | .fllt .. => 29
  | .flle .. => 30
  | .and .. => 31
  | .or .. => 32
  | .not .. => 33
  | .none .. => 34
  | .some .. => 35
  | .istSome .. => 36
  | .case .. => 37
  | .why .. => 38
  | .forallSlots .. => 39
  | .existsSlots .. => 40
  | .reaches .. => 41
  | .refEq .. => 42
  | .slotRef .. => 43
  | .arrNil .. => 44
  | .arrCons .. => 45
  | .arrGet .. => 46
  | .arrSet .. => 47
  | .strLit .. => 48
  | .strLen .. => 49
  | .strCat .. => 50
  | .strGet .. => 51
  | .strEq .. => 52
  | .strLt .. => 53
  | .strWeit .. => 54

def kN {Γ : Ctx} {Λ : List (Res D)} {o : Option (Int × Int)} : NutzlastExpr D Γ Λ o → Nat
  | .empty .. => 0
  | .num .. => 1

def kA {Γ : Ctx} {Λ : List (Res D)} {τs : List Ty} : Args D Γ Λ τs → Nat
  | .nil .. => 0
  | .cons .. => 1

def kR {Γ : Ctx} {Λ : List (Res D)} {o : Option Ty} : ErgExpr D Γ Λ o → Nat
  | .empty .. => 0
  | .val .. => 1

def kS {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} : Stmt D V l Γ Λ Λ' → Nat
  | .assignSlot .. => 0
  | .assignThru .. => 1
  | .assignGlob .. => 2
  | .putBytes .. => 3
  | .assignVar .. => 4
  | .shift .. => 5
  | .ite .. => 6
  | .onOption .. => 7
  | .onTag .. => 8
  | .onWhy .. => 9
  | .call .. => 10
  | .callInd .. => 11
  | .locks .. => 12
  | .breaking .. => 13
  | .traverse .. => 14
  | .retry .. => 15
  | .forever .. => 16
  | .axiomCall .. => 17
  | .regWrite .. => 18
  | .transition .. => 19
  | .publish .. => 20
  | .advances .. => 21
  | .retires .. => 22
  | .ret .. => 23
  | .retWhy .. => 24
  | .leave .. => 25
  | .next .. => 26
  | .assignSlotRef .. => 27

def kB {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} : Block D V l Γ Λ Λ' → Nat
  | .nil .. => 0
  | .cons .. => 1
  | .bind .. => 2
  | .bindCall .. => 3
  | .bindCallInd .. => 4
  | .bindCallElse .. => 5
  | .bindAxiom .. => 6
  | .bindAxiomElse .. => 7
  | .regRead .. => 8
  | .regReadElse .. => 9
  | .awaits .. => 10
  | .exchange .. => 11
  | .narrow .. => 12
  | .check .. => 13
  | .float .. => 14
  | .floatLit .. => 15
  | .floatOf .. => 16
  | .floatNarrow .. => 17

def kEnd {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} : Endblock D V l Γ Λ → Nat
  | .ret .. => 0
  | .retWhy .. => 1
  | .leave .. => 2
  | .next .. => 3
  | .cons .. => 4
  | .bind .. => 5
  | .bindCall .. => 6
  | .bindCallElse .. => 7
  | .bindAxiom .. => 8
  | .bindAxiomElse .. => 9
  | .regRead .. => 10
  | .regReadElse .. => 11
  | .awaits .. => 12
  | .bindCallInd .. => 13

def kArms {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option (Int × Int))} : Arms D V l Γ Λ Λ' cs → Nat
  | .nil .. => 0
  | .cons .. => 1

def kGArms {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat} : GrundArms D V l Γ Λ Λ' n → Nat
  | .nil .. => 0
  | .cons .. => 1

mutual
def fzE {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} : Expr D Γ Λ τ → List FZelle
  | .lit .. => [⟨0, 0, 0, false, []⟩]
  | .tru .. => [⟨0, 0, 1, false, []⟩]
  | .fls .. => [⟨0, 0, 2, false, []⟩]
  | .var .. => [⟨0, 0, 3, false, []⟩]
  | .glob .. => [⟨0, 0, 4, false, []⟩]
  | .slot (i := i) .. => [⟨0, 0, 5, false, [tk i]⟩, ⟨1, 0, 5, false, [0, 0, kE i]⟩] ++ fzE i
  | .thru (p := p) (i := i) .. => [⟨0, 0, 6, false, [tk p, tk i]⟩, ⟨1, 0, 6, false, [0, 0, kE p]⟩, ⟨1, 0, 6, false, [1, 0, kE i]⟩] ++ fzE p ++ fzE i
  | .ptrOf .. => [⟨0, 0, 7, false, []⟩]
  | .fnref .. => [⟨0, 0, 8, false, []⟩]
  | .oldG .. => [⟨0, 0, 9, false, []⟩]
  | .oldS (i := i) .. => [⟨0, 0, 10, false, [tk i]⟩, ⟨1, 0, 10, false, [0, 0, kE i]⟩] ++ fzE i
  | .widen (e := e) .. => [⟨0, 0, 11, false, [tk e]⟩, ⟨1, 0, 11, false, [0, 0, kE e]⟩] ++ fzE e
  | .add (a := a) (b := b) .. => [⟨0, 0, 12, false, [tk a, tk b]⟩, ⟨1, 0, 12, false, [0, 0, kE a]⟩, ⟨1, 0, 12, false, [1, 0, kE b]⟩] ++ fzE a ++ fzE b
  | .sub (a := a) (b := b) .. => [⟨0, 0, 13, false, [tk a, tk b]⟩, ⟨1, 0, 13, false, [0, 0, kE a]⟩, ⟨1, 0, 13, false, [1, 0, kE b]⟩] ++ fzE a ++ fzE b
  | .neg (a := a) .. => [⟨0, 0, 14, false, [tk a]⟩, ⟨1, 0, 14, false, [0, 0, kE a]⟩] ++ fzE a
  | .mul (a := a) (b := b) .. => [⟨0, 0, 15, false, [tk a, tk b]⟩, ⟨1, 0, 15, false, [0, 0, kE a]⟩, ⟨1, 0, 15, false, [1, 0, kE b]⟩] ++ fzE a ++ fzE b
  | .div (a := a) (b := b) .. => [⟨0, 0, 16, false, [tk a, tk b]⟩, ⟨1, 0, 16, false, [0, 0, kE a]⟩, ⟨1, 0, 16, false, [1, 0, kE b]⟩] ++ fzE a ++ fzE b
  | .rem (a := a) (b := b) .. => [⟨0, 0, 17, false, [tk a, tk b]⟩, ⟨1, 0, 17, false, [0, 0, kE a]⟩, ⟨1, 0, 17, false, [1, 0, kE b]⟩] ++ fzE a ++ fzE b
  | .sdiv (a := a) (b := b) .. => [⟨0, 0, 18, false, [tk a, tk b]⟩, ⟨1, 0, 18, false, [0, 0, kE a]⟩, ⟨1, 0, 18, false, [1, 0, kE b]⟩] ++ fzE a ++ fzE b
  | .srem (a := a) (b := b) .. => [⟨0, 0, 19, false, [tk a, tk b]⟩, ⟨1, 0, 19, false, [0, 0, kE a]⟩, ⟨1, 0, 19, false, [1, 0, kE b]⟩] ++ fzE a ++ fzE b
  | .getBytes (i := i) .. => [⟨0, 0, 20, false, [tk i]⟩, ⟨1, 0, 20, false, [0, 0, kE i]⟩] ++ fzE i
  | .band (a := a) (b := b) .. => [⟨0, 0, 21, false, [tk a, tk b]⟩, ⟨1, 0, 21, false, [0, 0, kE a]⟩, ⟨1, 0, 21, false, [1, 0, kE b]⟩] ++ fzE a ++ fzE b
  | .bor (a := a) (b := b) .. => [⟨0, 0, 22, false, [tk a, tk b]⟩, ⟨1, 0, 22, false, [0, 0, kE a]⟩, ⟨1, 0, 22, false, [1, 0, kE b]⟩] ++ fzE a ++ fzE b
  | .bxor (a := a) (b := b) .. => [⟨0, 0, 23, false, [tk a, tk b]⟩, ⟨1, 0, 23, false, [0, 0, kE a]⟩, ⟨1, 0, 23, false, [1, 0, kE b]⟩] ++ fzE a ++ fzE b
  | .shl (a := a) (b := b) .. => [⟨0, 0, 24, false, [tk a, tk b]⟩, ⟨1, 0, 24, false, [0, 0, kE a]⟩, ⟨1, 0, 24, false, [1, 0, kE b]⟩] ++ fzE a ++ fzE b
  | .shr (a := a) (b := b) .. => [⟨0, 0, 25, false, [tk a, tk b]⟩, ⟨1, 0, 25, false, [0, 0, kE a]⟩, ⟨1, 0, 25, false, [1, 0, kE b]⟩] ++ fzE a ++ fzE b
  | .lt (a := a) (b := b) .. => [⟨0, 0, 26, false, [tk a, tk b]⟩, ⟨1, 0, 26, false, [0, 0, kE a]⟩, ⟨1, 0, 26, false, [1, 0, kE b]⟩] ++ fzE a ++ fzE b
  | .le (a := a) (b := b) .. => [⟨0, 0, 27, false, [tk a, tk b]⟩, ⟨1, 0, 27, false, [0, 0, kE a]⟩, ⟨1, 0, 27, false, [1, 0, kE b]⟩] ++ fzE a ++ fzE b
  | .eq (a := a) (b := b) .. => [⟨0, 0, 28, false, [tk a, tk b]⟩, ⟨1, 0, 28, false, [0, 0, kE a]⟩, ⟨1, 0, 28, false, [1, 0, kE b]⟩] ++ fzE a ++ fzE b
  | .fllt (a := a) (b := b) .. => [⟨0, 0, 29, false, [tk a, tk b]⟩, ⟨1, 0, 29, false, [0, 0, kE a]⟩, ⟨1, 0, 29, false, [1, 0, kE b]⟩] ++ fzE a ++ fzE b
  | .flle (a := a) (b := b) .. => [⟨0, 0, 30, false, [tk a, tk b]⟩, ⟨1, 0, 30, false, [0, 0, kE a]⟩, ⟨1, 0, 30, false, [1, 0, kE b]⟩] ++ fzE a ++ fzE b
  | .and (a := a) (b := b) .. => [⟨0, 0, 31, false, [tk a, tk b]⟩, ⟨1, 0, 31, false, [0, 0, kE a]⟩, ⟨1, 0, 31, false, [1, 0, kE b]⟩] ++ fzE a ++ fzE b
  | .or (a := a) (b := b) .. => [⟨0, 0, 32, false, [tk a, tk b]⟩, ⟨1, 0, 32, false, [0, 0, kE a]⟩, ⟨1, 0, 32, false, [1, 0, kE b]⟩] ++ fzE a ++ fzE b
  | .not (a := a) .. => [⟨0, 0, 33, false, [tk a]⟩, ⟨1, 0, 33, false, [0, 0, kE a]⟩] ++ fzE a
  | .none .. => [⟨0, 0, 34, false, []⟩]
  | .some (e := e) .. => [⟨0, 0, 35, false, [tk e]⟩, ⟨1, 0, 35, false, [0, 0, kE e]⟩] ++ fzE e
  | .istSome (e := e) .. => [⟨0, 0, 36, false, [tk e]⟩, ⟨1, 0, 36, false, [0, 0, kE e]⟩] ++ fzE e
  | .case (nutz := nutz) .. => [⟨0, 0, 37, false, []⟩, ⟨1, 0, 37, false, [0, 1, kN nutz]⟩] ++ fzN nutz
  | .why .. => [⟨0, 0, 38, false, []⟩]
  | .forallSlots (body := body) .. => [⟨0, 0, 39, false, [tk body]⟩, ⟨1, 0, 39, false, [0, 0, kE body]⟩] ++ fzE body
  | .existsSlots (body := body) .. => [⟨0, 0, 40, false, [tk body]⟩, ⟨1, 0, 40, false, [0, 0, kE body]⟩] ++ fzE body
  | .reaches (a := a) (b := b) .. => [⟨0, 0, 41, false, [tk a, tk b]⟩, ⟨1, 0, 41, false, [0, 0, kE a]⟩, ⟨1, 0, 41, false, [1, 0, kE b]⟩] ++ fzE a ++ fzE b
  | .refEq (a := a) (b := b) .. => [⟨0, 0, 42, false, [tk a, tk b]⟩, ⟨1, 0, 42, false, [0, 0, kE a]⟩, ⟨1, 0, 42, false, [1, 0, kE b]⟩] ++ fzE a ++ fzE b
  | .slotRef (r := r) .. => [⟨0, 0, 43, false, [tk r]⟩, ⟨1, 0, 43, false, [0, 0, kE r]⟩] ++ fzE r
  | .arrNil .. => [⟨0, 0, 44, false, []⟩]
  | .arrCons a b => [⟨0, 0, 45, false, [tk a, tk b]⟩, ⟨1, 0, 45, false, [0, 0, kE a]⟩, ⟨1, 0, 45, false, [1, 0, kE b]⟩] ++ fzE a ++ fzE b
  | .arrGet a b => [⟨0, 0, 46, false, [tk a, tk b]⟩, ⟨1, 0, 46, false, [0, 0, kE a]⟩, ⟨1, 0, 46, false, [1, 0, kE b]⟩] ++ fzE a ++ fzE b
  | .arrSet a i v => [⟨0, 0, 47, false, [tk a, tk i, tk v]⟩, ⟨1, 0, 47, false, [0, 0, kE a]⟩, ⟨1, 0, 47, false, [1, 0, kE i]⟩, ⟨1, 0, 47, false, [2, 0, kE v]⟩] ++ fzE a ++ fzE i ++ fzE v
  | .strLit .. => [⟨0, 0, 48, false, []⟩]
  | .strLen e => [⟨0, 0, 49, false, [tk e]⟩, ⟨1, 0, 49, false, [0, 0, kE e]⟩] ++ fzE e
  | .strCat a b => [⟨0, 0, 50, false, [tk a, tk b]⟩, ⟨1, 0, 50, false, [0, 0, kE a]⟩, ⟨1, 0, 50, false, [1, 0, kE b]⟩] ++ fzE a ++ fzE b
  | .strGet a b => [⟨0, 0, 51, false, [tk a, tk b]⟩, ⟨1, 0, 51, false, [0, 0, kE a]⟩, ⟨1, 0, 51, false, [1, 0, kE b]⟩] ++ fzE a ++ fzE b
  | .strEq a b => [⟨0, 0, 52, false, [tk a, tk b]⟩, ⟨1, 0, 52, false, [0, 0, kE a]⟩, ⟨1, 0, 52, false, [1, 0, kE b]⟩] ++ fzE a ++ fzE b
  | .strLt a b => [⟨0, 0, 53, false, [tk a, tk b]⟩, ⟨1, 0, 53, false, [0, 0, kE a]⟩, ⟨1, 0, 53, false, [1, 0, kE b]⟩] ++ fzE a ++ fzE b
  | .strWeit _ e => [⟨0, 0, 54, false, [tk e]⟩, ⟨1, 0, 54, false, [0, 0, kE e]⟩] ++ fzE e

def fzN {Γ : Ctx} {Λ : List (Res D)} {o : Option (Int × Int)} : NutzlastExpr D Γ Λ o → List FZelle
  | .empty .. => [⟨0, 1, 0, false, []⟩]
  | .num (e := e) .. => [⟨0, 1, 1, false, [tk e]⟩, ⟨1, 1, 1, false, [0, 0, kE e]⟩] ++ fzE e

def fzA {Γ : Ctx} {Λ : List (Res D)} {τs : List Ty} : Args D Γ Λ τs → List FZelle
  | .nil .. => [⟨0, 2, 0, false, []⟩]
  | .cons (e := e) (rest := rest) .. => [⟨0, 2, 1, false, [tk e]⟩, ⟨1, 2, 1, false, [0, 0, kE e]⟩, ⟨1, 2, 1, false, [1, 2, kA rest]⟩] ++ fzE e ++ fzA rest

def fzR {Γ : Ctx} {Λ : List (Res D)} {o : Option Ty} : ErgExpr D Γ Λ o → List FZelle
  | .empty .. => [⟨0, 3, 0, false, []⟩]
  | .val (e := e) .. => [⟨0, 3, 1, false, [tk e]⟩, ⟨1, 3, 1, false, [0, 0, kE e]⟩] ++ fzE e

def fzS {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} : Stmt D V l Γ Λ Λ' → List FZelle
  | .assignSlot (i := i) (e := e) .. => [⟨0, 4, 0, l, [tk i, tk e]⟩, ⟨1, 4, 0, l, [0, 0, kE i]⟩, ⟨1, 4, 0, l, [1, 0, kE e]⟩] ++ fzE i ++ fzE e
  | .assignThru (p := p) (i := i) (e := e) .. => [⟨0, 4, 1, l, [tk p, tk i, tk e]⟩, ⟨1, 4, 1, l, [0, 0, kE p]⟩, ⟨1, 4, 1, l, [1, 0, kE i]⟩, ⟨1, 4, 1, l, [2, 0, kE e]⟩] ++ fzE p ++ fzE i ++ fzE e
  | .assignSlotRef (r := r) (e := e) .. => [⟨0, 4, 27, l, [tk r, tk e]⟩, ⟨1, 4, 27, l, [0, 0, kE r]⟩, ⟨1, 4, 27, l, [1, 0, kE e]⟩] ++ fzE r ++ fzE e
  | .assignGlob (e := e) .. => [⟨0, 4, 2, l, [tk e]⟩, ⟨1, 4, 2, l, [0, 0, kE e]⟩] ++ fzE e
  | .putBytes (i := i) (e := e) .. => [⟨0, 4, 3, l, [tk i, tk e]⟩, ⟨1, 4, 3, l, [0, 0, kE i]⟩, ⟨1, 4, 3, l, [1, 0, kE e]⟩] ++ fzE i ++ fzE e
  | .assignVar (e := e) .. => [⟨0, 4, 4, l, [tk e]⟩, ⟨1, 4, 4, l, [0, 0, kE e]⟩] ++ fzE e
  | .shift (i := i) .. => [⟨0, 4, 5, l, [tk i]⟩, ⟨1, 4, 5, l, [0, 0, kE i]⟩] ++ fzE i
  | .ite (c := c) (t := t) (e := e) .. => [⟨0, 4, 6, l, [tk c]⟩, ⟨1, 4, 6, l, [0, 0, kE c]⟩, ⟨1, 4, 6, l, [1, 5, kB t]⟩, ⟨1, 4, 6, l, [2, 5, kB e]⟩] ++ fzE c ++ fzB t ++ fzB e
  | .onOption (o := o) (p := p) (a := a) .. => [⟨0, 4, 7, l, [tk o]⟩, ⟨1, 4, 7, l, [0, 0, kE o]⟩, ⟨1, 4, 7, l, [1, 5, kB p]⟩, ⟨1, 4, 7, l, [2, 5, kB a]⟩] ++ fzE o ++ fzB p ++ fzB a
  | .onTag (v := v) (arms := arms) .. => [⟨0, 4, 8, l, [tk v]⟩, ⟨1, 4, 8, l, [0, 0, kE v]⟩, ⟨1, 4, 8, l, [1, 7, kArms arms]⟩] ++ fzE v ++ fzArms arms
  | .onWhy (r := r) (arms := arms) .. => [⟨0, 4, 9, l, [tk r]⟩, ⟨1, 4, 9, l, [0, 0, kE r]⟩, ⟨1, 4, 9, l, [1, 8, kGArms arms]⟩] ++ fzE r ++ fzGArms arms
  | .call (args := args) .. => [⟨0, 4, 10, l, []⟩, ⟨1, 4, 10, l, [0, 2, kA args]⟩] ++ fzA args
  | .callInd (p := p) (args := args) .. => [⟨0, 4, 11, l, [tk p]⟩, ⟨1, 4, 11, l, [0, 0, kE p]⟩, ⟨1, 4, 11, l, [1, 2, kA args]⟩] ++ fzE p ++ fzA args
  | .locks (body := body) .. => [⟨0, 4, 12, l, []⟩, ⟨1, 4, 12, l, [0, 5, kB body]⟩] ++ fzB body
  | .breaking (body := body) .. => [⟨0, 4, 13, l, []⟩, ⟨1, 4, 13, l, [0, 5, kB body]⟩] ++ fzB body
  | .traverse (inv := inv) (body := body) .. => [⟨0, 4, 14, l, [tk inv]⟩, ⟨1, 4, 14, l, [0, 0, kE inv]⟩, ⟨1, 4, 14, l, [1, 5, kB body]⟩] ++ fzE inv ++ fzB body
  | .retry (bis := bis) (body := body) (ueberlauf := ueberlauf) .. => [⟨0, 4, 15, l, [tk bis]⟩, ⟨1, 4, 15, l, [0, 0, kE bis]⟩, ⟨1, 4, 15, l, [1, 5, kB body]⟩, ⟨1, 4, 15, l, [2, 5, kB ueberlauf]⟩] ++ fzE bis ++ fzB body ++ fzB ueberlauf
  | .forever (inv := inv) (body := body) .. => [⟨0, 4, 16, l, [tk inv]⟩, ⟨1, 4, 16, l, [0, 0, kE inv]⟩, ⟨1, 4, 16, l, [1, 5, kB body]⟩] ++ fzE inv ++ fzB body
  | .axiomCall (args := args) .. => [⟨0, 4, 17, l, []⟩, ⟨1, 4, 17, l, [0, 2, kA args]⟩] ++ fzA args
  | .regWrite (e := e) .. => [⟨0, 4, 18, l, [tk e]⟩, ⟨1, 4, 18, l, [0, 0, kE e]⟩] ++ fzE e
  | .transition .. => [⟨0, 4, 19, l, []⟩]
  | .publish (e := e) .. => [⟨0, 4, 20, l, [tk e]⟩, ⟨1, 4, 20, l, [0, 0, kE e]⟩] ++ fzE e
  | .advances .. => [⟨0, 4, 21, l, []⟩]
  | .retires .. => [⟨0, 4, 22, l, []⟩]
  | .ret (e := e) .. => [⟨0, 4, 23, l, []⟩, ⟨1, 4, 23, l, [0, 3, kR e]⟩] ++ fzR e
  | .retWhy .. => [⟨0, 4, 24, l, []⟩]
  | .leave .. => [⟨0, 4, 25, l, []⟩]
  | .next .. => [⟨0, 4, 26, l, []⟩]

def fzB {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} : Block D V l Γ Λ Λ' → List FZelle
  | .nil .. => [⟨0, 5, 0, l, []⟩]
  | .cons (s := s) (rest := rest) .. => [⟨0, 5, 1, l, []⟩, ⟨1, 5, 1, l, [0, 4, kS s]⟩, ⟨1, 5, 1, l, [1, 5, kB rest]⟩] ++ fzS s ++ fzB rest
  | .bind (e := e) (rest := rest) .. => [⟨0, 5, 2, l, [tk e]⟩, ⟨1, 5, 2, l, [0, 0, kE e]⟩, ⟨1, 5, 2, l, [1, 5, kB rest]⟩] ++ fzE e ++ fzB rest
  | .bindCall (args := args) (rest := rest) .. => [⟨0, 5, 3, l, []⟩, ⟨1, 5, 3, l, [0, 2, kA args]⟩, ⟨1, 5, 3, l, [1, 5, kB rest]⟩] ++ fzA args ++ fzB rest
  | .bindCallInd (p := p) (args := args) (rest := rest) .. => [⟨0, 5, 4, l, [tk p]⟩, ⟨1, 5, 4, l, [0, 0, kE p]⟩, ⟨1, 5, 4, l, [1, 2, kA args]⟩, ⟨1, 5, 4, l, [2, 5, kB rest]⟩] ++ fzE p ++ fzA args ++ fzB rest
  | .bindCallElse (args := args) (err := err) (rest := rest) .. => [⟨0, 5, 5, l, []⟩, ⟨1, 5, 5, l, [0, 2, kA args]⟩, ⟨1, 5, 5, l, [1, 6, kEnd err]⟩, ⟨1, 5, 5, l, [2, 5, kB rest]⟩] ++ fzA args ++ fzEnd err ++ fzB rest
  | .bindAxiom (args := args) (rest := rest) .. => [⟨0, 5, 6, l, []⟩, ⟨1, 5, 6, l, [0, 2, kA args]⟩, ⟨1, 5, 6, l, [1, 5, kB rest]⟩] ++ fzA args ++ fzB rest
  | .bindAxiomElse (args := args) (err := err) (rest := rest) .. => [⟨0, 5, 7, l, []⟩, ⟨1, 5, 7, l, [0, 2, kA args]⟩, ⟨1, 5, 7, l, [1, 6, kEnd err]⟩, ⟨1, 5, 7, l, [2, 5, kB rest]⟩] ++ fzA args ++ fzEnd err ++ fzB rest
  | .regRead (rest := rest) .. => [⟨0, 5, 8, l, []⟩, ⟨1, 5, 8, l, [0, 5, kB rest]⟩] ++ fzB rest
  | .regReadElse (zusage := zusage) (sonst := sonst) (rest := rest) .. => [⟨0, 5, 9, l, [tk zusage]⟩, ⟨1, 5, 9, l, [0, 0, kE zusage]⟩, ⟨1, 5, 9, l, [1, 6, kEnd sonst]⟩, ⟨1, 5, 9, l, [2, 5, kB rest]⟩] ++ fzE zusage ++ fzEnd sonst ++ fzB rest
  | .awaits (rest := rest) .. => [⟨0, 5, 10, l, []⟩, ⟨1, 5, 10, l, [0, 5, kB rest]⟩] ++ fzB rest
  | .exchange (neu := neu) (rest := rest) .. => [⟨0, 5, 11, l, [tk neu]⟩, ⟨1, 5, 11, l, [0, 0, kE neu]⟩, ⟨1, 5, 11, l, [1, 5, kB rest]⟩] ++ fzE neu ++ fzB rest
  | .narrow (e := e) (sonst := sonst) (rest := rest) .. => [⟨0, 5, 12, l, [tk e]⟩, ⟨1, 5, 12, l, [0, 0, kE e]⟩, ⟨1, 5, 12, l, [1, 6, kEnd sonst]⟩, ⟨1, 5, 12, l, [2, 5, kB rest]⟩] ++ fzE e ++ fzEnd sonst ++ fzB rest
  | .check (c := c) (sonst := sonst) (rest := rest) .. => [⟨0, 5, 13, l, [tk c]⟩, ⟨1, 5, 13, l, [0, 0, kE c]⟩, ⟨1, 5, 13, l, [1, 6, kEnd sonst]⟩, ⟨1, 5, 13, l, [2, 5, kB rest]⟩] ++ fzE c ++ fzEnd sonst ++ fzB rest
  | .float (a := a) (b := b) (rest := rest) .. => [⟨0, 5, 14, l, [tk a, tk b]⟩, ⟨1, 5, 14, l, [0, 0, kE a]⟩, ⟨1, 5, 14, l, [1, 0, kE b]⟩, ⟨1, 5, 14, l, [2, 5, kB rest]⟩] ++ fzE a ++ fzE b ++ fzB rest
  | .floatLit (rest := rest) .. => [⟨0, 5, 15, l, []⟩, ⟨1, 5, 15, l, [0, 5, kB rest]⟩] ++ fzB rest
  | .floatOf (e := e) (rest := rest) .. => [⟨0, 5, 16, l, [tk e]⟩, ⟨1, 5, 16, l, [0, 0, kE e]⟩, ⟨1, 5, 16, l, [1, 5, kB rest]⟩] ++ fzE e ++ fzB rest
  | .floatNarrow (e := e) (sonst := sonst) (rest := rest) .. => [⟨0, 5, 17, l, [tk e]⟩, ⟨1, 5, 17, l, [0, 0, kE e]⟩, ⟨1, 5, 17, l, [1, 6, kEnd sonst]⟩, ⟨1, 5, 17, l, [2, 5, kB rest]⟩] ++ fzE e ++ fzEnd sonst ++ fzB rest

def fzEnd {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} : Endblock D V l Γ Λ → List FZelle
  | .ret (e := e) .. => [⟨0, 6, 0, l, []⟩, ⟨1, 6, 0, l, [0, 3, kR e]⟩] ++ fzR e
  | .retWhy .. => [⟨0, 6, 1, l, []⟩]
  | .leave .. => [⟨0, 6, 2, l, []⟩]
  | .next .. => [⟨0, 6, 3, l, []⟩]
  | .cons (s := s) (rest := rest) .. => [⟨0, 6, 4, l, []⟩, ⟨1, 6, 4, l, [0, 4, kS s]⟩, ⟨1, 6, 4, l, [1, 6, kEnd rest]⟩] ++ fzS s ++ fzEnd rest
  | .bind (e := e) (rest := rest) .. => [⟨0, 6, 5, l, [tk e]⟩, ⟨1, 6, 5, l, [0, 0, kE e]⟩, ⟨1, 6, 5, l, [1, 6, kEnd rest]⟩] ++ fzE e ++ fzEnd rest
  | .bindCall (args := args) (rest := rest) .. => [⟨0, 6, 6, l, []⟩, ⟨1, 6, 6, l, [0, 2, kA args]⟩, ⟨1, 6, 6, l, [1, 6, kEnd rest]⟩] ++ fzA args ++ fzEnd rest
  | .bindCallElse (args := args) (err := err) (rest := rest) .. => [⟨0, 6, 7, l, []⟩, ⟨1, 6, 7, l, [0, 2, kA args]⟩, ⟨1, 6, 7, l, [1, 6, kEnd err]⟩, ⟨1, 6, 7, l, [2, 6, kEnd rest]⟩] ++ fzA args ++ fzEnd err ++ fzEnd rest
  | .bindAxiom (args := args) (rest := rest) .. => [⟨0, 6, 8, l, []⟩, ⟨1, 6, 8, l, [0, 2, kA args]⟩, ⟨1, 6, 8, l, [1, 6, kEnd rest]⟩] ++ fzA args ++ fzEnd rest
  | .bindAxiomElse (args := args) (err := err) (rest := rest) .. => [⟨0, 6, 9, l, []⟩, ⟨1, 6, 9, l, [0, 2, kA args]⟩, ⟨1, 6, 9, l, [1, 6, kEnd err]⟩, ⟨1, 6, 9, l, [2, 6, kEnd rest]⟩] ++ fzA args ++ fzEnd err ++ fzEnd rest
  | .regRead (rest := rest) .. => [⟨0, 6, 10, l, []⟩, ⟨1, 6, 10, l, [0, 6, kEnd rest]⟩] ++ fzEnd rest
  | .regReadElse (zusage := zusage) (sonst := sonst) (rest := rest) .. => [⟨0, 6, 11, l, [tk zusage]⟩, ⟨1, 6, 11, l, [0, 0, kE zusage]⟩, ⟨1, 6, 11, l, [1, 6, kEnd sonst]⟩, ⟨1, 6, 11, l, [2, 6, kEnd rest]⟩] ++ fzE zusage ++ fzEnd sonst ++ fzEnd rest
  | .awaits (rest := rest) .. => [⟨0, 6, 12, l, []⟩, ⟨1, 6, 12, l, [0, 6, kEnd rest]⟩] ++ fzEnd rest
  | .bindCallInd (p := p) (args := args) (rest := rest) .. => [⟨0, 6, 13, l, [tk p]⟩, ⟨1, 6, 13, l, [0, 0, kE p]⟩, ⟨1, 6, 13, l, [1, 2, kA args]⟩, ⟨1, 6, 13, l, [2, 6, kEnd rest]⟩] ++ fzE p ++ fzA args ++ fzEnd rest

def fzArms {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option (Int × Int))} : Arms D V l Γ Λ Λ' cs → List FZelle
  | .nil .. => [⟨0, 7, 0, l, []⟩]
  | .cons (b := b) (rest := rest) .. => [⟨0, 7, 1, l, []⟩, ⟨1, 7, 1, l, [0, 5, kB b]⟩, ⟨1, 7, 1, l, [1, 7, kArms rest]⟩] ++ fzB b ++ fzArms rest

def fzGArms {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat} : GrundArms D V l Γ Λ Λ' n → List FZelle
  | .nil .. => [⟨0, 8, 0, l, []⟩]
  | .cons (b := b) (rest := rest) .. => [⟨0, 8, 1, l, []⟩, ⟨1, 8, 1, l, [0, 5, kB b]⟩, ⟨1, 8, 1, l, [1, 8, kGArms rest]⟩] ++ fzB b ++ fzGArms rest

end

/-- **The fine cells of a program**: of every body and every contract and invariant. -/
def _root_.Gabbro.Grammatik.Gen.Einsatz.feinZellen (e : Gen.Einsatz) : List FZelle :=
  letI := e.aufz
  e.fs.flatMap (fun f => fzEnd (e.P.rumpf f) ++ fzE (e.P.requires f) ++ fzE (e.P.ensures f)) ++
    e.D.invs.flatMap fun i => fzE (e.P.invariante i)

/-- The occurrence relation of the fine cells. -/
abbrev _root_.Gabbro.Grammatik.Gen.Einsatz.HatF (e : Gen.Einsatz) (z : FZelle) : Prop := z ∈ e.feinZellen

end Gabbro.Grammatik.Gen.Fein
