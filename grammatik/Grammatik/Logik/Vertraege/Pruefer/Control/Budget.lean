module

public import Grammatik.Logik.Invarianten.VC.Compiler

@[expose] public section

namespace Gabbro.Grammatik.Vertraege.Pruefer

variable {D : Deklaration} {V : Vertrag D}

/-- Saturation makes the preflight independent of the magnitude of a type's
    interval. It never constructs decoded values or generates a continuation. -/
def specializationCount (limit : Nat) : Ty → Nat
  | .int lo hi => min (limit + 1) (hi - lo + 1).toNat
  | .bool => 2
  | _ => 1

def argumentSpecializations (limit : Nat) (types : Ctx) : Nat :=
  types.foldr (fun type rest => min (limit + 1) (specializationCount limit type * rest)) 1

def resultSpecializations (limit : Nat) : Option Ty → Nat
  | none => 1
  | some type => specializationCount limit type

/-- Interval widening does not create a new observation or split a decoded
    value. Follow the same return rule as the semantic compiler. -/
def expressionReturnSpecializations (limit : Nat) {Γ Λ type} : Expr D Γ Λ type → Nat
  | .var _ => 1
  | .widen _ _ body => expressionReturnSpecializations limit body
  | _ => specializationCount limit type

def returnSpecializations (limit : Nat) {Γ Λ kind} : ErgExpr D Γ Λ kind → Nat
  | .empty => 1
  | .val expression => expressionReturnSpecializations limit expression

mutual

/-- This scan only refines the resource estimate. Actual admission still
    comes from the unchanged semantic condition, including every early exit. -/
def statementMayContinue {l Γ Λ Λ'} : Stmt D V l Γ Λ Λ' → Bool
  | .ret .. | .retWhy .. | .retScoped .. | .retWhyScoped .. | .leave .. | .next .. => false
  | .ite _ yes no => blockMayContinue yes || blockMayContinue no
  | .breaking _ body | .locks _ _ body => blockMayContinue body
  | .onWhy _ arms => reasonsMayContinue arms
  | _ => true

def blockMayContinue {l Γ Λ Λ'} : Block D V l Γ Λ Λ' → Bool
  | .cons first rest => statementMayContinue first && blockMayContinue rest
  | .bind _ rest | .bindCall _ _ _ _ _ rest | .bindCallElse _ _ _ _ _ _ rest
    | .narrow _ _ _ _ rest | .narrowRequired _ _ _ rest | .check _ _ rest => blockMayContinue rest
  | _ => true

def reasonsMayContinue {l Γ Λ Λ' count} : GrundArms D V l Γ Λ Λ' count → Bool
  | .nil => false
  | .cons head tail => blockMayContinue head || reasonsMayContinue tail

end

mutual

/-- Bound the finite-specialization compiler before executing it. Products
    include discarded call results and argument selection, not merely the
    largest individual type. Refusing this budget supplies no semantic fact. -/
def statementSpecializations (limit : Nat) {l Γ Λ Λ'} : Stmt D V l Γ Λ Λ' → Nat
  | .assignVar (τ := type) _ _ => specializationCount limit type
  | .ret expression _ | .retScoped expression _ => returnSpecializations limit expression
  | .call f _ _ _ => min (limit + 1)
      (argumentSpecializations limit (D.params f) * resultSpecializations limit (D.erg f))
  | .ite _ yes no => min (limit + 1)
      (blockSpecializations limit yes + blockSpecializations limit no)
  | .breaking _ body | .locks _ _ body => blockSpecializations limit body
  | .onWhy _ arms => reasonSpecializations limit arms
  | .retry 0 _ _ overflow => min (limit + 1) (1 + blockSpecializations limit overflow)
  | .retry count _ body overflow => min (limit + 1)
      ((count + 1) * blockSpecializations limit body + blockSpecializations limit overflow)
  | .traverse table _ body => min (limit + 1)
      ((D.count table).toNat * blockSpecializations limit body + 1)
  | _ => 1

def blockSpecializations (limit : Nat) {l Γ Λ Λ'} : Block D V l Γ Λ Λ' → Nat
  | .nil => 1
  | .cons head tail =>
      if statementMayContinue head then min (limit + 1)
        (statementSpecializations limit head * blockSpecializations limit tail)
      else statementSpecializations limit head
  | .bind (τ := type) _ tail => min (limit + 1)
      (specializationCount limit type * blockSpecializations limit tail)
  | .bindCall f _ _ _ _ tail => min (limit + 1)
      (argumentSpecializations limit (D.params f) * resultSpecializations limit (D.erg f) *
        blockSpecializations limit tail)
  | .bindCallElse f _ _ _ _ failure tail => min (limit + 1)
      (argumentSpecializations limit (D.params f) *
        (resultSpecializations limit (D.erg f) * blockSpecializations limit tail +
          D.gruende f * endSpecializations limit failure))
  | .check _ failure tail => min (limit + 1)
      (endSpecializations limit failure + blockSpecializations limit tail)
  | .narrow (lo := lo) (hi := hi) _ _ _ failure tail => min (limit + 1)
      (specializationCount limit (.int lo hi) *
        (endSpecializations limit failure + blockSpecializations limit tail))
  | .narrowRequired (lo := lo) (hi := hi) _ _ _ tail => min (limit + 1)
      (specializationCount limit (.int lo hi) * blockSpecializations limit tail)
  | _ => 1

def endSpecializations (limit : Nat) {l Γ Λ} : Endblock D V l Γ Λ → Nat
  | .ret expression _ | .retScoped expression _ => returnSpecializations limit expression
  | .cons head tail =>
      if statementMayContinue head then min (limit + 1)
        (statementSpecializations limit head * endSpecializations limit tail)
      else statementSpecializations limit head
  | .bind (τ := type) _ tail => min (limit + 1)
      (specializationCount limit type * endSpecializations limit tail)
  | .bindCall f _ _ _ _ tail => min (limit + 1)
      (argumentSpecializations limit (D.params f) * resultSpecializations limit (D.erg f) *
        endSpecializations limit tail)
  | .bindCallElse f _ _ _ _ failure tail => min (limit + 1)
      (argumentSpecializations limit (D.params f) *
        (resultSpecializations limit (D.erg f) * endSpecializations limit tail +
          D.gruende f * endSpecializations limit failure))
  | .ite _ yes no => min (limit + 1)
      (endSpecializations limit yes + endSpecializations limit no)
  | .narrow (lo := lo) (hi := hi) _ _ _ failure tail => min (limit + 1)
      (specializationCount limit (.int lo hi) *
        (endSpecializations limit failure + endSpecializations limit tail))
  | .narrowRequired (lo := lo) (hi := hi) _ _ _ tail => min (limit + 1)
      (specializationCount limit (.int lo hi) * endSpecializations limit tail)
  | _ => 1

def reasonSpecializations (limit : Nat) {l Γ Λ Λ' count} :
    GrundArms D V l Γ Λ Λ' count → Nat
  | .nil => 0
  | .cons head tail => min (limit + 1)
      (blockSpecializations limit head + reasonSpecializations limit tail)

end

end Gabbro.Grammatik.Vertraege.Pruefer
