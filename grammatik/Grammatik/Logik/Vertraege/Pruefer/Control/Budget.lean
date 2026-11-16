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
def selectionSpecializations (limit : Nat) {Γ Λ type} : Expr D Γ Λ type → Nat
  | .var _ => 1
  | .widen _ _ body => selectionSpecializations limit body
  | _ => specializationCount limit type

def argumentSelectionSpecializations (limit : Nat) {Γ Λ types} : Args D Γ Λ types → Nat
  | .nil => 1
  | .cons head tail => min (limit + 1)
      (selectionSpecializations limit head * argumentSelectionSpecializations limit tail)

def returnSpecializations (limit : Nat) {Γ Λ kind} : ErgExpr D Γ Λ kind → Nat
  | .empty => 1
  | .val expression => selectionSpecializations limit expression

mutual

/-- Charge a continuation only on paths that reach it. Early returns carry
    their own cost; a discarded call shares its already compiled tail. This
    mirrors the WP compiler rather than multiplying unrelated exit families. -/
def statementSpecializations (limit continuation : Nat) {l Γ Λ Λ'} : Stmt D V l Γ Λ Λ' → Nat
  | .assignVar _ expression => min (limit + 1)
      (selectionSpecializations limit expression * continuation)
  | .ret expression _ | .retScoped expression _ => returnSpecializations limit expression
  | .retWhy .. | .retWhyScoped .. | .leave .. | .next .. => 1
  | .call f args _ _ => min (limit + 1)
      (argumentSelectionSpecializations limit args * resultSpecializations limit (D.erg f) + continuation)
  | .ite _ yes no => min (limit + 1)
      (blockSpecializations limit continuation yes + blockSpecializations limit continuation no)
  | .breaking _ body | .locks _ _ body => blockSpecializations limit continuation body
  | .onWhy _ arms => reasonSpecializations limit continuation arms
  | .retry 0 _ _ overflow => min (limit + 1)
      (continuation + blockSpecializations limit continuation overflow)
  | .retry count _ body overflow => min (limit + 1)
      ((count + 1) * blockSpecializations limit continuation body +
        blockSpecializations limit continuation overflow)
  | .traverse table _ body => min (limit + 1)
      ((D.count table).toNat * blockSpecializations limit continuation body + continuation)
  | _ => continuation

def blockSpecializations (limit continuation : Nat) {l Γ Λ Λ'} : Block D V l Γ Λ Λ' → Nat
  | .nil => continuation
  | .cons head tail => statementSpecializations limit (blockSpecializations limit continuation tail) head
  | .bind expression tail => min (limit + 1)
      (selectionSpecializations limit expression * blockSpecializations limit continuation tail)
  | .bindCall f args _ _ _ tail => min (limit + 1)
      (argumentSelectionSpecializations limit args * resultSpecializations limit (D.erg f) *
        blockSpecializations limit continuation tail)
  | .bindCallElse f args _ _ _ failure tail => min (limit + 1)
      (argumentSelectionSpecializations limit args *
        (resultSpecializations limit (D.erg f) * blockSpecializations limit continuation tail +
          D.gruende f * endSpecializations limit failure))
  | .check _ failure tail => min (limit + 1)
      (endSpecializations limit failure + blockSpecializations limit continuation tail)
  | .narrow (lo := lo) (hi := hi) _ _ _ failure tail => min (limit + 1)
      (specializationCount limit (.int lo hi) *
        (endSpecializations limit failure + blockSpecializations limit continuation tail))
  | .narrowRequired (lo := lo) (hi := hi) _ _ _ tail => min (limit + 1)
      (specializationCount limit (.int lo hi) * blockSpecializations limit continuation tail)
  | _ => continuation

def endSpecializations (limit : Nat) {l Γ Λ} : Endblock D V l Γ Λ → Nat
  | .ret expression _ | .retScoped expression _ => returnSpecializations limit expression
  | .cons head tail => statementSpecializations limit (endSpecializations limit tail) head
  | .bind expression tail => min (limit + 1)
      (selectionSpecializations limit expression * endSpecializations limit tail)
  | .bindCall f args _ _ _ tail => min (limit + 1)
      (argumentSelectionSpecializations limit args * resultSpecializations limit (D.erg f) *
        endSpecializations limit tail)
  | .bindCallElse f args _ _ _ failure tail => min (limit + 1)
      (argumentSelectionSpecializations limit args *
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

def reasonSpecializations (limit continuation : Nat) {l Γ Λ Λ' count} :
    GrundArms D V l Γ Λ Λ' count → Nat
  | .nil => 0
  | .cons head tail => min (limit + 1)
      (blockSpecializations limit continuation head + reasonSpecializations limit continuation tail)

end

end Gabbro.Grammatik.Vertraege.Pruefer
