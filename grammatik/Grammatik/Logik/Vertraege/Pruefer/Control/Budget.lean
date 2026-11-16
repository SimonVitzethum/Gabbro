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
def selectionSpecializations (expansion limit : Nat) {Γ Λ type} : Expr D Γ Λ type → Nat
  | .var _ => 1
  | .widen _ _ body => selectionSpecializations expansion limit body
  | _ => if specializationCount expansion type > expansion then 1
      else specializationCount limit type

def argumentSelectionSpecializations (expansion limit : Nat) {Γ Λ types} : Args D Γ Λ types → Nat
  | .nil => 1
  | .cons head tail => min (limit + 1)
      (selectionSpecializations expansion limit head * argumentSelectionSpecializations expansion limit tail)

def returnSpecializations (expansion limit : Nat) {Γ Λ kind} : ErgExpr D Γ Λ kind → Nat
  | .empty => 1
  | .val expression => selectionSpecializations expansion limit expression

mutual

/-- Charge a continuation only on paths that reach it. Early returns carry
    their own cost; a discarded call shares its already compiled tail. This
    mirrors the WP compiler rather than multiplying unrelated exit families. -/
def statementSpecializations (expansion limit continuation : Nat) {l Γ Λ Λ'} : Stmt D V l Γ Λ Λ' → Nat
  | .assignVar _ expression => min (limit + 1)
      (selectionSpecializations expansion limit expression * continuation)
  | .ret expression _ | .retScoped expression _ => returnSpecializations expansion limit expression
  | .retWhy .. | .retWhyScoped .. | .leave .. | .next .. => 1
  | .call f args _ _ => min (limit + 1)
      (argumentSelectionSpecializations expansion limit args * resultSpecializations limit (D.erg f) + continuation)
  | .ite _ yes no => min (limit + 1)
      (blockSpecializations expansion limit continuation yes + blockSpecializations expansion limit continuation no)
  | .breaking _ body | .locks _ _ body => blockSpecializations expansion limit continuation body
  | .onWhy _ arms => reasonSpecializations expansion limit continuation arms
  | .retry 0 _ _ overflow => min (limit + 1)
      (continuation + blockSpecializations expansion limit continuation overflow)
  | .retry count _ body overflow => min (limit + 1)
      ((count + 1) * blockSpecializations expansion limit continuation body +
        blockSpecializations expansion limit continuation overflow)
  | .traverse table _ body => min (limit + 1)
      ((D.count table).toNat * blockSpecializations expansion limit continuation body + continuation)
  | _ => continuation

def blockSpecializations (expansion limit continuation : Nat) {l Γ Λ Λ'} : Block D V l Γ Λ Λ' → Nat
  | .nil => continuation
  | .cons head tail => statementSpecializations expansion limit (blockSpecializations expansion limit continuation tail) head
  | .bind expression tail => min (limit + 1)
      (selectionSpecializations expansion limit expression * blockSpecializations expansion limit continuation tail)
  | .bindCall f args _ _ _ tail => min (limit + 1)
      (argumentSelectionSpecializations expansion limit args * resultSpecializations limit (D.erg f) *
        blockSpecializations expansion limit continuation tail)
  | .bindCallElse f args _ _ _ failure tail => min (limit + 1)
      (argumentSelectionSpecializations expansion limit args *
        (resultSpecializations limit (D.erg f) * blockSpecializations expansion limit continuation tail +
          D.gruende f * endSpecializations expansion limit failure))
  | .check _ failure tail => min (limit + 1)
      (endSpecializations expansion limit failure + blockSpecializations expansion limit continuation tail)
  | .narrow (lo := lo) (hi := hi) _ _ _ failure tail => min (limit + 1)
      (specializationCount limit (.int lo hi) *
        (endSpecializations expansion limit failure + blockSpecializations expansion limit continuation tail))
  | .narrowRequired (lo := lo) (hi := hi) _ _ _ tail => min (limit + 1)
      (specializationCount limit (.int lo hi) * blockSpecializations expansion limit continuation tail)
  | _ => continuation

def endSpecializations (expansion limit : Nat) {l Γ Λ} : Endblock D V l Γ Λ → Nat
  | .ret expression _ | .retScoped expression _ => returnSpecializations expansion limit expression
  | .cons head tail => statementSpecializations expansion limit (endSpecializations expansion limit tail) head
  | .bind expression tail => min (limit + 1)
      (selectionSpecializations expansion limit expression * endSpecializations expansion limit tail)
  | .bindCall f args _ _ _ tail => min (limit + 1)
      (argumentSelectionSpecializations expansion limit args * resultSpecializations limit (D.erg f) *
        endSpecializations expansion limit tail)
  | .bindCallElse f args _ _ _ failure tail => min (limit + 1)
      (argumentSelectionSpecializations expansion limit args *
        (resultSpecializations limit (D.erg f) * endSpecializations expansion limit tail +
          D.gruende f * endSpecializations expansion limit failure))
  | .ite _ yes no => min (limit + 1)
      (endSpecializations expansion limit yes + endSpecializations expansion limit no)
  | .narrow (lo := lo) (hi := hi) _ _ _ failure tail => min (limit + 1)
      (specializationCount limit (.int lo hi) *
        (endSpecializations expansion limit failure + endSpecializations expansion limit tail))
  | .narrowRequired (lo := lo) (hi := hi) _ _ _ tail => min (limit + 1)
      (specializationCount limit (.int lo hi) * endSpecializations expansion limit tail)
  | _ => 1

def reasonSpecializations (expansion limit continuation : Nat) {l Γ Λ Λ' count} :
    GrundArms D V l Γ Λ Λ' count → Nat
  | .nil => 0
  | .cons head tail => min (limit + 1)
      (blockSpecializations expansion limit continuation head + reasonSpecializations expansion limit continuation tail)

end

end Gabbro.Grammatik.Vertraege.Pruefer
