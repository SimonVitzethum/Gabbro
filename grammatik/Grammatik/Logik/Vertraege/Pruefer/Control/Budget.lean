module

public import Grammatik.Logik.Invarianten.VC.Compiler

@[expose] public section

namespace Gabbro.Grammatik.Vertraege.Pruefer

variable {D : Deklaration} {V : Vertrag D}

/-- Saturation makes the preflight independent of the magnitude of a type's
    interval. It never constructs decoded values or generates a continuation. -/
def specializationCount (limit : Nat) : Ty → Nat
  | .int _ _ => 1
  | .bool => 2
  | _ => 1

def argumentSpecializations (limit : Nat) (types : Ctx) : Nat :=
  types.foldr (fun type rest => min (limit + 1) (specializationCount limit type * rest)) 1

def resultSpecializations (limit : Nat) : Option Ty → Nat
  | none => 1
  | some type => specializationCount limit type

/-- This is the source case carrying a certified uniform return family and
    permitting shared, result-independent call continuations. -/
def uniformPost (program : Programm D) (f : D.Fn) : Bool :=
  match program.ensures f with
  | .tru => true
  | _ => false

/-- Wide domains fail before enumeration and the constant fallback creates
    one continuation. Interval widening shares the decoded input selection. -/
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
def statementSpecializations (program : Programm D) (uniformReturn : Bool) (expansion limit continuation : Nat) {l Γ Λ Λ'} : Stmt D V l Γ Λ Λ' → Nat
  | .assignVar _ expression => min (limit + 1)
      (selectionSpecializations expansion limit expression * continuation)
  | .ret expression _ | .retScoped expression _ =>
      if uniformReturn then 1 else returnSpecializations expansion limit expression
  | .retWhy .. | .retWhyScoped .. | .leave .. | .next .. => 1
  | .call f args _ _ => min (limit + 1)
      (argumentSelectionSpecializations expansion limit args *
        (if uniformPost program f then 1 else resultSpecializations limit (D.erg f)) + continuation)
  | .ite _ yes no => min (limit + 1)
      (blockSpecializations program uniformReturn expansion limit continuation yes + blockSpecializations program uniformReturn expansion limit continuation no)
  | .breaking _ body | .locks _ _ body => blockSpecializations program uniformReturn expansion limit continuation body
  | .onWhy _ arms => reasonSpecializations program uniformReturn expansion limit continuation arms
  | .retry 0 _ _ overflow => min (limit + 1)
      (continuation + blockSpecializations program uniformReturn expansion limit continuation overflow)
  | .retry count _ body overflow => min (limit + 1)
      ((count + 1) * blockSpecializations program uniformReturn expansion limit continuation body +
        blockSpecializations program uniformReturn expansion limit continuation overflow)
  | .traverse table _ body => min (limit + 1)
      ((D.count table).toNat * blockSpecializations program uniformReturn expansion limit continuation body + continuation)
  | _ => continuation

def blockSpecializations (program : Programm D) (uniformReturn : Bool) (expansion limit continuation : Nat) {l Γ Λ Λ'} : Block D V l Γ Λ Λ' → Nat
  | .nil => continuation
  | .cons head tail => statementSpecializations program uniformReturn expansion limit (blockSpecializations program uniformReturn expansion limit continuation tail) head
  | .bind expression tail => min (limit + 1)
      (selectionSpecializations expansion limit expression * blockSpecializations program uniformReturn expansion limit continuation tail)
  | .bindCall f args _ _ _ tail => min (limit + 1)
      (argumentSelectionSpecializations expansion limit args * resultSpecializations limit (D.erg f) *
        blockSpecializations program uniformReturn expansion limit continuation tail)
  | .bindCallElse f args _ _ _ failure tail => min (limit + 1)
      (argumentSelectionSpecializations expansion limit args *
        (resultSpecializations limit (D.erg f) * blockSpecializations program uniformReturn expansion limit continuation tail +
          D.gruende f * endSpecializations program uniformReturn expansion limit failure))
  | .check _ failure tail => min (limit + 1)
      (endSpecializations program uniformReturn expansion limit failure + blockSpecializations program uniformReturn expansion limit continuation tail)
  | .narrow (lo := lo) (hi := hi) _ _ _ failure tail => min (limit + 1)
      (specializationCount limit (.int lo hi) *
        (endSpecializations program uniformReturn expansion limit failure + blockSpecializations program uniformReturn expansion limit continuation tail))
  | .narrowRequired (lo := lo) (hi := hi) _ _ _ tail => min (limit + 1)
      (specializationCount limit (.int lo hi) * blockSpecializations program uniformReturn expansion limit continuation tail)
  | _ => continuation

def endSpecializations (program : Programm D) (uniformReturn : Bool) (expansion limit : Nat) {l Γ Λ} : Endblock D V l Γ Λ → Nat
  | .ret expression _ | .retScoped expression _ =>
      if uniformReturn then 1 else returnSpecializations expansion limit expression
  | .cons head tail => statementSpecializations program uniformReturn expansion limit (endSpecializations program uniformReturn expansion limit tail) head
  | .bind expression tail => min (limit + 1)
      (selectionSpecializations expansion limit expression * endSpecializations program uniformReturn expansion limit tail)
  | .bindCall f args _ _ _ tail => min (limit + 1)
      (argumentSelectionSpecializations expansion limit args * resultSpecializations limit (D.erg f) *
        endSpecializations program uniformReturn expansion limit tail)
  | .bindCallElse f args _ _ _ failure tail => min (limit + 1)
      (argumentSelectionSpecializations expansion limit args *
        (resultSpecializations limit (D.erg f) * endSpecializations program uniformReturn expansion limit tail +
          D.gruende f * endSpecializations program uniformReturn expansion limit failure))
  | .ite _ yes no => min (limit + 1)
      (endSpecializations program uniformReturn expansion limit yes + endSpecializations program uniformReturn expansion limit no)
  | .narrow (lo := lo) (hi := hi) _ _ _ failure tail => min (limit + 1)
      (specializationCount limit (.int lo hi) *
        (endSpecializations program uniformReturn expansion limit failure + endSpecializations program uniformReturn expansion limit tail))
  | .narrowRequired (lo := lo) (hi := hi) _ _ _ tail => min (limit + 1)
      (specializationCount limit (.int lo hi) * endSpecializations program uniformReturn expansion limit tail)
  | _ => 1

def reasonSpecializations (program : Programm D) (uniformReturn : Bool) (expansion limit continuation : Nat) {l Γ Λ Λ' count} :
    GrundArms D V l Γ Λ Λ' count → Nat
  | .nil => 0
  | .cons head tail => min (limit + 1)
      (blockSpecializations program uniformReturn expansion limit continuation head + reasonSpecializations program uniformReturn expansion limit continuation tail)

end

end Gabbro.Grammatik.Vertraege.Pruefer
