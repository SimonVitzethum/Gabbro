module

public import Grammatik.Logik.Invarianten.VC.Compiler

@[expose] public section

namespace Gabbro.Grammatik.Vertraege.Pruefer

variable {D : Deklaration} {V : Vertrag D}

mutual

/-- Saturation makes the preflight independent of the magnitude of a type's
    interval. It never constructs decoded values or generates a continuation. -/
def specializationCount (limit : Nat) : Ty → Nat
  | .int _ _ => 1
  | .bool => 2
  | .prod _ fields => argumentSpecializations limit fields
  | .why count => min (limit + 1) count
  | .opt count => min (limit + 1) (count.toNat + 1)
  | .sum cases => caseSpecializations limit cases
  | _ => 1
termination_by structural kind => kind

def caseSpecializations (limit : Nat) : List (Option Ty) → Nat
  | [] => 0
  | none :: rest => min (limit + 1) (1 + caseSpecializations limit rest)
  | some kind :: rest => min (limit + 1) (specializationCount limit kind + caseSpecializations limit rest)
termination_by structural cases => cases

def argumentSpecializations (limit : Nat) : Ctx → Nat
  | [] => 1
  | kind :: rest => min (limit + 1) (specializationCount limit kind * argumentSpecializations limit rest)
termination_by structural kinds => kinds

end

def resultSpecializations (limit : Nat) : Option Ty → Nat
  | none => 1
  | some type => specializationCount limit type

/-- Literal truth permits a certified shared call continuation without
    observing the answer. This flag estimates its finite compilation work. -/
def uniformPost (program : Programm D) (f : D.Fn) : Bool :=
  match program.ensures f with
  | .tru => true
  | _ => false

/-- Integer selections have one symbolic continuation, independently of their
    range. Finite Boolean alternatives retain their actual case count. -/
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
def statementSpecializations (program : Programm D) (uniformReturn : Bool) (join : Bool) (expansion limit continuation : Nat) {l Γ Λ Λ'} : Stmt D V l Γ Λ Λ' → Nat
  | .assignVar _ expression => min (limit + 1)
      (selectionSpecializations expansion limit expression * continuation)
  | .ret expression _ | .retScoped expression _ =>
      if uniformReturn then 1 else returnSpecializations expansion limit expression
  | .retWhy .. | .retWhyScoped .. | .leave .. | .next .. => 1
  | .call f args _ _ => min (limit + 1)
      (argumentSelectionSpecializations expansion limit args *
        (if uniformPost program f then 1 else resultSpecializations limit (D.erg f)) + continuation)
  | .ite _ yes no => min (limit + 1)
      (if join then blockSpecializations program uniformReturn join expansion limit 1 yes +
          blockSpecializations program uniformReturn join expansion limit 1 no + continuation
        else blockSpecializations program uniformReturn join expansion limit continuation yes +
          blockSpecializations program uniformReturn join expansion limit continuation no)
  | .breaking _ body | .locks _ _ body => blockSpecializations program uniformReturn join expansion limit continuation body
  | .onWhy _ arms => reasonSpecializations program uniformReturn join expansion limit continuation arms
  | .onOption _ present absent => min (limit + 1)
      (blockSpecializations program uniformReturn join expansion limit continuation present +
        blockSpecializations program uniformReturn join expansion limit continuation absent)
  | .onTag _ arms =>
      if join then min (limit + 1)
        (tagSpecializations program uniformReturn join expansion limit 1 arms + continuation)
      else tagSpecializations program uniformReturn join expansion limit continuation arms
  | .retry 0 _ _ overflow => min (limit + 1)
      (continuation + blockSpecializations program uniformReturn join expansion limit continuation overflow)
  | .retry count _ body overflow => min (limit + 1)
      ((count + 1) * blockSpecializations program uniformReturn join expansion limit continuation body +
        blockSpecializations program uniformReturn join expansion limit continuation overflow)
  | .traverse table _ body => min (limit + 1)
      ((if (D.count table).toNat ≤ expansion then (D.count table).toNat else 1) * blockSpecializations program uniformReturn join expansion limit continuation body + continuation)
  | _ => continuation

def blockSpecializations (program : Programm D) (uniformReturn : Bool) (join : Bool) (expansion limit continuation : Nat) {l Γ Λ Λ'} : Block D V l Γ Λ Λ' → Nat
  | .nil => continuation
  | .cons head tail => statementSpecializations program uniformReturn join expansion limit (blockSpecializations program uniformReturn join expansion limit continuation tail) head
  | .bind expression tail => min (limit + 1)
      (selectionSpecializations expansion limit expression * blockSpecializations program uniformReturn join expansion limit continuation tail)
  | .bindAxiom a _ _ _ _ _ _ tail | .bindAxiomOpt _ a _ _ _ _ _ tail => min (limit + 1)
      (resultSpecializations limit (D.aerg a) * blockSpecializations program uniformReturn join expansion limit continuation tail)
  | .bindAxiomElse a _ _ _ _ _ _ _ failure tail | .bindAxiomOptElse _ a _ _ _ _ _ _ failure tail => min (limit + 1)
      (resultSpecializations limit (D.aerg a) * blockSpecializations program uniformReturn join expansion limit continuation tail +
        D.agruende a * endSpecializations program uniformReturn join expansion limit failure)
  | .bindCall f args _ _ _ tail => min (limit + 1)
      (argumentSelectionSpecializations expansion limit args * resultSpecializations limit (D.erg f) *
        blockSpecializations program uniformReturn join expansion limit continuation tail)
  | .bindCallElse f args _ _ _ failure tail => min (limit + 1)
      (argumentSelectionSpecializations expansion limit args *
        (resultSpecializations limit (D.erg f) * blockSpecializations program uniformReturn join expansion limit continuation tail +
          D.gruende f * endSpecializations program uniformReturn join expansion limit failure))
  | .check _ failure tail => min (limit + 1)
      (endSpecializations program uniformReturn join expansion limit failure + blockSpecializations program uniformReturn join expansion limit continuation tail)
  | .floatNarrow _ _ _ failure tail => min (limit + 1)
      (endSpecializations program uniformReturn join expansion limit failure +
        blockSpecializations program uniformReturn join expansion limit continuation tail)
  | .narrow (lo := lo) (hi := hi) _ _ _ failure tail => min (limit + 1)
      (specializationCount limit (.int lo hi) *
        (endSpecializations program uniformReturn join expansion limit failure + blockSpecializations program uniformReturn join expansion limit continuation tail))
  | .narrowRequired (lo := lo) (hi := hi) _ _ _ tail => min (limit + 1)
      (specializationCount limit (.int lo hi) * blockSpecializations program uniformReturn join expansion limit continuation tail)
  | _ => continuation

def endSpecializations (program : Programm D) (uniformReturn : Bool) (join : Bool) (expansion limit : Nat) {l Γ Λ} : Endblock D V l Γ Λ → Nat
  | .ret expression _ | .retScoped expression _ =>
      if uniformReturn then 1 else returnSpecializations expansion limit expression
  | .cons head tail => statementSpecializations program uniformReturn join expansion limit (endSpecializations program uniformReturn join expansion limit tail) head
  | .bind expression tail => min (limit + 1)
      (selectionSpecializations expansion limit expression * endSpecializations program uniformReturn join expansion limit tail)
  | .bindAxiom a _ _ _ _ _ _ tail | .bindAxiomOpt _ a _ _ _ _ _ tail => min (limit + 1)
      (resultSpecializations limit (D.aerg a) * endSpecializations program uniformReturn join expansion limit tail)
  | .bindAxiomElse a _ _ _ _ _ _ _ failure tail | .bindAxiomOptElse _ a _ _ _ _ _ _ failure tail => min (limit + 1)
      (resultSpecializations limit (D.aerg a) * endSpecializations program uniformReturn join expansion limit tail +
        D.agruende a * endSpecializations program uniformReturn join expansion limit failure)
  | .bindCall f args _ _ _ tail => min (limit + 1)
      (argumentSelectionSpecializations expansion limit args * resultSpecializations limit (D.erg f) *
        endSpecializations program uniformReturn join expansion limit tail)
  | .bindCallElse f args _ _ _ failure tail => min (limit + 1)
      (argumentSelectionSpecializations expansion limit args *
        (resultSpecializations limit (D.erg f) * endSpecializations program uniformReturn join expansion limit tail +
          D.gruende f * endSpecializations program uniformReturn join expansion limit failure))
  | .ite _ yes no => min (limit + 1)
      (endSpecializations program uniformReturn join expansion limit yes + endSpecializations program uniformReturn join expansion limit no)
  | .floatNarrow _ _ _ failure tail => min (limit + 1)
      (endSpecializations program uniformReturn join expansion limit failure +
        endSpecializations program uniformReturn join expansion limit tail)
  | .narrow (lo := lo) (hi := hi) _ _ _ failure tail => min (limit + 1)
      (specializationCount limit (.int lo hi) *
        (endSpecializations program uniformReturn join expansion limit failure + endSpecializations program uniformReturn join expansion limit tail))
  | .narrowRequired (lo := lo) (hi := hi) _ _ _ tail => min (limit + 1)
      (specializationCount limit (.int lo hi) * endSpecializations program uniformReturn join expansion limit tail)
  | _ => 1

def reasonSpecializations (program : Programm D) (uniformReturn : Bool) (join : Bool) (expansion limit continuation : Nat) {l Γ Λ Λ' count} :
    GrundArms D V l Γ Λ Λ' count → Nat
  | .nil => 0
  | .cons head tail => min (limit + 1)
      (blockSpecializations program uniformReturn join expansion limit continuation head + reasonSpecializations program uniformReturn join expansion limit continuation tail)

def tagSpecializations (program : Programm D) (uniformReturn : Bool) (join : Bool) (expansion limit continuation : Nat) {l Γ Λ Λ' cases} :
    Arms D V l Γ Λ Λ' cases → Nat
  | .nil => 0
  | .cons (c := none) head tail => min (limit + 1)
      (blockSpecializations program uniformReturn join expansion limit continuation head +
        tagSpecializations program uniformReturn join expansion limit continuation tail)
  | .cons (c := some kind) head tail => min (limit + 1)
      (specializationCount limit kind * blockSpecializations program uniformReturn join expansion limit continuation head +
        tagSpecializations program uniformReturn join expansion limit continuation tail)

end

end Gabbro.Grammatik.Vertraege.Pruefer
