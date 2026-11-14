module

public import Grammatik.Logik.Vertraege.Pruefer.Leaves

@[expose] public section

namespace Gabbro.Grammatik.Vertraege.Pruefer

open Invarianten Invarianten.Frag Invarianten.Elim Invarianten.VC

variable {D : Deklaration} {S : SperrInv D} {program : Programm D}

/-- Enumerate decoded results, never a sample of possible answers. -/
structure Results (D : Deklaration) (result : Option Ty) where
  values : List (ErgVal D result)
  complete : ∀ value, value ∈ values

def results (budget : Nat) : (result : Option Ty) → Except Frag.Refusal (Results D result)
  | none => .ok { values := [()], complete := fun value => by cases value; simp }
  | some τ => do
      let domain ← localDomain (D := D) budget τ
      return {
          values := domain.values, complete := domain.complete }

/-- Argument selection retains correlation with memory by P20's exact local
    equality. The canonical evalArgs remains the only argument evaluator. -/
def arguments (budget : Nat) (args : Args D Γ Λ params) (locals : Env D Γ)
    (target : Env D params → Runtime program (fun _ => []) S → World D → Prop)
    (compile : ∀ actual, Except Frag.Refusal (Condition (target actual))) :
    Except Frag.Refusal (Condition (fun runtime world =>
      target (evalArgs world args world locals) runtime world)) :=
  match args with
  | .nil => compile .nil
  | .cons head tail => do
      let selected ← localSelect budget head locals
        (fun value runtime world => target (.cons value (evalArgs world tail world locals)) runtime world)
        (fun value => arguments budget tail locals
          (fun rest => target (.cons value rest)) (fun rest => compile (.cons value rest)))
      return selected.map (fun _ _ ready => ready)

/-- Every result gets a separate checked continuation and callee ensures.
    All callees are checked as a conjunction at the program gate; this rule's
    semantic handler class is the existing contract-respecting class. -/
def callCondition (policy : CallPolicy program) (budget : Nat) (f : D.Fn)
    (actual : Env D (D.params f)) (noReasons : D.gruende f = 0)
    (target : ErgVal D (D.erg f) → Runtime program (fun _ => []) S → World D → Prop)
    (compile : ∀ value, Except Frag.Refusal (Condition (target value))) :
    Except Frag.Refusal (Condition (fun runtime world => ∀ allowed,
      HandlerSafe policy runtime allowed →
      match runtime.calls f world actual with
      | .ok next value => target value runtime next
      | .why _ _ => False
      | .logik error => allowed error
      | .hardware _ => True)) := do
  let pre ← policy.encode f actual
  let domain ← results (D := D) budget (D.erg f)
  let branches ← allConditions domain.values
    (fun value runtime world => ReqAmEintritt program f world actual →
      RespektiertRahmen program runtime.calls → ∀ next,
      runtime.calls f world actual = .ok next value → target value runtime next)
    (fun value => do
      let post ← postFormula program f actual value
      let tail ← compile value
      return {
          formula := callWP f post.val tail.formula
          sound := fun runtime world valid requires respects next returned =>
            tail.sound runtime next (callWP_sound f post.val tail.formula world next valid
              (runtime.evidence.frame f world actual next value returned)
              ((post.property world next).mpr (respects.1 f world actual requires next value returned))) })
  return {
      formula := conj pre.val branches.formula
      sound := fun runtime world valid allowed safe => by
        have parts := (conj_denote _ _ _).mp valid
        have entry := (pre.property world).mp parts.1
        cases reply : runtime.calls f world actual with
        | ok next value => exact branches.sound runtime world parts.2 value (domain.complete value)
            (policy.requires f world actual entry) safe.1 next reply
        | why next reason => exact (Fin.cast noReasons reason).elim0
        | logik error => exact safe.2 f world actual entry error reply
        | hardware _ => trivial }

end Gabbro.Grammatik.Vertraege.Pruefer
