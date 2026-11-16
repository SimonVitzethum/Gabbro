module

public import Grammatik.Logik.Vertraege.Pruefer.Leaves

@[expose] public section

namespace Gabbro.Grammatik.Vertraege.Pruefer

open Invarianten Invarianten.Frag Invarianten.Elim Invarianten.Elim.Korrekt Invarianten.VC

variable {D : Deklaration} {S : SperrInv D} {program : Programm D}

/-- Enumerate decoded results, never a sample of possible answers. -/
structure Results (D : Deklaration) (result : Option Ty) where
  values : List (ErgVal D result)
  complete : ∀ value, value ∈ values

def results (budget : Nat) : (result : Option Ty) → Except Invarianten.Frag.Refusal (Results D result)
  | none => .ok
      { values := [show ErgVal D none from ()]
        complete := fun value => by cases value; exact List.mem_cons_self }
  | some τ => do
      let domain ← localDomain (D := D) budget τ
      return {
          values := domain.values, complete := domain.complete }

/-- Argument selection retains correlation with memory by P20's exact local
    equality. The canonical evalArgs remains the only argument evaluator. -/
def arguments (budget : Nat) (args : Args D Γ Λ params) (locals : Env D Γ)
    (target : Env D params → Runtime program (fun _ => []) S → World D → Prop)
    (compile : ∀ actual, Except Invarianten.Frag.Refusal (Condition (target actual))) :
    Except Invarianten.Frag.Refusal (Condition (fun runtime world =>
      target (evalArgs world args world locals) runtime world)) :=
  match params, args, target, compile with
  | [], .nil, _, compile => compile .nil
  | _ :: _, .cons head tail, target, compile => do
      let selected ← selectValue budget head locals
        (fun value runtime world => target (.cons value (evalArgs world tail world locals)) runtime world)
        (fun value => arguments budget tail locals
          (fun rest => target (.cons value rest)) (fun rest => compile (.cons value rest)))
      return selected.map (fun _ _ ready => ready)

/-- A shared certificate quantifies every result without specialization.
    Value-dependent continuations retain their complete domain and callee ensures.
    All callees are checked as a conjunction at the program gate; this rule's
    semantic handler class is the existing contract-respecting class. -/
def callOutcomesCondition (policy : CallPolicy program) (budget : Nat) (f : D.Fn)
    (actual : Env D (D.params f))
    (target : ErgVal D (D.erg f) → Runtime program (fun _ => []) S → World D → Prop)
    (failure : Fin (D.gruende f) → Runtime program (fun _ => []) S → World D → Prop)
    (compile : ∀ value, Except Invarianten.Frag.Refusal (Condition (target value)))
    (compileFailure : ∀ reason, Except Invarianten.Frag.Refusal (Condition (failure reason)))
    (shared : Option (Condition (fun runtime world => ∀ value, target value runtime world)) := none) :
    Except Invarianten.Frag.Refusal (Condition (fun runtime world => ∀ allowed,
      HandlerSafe policy runtime allowed →
      match runtime.calls f world actual with
      | .ok next value => target value runtime next
      | .why next reason => failure reason runtime next
      | .logik error => allowed error
      | .hardware _ => True)) := do
  let pre ← policy.encode f actual
  let branches : Condition (fun runtime world => ∀ value, ReqAmEintritt program f world actual →
      RespektiertRahmen program runtime.calls → ∀ next,
      runtime.calls f world actual = .ok next value → target value runtime next) ←
    match shared with
    | some tail => pure {
        formula := callWP f .tru tail.formula
        sound := fun runtime world valid value _ _ next returned =>
          tail.sound runtime next (callWP_sound f .tru tail.formula world next valid
            (runtime.evidence.frame f world actual next value returned) trivial) value }
    | none => do
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
        pure (branches.map (fun runtime world ready value =>
          ready value (domain.complete value)))
  -- RespektiertRahmen promises a frame only for normal answers. A reason
  -- handler therefore starts in an arbitrary typed world, with no reused
  -- entry-memory facts or invented callee ensures.
  let failures ← allConditions (List.finRange (D.gruende f))
    (fun reason runtime _ => ∀ next, failure reason runtime next)
    (fun reason => do
      let tail ← compileFailure reason
      return {
          formula := havoc (fun _ => true)
            (lower (.imp (typeFacts (qfKeys tail.formula)) (quoteQF tail.formula)))
          sound := fun runtime world valid next => by
            have universal := havoc_sound (fun _ => true) _ (assignment world) (assignment next)
              valid (fun _ _ impossible => Bool.noConfusion impossible)
            exact tail.sound runtime next ((quoteQF_denote _ _).mp
              (((lower_denote _ _).mp universal) (typeFacts_sound _ next))) })
  return {
      formula := conj pre.val (conj branches.formula failures.formula)
      sound := fun runtime world valid allowed safe => by
        have parts := (conj_denote _ _ _).mp valid
        have outcomes := (conj_denote _ _ _).mp parts.2
        have entry := (pre.property world).mp parts.1
        cases reply : runtime.calls f world actual with
        | ok next value =>
            exact branches.sound runtime world outcomes.1 value
              (policy.requires f world actual entry) safe.1 next reply
        | why next reason => exact failures.sound runtime world outcomes.2 reason (List.mem_finRange reason) next
        | logik error => exact safe.2 f world actual entry error reply
        | hardware _ => trivial }

/-- An empty reason channel is the same rule with an impossible failure arm. -/
def callCondition (policy : CallPolicy program) (budget : Nat) (f : D.Fn)
    (actual : Env D (D.params f)) (noReasons : D.gruende f = 0)
    (target : ErgVal D (D.erg f) → Runtime program (fun _ => []) S → World D → Prop)
    (compile : ∀ value, Except Invarianten.Frag.Refusal (Condition (target value)))
    (shared : Option (Condition (fun runtime world => ∀ value, target value runtime world)) := none) :
    Except Invarianten.Frag.Refusal (Condition (fun runtime world => ∀ allowed,
      HandlerSafe policy runtime allowed →
      match runtime.calls f world actual with
      | .ok next value => target value runtime next
      | .why _ _ => False
      | .logik error => allowed error
      | .hardware _ => True)) :=
  callOutcomesCondition policy budget f actual target (fun _ _ _ => False) compile
    (fun reason => (Fin.cast noReasons reason).elim0) shared

end Gabbro.Grammatik.Vertraege.Pruefer
