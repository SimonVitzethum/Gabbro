module

public import Grammatik.Logik.Vertraege.Pruefer.Control.Arguments
public import Grammatik.Logik.Vertraege.Pruefer.Control.Results

@[expose] public section

namespace Gabbro.Grammatik.Vertraege.Pruefer

open Invarianten Invarianten.Frag Invarianten.Elim Invarianten.Elim.Korrekt Invarianten.VC
open Invarianten.Frag.Symbolic Symbolic

variable {D : Deklaration} {S : SperrInv D} {program : Programm D}

/-- The call rule quantifies normal answers and written observations. Immutable
    arguments and caller locals retain their original realizing valuation. -/
def callOutcomesCondition {context : Context A next} (policy : CallPolicy program context)
    (budget : Nat) (f : D.Fn) (args : SymEnv D Nat (D.params f)) (argsBounded : args.Bounded next)
    (caller : SymEnv D Nat Γ) (callerBounded : caller.Bounded next)
    (target : Env D Γ → ErgVal D (D.erg f) → A → Runtime program (fun _ => []) S → World D → Prop)
    (failure : Env D Γ → Fin (D.gruende f) → A → Runtime program (fun _ => []) S → World D → Prop)
    (compile : ResultCompiler context caller (D.erg f) target)
    (compileFailure : ∀ reason, Except Frag.Refusal (Certificate context (fun valuation item runtime world =>
      ∀ actual, caller.Realizes valuation world actual → failure actual reason item runtime world))) :
    Except Frag.Refusal (Certificate context (fun valuation item runtime world => ∀ actual,
      caller.Realizes valuation world actual → ∀ supplied, args.Realizes valuation world supplied →
      ∀ allowed, HandlerSafe (policy.semantic item) runtime allowed →
      match runtime.calls f world supplied with
      | .ok after value => target actual value item runtime after
      | .why after reason => failure actual reason item runtime after
      | .logik error => allowed error
      | .hardware _ => True)) := do
  let pre ← policy.encode next (Nat.le_refl next) f args argsBounded
  let normal ← resultCondition args argsBounded caller callerBounded budget (D.erg f)
    (program.ensures f) target compile
  let failures ← allCertificates context (List.finRange (D.gruende f))
    (fun reason valuation item runtime world => ∀ actual, caller.Realizes valuation world actual →
      ∀ after, failure actual reason item runtime after)
    (fun reason => do
      let tail ← compileFailure reason
      return {
        formula := havocFormula (fun _ => true) tail.formula
        sound := fun valuation item present runtime world valid actual realized after =>
          tail.sound valuation item present runtime after
            (havocFormula_sound (fun _ => true) tail.formula valuation world after valid
              (fun _ impossible => Bool.noConfusion impossible)) actual
            ((caller.realizes_world actual valuation world after).mp realized) })
  return {
    formula := .and pre.val (.and (havocFormula (writtenObservation f) normal.formula) failures.formula)
    sound := fun valuation item present runtime world valid actual realized supplied suppliedRealized allowed safe => by
      have obligation := (pre.property valuation item present world supplied suppliedRealized).mp valid.1
      have required := (policy.semantic item).requires f world supplied obligation
      cases reply : runtime.calls f world supplied with
      | ok after value =>
          have transferred := havocFormula_sound (writtenObservation f) normal.formula valuation world after valid.2.1
            (fun key unchanged => frame_observation f world after (runtime.evidence.frame f world supplied after value reply) key unchanged)
          exact normal.sound valuation item present runtime after transferred world supplied suppliedRealized
            actual ((caller.realizes_world actual valuation world after).mp realized) value
            (safe.1.1 f world supplied required after value reply)
      | why after reason =>
          exact failures.sound valuation item present runtime world valid.2.2 reason
            (List.mem_finRange reason) actual realized after
      | logik error => exact safe.2 f world supplied obligation error reply
      | hardware error => trivial }

def callCondition {context : Context A next} (policy : CallPolicy program context)
    (budget : Nat) (f : D.Fn) (args : SymEnv D Nat (D.params f)) (argsBounded : args.Bounded next)
    (caller : SymEnv D Nat Γ) (callerBounded : caller.Bounded next) (noReasons : D.gruende f = 0)
    (target : Env D Γ → ErgVal D (D.erg f) → A → Runtime program (fun _ => []) S → World D → Prop)
    (compile : ResultCompiler context caller (D.erg f) target) :=
  callOutcomesCondition policy budget f args argsBounded caller callerBounded target
    (fun _ _ _ _ _ => False) compile (fun reason => (Fin.cast noReasons reason).elim0)

end Gabbro.Grammatik.Vertraege.Pruefer
