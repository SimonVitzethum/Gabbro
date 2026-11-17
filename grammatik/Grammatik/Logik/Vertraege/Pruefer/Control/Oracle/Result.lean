module

public import Grammatik.Logik.Vertraege.Pruefer.Control.Entry

@[expose] public section

namespace Gabbro.Grammatik.Vertraege.Pruefer.Symbolic

open Invarianten Invarianten.Frag Invarianten.Elim Invarianten.Elim.Korrekt Invarianten.Frag.Symbolic

variable {D : Deklaration} {program : Programm D} {S : SperrInv D}

/-- Every typed oracle answer and every typed poststate are covered. Runtime WP
    supplies no oracle frame premise, so no undeclared frame is assumed here. -/
def oracleResultCondition {context : Context A next} (symbols : SymEnv D Nat Γ)
    (bounded : symbols.Bounded next) (budget : Nat) (result : Option Ty)
    (target : Env D Γ → ErgVal D result → A → VC.Runtime program (fun _ => []) S → World D → Prop)
    (compile : ResultCompiler context symbols result target) :
    Except Frag.Refusal (Certificate context (fun valuation item runtime world => ∀ actual,
      symbols.Realizes valuation world actual → ∀ after value, target actual value item runtime after)) := do
  let pre ← resultCondition (.nil : SymEnv D Nat []) trivial symbols bounded budget result
    (.tru : Expr D (ErgCtx [] result) [] .bool) target compile
  return {
    formula := havocFormula (fun _ => true) pre.formula
    sound := fun valuation item present runtime world valid actual realized after value =>
      pre.sound valuation item present runtime after
        (havocFormula_sound (fun _ => true) pre.formula valuation world after valid
          (fun _ impossible => Bool.noConfusion impossible)) after .nil trivial trivial actual
        ((symbols.realizes_world actual valuation world after).mp realized) value rfl }

/-- The continuation is compiled once on a fresh symbolic scalar result. Its
    realizing valuation and the caller's immutable values survive poststate havoc. -/
def oracleContinuation {context : Context A next} (symbols : SymEnv D Nat Γ)
    (bounded : symbols.Bounded next) (budget : Nat) (result : Option Ty)
    (tail : Continuation (program := program) (S := S) context (ErgCtx Γ result)) :
    Except Frag.Refusal (Certificate context (fun valuation item runtime world => ∀ actual,
      symbols.Realizes valuation world actual → ∀ after value,
      tail.holds item runtime after (ergEnv result value actual))) :=
  oracleResultCondition symbols bounded budget result (fun actual value item runtime after =>
    tail.holds item runtime after (ergEnv result value actual))
    (fun more larger returned returnedBounded => do
      let pre ← tail.encode more larger (withResult result returned symbols)
        (withResult_bounded result returned symbols returnedBounded (symbols.bounded_mono bounded larger))
      return pre.map (fun valuation _ _ world ready actual realized value selected => by
        have combined := withResult_realizes result returned symbols valuation world
          (ergEnv result value .nil) actual selected realized
        rw [envResult_ergEnv] at combined
        exact ready _ combined))

end Gabbro.Grammatik.Vertraege.Pruefer.Symbolic
