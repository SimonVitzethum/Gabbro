module

public import Grammatik.Logik.Vertraege.Pruefer.Control.Composition
public import Grammatik.Logik.Vertraege.Pruefer.Control.Havoc

@[expose] public section

namespace Gabbro.Grammatik.Vertraege.Pruefer.Symbolic

open Invarianten Invarianten.Frag.Symbolic

variable {D : Deklaration} {program : Programm D} {S : SperrInv D}

def branchCondition {context : Context A next} (symbols : SymEnv D Nat Γ)
    (test : Expr D Γ Λ .bool)
    {yes no : Env D Γ → A → VC.Runtime program (fun _ => []) S → World D → Prop}
    (positive : Certificate context (fun valuation item runtime world => ∀ actual,
      symbols.Realizes valuation world actual → yes actual item runtime world))
    (negative : Certificate context (fun valuation item runtime world => ∀ actual,
      symbols.Realizes valuation world actual → no actual item runtime world)) :
    Except Frag.Refusal (Certificate context (fun valuation item runtime world => ∀ actual,
      symbols.Realizes valuation world actual →
      let read := world.lese Λ test.orte
      if wahr? (eval read test read actual) = true then yes actual item runtime read else no actual item runtime read)) := do
  let pre ← booleanSelection symbols test
    (fun actual answer item runtime world => if wahr? answer = true then yes actual item runtime world else no actual item runtime world)
    (fun more larger symbol _ => by
      cases symbol with
      | known answer =>
        cases answer with
        | true => exact .ok ((positive.weaken larger).map (fun _ _ _ _ ready actual realized value selected => by
            change true = value at selected
            rw [← selected]
            exact ready actual realized))
        | false => exact .ok ((negative.weaken larger).map (fun _ _ _ _ ready actual realized value selected => by
            change false = value at selected
            rw [← selected]
            exact ready actual realized)))
  return (pre.read Λ test.orte).map (fun valuation _ _ world ready actual realized =>
    ready actual ((symbols.realizes_world actual valuation world (world.lese Λ test.orte)).mp realized))

end Gabbro.Grammatik.Vertraege.Pruefer.Symbolic
