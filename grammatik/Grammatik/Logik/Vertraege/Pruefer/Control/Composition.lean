module

public import Grammatik.Logik.Vertraege.Pruefer.Control.Selection

@[expose] public section

namespace Gabbro.Grammatik.Vertraege.Pruefer.Symbolic

open Invarianten Invarianten.Frag.Symbolic

variable {D : Deklaration} {V : Vertrag D} {program : Programm D} {S : SperrInv D}

def returnCondition {context : Context A next} (symbols : SymEnv D Nat Γ)
    (bounded : symbols.Bounded next) (result : Option Ty) (expression : ErgExpr D Γ Λ result)
    (post : Continuation (program := program) (S := S) context (ErgCtx [] result)) :
    Except Frag.Refusal (Certificate context (fun valuation item runtime world => ∀ actual,
      symbols.Realizes valuation world actual →
      post.holds item runtime world (ergEnv result (evalErg world expression world actual) .nil))) :=
  match result, expression, post with
  | none, .empty, post => do
      let pre ← post.encode next (Nat.le_refl next) .nil trivial
      return pre.map (fun _ _ _ _ ready _ _ => ready .nil trivial)
  | some _, .val expression, post =>
      selectValue symbols bounded expression
        (fun _ value item runtime world => post.holds item runtime world (.cons value .nil))
        (fun more larger symbol valueBounded => do
          let pre ← post.encode more larger (.cons symbol .nil) ⟨valueBounded, trivial⟩
          return pre.map (fun _ _ _ _ ready _ _ value selected => ready (.cons value .nil) ⟨selected, trivial⟩))

def retEndCondition (policy : CallPolicy program) {context : Context A next}
    {l : Bool} (symbols : SymEnv D Nat Γ) (bounded : symbols.Bounded next)
    (expression : ErgExpr D Γ Λ V.erg) (inventory : Λ.Perm V.ende)
    (goals : Goals (program := program) (S := S) context V Γ) :
    Except Frag.Refusal (EndCondition policy (.ret expression inventory : Endblock D V l Γ Λ) symbols goals) := do
  let pre ← returnCondition symbols bounded V.erg expression goals.returned
  return (pre.read Λ expression.orte).map (fun valuation item runtime world ready actual realized _ _ => by
    have current := (symbols.realizes_world actual valuation world (world.lese Λ expression.orte)).mp realized
    unfold VC.Runtime.wpE
    simp only [execEndH, Goals.endHolds]
    exact ready actual current)

/-- The same certified scalar selection composes with the actual block WP.
    Scope shrinkage is proved against execBlockH, including early exits. -/
def bindBlockCondition (policy : CallPolicy program) {context : Context A next}
    {l : Bool} (symbols : SymEnv D Nat Γ) (bounded : symbols.Bounded next)
    (expression : Expr D Γ Λ τ) (rest : Block D V l (τ :: Γ) Λ Λ')
    (goals : Goals (program := program) (S := S) context V Γ)
    (compile : ∀ more (larger : next ≤ more) (symbol : SymValue D Nat τ), symbol.Bounded more →
      Except Frag.Refusal (BlockCondition policy rest (.cons symbol symbols) ((goals.weaken larger).shrink τ))) :
    Except Frag.Refusal (BlockCondition policy (.bind expression rest) symbols goals) := do
  let pre ← selectValue symbols bounded expression
    (fun actual value item runtime world => ∀ allowed, HandlerSafe policy runtime allowed →
      runtime.wpB rest ((goals.shrink τ).holds item runtime allowed) world (.cons value actual))
    (fun more larger symbol valueBounded => do
      let pre ← compile more larger symbol valueBounded
      return pre.map (fun _ _ _ _ ready actual realized value selected =>
        ready (.cons value actual) ⟨selected, realized⟩))
  return (pre.read Λ expression.orte).map (fun valuation item runtime world ready actual realized allowed safe => by
    have current := (symbols.realizes_world actual valuation world (world.lese Λ expression.orte)).mp realized
    have tail := ready actual current allowed safe
    unfold VC.Runtime.wpB at tail ⊢
    simp only [execBlockH]
    exact (goals.holds_shrink τ item runtime allowed _).mp tail)

/-- End blocks use the identical symbolic selection and the model's own
    end-output shrink operation. No second syntax walker is introduced. -/
def bindEndCondition (policy : CallPolicy program) {context : Context A next}
    {l : Bool} (symbols : SymEnv D Nat Γ) (bounded : symbols.Bounded next)
    (expression : Expr D Γ Λ τ) (rest : Endblock D V l (τ :: Γ) Λ)
    (goals : Goals (program := program) (S := S) context V Γ)
    (compile : ∀ more (larger : next ≤ more) (symbol : SymValue D Nat τ), symbol.Bounded more →
      Except Frag.Refusal (EndCondition policy rest (.cons symbol symbols) ((goals.weaken larger).shrink τ))) :
    Except Frag.Refusal (EndCondition policy (.bind expression rest) symbols goals) := do
  let pre ← selectValue symbols bounded expression
    (fun actual value item runtime world => ∀ allowed, HandlerSafe policy runtime allowed →
      runtime.wpE rest ((goals.shrink τ).endHolds item runtime allowed) world (.cons value actual))
    (fun more larger symbol valueBounded => do
      let pre ← compile more larger symbol valueBounded
      return pre.map (fun _ _ _ _ ready actual realized value selected =>
        ready (.cons value actual) ⟨selected, realized⟩))
  return (pre.read Λ expression.orte).map (fun valuation item runtime world ready actual realized allowed safe => by
    have current := (symbols.realizes_world actual valuation world (world.lese Λ expression.orte)).mp realized
    have tail := ready actual current allowed safe
    unfold VC.Runtime.wpE at tail ⊢
    simp only [execEndH]
    exact (goals.endHolds_shrink τ item runtime allowed _).mp tail)

end Gabbro.Grammatik.Vertraege.Pruefer.Symbolic
