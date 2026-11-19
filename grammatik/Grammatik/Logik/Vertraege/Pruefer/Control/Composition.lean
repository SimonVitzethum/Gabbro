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

def retEndCondition (policy : A → CallObligation program) {context : Context A next}
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
def bindBlockCondition (policy : A → CallObligation program) {context : Context A next}
    {l : Bool} (symbols : SymEnv D Nat Γ) (bounded : symbols.Bounded next)
    (expression : Expr D Γ Λ τ) (rest : Block D V l (τ :: Γ) Λ Λ')
    (goals : Goals (program := program) (S := S) context V Γ)
    (compile : ∀ more (larger : next ≤ more) (symbol : SymValue D Nat τ), symbol.Bounded more →
      Except Frag.Refusal (BlockCondition policy rest (.cons symbol symbols) ((goals.weaken larger).shrink τ))) :
    Except Frag.Refusal (BlockCondition policy (.bind expression rest) symbols goals) := do
  let pre ← selectValue symbols bounded expression
    (fun actual value item runtime world => ∀ allowed, HandlerSafe (policy item) runtime allowed →
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
def bindEndCondition (policy : A → CallObligation program) {context : Context A next}
    {l : Bool} (symbols : SymEnv D Nat Γ) (bounded : symbols.Bounded next)
    (expression : Expr D Γ Λ τ) (rest : Endblock D V l (τ :: Γ) Λ)
    (goals : Goals (program := program) (S := S) context V Γ)
    (compile : ∀ more (larger : next ≤ more) (symbol : SymValue D Nat τ), symbol.Bounded more →
      Except Frag.Refusal (EndCondition policy rest (.cons symbol symbols) ((goals.weaken larger).shrink τ))) :
    Except Frag.Refusal (EndCondition policy (.bind expression rest) symbols goals) := do
  let pre ← selectValue symbols bounded expression
    (fun actual value item runtime world => ∀ allowed, HandlerSafe (policy item) runtime allowed →
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

/-- One certificate per value of a complete finite list, conjoined: every case is required, so the actual value is
    covered whichever it is. Used for dispatch over finite payloads (`onOption`). -/
def everyValue {context : Context A next} {α : Type}
    (target : α → Assignment Nat → A → VC.Runtime program (fun _ => []) S → World D → Prop)
    (compile : ∀ value, Except Frag.Refusal (Certificate context (target value))) :
    (values : List α) →
    Except Frag.Refusal (Certificate context (fun valuation item runtime world =>
      ∀ value ∈ values, target value valuation item runtime world))
  | [] => .ok
      { formula := .tru
        sound := fun _ _ _ _ _ _ _ member => absurd member List.not_mem_nil }
  | value :: rest => do
      let head ← compile value
      let tail ← everyValue target compile rest
      return {
        formula := .and head.formula tail.formula
        sound := fun valuation item present runtime world valid current member => by
          have parts : head.formula.denote (values valuation world) ∧
              tail.formula.denote (values valuation world) := valid
          rcases List.mem_cons.mp member with same | member
          · rw [same]
            exact head.sound valuation item present runtime world parts.1
          · exact tail.sound valuation item present runtime world parts.2 current member }

/-- `match` on an option: the `Some` block is certified for every index of the complete domain, the `None` block
    once; whichever the actual value is, its block's certificate applies. -/
def optionCondition (policy : A → CallObligation program) {context : Context A next} {l : Bool}
    {Γ : Ctx} {Λ Λ' : List (Res D)} {count : Int}
    (symbols : SymEnv D Nat Γ) (expression : Expr D Γ Λ (.opt count))
    (present : Block D V l (Ty.index count :: Γ) Λ Λ') (absent : Block D V l Γ Λ Λ')
    (goals : Goals (program := program) (S := S) context V Γ)
    (domain : Invarianten.VC.LocalDomain D (Ty.index count))
    (absentCase : BlockCondition policy absent symbols goals)
    (presentCase : ∀ index, Except Frag.Refusal
      (BlockCondition policy present (.cons (.known index) symbols) (goals.shrink (Ty.index count)))) :
    Except Frag.Refusal (StatementCondition policy (.onOption expression present absent) symbols goals) := do
  let some ← everyValue
    (fun index valuation item (runtime : VC.Runtime program (fun _ => []) S) world =>
      ∀ actual, symbols.Realizes valuation world actual → ∀ allowed, HandlerSafe (policy item) runtime allowed →
        runtime.wpB present ((goals.shrink (Ty.index count)).holds item runtime allowed) world (.cons index actual))
    (fun index => do
      let pre ← presentCase index
      return pre.map (fun _ _ _ _ ready actual realized allowed safe =>
        ready (.cons index actual) ⟨rfl, realized⟩ allowed safe))
    domain.values
  let both : Certificate context (fun valuation item (runtime : VC.Runtime program (fun _ => []) S) world =>
      (∀ index ∈ domain.values, ∀ actual, symbols.Realizes valuation world actual → ∀ allowed,
        HandlerSafe (policy item) runtime allowed →
        runtime.wpB present ((goals.shrink (Ty.index count)).holds item runtime allowed) world (.cons index actual)) ∧
      (∀ actual, symbols.Realizes valuation world actual → ∀ allowed, HandlerSafe (policy item) runtime allowed →
        runtime.wpB absent (goals.holds item runtime allowed) world actual)) :=
    { formula := .and some.formula absentCase.formula
      sound := fun valuation item ready runtime world valid =>
        ⟨some.sound valuation item ready runtime world valid.1,
         absentCase.sound valuation item ready runtime world valid.2⟩ }
  return (both.read Λ expression.orte).map (fun valuation item runtime world ready actual realized allowed safe => by
    have current := (symbols.realizes_world actual valuation world (world.lese Λ expression.orte)).mp realized
    unfold VC.Runtime.wpS
    simp only [execStmtH]
    cases selected : eval (world.lese Λ expression.orte) expression (world.lese Λ expression.orte) actual with
    | some index =>
        have case := ready.1 index (domain.complete index) actual current allowed safe
        unfold VC.Runtime.wpB at case
        exact (goals.holds_shrink (Ty.index count) item runtime allowed _).mp case
    | none =>
        have case := ready.2 actual current allowed safe
        unfold VC.Runtime.wpB at case
        exact case)

end Gabbro.Grammatik.Vertraege.Pruefer.Symbolic
