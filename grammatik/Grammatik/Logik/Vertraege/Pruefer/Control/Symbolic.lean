module

public import Grammatik.Logik.Vertraege.Pruefer.Control.Policy
public import Grammatik.Logik.Invarianten.Frag.Symbolic.Scope
public import Grammatik.Logik.Invarianten.Frag.Symbolic.Translation

@[expose] public section

namespace Gabbro.Grammatik.Vertraege.Pruefer.Symbolic

open Invarianten Invarianten.Frag.Symbolic

variable {D : Deklaration} {V : Vertrag D} {program : Programm D} {S : SperrInv D}

/-- A continuation's computational input is symbolic. Its semantic target still
    refers to the actual Env and runtime, under frozen entry-data assumptions. -/
structure Continuation (context : Context A next) (Γ : Ctx) where
  holds : A → VC.Runtime program (fun _ => []) S → World D → Env D Γ → Prop
  encode : ∀ more (larger : next ≤ more) (symbols : SymEnv D Nat Γ), symbols.Bounded more →
    Except Frag.Refusal (Certificate (program := program) (S := S) (context.weaken larger)
      (fun valuation item runtime world => ∀ actual,
        symbols.Realizes valuation world actual → holds item runtime world actual))

def Continuation.truth (context : Context A next) :
    Continuation (program := program) (S := S) context Γ where
  holds := fun _ _ _ _ => True
  encode := fun _ _ _ _ => .ok {
    formula := .tru
    sound := fun _ _ _ _ _ _ _ _ => trivial }

def Continuation.ofFormula (context : Context A next) (formula : Elim.QF (Frag.Observation D)) :
    Continuation (program := program) (S := S) context Γ where
  holds := fun _ _ world _ => formula.denote (Frag.assignment world)
  encode := fun _ _ _ _ => .ok {
    formula := renameProp Sum.inl (VC.quoteQF formula)
    sound := fun valuation _ _ _ world valid _ _ =>
      (VC.quoteQF_denote formula (Frag.assignment world)).mp
        ((renameProp_denote Sum.inl (fun _ _ same => Sum.inl.inj same) _ _).mp valid) }

def Continuation.weaken {context : Context A next} (tail : Continuation (program := program) (S := S) context Γ)
    (larger : next ≤ more) : Continuation (program := program) (S := S) (context.weaken larger) Γ where
  holds := tail.holds
  encode := fun last beyond symbols bounded => tail.encode last (Nat.le_trans larger beyond) symbols bounded

def Continuation.shrink {context : Context A next} (tail : Continuation (program := program) (S := S) context Γ)
    (τ : Ty) : Continuation (program := program) (S := S) context (τ :: Γ) where
  holds := fun item runtime world actual => tail.holds item runtime world actual.tail
  encode := fun more larger symbols bounded => by
    cases symbols with
    | cons value rest => exact do
        let pre ← tail.encode more larger rest bounded.2
        return pre.map (fun _ _ _ _ ready actual realized => by
          cases actual
          exact ready _ realized.2)

def Continuation.withFact {context : Context A next}
    (tail : Continuation (program := program) (S := S) context Γ) (fact : Elim.QF (Frag.Observation D)) :
    Continuation (program := program) (S := S) context Γ where
  holds := fun item runtime world actual => fact.denote (Frag.assignment world) ∧ tail.holds item runtime world actual
  encode := fun more larger symbols bounded => do
    let pre ← tail.encode more larger symbols bounded
    return {
      formula := .and (renameProp Sum.inl (VC.quoteQF fact)) pre.formula
      sound := fun valuation item present runtime world valid actual realized => by
        have factValid := (renameProp_denote Sum.inl (fun _ _ same => Sum.inl.inj same) _ _).mp valid.1
        exact ⟨(VC.quoteQF_denote fact (Frag.assignment world)).mp factValid,
          pre.sound valuation item present runtime world valid.2 actual realized⟩ }

def Continuation.atWorld {context : Context A next}
    (tail : Continuation (program := program) (S := S) context Γ) (step : World D → World D)
    (same : ∀ world, Frag.assignment (step world) = Frag.assignment world) :
    Continuation (program := program) (S := S) context Γ where
  holds := fun item runtime world actual => tail.holds item runtime (step world) actual
  encode := fun more larger symbols bounded => do
    let pre ← tail.encode more larger symbols bounded
    return {
      formula := pre.formula
      sound := fun valuation item present runtime world valid actual realized => by
        have valuesSame : values valuation (step world) = values valuation world := by
          funext key
          cases key with
          | inl memory => exact congrFun (same world) memory
          | inr _ => rfl
        exact pre.sound valuation item present runtime (step world) (by rw [valuesSame]; exact valid)
          actual ((symbols.realizes_world actual valuation world (step world)).mp realized) }

structure Goals (context : Context A next) (V : Vertrag D) (Γ : Ctx) where
  normal : Continuation (program := program) (S := S) context Γ
  escape : Continuation (program := program) (S := S) context Γ
  again : Continuation (program := program) (S := S) context Γ
  returned : Continuation (program := program) (S := S) context (ErgCtx [] V.erg)
  reason : Continuation (program := program) (S := S) context []

def Goals.holds {context : Context A next} {l : Bool}
    (goals : Goals (program := program) (S := S) context V Γ) (item : A)
    (runtime : VC.Runtime program (fun _ => []) S) (allowed : Logik D → Prop) : Ausgang V l Γ → Prop
  | .ok world actual => goals.normal.holds item runtime world actual
  | .leave _ world actual => goals.escape.holds item runtime world actual
  | .next _ world actual => goals.again.holds item runtime world actual
  | .zurueck world value => goals.returned.holds item runtime world (ergEnv V.erg value .nil)
  | .why world _ => goals.reason.holds item runtime world .nil
  | .logik error => allowed error
  | .hardware _ => True

def Goals.endHolds {context : Context A next} {l : Bool}
    (goals : Goals (program := program) (S := S) context V Γ) (item : A)
    (runtime : VC.Runtime program (fun _ => []) S) (allowed : Logik D → Prop) : EndAusgang V l Γ → Prop
  | .leave _ world actual => goals.escape.holds item runtime world actual
  | .next _ world actual => goals.again.holds item runtime world actual
  | .zurueck world value => goals.returned.holds item runtime world (ergEnv V.erg value .nil)
  | .why world _ => goals.reason.holds item runtime world .nil
  | .logik error => allowed error
  | .hardware _ => True

def Goals.weaken {context : Context A next} (goals : Goals (program := program) (S := S) context V Γ)
    (larger : next ≤ more) : Goals (program := program) (S := S) (context.weaken larger) V Γ where
  normal := goals.normal.weaken larger
  escape := goals.escape.weaken larger
  again := goals.again.weaken larger
  returned := goals.returned.weaken larger
  reason := goals.reason.weaken larger

def Goals.shrink {context : Context A next} (goals : Goals (program := program) (S := S) context V Γ)
    (τ : Ty) : Goals (program := program) (S := S) context V (τ :: Γ) where
  normal := goals.normal.shrink τ
  escape := goals.escape.shrink τ
  again := goals.again.shrink τ
  returned := goals.returned
  reason := goals.reason

def Goals.releasing {context : Context A next} (goals : Goals (program := program) (S := S) context V Γ)
    (lock : D.Lock) (fact : Elim.QF (Frag.Observation D)) : Goals (program := program) (S := S) context V Γ where
  normal := (goals.normal.atWorld (fun world => world.gibt lock) (fun world => VC.assignment_gibt world lock)).withFact fact
  escape := (goals.escape.atWorld (fun world => world.gibt lock) (fun world => VC.assignment_gibt world lock)).withFact fact
  again := (goals.again.atWorld (fun world => world.gibt lock) (fun world => VC.assignment_gibt world lock)).withFact fact
  returned := goals.returned.withFact fact
  reason := goals.reason.withFact fact

theorem Goals.holds_shrink {context : Context A next} {l : Bool}
    (goals : Goals (program := program) (S := S) context V Γ) (τ : Ty) (item : A)
    (runtime : VC.Runtime program (fun _ => []) S) (allowed : Logik D → Prop) (outcome : Ausgang V l (τ :: Γ)) :
    (goals.shrink τ).holds item runtime allowed outcome ↔
      goals.holds item runtime allowed outcome.schrumpf := by
  cases outcome <;> rfl

theorem Goals.endHolds_shrink {context : Context A next} {l : Bool}
    (goals : Goals (program := program) (S := S) context V Γ) (τ : Ty) (item : A)
    (runtime : VC.Runtime program (fun _ => []) S) (allowed : Logik D → Prop) (outcome : EndAusgang V l (τ :: Γ)) :
    (goals.shrink τ).endHolds item runtime allowed outcome ↔
      goals.endHolds item runtime allowed outcome.schrumpf := by
  cases outcome <;> rfl

abbrev StatementCondition (policy : A → CallObligation program) {context : Context A next}
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (code : Stmt D V l Γ Λ Λ')
    (symbols : SymEnv D Nat Γ) (goals : Goals (S := S) context V Γ) :=
  Certificate context (fun valuation item (runtime : VC.Runtime program (fun _ => []) S) world =>
    ∀ actual, symbols.Realizes valuation world actual → ∀ allowed,
      HandlerSafe (policy item) runtime allowed → runtime.wpS code (goals.holds item runtime allowed) world actual)

abbrev BlockCondition (policy : A → CallObligation program) {context : Context A next}
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (code : Block D V l Γ Λ Λ')
    (symbols : SymEnv D Nat Γ) (goals : Goals (S := S) context V Γ) :=
  Certificate context (fun valuation item (runtime : VC.Runtime program (fun _ => []) S) world =>
    ∀ actual, symbols.Realizes valuation world actual → ∀ allowed,
      HandlerSafe (policy item) runtime allowed → runtime.wpB code (goals.holds item runtime allowed) world actual)

abbrev EndCondition (policy : A → CallObligation program) {context : Context A next}
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (code : Endblock D V l Γ Λ)
    (symbols : SymEnv D Nat Γ) (goals : Goals (S := S) context V Γ) :=
  Certificate context (fun valuation item (runtime : VC.Runtime program (fun _ => []) S) world =>
    ∀ actual, symbols.Realizes valuation world actual → ∀ allowed,
      HandlerSafe (policy item) runtime allowed → runtime.wpE code (goals.endHolds item runtime allowed) world actual)

end Gabbro.Grammatik.Vertraege.Pruefer.Symbolic
