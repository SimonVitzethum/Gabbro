module

public import Grammatik.Logik.Invarianten.VC.Writer

@[expose] public section

namespace Gabbro.Grammatik.Invarianten.VC

open Frag Elim Elim.Korrekt Modell

variable {D : Deklaration} {V : Vertrag D} {S : SperrInv D}

/-- Separate continuations are essential for mutable locals and loop control.
    A return owes the final invariant; `next` owes the next pass, not the exit. -/
structure Goals (D : Deklaration) (Γ : Ctx) where
  normal : Env D Γ → Except Refusal (QF (Observation D))
  escape : Env D Γ → Except Refusal (QF (Observation D))
  again : Env D Γ → Except Refusal (QF (Observation D))
  terminal : QF (Observation D)

def denotes (formula : Except Refusal (QF (Observation D))) (world : World D) : Prop :=
  match formula with
  | .ok body => body.denote (assignment world)
  | .error _ => False

def Goals.holds {l : Bool} {Γ : Ctx} (goals : Goals D Γ) : Ausgang V l Γ → Prop
  | .ok world locals => denotes (goals.normal locals) world
  | .leave _ world locals => denotes (goals.escape locals) world
  | .next _ world locals => denotes (goals.again locals) world
  | .zurueck world _ | .why world _ => goals.terminal.denote (assignment world)
  | .logik _ | .hardware _ => True

def Goals.shrink {Γ : Ctx} (goals : Goals D Γ) (τ : Ty) : Goals D (τ :: Γ) where
  normal := fun locals => goals.normal locals.tail
  escape := fun locals => goals.escape locals.tail
  again := fun locals => goals.again locals.tail
  terminal := goals.terminal

theorem Goals.holds_shrink {l : Bool} {Γ : Ctx} (goals : Goals D Γ) (τ : Ty)
    (outcome : Ausgang V l (τ :: Γ)) :
    (goals.shrink τ).holds outcome ↔ goals.holds outcome.schrumpf := by
  cases outcome <;> rfl

/-- Runtime parameters are quantified by certificates, never inspected by the
    generator. In particular no oracle answer or callee ensures is evaluated. -/
structure Runtime (program : Programm D) (checked : D.Fn → List D.Inv) (S : SperrInv D) where
  oracle : Orakel D
  passes : Nat
  calls : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f
  evidence : CallEvidence program checked calls
  environment : Umwelt D
  havoc : HavocOk S environment

def Runtime.wpS (runtime : Runtime program checked S)
    (code : Stmt D V l Γ Λ Λ') (post : Ausgang V l Γ → Prop)
    (world : World D) (locals : Env D Γ) : Prop :=
  post (execStmtH S runtime.oracle runtime.environment runtime.passes runtime.calls code world locals)

def Runtime.wpB (runtime : Runtime program checked S)
    (code : Block D V l Γ Λ Λ') (post : Ausgang V l Γ → Prop)
    (world : World D) (locals : Env D Γ) : Prop :=
  post (execBlockH S runtime.oracle runtime.environment runtime.passes runtime.calls code world locals)

def Runtime.wpE (runtime : Runtime program checked S)
    (code : Endblock D V l Γ Λ) (post : EndAusgang V l Γ → Prop)
    (world : World D) (locals : Env D Γ) : Prop :=
  post (execEndH S runtime.oracle runtime.environment runtime.passes runtime.calls code world locals)

structure Condition {program : Programm D} {checked : D.Fn → List D.Inv}
    (target : Runtime program checked S → World D → Prop) where
  formula : QF (Observation D)
  sound : ∀ runtime world, formula.denote (assignment world) → target runtime world

def Condition.map {program : Programm D} {checked : D.Fn → List D.Inv}
    {target other : Runtime program checked S → World D → Prop} (pre : Condition target)
    (implies : ∀ runtime world, target runtime world → other runtime world) : Condition other where
  formula := pre.formula
  sound := fun runtime world valid => implies runtime world (pre.sound runtime world valid)

def Condition.read {program : Programm D} {checked : D.Fn → List D.Inv}
    {target : Runtime program checked S → World D → Prop} (pre : Condition target)
    (resources : List (Res D)) (carriers : List (D.Tab ⊕ D.Glob)) :
    Condition (fun runtime world => target runtime (world.lese resources carriers)) where
  formula := pre.formula
  sound := fun runtime world valid => pre.sound runtime _ (by
    rw [assignment_lese]
    exact valid)

def formulaCondition {program : Programm D} {checked : D.Fn → List D.Inv}
    (formula : QF (Observation D)) :
    Condition (fun (_ : Runtime program checked S) world => formula.denote (assignment world)) where
  formula := formula
  sound := fun _ _ valid => valid

/-- Branch composition shares one read world with the canonical semantics. -/
def branchCondition {program : Programm D} {checked : D.Fn → List D.Inv}
    {Γ : Ctx} {Λ : List (Res D)} (test : Expr D Γ Λ .bool) (locals : Env D Γ)
    {yes no : Runtime program checked S → World D → Prop}
    (positive : Condition yes) (negative : Condition no) :
    Except Refusal (Condition (fun runtime world =>
      let read := world.lese Λ test.orte
      if eval read test read locals then yes runtime read else no runtime read)) := do
  let guard ← translate test locals
  return
    { formula := lower (.and (.imp guard.payload (quoteQF positive.formula))
        (.imp (.not guard.payload) (quoteQF negative.formula)))
      sound := fun runtime world valid => by
        let read := world.lese Λ test.orte
        have branches := (lower_denote _ (assignment world)).mp valid
        have agree : assignment read = assignment world := assignment_lese _ _ _
        cases tested : eval read test read locals with
        | true =>
            have present := (guard.correct read).mp tested
            rw [agree] at present
            have ready := (quoteQF_denote _ _).mp (branches.1 present)
            have result := positive.sound runtime read (by rw [agree]; exact ready)
            simpa only [tested, ↓reduceIte] using result
        | false =>
            have absent : ¬ guard.payload.denote (assignment world) := by
              intro present
              rw [← agree] at present
              have impossible := (guard.correct read).mpr present
              simp only [tested, Bool.false_eq_true] at impossible
            have ready := (quoteQF_denote _ _).mp (branches.2 absent)
            have result := negative.sound runtime read (by rw [agree]; exact ready)
            simpa only [tested, Bool.false_eq_true, ↓reduceIte] using result }

abbrev StatementCondition (program : Programm D) (checked : D.Fn → List D.Inv) (S : SperrInv D)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (code : Stmt D V l Γ Λ Λ') (locals : Env D Γ) (goals : Goals D Γ) :=
  Condition (fun runtime : Runtime program checked S =>
    fun world => runtime.wpS code goals.holds world locals)

abbrev BlockCondition (program : Programm D) (checked : D.Fn → List D.Inv) (S : SperrInv D)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (code : Block D V l Γ Λ Λ') (locals : Env D Γ) (goals : Goals D Γ) :=
  Condition (fun runtime : Runtime program checked S =>
    fun world => runtime.wpB code goals.holds world locals)

end Gabbro.Grammatik.Invarianten.VC
