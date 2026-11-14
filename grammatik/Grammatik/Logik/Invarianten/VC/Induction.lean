module

public import Grammatik.Logik.Invarianten.VC.Leaves

@[expose] public section

namespace Gabbro.Grammatik.Invarianten.VC

open Frag Elim Elim.Korrekt Modell

variable {D : Deklaration} {V : Vertrag D} {S : SperrInv D}
variable {program : Programm D} {checked : D.Fn → List D.Inv}

structure EnvironmentDomain (D : Deklaration) (Γ : Ctx) where
  values : List (Env D Γ)
  complete : ∀ locals : Env D Γ, locals ∈ values

def environmentDomain (budget : Nat) : (Γ : Ctx) → Except Refusal (EnvironmentDomain D Γ)
  | [] => .ok
      { values := [.nil]
        complete := fun locals => by cases locals; simp }
  | τ :: Γ => do
      let head ← localDomain (D := D) budget τ
      let tail ← environmentDomain budget Γ
      if head.values.length * tail.values.length ≤ budget then
        return { values := head.values.flatMap (fun value => tail.values.map (.cons value))
            complete := fun locals => by
              cases locals with
              | cons value rest =>
                  exact List.mem_flatMap.mpr ⟨value, head.complete value,
                    List.mem_map.mpr ⟨rest, tail.complete rest, rfl⟩⟩ }
      else .error (.unsupported "inductive loop local-state set exceeds the VC budget")

/-- Universal preservation checks do not accidentally retain the entry world's
    values. Every observation in the generated condition is universally havoced. -/
def inductiveCondition (invariant : QF (Observation D))
    {target : Runtime program checked S → World D → Prop} (pre : Condition target) :
    Condition (fun runtime (_ : World D) => ∀ world,
      invariant.denote (assignment world) → target runtime world) where
  formula := havoc (fun _ => true)
    (lower (.imp (.and (typeFacts (qfKeys invariant ++ qfKeys pre.formula))
      (quoteQF invariant)) (quoteQF pre.formula)))
  sound := fun runtime initial valid world holds => by
    have everywhere := havoc_sound (fun _ => true) _ (assignment initial) (assignment world) valid
      (fun _ _ impossible => by cases impossible)
    exact pre.sound runtime world ((quoteQF_denote _ _).mp (((lower_denote _ _).mp everywhere)
      ⟨typeFacts_sound _ world, (quoteQF_denote _ _).mpr holds⟩))

/-- Declared same-fragment invariants support arbitrarily large static bounds.
    The finite local-state domain is complete and budgeted. The generated VC
    checks entry, preservation, successful exit AND the overflow continuation.
    Changing a local requires all its typed successor cases, not a fixed env. -/
def retryInvariantCondition {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (budget count : Nat) (invariant : QF (Observation D))
    (test : Expr D Γ Λ .bool) (body : Block D V true Γ Λ Λ) (overflow : Block D V l Γ Λ Λ)
    (compileBody : ∀ locals goals, Except Refusal (BlockCondition program checked S body locals goals))
    (compileOverflow : ∀ locals goals, Except Refusal (BlockCondition program checked S overflow locals goals))
    (locals : Env D Γ) (goals : Goals D Γ) :
    Except Refusal (StatementCondition program checked S (.retry count test body overflow) locals goals) := do
  let domain ← environmentDomain (D := D) budget Γ
  let passGoals : Goals D Γ :=
    { normal := fun _ => .ok invariant
      escape := goals.normal
      again := fun _ => .ok invariant
      terminal := goals.terminal }
  let compilePass := fun env => do
    let done ← requireCondition (program := program) (checked := checked) (S := S) (goals.normal env)
    let step ← compileBody env passGoals
    let exceeded ← compileOverflow env goals
    let advance : Condition (fun runtime world =>
        runtime.wpB body passGoals.holds world env ∧ runtime.wpB overflow goals.holds world env) :=
      { formula := conj step.formula exceeded.formula
        sound := fun runtime world valid =>
          let parts := (conj_denote _ _ _).mp valid
          ⟨step.sound runtime world parts.1, exceeded.sound runtime world parts.2⟩ }
    let branch ← branchCondition test env done advance
    return inductiveCondition invariant branch
  let checks ← allConditions domain.values _ compilePass
  return { formula := conj invariant checks.formula
      sound := fun runtime world valid => by
        have parts := (conj_denote _ _ _).mp valid
        have obligations := checks.sound runtime world parts.2
        let I : Nat → World D → Env D Γ → Prop :=
          fun _ next _ => invariant.denote (assignment next)
        let doneTest := fun next env =>
          let read := next.lese Λ test.orte
          (read, wahr? (eval read test read env))
        have stepRule : ∀ n next env, I (n + 1) next env →
            (doneTest next env).2 = false →
            runtime.wpB body (WP.PassSchritt goals.holds I n) (doneTest next env).1 env := by
          intro n next env holds unfinished
          have ready := obligations env (domain.complete env) next holds
          have tested : eval (next.lese Λ test.orte) test (next.lese Λ test.orte) env = false := unfinished
          simp only [tested, Bool.false_eq_true, ↓reduceIte] at ready
          have run := ready.1
          unfold Runtime.wpB at run ⊢
          cases result : execBlockH S runtime.oracle runtime.environment runtime.passes runtime.calls body
            (next.lese Λ test.orte) env <;>
            simpa only [result, Goals.holds, WP.PassSchritt, passGoals, I, denotes] using run
        apply WP.retry_regel
          (execBlockH S runtime.oracle runtime.environment runtime.passes runtime.calls body)
          doneTest (execBlockH S runtime.oracle runtime.environment runtime.passes runtime.calls overflow)
          goals.holds I ?_ ?_ stepRule count world locals parts.1
        · intro n next env holds finished
          have ready := obligations env (domain.complete env) next holds
          have tested : eval (next.lese Λ test.orte) test (next.lese Λ test.orte) env = true := finished
          simpa only [tested, ↓reduceIte, Goals.holds] using ready
        · intro next env holds unfinished
          have ready := obligations env (domain.complete env) next holds
          have tested : eval (next.lese Λ test.orte) test (next.lese Λ test.orte) env = false := unfinished
          simp only [tested, Bool.false_eq_true, ↓reduceIte] at ready
          exact ready.2 }

end Gabbro.Grammatik.Invarianten.VC
