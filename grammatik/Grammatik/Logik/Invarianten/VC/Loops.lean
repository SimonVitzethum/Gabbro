module

public import Grammatik.Logik.Invarianten.VC.Continuation

@[expose] public section

namespace Gabbro.Grammatik.Invarianten.VC

open Frag Elim Elim.Korrekt Modell

variable {D : Deklaration} {V : Vertrag D} {S : SperrInv D}
variable {program : Programm D} {checked : D.Fn → List D.Inv}

/-- Static unrolling uses exactly the model's extra test after the last pass.
    Overflow is a real continuation, never silently treated as success. -/
def retryCondition {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (test : Expr D Γ Λ .bool) (body : Block D V true Γ Λ Λ)
    (overflow : Block D V l Γ Λ Λ)
    (compileBody : ∀ locals goals, Except Frag.Refusal (BlockCondition program checked S body locals goals))
    (compileOverflow : ∀ locals goals, Except Frag.Refusal (BlockCondition program checked S overflow locals goals))
    (count : Nat) (locals : Env D Γ) (goals : Goals D Γ) :
    Except Frag.Refusal (Condition (fun runtime : Runtime program checked S => fun world =>
      goals.holds (V := V) (l := l) (retryLauf (V := V) (l := l)
        (execBlockH S runtime.oracle runtime.environment runtime.passes runtime.calls body)
        (fun world env => let read := world.lese Λ test.orte
          (read, wahr? (eval read test read env)))
        (execBlockH S runtime.oracle runtime.environment runtime.passes runtime.calls overflow)
        count world locals))) :=
  match count with
  | 0 => do
      let done ← requireCondition (program := program) (checked := checked) (S := S) (goals.normal locals)
      let exceeded ← compileOverflow locals goals
      let combined ← branchCondition test locals done exceeded
      return combined.map (fun runtime world ready => by
        cases tested : eval (world.lese Λ test.orte) test (world.lese Λ test.orte) locals <;>
          simpa only [retryLauf, Runtime.wpB, wahr?, tested, eq_self,
            Bool.false_eq_true, ↓reduceIte, Goals.holds] using ready)
  | count + 1 => do
      let resume := fun env => retryCondition test body overflow compileBody compileOverflow count env goals
      let passGoals : Goals D Γ :=
        { normal := fun env => generatedFormula (resume env)
          escape := goals.normal
          again := fun env => generatedFormula (resume env)
          terminal := goals.terminal }
      let step ← compileBody locals passGoals
      let done ← requireCondition (program := program) (checked := checked) (S := S) (goals.normal locals)
      let advanced : Condition (fun runtime : Runtime program checked S => fun world =>
        goals.holds (V := V) (l := l) (match execBlockH S runtime.oracle runtime.environment
          runtime.passes runtime.calls body world locals with
          | .ok next env | .next _ next env => retryLauf (V := V) (l := l)
              (execBlockH S runtime.oracle runtime.environment runtime.passes runtime.calls body)
              (fun world env => let read := world.lese Λ test.orte
                (read, wahr? (eval read test read env)))
              (execBlockH S runtime.oracle runtime.environment runtime.passes runtime.calls overflow)
              count next env
          | .leave _ next env => .ok next env
          | .zurueck next value => .zurueck next value
          | .why next reason => .why next reason
          | .logik error => .logik error
          | .hardware error => .hardware error)) := step.map (fun runtime world ready => by
        unfold Runtime.wpB at ready
        cases result : execBlockH S runtime.oracle runtime.environment runtime.passes runtime.calls body world locals with
        | ok next env =>
            rw [result] at ready
            exact generated_sound (resume env) runtime next ready
        | next h next env =>
            rw [result] at ready
            exact generated_sound (resume env) runtime next ready
        | leave h next env => exact (show denotes (goals.normal env) next from by simpa [result, Goals.holds, passGoals] using ready)
        | zurueck next value => simpa only [result, Goals.holds] using ready
        | why next reason => simpa only [result, Goals.holds] using ready
        | logik error => trivial
        | hardware error => trivial)
      let combined ← branchCondition test locals done advanced
      return combined.map (fun runtime world ready => by
        cases tested : eval (world.lese Λ test.orte) test (world.lese Λ test.orte) locals <;>
          simpa only [retryLauf, wahr?, tested, eq_self,
            Bool.false_eq_true, ↓reduceIte, Goals.holds] using ready)

/-- A traversal's checked annotation is tested at every boundary, including
    `leave`. Unrolling has a static count; no runtime or alternate interpreter
    is introduced here. The callback compiles the canonical G body. -/
def traverseCondition {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (table : D.Tab) (annotation : Expr D Γ Λ .bool)
    (body : Block D V true (.index (D.count table) :: Γ) Λ Λ)
    (compileBody : ∀ locals goals, Except Frag.Refusal (BlockCondition program checked S body locals goals))
    (indices : List (Wert D (.index (D.count table)))) (locals : Env D Γ) (goals : Goals D Γ) :
    Except Frag.Refusal (Condition (fun runtime : Runtime program checked S => fun world =>
      goals.holds (V := V) (l := l) (traverseLauf (V := V) (l := l)
        (execBlockH S runtime.oracle runtime.environment runtime.passes runtime.calls body)
        (fun world env => let read := world.lese Λ annotation.orte
          (read, wahr? (eval read annotation read env))) indices world locals))) :=
  match indices with
  | [] => do
      let done ← requireCondition (program := program) (checked := checked) (S := S) (goals.normal locals)
      let stopped : Condition (fun (_ : Runtime program checked S) (_ : World D) => True) :=
        { formula := .tru
          sound := fun _ _ _ => trivial }
      let combined ← branchCondition annotation locals done stopped
      return combined.map (fun runtime world ready => by
        cases tested : eval (world.lese Λ annotation.orte) annotation (world.lese Λ annotation.orte) locals <;>
          simpa only [traverseLauf, wahr?, tested, eq_self,
            Bool.false_eq_true, ↓reduceIte, Goals.holds] using ready)
  | index :: indices => do
      let resume := fun env => traverseCondition table annotation body compileBody indices env goals
      let exit := fun env => traverseCondition table annotation body compileBody [] env goals
      let passGoals : Goals D (.index (D.count table) :: Γ) :=
        { normal := fun env => generatedFormula (resume env.tail)
          escape := fun env => generatedFormula (exit env.tail)
          again := fun env => generatedFormula (resume env.tail)
          terminal := goals.terminal }
      let step ← compileBody (.cons index locals) passGoals
      let advanced : Condition (fun runtime : Runtime program checked S => fun world =>
        goals.holds (V := V) (l := l) (match execBlockH S runtime.oracle runtime.environment
          runtime.passes runtime.calls body world (.cons index locals) with
          | .ok next env | .next _ next env => traverseLauf (V := V) (l := l)
              (execBlockH S runtime.oracle runtime.environment runtime.passes runtime.calls body)
              (fun world env => let read := world.lese Λ annotation.orte
                (read, wahr? (eval read annotation read env))) indices next env.tail
          | .leave _ next env => if wahr? (eval (next.lese Λ annotation.orte) annotation
              (next.lese Λ annotation.orte) env.tail) = true
              then .ok (next.lese Λ annotation.orte) env.tail else .logik .schleife
          | .zurueck next value => .zurueck next value
          | .why next reason => .why next reason
          | .logik error => .logik error
          | .hardware error => .hardware error)) := step.map (fun runtime world ready => by
        unfold Runtime.wpB at ready
        cases result : execBlockH S runtime.oracle runtime.environment runtime.passes runtime.calls body world (.cons index locals) with
        | ok next env =>
            rw [result] at ready
            exact generated_sound (resume env.tail) runtime next ready
        | next h next env =>
            rw [result] at ready
            exact generated_sound (resume env.tail) runtime next ready
        | leave h next env =>
            rw [result] at ready
            exact generated_sound (exit env.tail) runtime next ready
        | zurueck next value => simpa only [result, Goals.holds] using ready
        | why next reason => simpa only [result, Goals.holds] using ready
        | logik error => trivial
        | hardware error => trivial)
      let stopped : Condition (fun (_ : Runtime program checked S) (_ : World D) => True) :=
        { formula := .tru
          sound := fun _ _ _ => trivial }
      let combined ← branchCondition annotation locals advanced stopped
      return combined.map (fun runtime world ready => by
        cases tested : eval (world.lese Λ annotation.orte) annotation
          (world.lese Λ annotation.orte) locals <;>
          simpa only [traverseLauf, wahr?, tested, Bool.true_eq_false,
            Bool.false_eq_true, ↓reduceIte, Goals.holds] using ready)
termination_by indices.length
decreasing_by all_goals simp_wf <;> omega

end Gabbro.Grammatik.Invarianten.VC
