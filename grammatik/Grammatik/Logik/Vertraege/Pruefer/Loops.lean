module

public import Grammatik.Logik.Vertraege.Pruefer.Calls

@[expose] public section

namespace Gabbro.Grammatik.Vertraege.Pruefer

open Invarianten Invarianten.Frag Invarianten.Elim Invarianten.Elim.Korrekt Invarianten.VC

variable {D : Deklaration} {V : Vertrag D} {S : SperrInv D} {program : Programm D}
variable (policy : CallPolicy program)

/-- Exact bounded unrolling, including the final test and overflow branch.
    Unlike an invariant-only post, the post keeps every logic stop visible. -/
def retryCondition {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (test : Expr D Γ Λ .bool) (body : Block D V true Γ Λ Λ)
    (overflow : Block D V l Γ Λ Λ)
    (compileBody : ∀ locals goals, Except Invarianten.Frag.Refusal (BlockCondition (S := S) policy body locals goals))
    (compileOverflow : ∀ locals goals, Except Invarianten.Frag.Refusal (BlockCondition (S := S) policy overflow locals goals))
    (count : Nat) (locals : Env D Γ) (goals : Goals D V Γ) :
    Except Invarianten.Frag.Refusal (StatementCondition (S := S) policy (.retry count test body overflow) locals goals) :=
  match count with
  | 0 => do
      let done ← requireCondition (program := program) (checked := fun _ => []) (S := S) (goals.normal locals)
      let exceeded ← compileOverflow locals goals
      let combined ← branchCondition test locals
        (withHandlers policy done) exceeded
      return combined.map (fun runtime world ready allowed safe => by
        cases tested : eval (world.lese Λ test.orte) test (world.lese Λ test.orte) locals <;>
          simp only [tested, wahr?, eq_self, Bool.false_eq_true, ↓reduceIte] at ready <;>
          have ready := ready allowed safe <;>
          simpa only [Runtime.wpS, Runtime.wpB, execStmtH, retryLauf, wahr?, tested,
            Bool.false_eq_true, ↓reduceIte, Goals.holds] using ready)
  | count + 1 => do
      let resume := fun env => retryCondition test body overflow compileBody compileOverflow count env goals
      let passGoals : Goals D V Γ :=
        { normal := fun env => generatedFormula (resume env)
          escape := goals.normal
          again := fun env => generatedFormula (resume env)
          returned := goals.returned
          reason := goals.reason }
      let step ← compileBody locals passGoals
      let done ← requireCondition (program := program) (checked := fun _ => []) (S := S) (goals.normal locals)
      let advanced : Condition (fun runtime : Runtime program (fun _ => []) S => fun world =>
        ∀ allowed, HandlerSafe policy runtime allowed →
        goals.holds (l := l) allowed (match execBlockH S runtime.oracle runtime.environment
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
          | .hardware error => .hardware error)) := step.map (fun runtime world ready allowed safe => by
        have ready := ready allowed safe
        unfold Runtime.wpB at ready
        cases result : execBlockH S runtime.oracle runtime.environment runtime.passes runtime.calls body world locals with
        | ok next env =>
            rw [result] at ready
            exact generated_sound (resume env) runtime next ready allowed safe
        | next h next env =>
            rw [result] at ready
            exact generated_sound (resume env) runtime next ready allowed safe
        | leave h next env => simpa only [result, Goals.holds, passGoals] using ready
        | zurueck next value => simpa only [result, Goals.holds, passGoals] using ready
        | why next reason => simpa only [result, Goals.holds, passGoals] using ready
        | logik error => simpa only [result, Goals.holds] using ready
        | hardware error => trivial)
      let combined ← branchCondition test locals
        (withHandlers policy done) advanced
      return combined.map (fun runtime world ready allowed safe => by
        cases tested : eval (world.lese Λ test.orte) test (world.lese Λ test.orte) locals <;>
          simp only [tested, wahr?, eq_self, Bool.false_eq_true, ↓reduceIte] at ready <;>
          have ready := ready allowed safe <;>
          cases result : execBlockH S runtime.oracle runtime.environment runtime.passes runtime.calls
            body (world.lese Λ test.orte) locals <;>
          simpa only [Runtime.wpS, execStmtH, retryLauf, wahr?, tested, result,
            Bool.false_eq_true, ↓reduceIte, Goals.holds] using ready)

/-- An inductive hint is checked at entry, at every ordinary/continue
    successor, at successful exit, and before overflow. No hint is trusted. -/
def retryInvariantCondition {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (budget count : Nat) (invariant : QF (Observation D))
    (test : Expr D Γ Λ .bool) (body : Block D V true Γ Λ Λ) (overflow : Block D V l Γ Λ Λ)
    (compileBody : ∀ locals goals, Except Invarianten.Frag.Refusal (BlockCondition (S := S) policy body locals goals))
    (compileOverflow : ∀ locals goals, Except Invarianten.Frag.Refusal (BlockCondition (S := S) policy overflow locals goals))
    (locals : Env D Γ) (goals : Goals D V Γ) :
    Except Invarianten.Frag.Refusal (StatementCondition (S := S) policy (.retry count test body overflow) locals goals) := do
  let domain ← environmentDomain (D := D) budget Γ
  let passGoals : Goals D V Γ :=
    { normal := fun _ => .ok invariant
      escape := goals.normal
      again := fun _ => .ok invariant
      returned := goals.returned
      reason := goals.reason }
  let compilePass := fun env => do
    let done ← requireCondition (program := program) (checked := fun _ => []) (S := S) (goals.normal env)
    let step ← compileBody env passGoals
    let exceeded ← compileOverflow env goals
    let advance : Condition (fun runtime world => ∀ allowed,
        HandlerSafe policy runtime allowed →
        runtime.wpB body (passGoals.holds allowed) world env ∧
        runtime.wpB overflow (goals.holds allowed) world env) :=
      { formula := conj step.formula exceeded.formula
        sound := fun runtime world valid allowed safe =>
          let parts := (conj_denote _ _ _).mp valid
          ⟨step.sound runtime world parts.1 allowed safe, exceeded.sound runtime world parts.2 allowed safe⟩ }
    let branch ← branchCondition test env (withHandlers policy done) advance
    return inductiveCondition invariant branch
  let checks ← allConditions domain.values _ compilePass
  return {
      formula := conj invariant checks.formula
      sound := fun runtime world valid allowed safe => by
        have parts := (conj_denote _ _ _).mp valid
        have obligations := checks.sound runtime world parts.2
        let I : Nat → World D → Env D Γ → Prop :=
          fun _ next _ => invariant.denote (assignment next)
        let doneTest := fun (next : World D) (env : Env D Γ) =>
          let read := next.lese Λ test.orte
          (read, wahr? (eval read test read env))
        have stepRule : ∀ n next env, I (n + 1) next env →
            (doneTest next env).2 = false →
            runtime.wpB body (WP.PassSchritt (goals.holds (l := l) allowed) I n) (doneTest next env).1 env := by
          intro n next env holds unfinished
          have ready := obligations env (domain.complete env) next holds
          have tested : eval (next.lese Λ test.orte) test (next.lese Λ test.orte) env = false := unfinished
          simp only [tested, wahr?, Bool.false_eq_true, ↓reduceIte] at ready
          have ready := ready allowed safe
          have run := ready.1
          unfold Runtime.wpB at run ⊢
          cases result : execBlockH S runtime.oracle runtime.environment runtime.passes runtime.calls body
            (next.lese Λ test.orte) env <;>
            simpa only [result, Goals.holds, WP.PassSchritt, passGoals, I, denotes] using run
        apply WP.retry_regel
          (execBlockH S runtime.oracle runtime.environment runtime.passes runtime.calls body)
          doneTest (execBlockH S runtime.oracle runtime.environment runtime.passes runtime.calls overflow)
          (goals.holds (l := l) allowed) I ?_ ?_ stepRule count world locals parts.1
        · intro n next env holds finished
          have ready := obligations env (domain.complete env) next holds
          have tested : eval (next.lese Λ test.orte) test (next.lese Λ test.orte) env = true := finished
          simp only [tested, wahr?, eq_self, ↓reduceIte] at ready
          simpa only [Goals.holds] using ready allowed safe
        · intro next env holds unfinished
          have ready := obligations env (domain.complete env) next holds
          have tested : eval (next.lese Λ test.orte) test (next.lese Λ test.orte) env = false := unfinished
          simp only [tested, wahr?, Bool.false_eq_true, ↓reduceIte] at ready
          exact (ready allowed safe).2 }

/-- Exact traversal checking retains the model's annotation test at entry,
    each pass and every leave. A false annotation cannot hide a logic stop. -/
def traverseCondition {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (table : D.Tab) (annotation : Expr D Γ Λ .bool)
    (body : Block D V true (.index (D.count table) :: Γ) Λ Λ)
    (compileBody : ∀ locals goals, Except Frag.Refusal (BlockCondition (S := S) policy body locals goals))
    (indices : List (Wert D (.index (D.count table)))) (locals : Env D Γ) (goals : Goals D V Γ) :
    Except Frag.Refusal (Condition (fun runtime : Runtime program (fun _ => []) S => fun world =>
      ∀ allowed, HandlerSafe policy runtime allowed →
        goals.holds (l := l) allowed (traverseLauf (V := V) (l := l)
          (execBlockH S runtime.oracle runtime.environment runtime.passes runtime.calls body)
          (fun world env => let read := world.lese Λ annotation.orte
            (read, wahr? (eval read annotation read env))) indices world locals))) :=
  let refused : Condition (fun (_ : Runtime program (fun _ => []) S) (_ : World D) => False) :=
    { formula := .fls, sound := fun _ _ impossible => False.elim impossible }
  match indices with
  | [] => do
      let done ← requireCondition (program := program) (checked := fun _ => []) (S := S) (goals.normal locals)
      let combined ← branchCondition annotation locals
        (done.map (fun runtime _ ready (allowed : Logik D → Prop)
          (_ : HandlerSafe policy runtime allowed) => ready)) refused
      return combined.map (fun runtime world ready allowed safe => by
        cases tested : eval (world.lese Λ annotation.orte) annotation (world.lese Λ annotation.orte) locals with
        | false =>
            simp only [wahr?, tested, Bool.false_eq_true, ↓reduceIte] at ready
            exact ready.elim
        | true =>
            simp only [wahr?, tested, ↓reduceIte] at ready
            simpa only [traverseLauf, wahr?, tested, ↓reduceIte, Goals.holds] using ready allowed safe)
  | index :: indices => do
      let resume := fun env => traverseCondition table annotation body compileBody indices env goals
      let exit := fun env => traverseCondition table annotation body compileBody [] env goals
      let passGoals : Goals D V (.index (D.count table) :: Γ) :=
        { normal := fun env => generatedFormula (resume env.tail)
          escape := fun env => generatedFormula (exit env.tail)
          again := fun env => generatedFormula (resume env.tail)
          returned := goals.returned
          reason := goals.reason }
      let step ← compileBody (.cons index locals) passGoals
      let advanced : Condition (fun runtime : Runtime program (fun _ => []) S => fun world =>
        ∀ allowed, HandlerSafe policy runtime allowed →
        goals.holds (l := l) allowed (match execBlockH S runtime.oracle runtime.environment
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
          | .hardware error => .hardware error)) := step.map (fun runtime world ready allowed safe => by
        have ready := ready allowed safe
        unfold Runtime.wpB at ready
        cases result : execBlockH S runtime.oracle runtime.environment runtime.passes runtime.calls body
            world (.cons index locals) with
        | ok next env =>
            rw [result] at ready
            exact generated_sound (resume env.tail) runtime next ready allowed safe
        | next h next env =>
            rw [result] at ready
            exact generated_sound (resume env.tail) runtime next ready allowed safe
        | leave h next env =>
            rw [result] at ready
            exact generated_sound (exit env.tail) runtime next ready allowed safe
        | zurueck next value => simpa only [result, Goals.holds, passGoals] using ready
        | why next reason => simpa only [result, Goals.holds, passGoals] using ready
        | logik error => simpa only [result, Goals.holds] using ready
        | hardware error => trivial)
      let combined ← branchCondition annotation locals advanced refused
      return combined.map (fun runtime world ready allowed safe => by
        cases tested : eval (world.lese Λ annotation.orte) annotation (world.lese Λ annotation.orte) locals with
        | false =>
            simp only [wahr?, tested, Bool.false_eq_true, ↓reduceIte] at ready
            exact ready.elim
        | true =>
            simp only [wahr?, tested, ↓reduceIte] at ready
            have ready := ready allowed safe
            cases result : execBlockH S runtime.oracle runtime.environment runtime.passes runtime.calls body
                (world.lese Λ annotation.orte) (.cons index locals) <;>
              simpa only [traverseLauf, wahr?, tested, Bool.true_eq_false,
                ↓reduceIte, Goals.holds, result] using ready)
termination_by indices.length
decreasing_by all_goals simp_wf <;> omega

end Gabbro.Grammatik.Vertraege.Pruefer
