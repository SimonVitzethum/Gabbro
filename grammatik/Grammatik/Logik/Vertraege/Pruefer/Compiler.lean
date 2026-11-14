module

public import Grammatik.Logik.Vertraege.Pruefer.Locks

@[expose] public section

namespace Gabbro.Grammatik.Vertraege.Pruefer

open Invarianten Invarianten.Frag Invarianten.Elim Invarianten.VC

variable {D : Deklaration} {V : Vertrag D} {S : SperrInv D} {program : Programm D}

section Compiler

variable (policy : CallPolicy program) (facts : ∀ lock, Except Invarianten.Frag.Refusal (LockFormula S lock))
    (budget : VCBudget) (hint : Option (QF (Observation D)))

mutual

/-- Sufficient WPs for the canonical typed code. There is no source execution
    engine here: soundness refers only to execStmtH/execBlockH/execEndH. -/
def statement (fuel : Nat) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (code : Stmt D V l Γ Λ Λ') (locals : Env D Γ) (goals : Goals D V Γ) :
    Except Invarianten.Frag.Refusal (StatementCondition (S := S) policy code locals goals) :=
  match fuel with
  | 0 => .error (.unsupported "contract VC syntax-depth budget exceeded")
  | fuel + 1 =>
    match code with
    | .ite test yes no => do
        let positive ← block fuel yes locals goals
        let negative ← block fuel no locals goals
        let pre ← branchCondition test locals positive negative
        return pre.map (fun runtime world ready allowed safe => by
          cases tested : eval (world.lese Λ test.orte) test (world.lese Λ test.orte) locals <;>
            simp only [tested, Bool.false_eq_true, ↓reduceIte] at ready <;>
            have ready := ready allowed safe <;>
            simpa only [Runtime.wpS, Runtime.wpB, execStmtH, wahr?, tested,
              Bool.false_eq_true, ↓reduceIte] using ready)
    | .breaking _ body => do
        let pre ← block fuel body locals goals
        return pre.map (fun _ _ ready => ready)
    | .retry count test body overflow =>
        if count ≤ budget.expansion then
          retryCondition policy test body overflow
            (fun env target => block fuel body env target)
            (fun env target => block fuel overflow env target) count locals goals
        else
          match hint with
          | none => .error (.unsupported "loop exceeds unrolling budget and has no checked hint")
          | some invariant => retryInvariantCondition policy budget.expansion count invariant test body overflow
              (fun env target => block fuel body env target)
              (fun env target => block fuel overflow env target) locals goals
    | .locks lock rank body => do
        let fact ← facts lock
        let pre ← block fuel body locals (goals.releasing fact.formula)
        return lockCondition lock rank body locals goals fact pre
    | .retScoped expression cleanup => scopedReturnCondition budget.expansion facts expression cleanup locals goals
    | .call f args hp hr => do
        let normal ← requireCondition (program := program) (checked := fun _ => []) (S := S) (goals.normal locals)
        let pre ← arguments budget.expansion args locals _ (fun actual =>
          callCondition policy budget.expansion f actual hr
            (fun _ _ world => denotes (goals.normal locals) world) (fun _ => .ok normal))
        return (pre.read Λ args.orte).map (fun runtime world ready allowed safe => by
          have ready := ready allowed safe
          unfold Runtime.wpS
          dsimp only [execStmtH]
          cases reply : runtime.calls f (world.lese Λ args.orte)
            (evalArgs (world.lese Λ args.orte) args (world.lese Λ args.orte) locals) <;>
            simpa only [reply, Goals.holds] using ready)
    | _ => leafCondition policy budget.expansion code locals goals
termination_by fuel

def block (fuel : Nat) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (code : Block D V l Γ Λ Λ') (locals : Env D Γ) (goals : Goals D V Γ) :
    Except Invarianten.Frag.Refusal (BlockCondition (S := S) policy code locals goals) :=
  match fuel with
  | 0 => .error (.unsupported "contract VC syntax-depth budget exceeded")
  | fuel + 1 =>
    match code with
    | .nil => do
        let pre ← requireCondition (program := program) (checked := fun _ => []) (S := S) (goals.normal locals)
        return pre.map (fun _ _ ready _ _ => ready)
    | .cons first rest => do
        let tails := fun env => block fuel rest env goals
        let headGoals : Goals D V Γ := { goals with normal := fun env => generatedFormula (tails env) }
        let head ← statement fuel first locals headGoals
        return head.map (fun runtime world ready allowed safe => by
          have ready := ready allowed safe
          unfold Runtime.wpS at ready
          unfold Runtime.wpB
          simp only [execBlockH]
          cases result : execStmtH S runtime.oracle runtime.environment runtime.passes runtime.calls first world locals with
          | ok next env =>
              rw [result] at ready
              exact generated_sound (tails env) runtime next ready allowed safe
          | zurueck next value => simpa only [result, Goals.holds, headGoals] using ready
          | why next reason => simpa only [result, Goals.holds, headGoals] using ready
          | leave h next env => simpa only [result, Goals.holds, headGoals] using ready
          | next h next env => simpa only [result, Goals.holds, headGoals] using ready
          | logik error => simpa only [result, Goals.holds] using ready
          | hardware error => trivial)
    | .bind expression rest => do
        let pre ← localSelect budget.expansion expression locals _
          (fun value => block fuel rest (.cons value locals) (goals.shrink _))
        return (pre.read Λ expression.orte).map (fun runtime world ready allowed safe => by
          have ready := ready allowed safe
          unfold Runtime.wpB at ready ⊢
          simp only [execBlockH]
          exact (goals.holds_shrink _ allowed _).mp ready)
    | .bindCall f args he hp hr rest => do
        let pre ← arguments budget.expansion args locals _ (fun actual =>
          callCondition policy budget.expansion f actual hr _
            (fun value => block fuel rest (.cons (ergWert he value) locals) (goals.shrink _)))
        return (pre.read Λ args.orte).map (fun runtime world ready allowed safe => by
          have ready := ready allowed safe
          unfold Runtime.wpB
          dsimp only [execBlockH]
          cases reply : runtime.calls f (world.lese Λ args.orte)
              (evalArgs (world.lese Λ args.orte) args (world.lese Λ args.orte) locals) with
          | ok next value =>
              rw [reply] at ready
              exact (goals.holds_shrink _ allowed _).mp (ready allowed safe)
          | why next reason => exact (Fin.cast hr reason).elim0
          | logik error => simpa only [reply, Goals.holds] using ready
          | hardware error => trivial)
    | _ => .error (.unsupported "contract block is outside the checked control fragment")
termination_by fuel

def ending (fuel : Nat) {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (code : Endblock D V l Γ Λ) (locals : Env D Γ) (goals : Goals D V Γ) :
    Except Invarianten.Frag.Refusal (EndCondition (S := S) policy code locals goals) :=
  match fuel with
  | 0 => .error (.unsupported "contract VC syntax-depth budget exceeded")
  | fuel + 1 =>
    match code with
    | .ret expression _ => do
        let pre ← returnCondition (S := S) budget.expansion expression locals goals
        return (pre.read Λ expression.orte).map (fun _ _ ready _ _ => ready)
    | .retWhy _ _ => .ok
        { formula := goals.reason
          sound := fun _ _ ready _ _ => ready }
    | .leave _ => do
        let pre ← requireCondition (program := program) (checked := fun _ => []) (S := S) (goals.escape locals)
        return pre.map (fun _ _ ready _ _ => ready)
    | .next _ => do
        let pre ← requireCondition (program := program) (checked := fun _ => []) (S := S) (goals.again locals)
        return pre.map (fun _ _ ready _ _ => ready)
    | .cons first rest => do
        let tails := fun env => ending fuel rest env goals
        let headGoals : Goals D V Γ := { goals with normal := fun env => generatedFormula (tails env) }
        let head ← statement fuel first locals headGoals
        return head.map (fun runtime world ready allowed safe => by
          have ready := ready allowed safe
          unfold Runtime.wpS at ready
          unfold Runtime.wpE
          simp only [execEndH]
          cases result : execStmtH S runtime.oracle runtime.environment runtime.passes runtime.calls first world locals with
          | ok next env =>
              rw [result] at ready
              exact generated_sound (tails env) runtime next ready allowed safe
          | zurueck next value => simpa only [result, Goals.holds, Goals.endHolds, headGoals] using ready
          | why next reason => simpa only [result, Goals.holds, Goals.endHolds, headGoals] using ready
          | leave h next env => simpa only [result, Goals.holds, Goals.endHolds, headGoals] using ready
          | next h next env => simpa only [result, Goals.holds, Goals.endHolds, headGoals] using ready
          | logik error => simpa only [result, Goals.holds, Goals.endHolds] using ready
          | hardware error => trivial)
    | .ite test yes no => do
        let positive ← ending fuel yes locals goals
        let negative ← ending fuel no locals goals
        let pre ← branchCondition test locals positive negative
        return pre.map (fun runtime world ready allowed safe => by
          cases tested : eval (world.lese Λ test.orte) test (world.lese Λ test.orte) locals <;>
            simp only [tested, Bool.false_eq_true, ↓reduceIte] at ready <;>
            have ready := ready allowed safe <;>
            simpa only [Runtime.wpE, execEndH, wahr?, tested,
              Bool.false_eq_true, ↓reduceIte] using ready)
    | .bind expression rest => do
        let pre ← localSelect budget.expansion expression locals _
          (fun value => ending fuel rest (.cons value locals) (goals.shrink _))
        return (pre.read Λ expression.orte).map (fun runtime world ready allowed safe => by
          have ready := ready allowed safe
          unfold Runtime.wpE at ready ⊢
          simp only [execEndH]
          exact (goals.endHolds_shrink _ allowed _).mp ready)
    | .bindCall f args he hp hr rest => do
        let pre ← arguments budget.expansion args locals _ (fun actual =>
          callCondition policy budget.expansion f actual hr _
            (fun value => ending fuel rest (.cons (ergWert he value) locals) (goals.shrink _)))
        return (pre.read Λ args.orte).map (fun runtime world ready allowed safe => by
          have ready := ready allowed safe
          unfold Runtime.wpE
          dsimp only [execEndH]
          cases reply : runtime.calls f (world.lese Λ args.orte)
              (evalArgs (world.lese Λ args.orte) args (world.lese Λ args.orte) locals) with
          | ok next value =>
              rw [reply] at ready
              exact (goals.endHolds_shrink _ allowed _).mp (ready allowed safe)
          | why next reason => exact (Fin.cast hr reason).elim0
          | logik error => simpa only [reply, Goals.endHolds] using ready
          | hardware error => trivial)
    | _ => .error (.unsupported "contract end block is outside the checked control fragment")
termination_by fuel

end

end Compiler

end Gabbro.Grammatik.Vertraege.Pruefer
