module

public import Grammatik.Logik.Invarianten.VC.Induction

@[expose] public section

namespace Gabbro.Grammatik.Invarianten.VC

open Frag Elim Elim.Korrekt Modell

variable {D : Deklaration} {V : Vertrag D} {S : SperrInv D}

/-- Depth limits source traversal; expansion limits local domains and loop
    unrolling. Neither limit is an assumption about runtime behaviour. -/
structure VCBudget where
  depth : Nat := 128
  expansion : Nat := 128

abbrev EndCondition (program : Programm D) (checked : D.Fn → List D.Inv) (S : SperrInv D)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (code : Endblock D V l Γ Λ) (locals : Env D Γ) (terminal : QF (Observation D)) :=
  Condition (fun runtime : Runtime program checked S =>
    fun world => runtime.wpE code (EndFlow terminal) world locals)

def finalGoals {Γ : Ctx} (terminal : QF (Observation D)) : Goals D Γ where
  normal := fun _ => .ok terminal
  escape := fun _ => .ok terminal
  again := fun _ => .ok terminal
  terminal := terminal

section Compiler

variable (program : Programm D) (checked : D.Fn → List D.Inv)
    (facts : ∀ lock, Except Frag.Refusal (LockFormula S lock)) (expansion : Nat)
    (loopInvariant : Option (QF (Observation D)))

mutual

def extendedStatement (fuel : Nat) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (code : Stmt D V l Γ Λ Λ') (locals : Env D Γ) (goals : Goals D Γ) :
    Except Frag.Refusal (StatementCondition program checked S code locals goals) :=
  match fuel with
  | 0 => .error (.unsupported "writer VC syntax-depth budget exceeded")
  | fuel + 1 =>
    match code with
    | .ite test yes no => do
        let positive ← extendedBlock fuel yes locals goals
        let negative ← extendedBlock fuel no locals goals
        let pre ← branchCondition test locals positive negative
        return pre.map (fun runtime world ready => by
          cases tested : eval (world.lese Λ test.orte) test (world.lese Λ test.orte) locals <;>
            simpa only [Runtime.wpS, Runtime.wpB, execStmtH, wahr?, tested,
              Bool.false_eq_true, ↓reduceIte] using ready)
    | .breaking label body => do
        let pre ← extendedBlock fuel body locals goals
        return pre.map (fun _ _ ready => ready)
    | .retry count test body overflow =>
        if count ≤ expansion then do
          let pre ← retryCondition (V := V) (l := l) test body overflow
            (fun env target => extendedBlock fuel body env target)
            (fun env target => extendedBlock fuel overflow env target) count locals goals
          return pre.map (fun _ _ ready => ready)
        else
          match loopInvariant with
          | none => .error (.unsupported "retry unrolling exceeds the VC budget; provide a checked loop invariant")
          | some invariant => retryInvariantCondition expansion count invariant test body overflow
              (fun env target => extendedBlock fuel body env target)
              (fun env target => extendedBlock fuel overflow env target) locals goals
    | .traverse table annotation body =>
        if (D.count table).toNat ≤ expansion then do
          let pre ← traverseCondition (V := V) (l := l) table annotation body
            (fun env target => extendedBlock fuel body env target)
            (alleIndizes (D.count table)) locals goals
          return pre.map (fun _ _ ready => ready)
        else .error (.unsupported "traverse static count exceeds the VC unrolling budget")
    | .locks lock rank body =>
        match facts lock with
        | .ok fact => do
            let pre ← extendedBlock fuel body locals (goals.releasing fact.formula)
            return lockCondition lock rank body locals goals fact pre
        | .error _ => do
            let pre ← extendedBlock fuel body locals goals
            return opaqueLockCondition lock rank body locals goals pre
    | .forever .. => .error (.unsupported "forever requires a checked inductive invariant")
    | other => leafCondition (program := program) (checked := checked) expansion facts other locals goals
termination_by fuel

def extendedBlock (fuel : Nat) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (code : Block D V l Γ Λ Λ') (locals : Env D Γ) (goals : Goals D Γ) :
    Except Frag.Refusal (BlockCondition program checked S code locals goals) :=
  match fuel with
  | 0 => .error (.unsupported "writer VC syntax-depth budget exceeded")
  | fuel + 1 =>
    match code with
    | .nil => do
        let pre ← requireCondition (program := program) (checked := checked) (S := S) (goals.normal locals)
        return pre.map (fun _ _ ready => ready)
    | .cons first rest => do
        let tails := fun env => extendedBlock fuel rest env goals
        let headGoals : Goals D Γ :=
          { goals with normal := fun env => generatedFormula (tails env) }
        let head ← extendedStatement fuel first locals headGoals
        return head.map (fun runtime world ready => by
          unfold Runtime.wpS at ready
          unfold Runtime.wpB
          simp only [execBlockH]
          cases result : execStmtH S runtime.oracle runtime.environment runtime.passes runtime.calls first world locals with
          | ok next env =>
              rw [result] at ready
              exact generated_sound (tails env) runtime next ready
          | zurueck next value => simpa only [result, Goals.holds] using ready
          | why next reason => simpa only [result, Goals.holds] using ready
          | leave h next env => simpa only [result, Goals.holds] using ready
          | next h next env => simpa only [result, Goals.holds] using ready
          | logik error => trivial
          | hardware error => trivial)
    | .bind expression rest =>
        bindingCondition expansion expression rest locals goals
          (fun env => extendedBlock fuel rest env (goals.shrink _))
    | .bindCall f args he hp hr rest =>
        boundCallCondition expansion f args he hp hr rest locals goals
          (fun env => extendedBlock fuel rest env (goals.shrink _))
    | _ => .error (.unsupported "writer block constructor is outside the checked control fragment")
termination_by fuel

end

/-- End-block generation uses the same statement and local-continuation rules.
    Its result feeds the existing writer matrix and decider, with no proof of a
    particular program supplied by the caller. -/
def extendedEnd (fuel : Nat) {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (code : Endblock D V l Γ Λ) (locals : Env D Γ) (terminal : QF (Observation D)) :
    Except Frag.Refusal (EndCondition program checked S code locals terminal) :=
  match fuel with
  | 0 => .error (.unsupported "writer VC syntax-depth budget exceeded")
  | fuel + 1 =>
    match code with
    | .ret expression _ => .ok
        { formula := terminal
          sound := fun _ world valid => by
            change terminal.denote (assignment (world.lese Λ expression.orte))
            rw [assignment_lese]
            exact valid }
    | .retWhy _ _ | .leave _ | .next _ => .ok
        { formula := terminal
          sound := fun _ _ valid => valid }
    | .retScoped expression cleanup => do
        let pre ← leafCondition (l := l) expansion facts (.retScoped expression cleanup) locals (finalGoals terminal)
        return pre.map (fun runtime world ready => by
          unfold Runtime.wpS at ready
          unfold Runtime.wpE
          simp only [execStmtH, execEndH] at ready ⊢
          split <;> rename_i cleanupReady <;>
            simpa only [cleanupReady, ↓reduceIte, Goals.holds, EndFlow, finalGoals] using ready)
    | .retWhyScoped reason cleanup => do
        let pre ← leafCondition (l := l) expansion facts (.retWhyScoped reason cleanup) locals (finalGoals terminal)
        return pre.map (fun runtime world ready => by
          unfold Runtime.wpS at ready
          unfold Runtime.wpE
          simp only [execStmtH, execEndH] at ready ⊢
          split <;> rename_i cleanupReady <;>
            simpa only [cleanupReady, ↓reduceIte, Goals.holds, EndFlow, finalGoals] using ready)
    | .cons first rest => do
        let tails := fun env => extendedEnd fuel rest env terminal
        let headGoals : Goals D Γ :=
          { finalGoals terminal with normal := fun env => generatedFormula (tails env) }
        let head ← extendedStatement program checked facts expansion loopInvariant fuel first locals headGoals
        return head.map (fun runtime world ready => by
          unfold Runtime.wpS at ready
          unfold Runtime.wpE
          simp only [execEndH]
          cases result : execStmtH S runtime.oracle runtime.environment runtime.passes runtime.calls first world locals with
          | ok next env =>
              rw [result] at ready
              exact generated_sound (tails env) runtime next ready
          | zurueck next value => simpa only [result, Goals.holds, EndFlow, headGoals, finalGoals] using ready
          | why next reason => simpa only [result, Goals.holds, EndFlow, headGoals, finalGoals] using ready
          | leave h next env => simpa only [result, Goals.holds, EndFlow, headGoals, finalGoals, denotes] using ready
          | next h next env => simpa only [result, Goals.holds, EndFlow, headGoals, finalGoals, denotes] using ready
          | logik error => trivial
          | hardware error => trivial)
    | .ite test yes no => do
        let positive ← extendedEnd fuel yes locals terminal
        let negative ← extendedEnd fuel no locals terminal
        let pre ← branchCondition test locals positive negative
        return pre.map (fun runtime world ready => by
          cases tested : eval (world.lese Λ test.orte) test (world.lese Λ test.orte) locals <;>
            simpa only [Runtime.wpE, execEndH, wahr?, tested, eq_self,
              Bool.false_eq_true, ↓reduceIte] using ready)
    | .bind expression rest => do
        let pre ← localSelect expansion expression locals
          (fun value runtime world => runtime.wpE rest (EndFlow terminal) world (.cons value locals))
          (fun value => extendedEnd fuel rest (.cons value locals) terminal)
        return (pre.read Λ expression.orte).map (fun runtime world ready => by
          unfold Runtime.wpE at ready ⊢
          simp only [execEndH]
          cases result : execEndH S runtime.oracle runtime.environment runtime.passes runtime.calls rest
            (world.lese Λ expression.orte)
            (.cons (eval (world.lese Λ expression.orte) expression (world.lese Λ expression.orte) locals) locals) <;>
            simpa only [result, EndFlow, EndAusgang.schrumpf] using ready)
    | .bindCall f args he hp hr rest => do
        let domain ← localDomain (D := D) expansion _
        let tails ← allConditions domain.values
          (fun value runtime world => runtime.wpE rest (EndFlow terminal) world (.cons value locals))
          (fun value => do
            let pre ← extendedEnd fuel rest (.cons value locals) terminal
            return pre.freshResult _ value)
        let known ← invariantFormula program (checked f)
        return {
            formula := callWP f known.formula tails.formula
            sound := fun runtime world valid => by
              let read := world.lese Λ args.orte
              let actual := evalArgs read args read locals
              have validRead : (callWP f known.formula tails.formula).denote (assignment read) := by
                rw [assignment_lese]
                exact valid
              unfold Runtime.wpE
              dsimp only [execEndH]
              cases reply : runtime.calls f read actual with
              | ok next value =>
                  have frame := runtime.evidence.frame f read actual next value reply
                  have inv := (known.correct next).mpr
                    (runtime.evidence.invariants f read actual next value reply)
                  have ready := callWP_sound f known.formula tails.formula read next validRead frame inv
                  have result := tails.sound runtime next ready (ergWert he value) (domain.complete _)
                  unfold Runtime.wpE at result
                  cases outcome : execEndH S runtime.oracle runtime.environment runtime.passes runtime.calls rest
                    next (.cons (ergWert he value) locals) <;>
                    simpa only [outcome, EndFlow, EndAusgang.schrumpf] using result
              | why next reason => exact (Fin.cast hr reason).elim0
              | logik error => trivial
              | hardware error => trivial }
    | _ => .error (.unsupported "writer end block is outside the checked control fragment")
termination_by fuel

end Compiler

end Gabbro.Grammatik.Invarianten.VC
