module

public import Grammatik.Logik.Vertraege.Pruefer.Locks
public import Grammatik.Logik.Vertraege.Pruefer.Control.Budget

@[expose] public section

namespace Gabbro.Grammatik.Vertraege.Pruefer

open Invarianten Invarianten.Frag Invarianten.Elim Invarianten.VC

variable {D : Deklaration} {V : Vertrag D} {S : SperrInv D} {program : Programm D}

section Compiler

variable (policy : CallPolicy program) (facts : ∀ lock, Except Frag.Refusal (LockFormula S lock))
    (budget : VCBudget) (hint : Option (QF (Observation D)))

mutual

/-- Sufficient WPs for the canonical typed code. There is no source execution
    engine here: soundness refers only to execStmtH/execBlockH/execEndH. -/
def statement (fuel : Nat) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (code : Stmt D V l Γ Λ Λ') (locals : Env D Γ) (goals : Goals D V Γ) :
    Except Frag.Refusal (StatementCondition (S := S) policy code locals goals) :=
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
    | .onWhy expression arms => do
        let pre ← reasonCases fuel arms locals goals
        return (pre.read Λ expression.orte).map (fun runtime world ready allowed safe =>
          ready allowed safe (eval (world.lese Λ expression.orte) expression
            (world.lese Λ expression.orte) locals))
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
    | .traverse table annotation body =>
        if (D.count table).toNat ≤ budget.expansion then do
          let pre ← traverseCondition policy (V := V) (l := l) table annotation body
            (fun env target => block fuel body env target)
            (alleIndizes (D.count table)) locals goals
          return pre.map (fun _ _ ready => ready)
        else .error (.unsupported "traverse static count exceeds the contract VC budget")
    | .locks lock rank body => do
        let fact ← facts lock
        let pre ← block fuel body locals (goals.releasing fact.formula)
        return lockCondition lock rank body locals goals fact pre
    | .retScoped expression cleanup => scopedReturnCondition budget.expansion facts expression cleanup locals goals
    | .retWhyScoped reason cleanup => scopedReasonCondition facts reason cleanup locals goals
    | .call f args hp hr => do
        let normal ← requireCondition (program := program) (checked := fun _ => []) (S := S) (goals.normal locals)
        let pre ← arguments budget.expansion args locals _ (fun actual =>
          callCondition policy budget.expansion f actual hr
            (fun _ _ world => denotes (goals.normal locals) world) (fun _ => .ok normal)
            (match program.ensures f with
             | .tru => some (normal.map (fun _ _ ready _ => ready))
             | _ => none))
        return (pre.read Λ args.orte).map (fun runtime world ready allowed safe => by
          have ready := ready allowed safe
          unfold Runtime.wpS
          dsimp only [execStmtH]
          cases reply : runtime.calls f (world.lese Λ args.orte)
            (evalArgs (world.lese Λ args.orte) args (world.lese Λ args.orte) locals) <;>
            simpa only [reply, Goals.holds] using ready)
    | other => leafCondition policy budget.expansion other locals goals
termination_by fuel

def block (fuel : Nat) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (code : Block D V l Γ Λ Λ') (locals : Env D Γ) (goals : Goals D V Γ) :
    Except Frag.Refusal (BlockCondition (S := S) policy code locals goals) :=
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
        let pre ← selectValue budget.expansion expression locals _
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
    | .regRead register readable .nil => do
        let pre ← requireCondition (program := program) (checked := fun _ => []) (S := S) (goals.normal locals)
        return pre.map (fun runtime world ready allowed _ =>
          registerReadEmpty_sound runtime register readable world locals (goals.holds allowed)
            (fun next same => (denotes_assignment _ world next same.symm).mp ready)
            (fun _ => trivial))
    | .check test failure rest => do
        let positive ← block fuel rest locals goals
        let negative ← ending fuel failure locals goals
        let pre ← branchCondition test locals positive negative
        return pre.map (fun runtime world ready allowed safe => by
          unfold Runtime.wpB
          simp only [execBlockH]
          split
          · rename_i taken
            simp only [taken, ↓reduceIte] at ready
            exact ready allowed safe
          · rename_i untaken
            simp only [untaken, ↓reduceIte] at ready
            have ready := ready allowed safe
            cases outcome : execEndH S runtime.oracle runtime.environment runtime.passes runtime.calls
              failure (world.lese Λ test.orte) locals <;>
              simpa only [Runtime.wpE, outcome, Goals.holds, Goals.endHolds, EndAusgang.zuAusgang] using ready)
    | .narrow expression low high failure rest => do
        let pre ← narrowingCondition budget.expansion expression low high locals _ _
          (fun value => block fuel rest (.cons value locals) (goals.shrink _))
          (ending fuel failure locals goals)
        return (pre.read Λ expression.orte).map (fun runtime world ready allowed safe => by
          unfold Runtime.wpB
          simp only [execBlockH]
          split <;> rename_i fits
          · simp only [dif_pos fits] at ready
            exact (goals.holds_shrink _ allowed _).mp (ready allowed safe)
          · simp only [dif_neg fits] at ready
            have ready := ready allowed safe
            cases outcome : execEndH S runtime.oracle runtime.environment runtime.passes runtime.calls
              failure (world.lese Λ expression.orte) locals <;>
              simpa only [Runtime.wpE, outcome, Goals.holds, Goals.endHolds, EndAusgang.zuAusgang] using ready)
    | .narrowRequired expression low high rest => do
        let refused : Condition (fun (_ : Runtime program (fun _ => []) S) (_ : World D) => False) :=
          { formula := .fls, sound := fun _ _ impossible => False.elim impossible }
        let pre ← narrowingCondition budget.expansion expression low high locals _ _
          (fun value => block fuel rest (.cons value locals) (goals.shrink _)) (.ok refused)
        return (pre.read Λ expression.orte).map (fun runtime world ready allowed safe => by
          unfold Runtime.wpB
          simp only [execBlockH]
          split <;> rename_i fits
          · simp only [dif_pos fits] at ready
            exact (goals.holds_shrink _ allowed _).mp (ready allowed safe)
          · simp only [dif_neg fits] at ready
            )
    | .bindCallElse f args he hp hr failure rest => do
        let pre ← arguments budget.expansion args locals _ (fun actual =>
          callOutcomesCondition policy budget.expansion f actual _ _
            (fun value => block fuel rest (.cons (ergWert he value) locals) (goals.shrink _))
            (fun reason => ending fuel failure (.cons reason locals) (goals.shrink _)))
        return (pre.read Λ args.orte).map (fun runtime world ready allowed safe => by
          have ready := ready allowed safe
          unfold Runtime.wpB
          dsimp only [execBlockH]
          cases reply : runtime.calls f (world.lese Λ args.orte)
              (evalArgs (world.lese Λ args.orte) args (world.lese Λ args.orte) locals) with
          | ok next value =>
              rw [reply] at ready
              exact (goals.holds_shrink _ allowed _).mp (ready allowed safe)
          | why next reason =>
              rw [reply] at ready
              have ready := (goals.endHolds_shrink _ allowed _).mp (ready allowed safe)
              cases outcome : execEndH S runtime.oracle runtime.environment runtime.passes runtime.calls
                failure next (.cons reason locals) <;>
                simpa only [Runtime.wpE, outcome, Goals.holds, Goals.endHolds,
                  EndAusgang.schrumpf, EndAusgang.zuAusgang] using ready
          | logik error => simpa only [reply, Goals.holds] using ready
          | hardware error => trivial)
    | .bindCallInd .. | .bindCallIndElse .. =>
        .error (.unsupported "contract indirect binding needs a checked finite target dispatch")
    | .bindAxiom .. | .bindAxiomElse .. | .bindAxiomOpt .. | .bindAxiomOptElse .. =>
        .error (.unsupported "contract oracle binding needs quantified answer and poststate observations")
    | .regRead .. | .regReadElse .. =>
        .error (.unsupported "contract register binding needs a typed fresh result observation")
    | .awaits .. | .exchange .. =>
        .error (.unsupported "contract atomic binding needs rely-aware fresh observations")
    | .float .. | .floatLit .. | .floatOf .. | .floatNarrow .. =>
        .error (.unsupported "contract floating binding needs an exact typed range-check certificate")
termination_by fuel

def ending (fuel : Nat) {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (code : Endblock D V l Γ Λ) (locals : Env D Γ) (goals : Goals D V Γ) :
    Except Frag.Refusal (EndCondition (S := S) policy code locals goals) :=
  match fuel with
  | 0 => .error (.unsupported "contract VC syntax-depth budget exceeded")
  | fuel + 1 =>
    match code with
    | .ret expression _ => do
        let pre ← returnCondition (S := S) budget.expansion expression locals goals.returned goals.uniformReturn
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
        let pre ← selectValue budget.expansion expression locals _
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
    | .bindCallElse f args he hp hr failure rest => do
        let pre ← arguments budget.expansion args locals _ (fun actual =>
          callOutcomesCondition policy budget.expansion f actual _ _
            (fun value => ending fuel rest (.cons (ergWert he value) locals) (goals.shrink _))
            (fun reason => ending fuel failure (.cons reason locals) (goals.shrink _)))
        return (pre.read Λ args.orte).map (fun runtime world ready allowed safe => by
          have ready := ready allowed safe
          unfold Runtime.wpE
          dsimp only [execEndH]
          cases reply : runtime.calls f (world.lese Λ args.orte)
              (evalArgs (world.lese Λ args.orte) args (world.lese Λ args.orte) locals) with
          | ok next value =>
              rw [reply] at ready
              exact (goals.endHolds_shrink _ allowed _).mp (ready allowed safe)
          | why next reason =>
              rw [reply] at ready
              exact (goals.endHolds_shrink _ allowed _).mp (ready allowed safe)
          | logik error => simpa only [reply, Goals.endHolds] using ready
          | hardware error => trivial)
    | .narrow expression low high failure rest => do
        let pre ← narrowingCondition budget.expansion expression low high locals _ _
          (fun value => ending fuel rest (.cons value locals) (goals.shrink _))
          (ending fuel failure locals goals)
        return (pre.read Λ expression.orte).map (fun runtime world ready allowed safe => by
          unfold Runtime.wpE
          simp only [execEndH]
          split <;> rename_i fits
          · simp only [dif_pos fits] at ready
            exact (goals.endHolds_shrink _ allowed _).mp (ready allowed safe)
          · simp only [dif_neg fits] at ready
            exact ready allowed safe)
    | .narrowRequired expression low high rest => do
        let refused : Condition (fun (_ : Runtime program (fun _ => []) S) (_ : World D) => False) :=
          { formula := .fls, sound := fun _ _ impossible => False.elim impossible }
        let pre ← narrowingCondition budget.expansion expression low high locals _ _
          (fun value => ending fuel rest (.cons value locals) (goals.shrink _)) (.ok refused)
        return (pre.read Λ expression.orte).map (fun runtime world ready allowed safe => by
          unfold Runtime.wpE
          simp only [execEndH]
          split <;> rename_i fits
          · simp only [dif_pos fits] at ready
            exact (goals.endHolds_shrink _ allowed _).mp (ready allowed safe)
          · simp only [dif_neg fits] at ready
            )
    | .retScoped expression cleanup => do
        let pre ← scopedReturnCondition (policy := policy) (l := l) budget.expansion facts expression cleanup locals goals
        return pre.map (fun runtime world ready allowed safe => by
          have ready := ready allowed safe
          unfold Runtime.wpS at ready
          unfold Runtime.wpE
          simp only [execStmtH, execEndH] at ready ⊢
          split <;> rename_i cleanupReady <;>
            simpa only [cleanupReady, Bool.false_eq_true, ↓reduceIte, Goals.holds, Goals.endHolds] using ready)
    | .retWhyScoped reason cleanup => do
        let pre ← scopedReasonCondition (policy := policy) (l := l) facts reason cleanup locals goals
        return pre.map (fun runtime world ready allowed safe => by
          have ready := ready allowed safe
          unfold Runtime.wpS at ready
          unfold Runtime.wpE
          simp only [execStmtH, execEndH] at ready ⊢
          split <;> rename_i cleanupReady <;>
            simpa only [cleanupReady, Bool.false_eq_true, ↓reduceIte, Goals.holds, Goals.endHolds] using ready)
    | .bindCallInd .. | .bindCallIndElse .. =>
        .error (.unsupported "contract indirect end binding needs a checked finite target dispatch")
    | .bindAxiom .. | .bindAxiomElse .. | .bindAxiomOpt .. | .bindAxiomOptElse .. =>
        .error (.unsupported "contract oracle end binding needs quantified answer and poststate observations")
    | .regRead .. | .regReadElse .. =>
        .error (.unsupported "contract register end binding needs a typed fresh result observation")
    | .awaits .. | .exchange .. =>
        .error (.unsupported "contract atomic end binding needs rely-aware fresh observations")
    | .float .. | .floatLit .. | .floatOf .. | .floatNarrow .. =>
        .error (.unsupported "contract floating end binding needs an exact typed range-check certificate")
termination_by fuel

def reasonCases (fuel : Nat) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {count : Nat}
    (arms : GrundArms D V l Γ Λ Λ' count) (locals : Env D Γ) (goals : Goals D V Γ) :
    Except Frag.Refusal (Condition (fun runtime : Runtime program (fun _ => []) S => fun world =>
      ∀ allowed, HandlerSafe policy runtime allowed → ∀ reason : Fin count,
        goals.holds (l := l) allowed (execGrundH S runtime.oracle runtime.environment runtime.passes
          runtime.calls arms reason world locals))) :=
  match fuel with
  | 0 => .error (.unsupported "contract reason dispatch syntax-depth budget exceeded")
  | fuel + 1 => match arms with
    | .nil => .ok
        { formula := .tru
          sound := fun _ _ _ _ _ reason => reason.elim0 }
    | .cons (n := remaining) first rest => do
        let head ← block fuel first locals goals
        let tail ← reasonCases fuel rest locals goals
        return {
            formula := conj head.formula tail.formula
            sound := fun runtime world valid allowed safe (reason : Fin (remaining + 1)) => by
              have parts := (Invarianten.Elim.Korrekt.conj_denote _ _ _).mp valid
              rcases reason with ⟨ordinal, inside⟩
              cases ordinal with
              | zero => exact head.sound runtime world parts.1 allowed safe
              | succ ordinal =>
                  exact tail.sound runtime world parts.2 allowed safe
                    (show Fin remaining from ⟨ordinal, Nat.lt_of_succ_lt_succ inside⟩) }
termination_by fuel

end

end Compiler

end Gabbro.Grammatik.Vertraege.Pruefer
