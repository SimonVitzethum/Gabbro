module

public import Grammatik.Logik.Vertraege.Pruefer.Calls
public import Grammatik.Logik.Vertraege.Pruefer.Leaves
public import Grammatik.Logik.Vertraege.Pruefer.Control.Quantified

@[expose] public section

namespace Gabbro.Grammatik.Vertraege.Pruefer

open Invarianten Invarianten.Frag Invarianten.Elim Invarianten.Elim.Korrekt Invarianten.VC
open Invarianten.Frag.Symbolic Symbolic

variable {D : Deklaration} {V : Vertrag D} {S : SperrInv D} {program : Programm D}

abbrev LoopCompiler (policy : A → CallObligation program) (context : Context A next)
    (code : Block D V l Γ Λ Λ') :=
  ∀ more (larger : next ≤ more) (symbols : SymEnv D Nat Γ), symbols.Bounded more →
    ∀ goals : Symbolic.Goals (program := program) (S := S) (context.weaken larger) V Γ,
      Except Frag.Refusal (Symbolic.BlockCondition policy code symbols goals)

def withHandlers {context : Context A next} (policy : A → CallObligation program)
    {symbols : SymEnv D Nat Γ} {target : Env D Γ → A → Runtime program (fun _ => []) S → World D → Prop}
    (pre : Certificate context (fun valuation item runtime world => ∀ actual,
      symbols.Realizes valuation world actual → target actual item runtime world)) :
    Certificate context (fun valuation item runtime world => ∀ actual,
      symbols.Realizes valuation world actual → ∀ allowed, HandlerSafe (policy item) runtime allowed →
      target actual item runtime world) :=
  pre.map (fun _ _ _ _ ready actual realized _ _ => ready actual realized)

def retryCondition {context : Context A next} (policy : A → CallObligation program)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (test : Expr D Γ Λ .bool) (body : Block D V true Γ Λ Λ) (overflow : Block D V l Γ Λ Λ)
    (compileBody : LoopCompiler (S := S) policy context body)
    (compileOverflow : LoopCompiler (S := S) policy context overflow)
    (count : Nat) (symbols : SymEnv D Nat Γ) (bounded : symbols.Bounded next)
    (goals : Symbolic.Goals (program := program) (S := S) context V Γ) :
    Except Frag.Refusal (Symbolic.StatementCondition policy (.retry count test body overflow) symbols goals) :=
  match count with
  | 0 => do
      let done ← goals.normal.encode next (Nat.le_refl next) symbols bounded
      let exceeded ← compileOverflow next (Nat.le_refl next) symbols bounded goals
      let combined ← Symbolic.branchCondition (context := context) symbols test
        (withHandlers policy done) exceeded
      return combined.map (fun valuation item runtime world ready actual realized allowed safe => by
        have ready := ready actual realized
        cases tested : eval (world.lese Λ test.orte) test (world.lese Λ test.orte) actual <;>
          simp only [tested, wahr?, eq_self, Bool.false_eq_true, ↓reduceIte] at ready <;>
          have ready := ready allowed safe <;>
          simpa only [Runtime.wpS, Runtime.wpB, execStmtH, retryLauf, wahr?, tested,
            Bool.false_eq_true, ↓reduceIte, Symbolic.Goals.holds] using ready)
  | count + 1 => do
      let resume : Continuation (program := program) (S := S) context Γ := {
        holds := fun item runtime world actual => ∀ allowed, HandlerSafe (policy item) runtime allowed →
          runtime.wpS (.retry count test body overflow) (goals.holds item runtime allowed) world actual
        encode := fun more larger locals localBounded =>
          retryCondition policy test body overflow
            (fun last beyond env envBounded target => compileBody last (Nat.le_trans larger beyond) env envBounded target)
            (fun last beyond env envBounded target => compileOverflow last (Nat.le_trans larger beyond) env envBounded target)
            count locals localBounded (goals.weaken larger) }
      let passGoals : Symbolic.Goals (program := program) (S := S) context V Γ :=
        { normal := resume, escape := goals.normal, again := resume, returned := goals.returned, reason := goals.reason }
      let step ← compileBody next (Nat.le_refl next) symbols bounded passGoals
      let done ← goals.normal.encode next (Nat.le_refl next) symbols bounded
      let advanced : Certificate context (fun valuation item runtime world =>
        ∀ actual, symbols.Realizes valuation world actual → ∀ allowed, HandlerSafe (policy item) runtime allowed →
        goals.holds (l := l) item runtime allowed (match execBlockH S runtime.oracle runtime.environment
          runtime.passes runtime.calls body world actual with
          | .ok after env | .next _ after env => retryLauf (V := V) (l := l)
              (execBlockH S runtime.oracle runtime.environment runtime.passes runtime.calls body)
              (fun world env => let read := world.lese Λ test.orte
                (read, wahr? (eval read test read env)))
              (execBlockH S runtime.oracle runtime.environment runtime.passes runtime.calls overflow) count after env
          | .leave _ after env => .ok after env
          | .zurueck after value => .zurueck after value
          | .why after reason => .why after reason
          | .logik error => .logik error
          | .hardware error => .hardware error)) := step.map (fun valuation item runtime world ready actual realized allowed safe => by
        have ready := ready actual realized allowed safe
        unfold Runtime.wpB at ready
        cases result : execBlockH S runtime.oracle runtime.environment runtime.passes runtime.calls body world actual with
        | ok after env =>
            rw [result] at ready
            have continued := ready allowed safe
            simpa only [Runtime.wpS, execStmtH] using continued
        | next h after env =>
            rw [result] at ready
            have continued := ready allowed safe
            simpa only [Runtime.wpS, execStmtH] using continued
        | leave h after env => simpa only [result, Symbolic.Goals.holds, passGoals] using ready
        | zurueck after value => simpa only [result, Symbolic.Goals.holds, passGoals] using ready
        | why after reason => simpa only [result, Symbolic.Goals.holds, passGoals] using ready
        | logik error => simpa only [result, Symbolic.Goals.holds] using ready
        | hardware error => trivial)
      let combined ← Symbolic.branchCondition (context := context) symbols test
        (withHandlers policy done) advanced
      return combined.map (fun valuation item runtime world ready actual realized allowed safe => by
        have ready := ready actual realized
        cases tested : eval (world.lese Λ test.orte) test (world.lese Λ test.orte) actual <;>
          simp only [tested, wahr?, eq_self, Bool.false_eq_true, ↓reduceIte] at ready <;>
          have ready := ready allowed safe <;>
          cases result : execBlockH S runtime.oracle runtime.environment runtime.passes runtime.calls
            body (world.lese Λ test.orte) actual <;>
          simpa only [Runtime.wpS, execStmtH, retryLauf, wahr?, tested, result,
            Bool.false_eq_true, ↓reduceIte, Symbolic.Goals.holds] using ready)
termination_by count

def retryInvariantCondition {context : Context A next} (policy : A → CallObligation program)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (budget count : Nat) (invariant : QF (Observation D))
    (test : Expr D Γ Λ .bool) (body : Block D V true Γ Λ Λ) (overflow : Block D V l Γ Λ Λ)
    (compileBody : LoopCompiler (S := S) policy context body)
    (compileOverflow : LoopCompiler (S := S) policy context overflow)
    (symbols : SymEnv D Nat Γ) (bounded : symbols.Bounded next)
    (goals : Symbolic.Goals (program := program) (S := S) context V Γ) :
    Except Frag.Refusal (Symbolic.StatementCondition policy (.retry count test body overflow) symbols goals) := do
  let passGoals : Symbolic.Goals (program := program) (S := S) context V Γ :=
    { normal := Continuation.ofFormula context invariant
      escape := goals.normal
      again := Continuation.ofFormula context invariant
      returned := goals.returned, reason := goals.reason }
  let checks ← allEnvironments budget Γ
    (fun actual item runtime world => invariant.denote (assignment world) → ∀ allowed,
      HandlerSafe (policy item) runtime allowed →
      let read := world.lese Λ test.orte
      if wahr? (eval read test read actual) = true then goals.normal.holds item runtime read actual
      else runtime.wpB body ((passGoals.weaken (Nat.le_refl next)).holds item runtime allowed) read actual ∧
        runtime.wpB overflow (goals.holds item runtime allowed) read actual)
    (fun more larger locals localBounded => do
      let done ← goals.normal.encode more larger locals localBounded
      let step ← compileBody more larger locals localBounded (passGoals.weaken larger)
      let exceeded ← compileOverflow more larger locals localBounded (goals.weaken larger)
      let advance : Certificate (context.weaken larger) (fun valuation item runtime world => ∀ actual,
          locals.Realizes valuation world actual → ∀ allowed, HandlerSafe (policy item) runtime allowed →
          runtime.wpB body ((passGoals.weaken larger).holds item runtime allowed) world actual ∧
            runtime.wpB overflow ((goals.weaken larger).holds item runtime allowed) world actual) :=
        { formula := .and step.formula exceeded.formula
          sound := fun valuation item present runtime world valid actual realized allowed safe =>
            ⟨step.sound valuation item present runtime world valid.1 actual realized allowed safe,
              exceeded.sound valuation item present runtime world valid.2 actual realized allowed safe⟩ }
      let branch ← Symbolic.branchCondition locals test
        (withHandlers policy done) advance
      return {
        formula := .imp (renameProp Sum.inl (quoteQF invariant)) branch.formula
        sound := fun valuation item present runtime world valid actual realized inv allowed safe => by
          have ready := branch.sound valuation item present runtime world (valid
            ((renameProp_denote Sum.inl (fun _ _ same => Sum.inl.inj same) _ _).mpr
              ((quoteQF_denote invariant (assignment world)).mpr inv))) actual realized
          cases tested : wahr? (eval (world.lese Λ test.orte) test (world.lese Λ test.orte) actual) <;>
            simp only [tested, Bool.false_eq_true, ↓reduceIte] at ready ⊢ <;> exact ready allowed safe })
  return {
    formula := .and (renameProp Sum.inl (quoteQF invariant)) (havocFormula (fun _ => true) checks.formula)
    sound := fun valuation item present runtime world valid actual realized allowed safe => by
      have initial := (quoteQF_denote invariant (assignment world)).mp
        ((renameProp_denote Sum.inl (fun _ _ same => Sum.inl.inj same) _ _).mp valid.1)
      have obligations : ∀ after env, invariant.denote (assignment after) → _ := fun after env inv =>
        checks.sound valuation item present runtime after
          (havocFormula_sound (fun _ => true) checks.formula valuation world after valid.2
            (fun _ impossible => Bool.noConfusion impossible)) env inv
      let I : Nat → World D → Env D Γ → Prop := fun _ after _ => invariant.denote (assignment after)
      let doneTest := fun (after : World D) (env : Env D Γ) =>
        let read := after.lese Λ test.orte
        (read, wahr? (eval read test read env))
      have stepRule : ∀ n after env, I (n + 1) after env → (doneTest after env).2 = false →
          runtime.wpB body (WP.PassSchritt (goals.holds (l := l) item runtime allowed) I n) (doneTest after env).1 env := by
        intro n after env holds unfinished
        have ready := obligations after env holds
        have tested : eval (after.lese Λ test.orte) test (after.lese Λ test.orte) env = false := unfinished
        simp only [tested, wahr?, Bool.false_eq_true, ↓reduceIte] at ready
        have run := (ready allowed safe).1
        unfold Runtime.wpB at run ⊢
        cases result : execBlockH S runtime.oracle runtime.environment runtime.passes runtime.calls body
          (after.lese Λ test.orte) env <;>
          simpa only [result, Symbolic.Goals.holds, WP.PassSchritt, passGoals, Continuation.ofFormula, Symbolic.Goals.weaken, Continuation.weaken, I] using run
      apply WP.retry_regel
        (execBlockH S runtime.oracle runtime.environment runtime.passes runtime.calls body)
        doneTest (execBlockH S runtime.oracle runtime.environment runtime.passes runtime.calls overflow)
        (goals.holds (l := l) item runtime allowed) I ?_ ?_ stepRule count world actual initial
      · intro n after env holds finished
        have ready := obligations after env holds
        have tested : eval (after.lese Λ test.orte) test (after.lese Λ test.orte) env = true := finished
        simp only [tested, wahr?, eq_self, ↓reduceIte] at ready
        simpa only [Symbolic.Goals.holds] using ready allowed safe
      · intro after env holds unfinished
        have ready := obligations after env holds
        have tested : eval (after.lese Λ test.orte) test (after.lese Λ test.orte) env = false := unfinished
        simp only [tested, wahr?, Bool.false_eq_true, ↓reduceIte] at ready
        exact (ready allowed safe).2 }

-- Traversal uses the declaration's actual static index list; local values remain symbolic.
def traverseCondition {context : Context A next} (policy : A → CallObligation program)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (table : D.Tab) (annotation : Expr D Γ Λ .bool)
    (body : Block D V true (.index (D.count table) :: Γ) Λ Λ)
    (compileBody : LoopCompiler (S := S) policy context body)
    (indices : List (Wert D (.index (D.count table)))) (symbols : SymEnv D Nat Γ) (bounded : symbols.Bounded next)
    (goals : Symbolic.Goals (program := program) (S := S) context V Γ) :
    Except Frag.Refusal (Certificate context (fun valuation item (runtime : Runtime program (fun _ => []) S) world =>
      ∀ actual, symbols.Realizes valuation world actual → ∀ allowed, HandlerSafe (policy item) runtime allowed →
      goals.holds (l := l) item runtime allowed (traverseLauf (V := V) (l := l)
        (execBlockH S runtime.oracle runtime.environment runtime.passes runtime.calls body)
        (fun world env => let read := world.lese Λ annotation.orte
          (read, wahr? (eval read annotation read env))) indices world actual))) :=
  let refused : Certificate context (fun valuation _ (_ : Runtime program (fun _ => []) S) (world : World D) =>
      ∀ actual : Env D Γ, symbols.Realizes valuation world actual → False) :=
    { formula := .fls, sound := fun _ _ _ _ _ impossible => False.elim impossible }
  match indices with
  | [] => do
      let done ← goals.normal.encode next (Nat.le_refl next) symbols bounded
      let combined ← Symbolic.branchCondition (context := context) symbols annotation
        (withHandlers policy done)
        (withHandlers policy refused)
      return combined.map (fun valuation item runtime world ready actual realized allowed safe => by
        have ready := ready actual realized
        cases tested : eval (world.lese Λ annotation.orte) annotation (world.lese Λ annotation.orte) actual <;>
          simp only [wahr?, tested, Bool.false_eq_true, ↓reduceIte] at ready
        · exact False.elim (ready allowed safe)
        have ready := ready allowed safe
        simpa only [traverseLauf, wahr?, tested, ↓reduceIte, Symbolic.Goals.holds] using ready)
  | index :: indices => do
      let resume : Continuation (program := program) (S := S) context Γ := {
        holds := fun item runtime world actual => ∀ allowed, HandlerSafe (policy item) runtime allowed →
          goals.holds (l := l) item runtime allowed (traverseLauf (V := V) (l := l)
            (execBlockH S runtime.oracle runtime.environment runtime.passes runtime.calls body)
            (fun world env => let read := world.lese Λ annotation.orte
              (read, wahr? (eval read annotation read env))) indices world actual)
        encode := fun more larger locals localBounded =>
          traverseCondition policy table annotation body
            (fun last beyond env envBounded target => compileBody last (Nat.le_trans larger beyond) env envBounded target)
            indices locals localBounded (goals.weaken larger) }
      let exit : Continuation (program := program) (S := S) context Γ := {
        holds := fun item runtime world actual => ∀ allowed, HandlerSafe (policy item) runtime allowed →
          goals.holds (l := l) item runtime allowed (traverseLauf (V := V) (l := l)
            (execBlockH S runtime.oracle runtime.environment runtime.passes runtime.calls body)
            (fun world env => let read := world.lese Λ annotation.orte
              (read, wahr? (eval read annotation read env))) [] world actual)
        encode := fun more larger locals localBounded =>
          traverseCondition policy table annotation body
            (fun last beyond env envBounded target => compileBody last (Nat.le_trans larger beyond) env envBounded target)
            [] locals localBounded (goals.weaken larger) }
      let passGoals : Symbolic.Goals (program := program) (S := S) context V (.index (D.count table) :: Γ) :=
        { normal := resume.shrink _, escape := exit.shrink _, again := resume.shrink _,
          returned := goals.returned, reason := goals.reason }
      let step ← compileBody next (Nat.le_refl next) (.cons (.known index) symbols) ⟨trivial, bounded⟩ passGoals
      let advanced : Certificate context (fun valuation item runtime world =>
        ∀ actual, symbols.Realizes valuation world actual → ∀ allowed, HandlerSafe (policy item) runtime allowed →
        goals.holds (l := l) item runtime allowed (match execBlockH S runtime.oracle runtime.environment
          runtime.passes runtime.calls body world (.cons index actual) with
          | .ok after env | .next _ after env => traverseLauf (V := V) (l := l)
              (execBlockH S runtime.oracle runtime.environment runtime.passes runtime.calls body)
              (fun world env => let read := world.lese Λ annotation.orte
                (read, wahr? (eval read annotation read env))) indices after env.tail
          | .leave _ after env => traverseLauf (V := V) (l := l)
              (execBlockH S runtime.oracle runtime.environment runtime.passes runtime.calls body)
              (fun world env => let read := world.lese Λ annotation.orte
                (read, wahr? (eval read annotation read env))) [] after env.tail
          | .zurueck after value => .zurueck after value
          | .why after reason => .why after reason
          | .logik error => .logik error
          | .hardware error => .hardware error)) := step.map (fun valuation item runtime world ready actual realized allowed safe => by
        have ready := ready (.cons index actual) ⟨rfl, realized⟩ allowed safe
        unfold Runtime.wpB at ready
        cases result : execBlockH S runtime.oracle runtime.environment runtime.passes runtime.calls body
            world (.cons index actual) with
        | ok after env => rw [result] at ready; exact ready allowed safe
        | next h after env => rw [result] at ready; exact ready allowed safe
        | leave h after env => rw [result] at ready; exact ready allowed safe
        | zurueck after value => simpa only [result, Symbolic.Goals.holds, passGoals] using ready
        | why after reason => simpa only [result, Symbolic.Goals.holds, passGoals] using ready
        | logik error => simpa only [result, Symbolic.Goals.holds] using ready
        | hardware error => trivial)
      let combined ← Symbolic.branchCondition (context := context) symbols annotation advanced
        (withHandlers policy refused)
      return combined.map (fun valuation item runtime world ready actual realized allowed safe => by
        have ready := ready actual realized
        cases tested : eval (world.lese Λ annotation.orte) annotation (world.lese Λ annotation.orte) actual <;>
          simp only [wahr?, tested, Bool.false_eq_true, ↓reduceIte] at ready
        · exact False.elim (ready allowed safe)
        have ready := ready allowed safe
        cases result : execBlockH S runtime.oracle runtime.environment runtime.passes runtime.calls body
            (world.lese Λ annotation.orte) (.cons index actual) with
        | leave h after env =>
            cases finished : eval (after.lese Λ annotation.orte) annotation (after.lese Λ annotation.orte) env.tail <;>
              simpa only [traverseLauf, wahr?, tested, finished, Bool.true_eq_false, Bool.false_eq_true,
                ↓reduceIte, Symbolic.Goals.holds, result] using ready
        | ok after env | next h after env | zurueck after value | why after reason | logik error | hardware error =>
            simpa only [traverseLauf, wahr?, tested, Bool.true_eq_false, ↓reduceIte, Symbolic.Goals.holds, result] using ready)
termination_by indices.length
decreasing_by all_goals simp_wf <;> omega

end Gabbro.Grammatik.Vertraege.Pruefer
