module

public import Grammatik.Logik.Vertraege.Pruefer.Locks
public import Grammatik.Logik.Vertraege.Pruefer.Control.Budget
public import Grammatik.Logik.Vertraege.Pruefer.Indirect.Fallible
public import Grammatik.Logik.Vertraege.Pruefer.Control.Oracle.Block
public import Grammatik.Logik.Vertraege.Pruefer.Control.Oracle.End
public import Grammatik.Logik.Vertraege.Pruefer.Control.Join

@[expose] public section

namespace Gabbro.Grammatik.Vertraege.Pruefer

open Invarianten Invarianten.Frag Invarianten.Elim Invarianten.VC Invarianten.Frag.Symbolic Symbolic

variable {D : Deklaration} {V : Vertrag D} {S : SperrInv D} {program : Programm D}

mutual

def statement {context : Context A next} (policy : CallPolicy program context)
    (facts : ∀ lock, Except Frag.Refusal (LockFormula S lock)) (budget : VCBudget) (hint : Option (QF (Observation D)))
    (fuel : Nat) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (code : Stmt D V l Γ Λ Λ') (symbols : SymEnv D Nat Γ) (bounded : symbols.Bounded next)
    (goals : Symbolic.Goals (program := program) (S := S) context V Γ) :
    Except Frag.Refusal (Symbolic.StatementCondition policy.semantic code symbols goals) :=
  match fuel with
  | 0 => .error (.unsupported "contract VC syntax-depth budget exceeded")
  | fuel + 1 => match code with
    | .ite test yes no => do
        let positive ← block policy facts budget hint fuel yes symbols bounded (goals.joinIf budget.join)
        let negative ← block policy facts budget hint fuel no symbols bounded (goals.joinIf budget.join)
        let pre ← Symbolic.branchCondition symbols test positive negative
        return pre.map (fun valuation item runtime world ready actual realized allowed safe => by
          have ready := ready actual realized
          cases tested : eval (world.lese Λ test.orte) test (world.lese Λ test.orte) actual <;>
            simp only [tested, Bool.false_eq_true, ↓reduceIte] at ready <;>
            have ready := ready allowed safe <;>
            simpa only [Runtime.wpS, Runtime.wpB, execStmtH, wahr?, tested, Bool.false_eq_true, ↓reduceIte, Symbolic.Goals.joinIf_holds] using ready)
    | .onOption (n := count) expression present absent =>
        Symbolic.optionDispatch policy.semantic symbols expression present absent goals
          (fun _ => block policy facts budget hint fuel absent symbols bounded goals)
          (fun index => block policy facts budget hint fuel present (.cons (.known index) symbols) ⟨trivial, bounded⟩
            (goals.shrink (Ty.index count))) bounded
          (fun _ => block (policy.weaken (Nat.le_succ next)) facts budget hint fuel present (.cons (.integer (.var next))
            symbols) ⟨Symbolic.freshKeyBounded next, symbols.bounded_mono bounded (Nat.le_succ next)⟩
            ((goals.weaken (Nat.le_succ next)).shrink (Ty.index count)))
    | .breaking _ body => do
        let pre ← block policy facts budget hint fuel body symbols bounded goals
        return pre.map (fun _ _ _ _ ready actual realized allowed safe => ready actual realized allowed safe)
    | .onWhy expression arms => do
        let pre ← reasonCases policy facts budget hint fuel arms symbols bounded goals
        return ((pre.read Λ expression.orte).map (fun valuation item runtime world ready actual realized allowed safe =>
          ready actual ((symbols.realizes_world actual valuation world (world.lese Λ expression.orte)).mp realized)
            allowed safe (eval (world.lese Λ expression.orte) expression (world.lese Λ expression.orte) actual)))
    | .onTag expression arms => do
        let pre ← tagCases policy facts budget hint fuel arms symbols bounded goals
        return ((pre.read Λ expression.orte).map (fun valuation item runtime world ready actual realized allowed safe =>
          ready actual ((symbols.realizes_world actual valuation world (world.lese Λ expression.orte)).mp realized)
            allowed safe (eval (world.lese Λ expression.orte) expression (world.lese Λ expression.orte) actual)))
    | .retry count test body overflow =>
        if count ≤ budget.expansion then
          retryCondition policy.semantic test body overflow
            (fun more larger env envBounded target => block (policy.weaken larger) facts budget hint fuel body env envBounded target)
            (fun more larger env envBounded target => block (policy.weaken larger) facts budget hint fuel overflow env envBounded target)
            count symbols bounded goals
        else match hint with
          | none => .error (.unsupported "loop exceeds unrolling budget and has no checked hint")
          | some invariant => retryInvariantCondition policy.semantic budget.expansion count invariant test body overflow
              (fun more larger env envBounded target => block (policy.weaken larger) facts budget hint fuel body env envBounded target)
              (fun more larger env envBounded target => block (policy.weaken larger) facts budget hint fuel overflow env envBounded target)
              symbols bounded goals
    | .traverse table annotation body =>
        if (D.count table).toNat ≤ budget.expansion then
          traverseCondition policy.semantic table annotation body
            (fun more larger env envBounded target => block (policy.weaken larger) facts budget hint fuel body env envBounded target)
            (alleIndizes (D.count table)) symbols bounded goals
        else match annotation with
          | .tru => quantifiedTraverseCondition policy.semantic budget.expansion table body
              (fun more larger env envBounded target => block (policy.weaken larger) facts budget hint fuel body env envBounded target)
              symbols goals
          | _ => .error (.unsupported "large traverse needs a checked symbolic invariant")
    | .locks lock rank body => do
        let fact ← facts lock
        let pre ← block policy facts budget hint fuel body symbols bounded (goals.releasing lock fact.formula)
        return lockCondition policy.semantic lock rank body symbols goals fact pre
    | .retScoped expression cleanup => scopedReturnCondition policy.semantic facts expression cleanup symbols bounded goals
    | .retWhyScoped reason cleanup => scopedReasonCondition policy.semantic facts reason cleanup symbols goals
    | .call f args hp hr => do
        let result := fun (actual : Env D Γ) (_ : ErgVal D (D.erg f)) item (runtime : Runtime program (fun _ => []) S) world =>
          goals.normal.holds item runtime world actual
        let pre ← Symbolic.arguments budget.expansion args symbols bounded
          (fun actual supplied item runtime world => ∀ allowed, HandlerSafe (policy.semantic item) runtime allowed →
            match runtime.calls f world supplied with
            | .ok after value => result actual value item runtime after
            | .why _ _ => False
            | .logik error => allowed error
            | .hardware _ => True)
          (fun more larger supplied suppliedBounded => do
            let normal ← goals.normal.encode more larger symbols (symbols.bounded_mono bounded larger)
            callCondition (policy.weaken larger) budget.expansion f
              supplied suppliedBounded symbols (symbols.bounded_mono bounded larger) hr
              (fun actual _ item runtime world => goals.normal.holds item runtime world actual)
              (fun _ beyond _ _ => .ok ((normal.weaken beyond).map
                (fun _ _ _ _ ready actual realized _ _ => ready actual realized)))
              (some (normal.map (fun _ _ _ _ ready actual realized _ => ready actual realized))))
        return (pre.read Λ args.orte).map (fun valuation item runtime world ready actual realized allowed safe => by
          have ready := ready actual ((symbols.realizes_world actual valuation world (world.lese Λ args.orte)).mp realized) allowed safe
          unfold Runtime.wpS
          dsimp only [execStmtH]
          cases reply : runtime.calls f (world.lese Λ args.orte)
            (evalArgs (world.lese Λ args.orte) args (world.lese Λ args.orte) actual) <;>
            simpa only [reply, Symbolic.Goals.holds] using ready)
    | .callInd p args hp hr => callIndCondition policy budget.expansion p args hp hr symbols bounded goals
    | .callIndElse p args he hp hr failure => callIndElseCondition policy budget.expansion p args he hp hr failure
        symbols bounded goals (fun more larger reason => ending (policy.weaken larger) facts budget hint fuel failure
          (.cons (.known reason) symbols) ⟨trivial, symbols.bounded_mono bounded larger⟩ ((goals.weaken larger).shrink _))
    | other => leafCondition policy.semantic other symbols bounded goals
termination_by structural fuel

def block {context : Context A next} (policy : CallPolicy program context)
    (facts : ∀ lock, Except Frag.Refusal (LockFormula S lock)) (budget : VCBudget) (hint : Option (QF (Observation D)))
    (fuel : Nat) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (code : Block D V l Γ Λ Λ') (symbols : SymEnv D Nat Γ) (bounded : symbols.Bounded next)
    (goals : Symbolic.Goals (program := program) (S := S) context V Γ) :
    Except Frag.Refusal (Symbolic.BlockCondition policy.semantic code symbols goals) :=
  match fuel with
  | 0 => .error (.unsupported "contract VC syntax-depth budget exceeded")
  | fuel + 1 => match code with
    | .nil => do
        let pre ← goals.normal.encode next (Nat.le_refl next) symbols bounded
        return pre.map (fun _ _ _ _ ready actual realized _ _ => ready actual realized)
    | .cons first rest => do
        let continuation : Continuation (program := program) (S := S) context Γ := {
          holds := fun item runtime world actual => ∀ allowed, HandlerSafe (policy.semantic item) runtime allowed →
            runtime.wpB rest (goals.holds item runtime allowed) world actual
          encode := fun more larger env envBounded => block (policy.weaken larger) facts budget hint fuel rest env envBounded (goals.weaken larger) }
        let headGoals := { goals with normal := continuation }
        let head ← statement policy facts budget hint fuel first symbols bounded headGoals
        return head.map (fun valuation item runtime world ready actual realized allowed safe => by
          have ready := ready actual realized allowed safe
          unfold Runtime.wpS at ready
          unfold Runtime.wpB
          simp only [execBlockH]
          cases result : execStmtH S runtime.oracle runtime.environment runtime.passes runtime.calls first world actual with
          | ok after env => rw [result] at ready; exact ready allowed safe
          | zurueck after value => simpa only [result, Symbolic.Goals.holds, headGoals] using ready
          | why after reason => simpa only [result, Symbolic.Goals.holds, headGoals] using ready
          | leave h after env => simpa only [result, Symbolic.Goals.holds, headGoals] using ready
          | next h after env => simpa only [result, Symbolic.Goals.holds, headGoals] using ready
          | logik error => simpa only [result, Symbolic.Goals.holds] using ready
          | hardware error => trivial)
    | .bind expression rest =>
        bindBlockCondition (V := V) policy.semantic symbols bounded expression rest goals
          (fun more larger symbol valueBounded => block (policy.weaken larger) facts budget hint fuel rest
            (.cons symbol symbols) ⟨valueBounded, symbols.bounded_mono bounded larger⟩ ((goals.weaken larger).shrink _))
    | .bindCall f args he hp hr rest => bindCallBlockCondition policy budget.expansion f args he hp hr rest symbols bounded goals
        (fun more larger result resultBounded => block (policy.weaken larger) facts budget hint fuel rest
          (.cons (resultSymbol he result) symbols)
          ⟨resultSymbol_bounded he result resultBounded, symbols.bounded_mono bounded larger⟩ ((goals.weaken larger).shrink _))
    | .bindCallElse f args he hp hr failure rest =>
      bindCallElseBlockCondition policy budget.expansion f args he hp hr failure rest symbols bounded goals
        (fun more larger result resultBounded => block (policy.weaken larger) facts budget hint fuel rest
          (.cons (resultSymbol he result) symbols)
          ⟨resultSymbol_bounded he result resultBounded, symbols.bounded_mono bounded larger⟩ ((goals.weaken larger).shrink _))
        (fun more larger reason => ending (policy.weaken larger) facts budget hint fuel failure (.cons (.known reason) symbols)
          ⟨trivial, symbols.bounded_mono bounded larger⟩ ((goals.weaken larger).shrink _))
    | .check test failure rest => do
        let positive ← block policy facts budget hint fuel rest symbols bounded goals
        let negative ← ending policy facts budget hint fuel failure symbols bounded goals
        let pre ← Symbolic.branchCondition (no := fun actual item runtime world => ∀ allowed,
          HandlerSafe (policy.semantic item) runtime allowed →
            runtime.wpE failure (goals.endHolds item runtime allowed) world actual) symbols test positive negative
        return pre.map (fun valuation item runtime world ready actual realized allowed safe => by
          have ready := ready actual realized
          unfold Runtime.wpB
          cases tested : eval (world.lese Λ test.orte) test (world.lese Λ test.orte) actual with
          | true =>
              simp only [execBlockH, wahr?, tested, ↓reduceIte]
              simp only [tested, ↓reduceIte] at ready
              exact ready allowed safe
          | false =>
              simp only [execBlockH, wahr?, tested, Bool.false_eq_true, ↓reduceIte]
              simp only [tested, Bool.false_eq_true, ↓reduceIte] at ready
              have failed := ready allowed safe
              cases outcome : execEndH S runtime.oracle runtime.environment runtime.passes runtime.calls failure (world.lese Λ test.orte) actual <;>
                simpa only [Runtime.wpE, outcome, Symbolic.Goals.holds, Symbolic.Goals.endHolds, EndAusgang.zuAusgang] using failed)
    | .narrow expression low high failure rest => do
        let pre ← Symbolic.narrowingCondition symbols bounded expression low high
          (fun actual value item runtime world => ∀ allowed, HandlerSafe (policy.semantic item) runtime allowed →
            runtime.wpB rest ((goals.shrink _).holds item runtime allowed) world (.cons value actual)) _
          (fun more larger symbol valueBounded => do
            let tail ← block (policy.weaken larger) facts budget hint fuel rest (.cons symbol symbols)
              ⟨valueBounded, symbols.bounded_mono bounded larger⟩ ((goals.weaken larger).shrink _)
            return tail.map (fun _ _ _ _ ready actual realized value selected => ready (.cons value actual) ⟨selected, realized⟩))
          (ending policy facts budget hint fuel failure symbols bounded goals)
        return (pre.read Λ expression.orte).map (fun valuation item runtime world ready actual realized allowed safe => by
          have ready := ready actual ((symbols.realizes_world actual valuation world (world.lese Λ expression.orte)).mp realized)
          unfold Runtime.wpB
          simp only [execBlockH]
          split <;> rename_i fits
          · simp only [dif_pos fits] at ready
            exact (goals.holds_shrink _ item runtime allowed _).mp (ready allowed safe)
          · simp only [dif_neg fits] at ready
            have failed := ready allowed safe
            cases outcome : execEndH S runtime.oracle runtime.environment runtime.passes runtime.calls failure (world.lese Λ expression.orte) actual <;>
              simpa only [Runtime.wpE, outcome, Symbolic.Goals.holds, Symbolic.Goals.endHolds, EndAusgang.zuAusgang] using failed)
    | .narrowRequired expression low high rest => do
        let failed : Certificate context (fun _ _ (_ : Runtime program (fun _ => []) S) (_ : World D) =>
            ∀ _ : Env D Γ, False) := { formula := .fls, sound := fun _ _ _ _ _ impossible => False.elim impossible }
        let pre ← Symbolic.narrowingCondition symbols bounded expression low high
          (fun actual value item runtime world => ∀ allowed, HandlerSafe (policy.semantic item) runtime allowed →
            runtime.wpB rest ((goals.shrink _).holds item runtime allowed) world (.cons value actual)) (fun _ _ _ _ => False)
          (fun more larger symbol valueBounded => do
            let tail ← block (policy.weaken larger) facts budget hint fuel rest (.cons symbol symbols)
              ⟨valueBounded, symbols.bounded_mono bounded larger⟩ ((goals.weaken larger).shrink _)
            return tail.map (fun _ _ _ _ ready actual realized value selected => ready (.cons value actual) ⟨selected, realized⟩))
          (.ok (failed.map (fun _ _ _ _ impossible actual _ => impossible actual)))
        return (pre.read Λ expression.orte).map (fun valuation item runtime world ready actual realized allowed safe => by
          have ready := ready actual ((symbols.realizes_world actual valuation world (world.lese Λ expression.orte)).mp realized)
          unfold Runtime.wpB
          simp only [execBlockH]
          split <;> rename_i fits
          · simp only [dif_pos fits] at ready
            exact (goals.holds_shrink _ item runtime allowed _).mp (ready allowed safe)
          · simp only [dif_neg fits] at ready)
    | .regRead register readable .nil => do
        let pre ← goals.normal.encode next (Nat.le_refl next) symbols bounded
        return {
          formula := pre.formula
          sound := fun valuation item present runtime world valid actual realized allowed _ =>
            registerReadEmpty_sound runtime register readable world actual (goals.holds item runtime allowed)
              (fun after same => pre.sound valuation item present runtime after
                (by rw [symbolic_values_equal valuation after world same]; exact valid)
                actual ((symbols.realizes_world actual valuation world after).mp realized)) (fun _ => trivial) }
    | .bindCallInd p args he hp hr rest => bindCallIndBlockCondition policy budget.expansion p args he hp hr rest symbols bounded goals
        (fun more larger result resultBounded => block (policy.weaken larger) facts budget hint fuel rest
          (.cons (resultSymbol he result) symbols)
          ⟨resultSymbol_bounded he result resultBounded, symbols.bounded_mono bounded larger⟩ ((goals.weaken larger).shrink _))
    | .bindCallIndElse p args he hp hr failure rest =>
      bindCallIndElseBlockCondition policy budget.expansion p args he hp hr failure rest symbols bounded goals
        (fun more larger result resultBounded => block (policy.weaken larger) facts budget hint fuel rest
          (.cons (resultSymbol he result) symbols)
          ⟨resultSymbol_bounded he result resultBounded, symbols.bounded_mono bounded larger⟩ ((goals.weaken larger).shrink _))
        (fun more larger reason => ending (policy.weaken larger) facts budget hint fuel failure (.cons (.known reason) symbols)
          ⟨trivial, symbols.bounded_mono bounded larger⟩ ((goals.weaken larger).shrink _))
    | .bindAxiom a args he hw hg hd hgd rest => bindAxiomBlockCondition policy.semantic budget.expansion a args he hw hg hd hgd rest symbols bounded goals
        (fun more larger env envBounded => block (policy.weaken larger) facts budget hint fuel rest env envBounded ((goals.weaken larger).shrinkResult (some _)))
    | .bindAxiomElse a args he hr hw hg hd hgd failure rest => bindAxiomElseBlockCondition policy.semantic budget.expansion a args he hr hw hg hd hgd failure rest symbols bounded goals
        (fun more larger env envBounded => block (policy.weaken larger) facts budget hint fuel rest env envBounded ((goals.weaken larger).shrinkResult (some _)))
        (fun more larger env envBounded => ending (policy.weaken larger) facts budget hint fuel failure env envBounded
          ((goals.weaken larger).shrinkResult (some (.why (D.agruende a)))))
    | .bindAxiomOpt result a args he hp hd hgd rest => bindAxiomOptBlockCondition policy.semantic budget.expansion result a args he hp hd hgd rest symbols bounded goals
        (fun more larger env envBounded => block (policy.weaken larger) facts budget hint fuel rest env envBounded ((goals.weaken larger).shrinkResult result))
    | .bindAxiomOptElse result a args he hp hd hgd hr failure rest => bindAxiomOptElseBlockCondition policy.semantic budget.expansion result a args he hp hd hgd hr failure rest symbols bounded goals
        (fun more larger env envBounded => block (policy.weaken larger) facts budget hint fuel rest env envBounded ((goals.weaken larger).shrinkResult result))
        (fun more larger env envBounded => ending (policy.weaken larger) facts budget hint fuel failure env envBounded
          ((goals.weaken larger).shrinkResult (some (.why (D.agruende a)))))
    | .regRead .. | .regReadElse .. => .error (.unsupported "contract register binding needs a typed fresh result observation")
    | .awaits .. | .exchange .. => .error (.unsupported "contract atomic binding needs rely-aware fresh observations")
    | .floatNarrow expression low high failure rest => do
        let success ← block policy facts budget hint fuel rest (.cons .unobserved symbols)
          ⟨trivial, bounded⟩ (goals.shrink (.fl low high))
        let failed ← ending policy facts budget hint fuel failure symbols bounded goals
        return {
          formula := .and success.formula failed.formula
          sound := fun valuation item present runtime world valid actual realized allowed safe => by
            let read := world.lese Λ expression.orte
            have locals := (symbols.realizes_world actual valuation world read).mp realized
            have positive := (success.read Λ expression.orte).sound valuation item present runtime world valid.1
            have negative := (failed.read Λ expression.orte).sound valuation item present runtime world valid.2
            unfold Runtime.wpB
            simp only [execBlockH, ← show read = world.lese Λ expression.orte from rfl]
            cases gleitPasst low high (eval read expression read actual).x with
            | some value =>
              exact (goals.holds_shrink _ item runtime allowed _).mp
                (positive (.cons value actual) ⟨trivial, locals⟩ allowed safe)
            | none =>
              have fails := negative actual locals allowed safe
              unfold Runtime.wpE at fails
              cases outcome : execEndH S runtime.oracle runtime.environment runtime.passes runtime.calls failure read actual <;>
                simpa only [outcome, Symbolic.Goals.holds, Symbolic.Goals.endHolds, EndAusgang.zuAusgang] using fails }
    | .float .. | .floatLit .. | .floatOf .. => .error (.unsupported "contract floating binding needs an exact typed range-check certificate")
termination_by structural fuel
def ending {context : Context A next} (policy : CallPolicy program context)
    (facts : ∀ lock, Except Frag.Refusal (LockFormula S lock)) (budget : VCBudget) (hint : Option (QF (Observation D)))
    (fuel : Nat) {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (code : Endblock D V l Γ Λ) (symbols : SymEnv D Nat Γ) (bounded : symbols.Bounded next)
    (goals : Symbolic.Goals (program := program) (S := S) context V Γ) :
    Except Frag.Refusal (Symbolic.EndCondition policy.semantic code symbols goals) :=
  match fuel with
  | 0 => .error (.unsupported "contract VC syntax-depth budget exceeded")
  | fuel + 1 => match code with
    | .ret expression inventory => retEndCondition (V := V) (l := l) policy.semantic symbols bounded expression inventory goals
    | .retWhy _ _ => do
        let pre ← goals.reason.encode next (Nat.le_refl next) .nil trivial
        return pre.map (fun _ _ _ _ ready _ _ _ _ => ready .nil trivial)
    | .leave _ => do
        let pre ← goals.escape.encode next (Nat.le_refl next) symbols bounded
        return pre.map (fun _ _ _ _ ready actual realized _ _ => ready actual realized)
    | .next _ => do
        let pre ← goals.again.encode next (Nat.le_refl next) symbols bounded
        return pre.map (fun _ _ _ _ ready actual realized _ _ => ready actual realized)
    | .cons first rest => do
        let continuation : Continuation (program := program) (S := S) context Γ := {
          holds := fun item runtime world actual => ∀ allowed, HandlerSafe (policy.semantic item) runtime allowed →
            runtime.wpE rest (goals.endHolds item runtime allowed) world actual
          encode := fun more larger env envBounded => ending (policy.weaken larger) facts budget hint fuel rest env envBounded (goals.weaken larger) }
        let headGoals := { goals with normal := continuation }
        let head ← statement policy facts budget hint fuel first symbols bounded headGoals
        return head.map (fun valuation item runtime world ready actual realized allowed safe => by
          have ready := ready actual realized allowed safe
          unfold Runtime.wpS at ready
          unfold Runtime.wpE
          simp only [execEndH]
          cases result : execStmtH S runtime.oracle runtime.environment runtime.passes runtime.calls first world actual with
          | ok after env => rw [result] at ready; exact ready allowed safe
          | zurueck after value => simpa only [result, Symbolic.Goals.holds, Symbolic.Goals.endHolds, headGoals] using ready
          | why after reason => simpa only [result, Symbolic.Goals.holds, Symbolic.Goals.endHolds, headGoals] using ready
          | leave h after env => simpa only [result, Symbolic.Goals.holds, Symbolic.Goals.endHolds, headGoals] using ready
          | next h after env => simpa only [result, Symbolic.Goals.holds, Symbolic.Goals.endHolds, headGoals] using ready
          | logik error => simpa only [result, Symbolic.Goals.holds, Symbolic.Goals.endHolds] using ready
          | hardware error => trivial)
    | .ite test yes no => do
        let positive ← ending policy facts budget hint fuel yes symbols bounded goals
        let negative ← ending policy facts budget hint fuel no symbols bounded goals
        let pre ← Symbolic.branchCondition symbols test positive negative
        return pre.map (fun valuation item runtime world ready actual realized allowed safe => by
          have ready := ready actual realized
          cases tested : eval (world.lese Λ test.orte) test (world.lese Λ test.orte) actual <;>
            simp only [tested, Bool.false_eq_true, ↓reduceIte] at ready <;>
            have ready := ready allowed safe <;>
            simpa only [Runtime.wpE, execEndH, wahr?, tested, Bool.false_eq_true, ↓reduceIte] using ready)
    | .bind expression rest => bindEndCondition (V := V) (l := l) policy.semantic symbols bounded expression rest goals
        (fun more larger symbol valueBounded => ending (policy.weaken larger) facts budget hint fuel rest
          (.cons symbol symbols) ⟨valueBounded, symbols.bounded_mono bounded larger⟩ ((goals.weaken larger).shrink _))
    | .bindCall f args he hp hr rest => bindCallEndCondition policy budget.expansion f args he hp hr rest symbols bounded goals
        (fun more larger result resultBounded => ending (policy.weaken larger) facts budget hint fuel rest
          (.cons (resultSymbol he result) symbols)
          ⟨resultSymbol_bounded he result resultBounded, symbols.bounded_mono bounded larger⟩ ((goals.weaken larger).shrink _))
    | .bindCallElse f args he hp hr failure rest =>
      bindCallElseEndCondition policy budget.expansion f args he hp hr failure rest symbols bounded goals
        (fun more larger result resultBounded => ending (policy.weaken larger) facts budget hint fuel rest
          (.cons (resultSymbol he result) symbols)
          ⟨resultSymbol_bounded he result resultBounded, symbols.bounded_mono bounded larger⟩ ((goals.weaken larger).shrink _))
        (fun more larger reason => ending (policy.weaken larger) facts budget hint fuel failure (.cons (.known reason) symbols)
          ⟨trivial, symbols.bounded_mono bounded larger⟩ ((goals.weaken larger).shrink _))
    | .narrow expression low high failure rest => do
        let pre ← Symbolic.narrowingCondition symbols bounded expression low high
          (fun actual value item runtime world => ∀ allowed, HandlerSafe (policy.semantic item) runtime allowed →
            runtime.wpE rest ((goals.shrink _).endHolds item runtime allowed) world (.cons value actual)) _
          (fun more larger symbol valueBounded => do
            let tail ← ending (policy.weaken larger) facts budget hint fuel rest (.cons symbol symbols)
              ⟨valueBounded, symbols.bounded_mono bounded larger⟩ ((goals.weaken larger).shrink _)
            return tail.map (fun _ _ _ _ ready actual realized value selected => ready (.cons value actual) ⟨selected, realized⟩))
          (ending policy facts budget hint fuel failure symbols bounded goals)
        return (pre.read Λ expression.orte).map (fun valuation item runtime world ready actual realized allowed safe => by
          have ready := ready actual ((symbols.realizes_world actual valuation world (world.lese Λ expression.orte)).mp realized)
          unfold Runtime.wpE
          simp only [execEndH]
          split <;> rename_i fits
          · simp only [dif_pos fits] at ready
            exact (goals.endHolds_shrink _ item runtime allowed _).mp (ready allowed safe)
          · simp only [dif_neg fits] at ready
            exact ready allowed safe)
    | .narrowRequired expression low high rest => do
        let failed : Certificate context (fun _ _ (_ : Runtime program (fun _ => []) S) (_ : World D) =>
            ∀ _ : Env D Γ, False) := { formula := .fls, sound := fun _ _ _ _ _ impossible => False.elim impossible }
        let pre ← Symbolic.narrowingCondition symbols bounded expression low high
          (fun actual value item runtime world => ∀ allowed, HandlerSafe (policy.semantic item) runtime allowed →
            runtime.wpE rest ((goals.shrink _).endHolds item runtime allowed) world (.cons value actual)) (fun _ _ _ _ => False)
          (fun more larger symbol valueBounded => do
            let tail ← ending (policy.weaken larger) facts budget hint fuel rest (.cons symbol symbols)
              ⟨valueBounded, symbols.bounded_mono bounded larger⟩ ((goals.weaken larger).shrink _)
            return tail.map (fun _ _ _ _ ready actual realized value selected => ready (.cons value actual) ⟨selected, realized⟩))
          (.ok (failed.map (fun _ _ _ _ impossible actual _ => impossible actual)))
        return (pre.read Λ expression.orte).map (fun valuation item runtime world ready actual realized allowed safe => by
          have ready := ready actual ((symbols.realizes_world actual valuation world (world.lese Λ expression.orte)).mp realized)
          unfold Runtime.wpE
          simp only [execEndH]
          split <;> rename_i fits
          · simp only [dif_pos fits] at ready
            exact (goals.endHolds_shrink _ item runtime allowed _).mp (ready allowed safe)
          · simp only [dif_neg fits] at ready)
    | .retScoped expression cleanup => do
        let pre ← scopedReturnCondition (V := V) (l := l) policy.semantic facts expression cleanup symbols bounded goals
        return pre.map (fun valuation item runtime world ready actual realized allowed safe => by
          have ready := ready actual realized allowed safe
          unfold Runtime.wpS at ready
          unfold Runtime.wpE
          simp only [execStmtH, execEndH] at ready ⊢
          split <;> rename_i cleanupReady <;>
            simpa only [cleanupReady, Bool.false_eq_true, ↓reduceIte, Symbolic.Goals.holds, Symbolic.Goals.endHolds] using ready)
    | .retWhyScoped reason cleanup => do
        let pre ← scopedReasonCondition (V := V) (l := l) policy.semantic facts reason cleanup symbols goals
        return pre.map (fun valuation item runtime world ready actual realized allowed safe => by
          have ready := ready actual realized allowed safe
          unfold Runtime.wpS at ready
          unfold Runtime.wpE
          simp only [execStmtH, execEndH] at ready ⊢
          split <;> rename_i cleanupReady <;>
            simpa only [cleanupReady, Bool.false_eq_true, ↓reduceIte, Symbolic.Goals.holds, Symbolic.Goals.endHolds] using ready)
    | .bindCallInd p args he hp hr rest => bindCallIndEndCondition policy budget.expansion p args he hp hr rest symbols bounded goals
        (fun more larger result resultBounded => ending (policy.weaken larger) facts budget hint fuel rest
          (.cons (resultSymbol he result) symbols)
          ⟨resultSymbol_bounded he result resultBounded, symbols.bounded_mono bounded larger⟩ ((goals.weaken larger).shrink _))
    | .bindCallIndElse p args he hp hr failure rest =>
      bindCallIndElseEndCondition policy budget.expansion p args he hp hr failure rest symbols bounded goals
        (fun more larger result resultBounded => ending (policy.weaken larger) facts budget hint fuel rest
          (.cons (resultSymbol he result) symbols)
          ⟨resultSymbol_bounded he result resultBounded, symbols.bounded_mono bounded larger⟩ ((goals.weaken larger).shrink _))
        (fun more larger reason => ending (policy.weaken larger) facts budget hint fuel failure (.cons (.known reason) symbols)
          ⟨trivial, symbols.bounded_mono bounded larger⟩ ((goals.weaken larger).shrink _))
    | .bindAxiom a args he hw hg hd hgd rest => bindAxiomEndCondition policy.semantic budget.expansion a args he hw hg hd hgd rest symbols bounded goals
        (fun more larger env envBounded => ending (policy.weaken larger) facts budget hint fuel rest env envBounded ((goals.weaken larger).shrinkResult (some _)))
    | .bindAxiomElse a args he hr hw hg hd hgd failure rest => bindAxiomElseEndCondition policy.semantic budget.expansion a args he hr hw hg hd hgd failure rest symbols bounded goals
        (fun more larger env envBounded => ending (policy.weaken larger) facts budget hint fuel rest env envBounded ((goals.weaken larger).shrinkResult (some _)))
        (fun more larger env envBounded => ending (policy.weaken larger) facts budget hint fuel failure env envBounded
          ((goals.weaken larger).shrinkResult (some (.why (D.agruende a)))))
    | .bindAxiomOpt result a args he hp hd hgd rest => bindAxiomOptEndCondition policy.semantic budget.expansion result a args he hp hd hgd rest symbols bounded goals
        (fun more larger env envBounded => ending (policy.weaken larger) facts budget hint fuel rest env envBounded ((goals.weaken larger).shrinkResult result))
    | .bindAxiomOptElse result a args he hp hd hgd hr failure rest => bindAxiomOptElseEndCondition policy.semantic budget.expansion result a args he hp hd hgd hr failure rest symbols bounded goals
        (fun more larger env envBounded => ending (policy.weaken larger) facts budget hint fuel rest env envBounded ((goals.weaken larger).shrinkResult result))
        (fun more larger env envBounded => ending (policy.weaken larger) facts budget hint fuel failure env envBounded
          ((goals.weaken larger).shrinkResult (some (.why (D.agruende a)))))
    | .regRead .. | .regReadElse .. => .error (.unsupported "contract register end binding needs a typed fresh result observation")
    | .awaits .. | .exchange .. => .error (.unsupported "contract atomic end binding needs rely-aware fresh observations")
    | .floatNarrow expression low high failure rest => do
        let success ← ending policy facts budget hint fuel rest (.cons .unobserved symbols)
          ⟨trivial, bounded⟩ (goals.shrink (.fl low high))
        let failed ← ending policy facts budget hint fuel failure symbols bounded goals
        return {
          formula := .and success.formula failed.formula
          sound := fun valuation item present runtime world valid actual realized allowed safe => by
            let read := world.lese Λ expression.orte
            have locals := (symbols.realizes_world actual valuation world read).mp realized
            have positive := (success.read Λ expression.orte).sound valuation item present runtime world valid.1
            have negative := (failed.read Λ expression.orte).sound valuation item present runtime world valid.2
            unfold Runtime.wpE
            simp only [execEndH, ← show read = world.lese Λ expression.orte from rfl]
            cases gleitPasst low high (eval read expression read actual).x with
            | some value =>
              exact (goals.endHolds_shrink _ item runtime allowed _).mp
                (positive (.cons value actual) ⟨trivial, locals⟩ allowed safe)
            | none => exact negative actual locals allowed safe }
    | .float .. | .floatLit .. | .floatOf .. => .error (.unsupported "contract floating end binding needs an exact typed range-check certificate")
termination_by structural fuel

def reasonCases {context : Context A next} (policy : CallPolicy program context)
    (facts : ∀ lock, Except Frag.Refusal (LockFormula S lock)) (budget : VCBudget) (hint : Option (QF (Observation D)))
    (fuel : Nat) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {count : Nat}
    (arms : GrundArms D V l Γ Λ Λ' count) (symbols : SymEnv D Nat Γ) (bounded : symbols.Bounded next)
    (goals : Symbolic.Goals (program := program) (S := S) context V Γ) :
    Except Frag.Refusal (Certificate context (fun valuation item (runtime : Runtime program (fun _ => []) S) world =>
      ∀ actual, symbols.Realizes valuation world actual → ∀ allowed, HandlerSafe (policy.semantic item) runtime allowed →
      ∀ reason : Fin count, goals.holds (l := l) item runtime allowed
        (execGrundH S runtime.oracle runtime.environment runtime.passes runtime.calls arms reason world actual))) :=
  match fuel with
  | 0 => .error (.unsupported "contract reason dispatch syntax-depth budget exceeded")
  | fuel + 1 => match arms with
    | .nil => .ok { formula := .tru, sound := fun _ _ _ _ _ _ _ _ _ _ reason => reason.elim0 }
    | .cons (n := remaining) first rest => do
        let head ← block policy facts budget hint fuel first symbols bounded goals
        let tail ← reasonCases policy facts budget hint fuel rest symbols bounded goals
        return {
          formula := .and head.formula tail.formula
          sound := fun valuation item present runtime world valid actual realized allowed safe (reason : Fin (remaining + 1)) => by
            cases reason with
            | mk ordinal inside => cases ordinal with
              | zero => exact head.sound valuation item present runtime world valid.1 actual realized allowed safe
              | succ ordinal =>
                  exact tail.sound valuation item present runtime world valid.2 actual realized allowed safe
                    (show Fin remaining from ⟨ordinal, Nat.lt_of_succ_lt_succ inside⟩) }
termination_by structural fuel

def tagCases {context : Context A next} (policy : CallPolicy program context)
    (facts : ∀ lock, Except Frag.Refusal (LockFormula S lock)) (budget : VCBudget) (hint : Option (QF (Observation D)))
    (fuel : Nat) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option Ty)}
    (arms : Arms D V l Γ Λ Λ' cs) (symbols : SymEnv D Nat Γ) (bounded : symbols.Bounded next)
    (goals : Symbolic.Goals (program := program) (S := S) context V Γ) :
    Except Frag.Refusal (Certificate context (Symbolic.TagTarget policy.semantic arms symbols goals)) :=
  match fuel with
  | 0 => .error (.unsupported "contract tagged dispatch syntax-depth budget exceeded")
  | fuel + 1 => match cs, arms with
    | [], .nil => .ok (Symbolic.tagNil policy.semantic symbols goals)
    | none :: _, .cons first rest => do
        let head ← block policy facts budget hint fuel first symbols bounded goals
        let tail ← tagCases policy facts budget hint fuel rest symbols bounded goals
        return Symbolic.tagNone policy.semantic symbols goals head tail
    | some τ :: _, .cons first rest => do
        let tail ← tagCases policy facts budget hint fuel rest symbols bounded goals
        Symbolic.tagSomeDispatch policy.semantic symbols goals budget.expansion tail
          (fun payload => block policy facts budget hint fuel first (.cons (.known payload) symbols) ⟨trivial, bounded⟩ (goals.shrink τ))
          (fun _ => block policy facts budget hint fuel first (.cons .unobserved symbols) ⟨trivial, bounded⟩ (goals.shrink τ))
termination_by structural fuel

end

end Gabbro.Grammatik.Vertraege.Pruefer
