module

public import Grammatik.Logik.Vertraege.Pruefer.Compiler

@[expose] public section

namespace Gabbro.Grammatik.Vertraege.Pruefer

open Invarianten Invarianten.Frag Invarianten.Elim Invarianten.Elim.Korrekt Invarianten.VC
open Invarianten.Pruefer

variable {D : Deklaration} {S : SperrInv D} {program : Programm D}

/-- Obligations at all exits, preserving inherited errors explicitly. -/
def EndPost (program : Programm D) (f : D.Fn) (old : World D)
    (locals : Env D (D.params f)) (allowed : Logik D → Prop) :
    EndAusgang (vertragVon D f) false (D.params f) → Prop
  | .zurueck next value => EnsAmRueck program f old next locals value ∧ InvAmRueck program f next
  | .why next _ => InvAmRueck program f next
  | .leave _ _ _ | .next _ _ _ => False
  | .logik error => allowed error
  | .hardware _ => True

/-- One concrete parameter environment, shared by contract and measure checks. -/
def CheckedEnvironment (policy : CallPolicy program) (f : D.Fn)
    (locals : Env D (D.params f)) : Prop :=
  ∀ (runtime : Runtime program (fun _ => []) S) world allowed,
    HandlerSafe policy runtime allowed → ReqAmEintritt program f world locals →
      runtime.wpE (program.rumpf f) (EndPost program f world locals allowed) world locals

/-- This semantic certificate is OUTPUT of VC checking, never a checker input. -/

def CheckedExecution (policy : CallPolicy program) (f : D.Fn) : Prop :=
  ∀ (locals : Env D (D.params f)) (runtime : Runtime program (fun _ => []) S)
    world allowed, HandlerSafe policy runtime allowed → ReqAmEintritt program f world locals →
      runtime.wpE (program.rumpf f) (EndPost program f world locals allowed) world locals

/-- A refusal includes the values of the failed arithmetic VC in free-key
    order. The typed-world reconstruction API remains available in P20. -/
def invalidMessage (label : String) (formula : LProp (Observation D))
    (pre : QF (Observation D)) : String :=
  let matrix := writerMatrix formula .tru pre
  let names := (qfKeys matrix).eraseDups
  match Modell.counterexample names (quoteQF matrix) with
  | none => label ++ ": false VC (no counterexample extracted)"
  | some values => label ++ ": false VC; counterexample in observation order = " ++
      reprStr (names.map values)

/-- Diagnostics retain the concrete decoded arguments selected by the VC
    generator, including when the arithmetic counterexample has no memory keys. -/
def environmentValues : {context : Ctx} → Env D context → List Int
  | [], .nil => []
  | .int _ _ :: _, .cons value rest => value.n :: environmentValues rest
  | .bool :: _, .cons value rest => (if wahr? value = true then 1 else 0) :: environmentValues rest
  | τ :: _, .cons value rest => scalarValue τ value :: environmentValues rest

/-- The return formula conjoins checked ensures with all owed invariants. -/
def contractGoals (program : Programm D) (f : D.Fn) (locals : Env D (D.params f))
    (invariants : InvariantFormula program (D.invs.filter (schuldet f))) :
    Goals D (vertragVon D f) (D.params f) where
  normal := fun _ => .ok .tru
  escape := fun _ => .ok .tru
  again := fun _ => .ok .tru
  returned := fun value => (postFormula program f locals value).map (fun post => conj post.val invariants.formula)
  reason := invariants.formula

theorem contractGoals_sound (program : Programm D) (f : D.Fn) (locals : Env D (D.params f))
    (invariants : InvariantFormula program (D.invs.filter (schuldet f)))
    (old : World D) (allowed : Logik D → Prop) (outcome : EndAusgang (vertragVon D f) false (D.params f))
    (valid : (contractGoals program f locals invariants).endHolds allowed outcome) :
    EndPost program f old locals allowed outcome := by
  cases outcome with
  | zurueck next value =>
      cases result : postFormula program f locals value with
      | error cause => simp only [Goals.endHolds, contractGoals, result, Except.map, denotes] at valid
      | ok post =>
          have parts : post.val.denote (assignment next) ∧ invariants.formula.denote (assignment next) := by
            simpa only [Goals.endHolds, contractGoals, result, Except.map, denotes, conj_denote] using valid
          exact ⟨(post.property old next).mp parts.1, fun item member owed =>
            (invariants.correct next).mp parts.2 item (List.mem_filter.mpr ⟨member, owed⟩)⟩
  | why next reason =>
      exact fun item member owed =>
        (invariants.correct next).mp valid item (List.mem_filter.mpr ⟨member, owed⟩)
  | leave h _ _ => cases h
  | next h _ _ => cases h
  | logik error => exact valid
  | hardware error => trivial

/-- Name the dependent post-translation match once so proof certificates and
    the executable gate share the same matcher constant. This checks syntax
    only; postcondition truth is still decided by the unchanged closed VC. -/
def checkPostFormula (program : Programm D) (f : D.Fn) (locals : Env D (D.params f))
    (value : ErgVal D (D.erg f)) :
    Except Frag.Refusal (PLift (∃ post, postFormula program f locals value = .ok post)) :=
  match postFormula program f locals value with
  | .error cause => .error cause
  | .ok post => .ok ⟨⟨post, rfl⟩⟩

/-- Type facts, the caller requires and its accumulated WP form the closed
    arithmetic VC. No semantic truth proof is submitted to this procedure. -/
def checkEnvironment (program : Programm D) (S : SperrInv D) (policy : CallPolicy program)
    (sources : LockSources S) (budget : VCBudget) (hint : Option (QF (Observation D)))
    (f : D.Fn) (invariants : InvariantFormula program (D.invs.filter (schuldet f)))
    (locals : Env D (D.params f)) :
    Except Frag.Refusal (PLift (∀ (runtime : Runtime program (fun _ => []) S) world allowed,
      HandlerSafe policy runtime allowed → ReqAmEintritt program f world locals →
      runtime.wpE (program.rumpf f) (EndPost program f world locals allowed) world locals)) := do
  let requires ← translate (program.requires f) locals
  let domain ← results (D := D) budget.expansion (D.erg f)
  let _ ← collect domain.values
    (fun value => ∃ post, postFormula program f locals value = .ok post)
    (checkPostFormula program f locals)
  let compiled ← ending policy (lockFormula S sources) budget hint budget.depth
    (program.rumpf f) locals (contractGoals program f locals invariants)
  if accepted : decideB (close (writerMatrix requires.payload .tru compiled.formula)) (close_closed (writerMatrix requires.payload .tru compiled.formula)) = true then
    return ⟨fun runtime world allowed safe entry => by
      have closed := (lower_denote _ (assignment world)).mp
        (close_sound _ accepted (assignment world))
      have implication := (lower_denote _ (assignment world)).mp
        ((quoteQF_denote _ _).mp (closed (typeFacts_sound _ world)))
      have ready := (quoteQF_denote _ _).mp (implication ⟨(requires.bool_iff world).mp entry, trivial⟩)
      have outcome := compiled.sound runtime world ready allowed safe
      exact contractGoals_sound program f locals invariants world allowed _ outcome⟩
  -- A sufficient WP can contain call havoc and other overapproximations.
  -- Falsity of that WP is not evidence of a source execution violating its
  -- contract. Only the direct implication checker reports counterexamples.
  else .error (.unsupported ("contract VC abstraction cannot establish the postcondition or a call obligation" ++
    "; parameters = " ++ reprStr (environmentValues locals)))

/-- Check every decoded parameter environment in a complete budgeted domain. -/
def checkExecution (program : Programm D) (S : SperrInv D) (policy : CallPolicy program)
    (sources : LockSources S) (budget : VCBudget) (hint : Option (QF (Observation D))) (f : D.Fn) :
    Except Frag.Refusal (PLift (CheckedExecution (S := S) policy f)) := do
  let invariants ← invariantFormula program (D.invs.filter (schuldet f))
  let domain ← environments (D := D) budget.expansion (D.params f)
  if argumentSpecializations budget.specializations (D.params f) *
      endSpecializations budget.specializations (program.rumpf f) > budget.specializations then
    .error (.unsupported "contract VC specialization product exceeds the work budget")
  else pure ()
  let checked ← collect domain.values
    (fun locals => ∀ (runtime : Runtime program (fun _ => []) S) world allowed,
      HandlerSafe policy runtime allowed → ReqAmEintritt program f world locals →
      runtime.wpE (program.rumpf f) (EndPost program f world locals allowed) world locals)
    (checkEnvironment program S policy sources budget hint f invariants)
  return ⟨fun locals => checked.down locals (domain.complete locals)⟩

end Gabbro.Grammatik.Vertraege.Pruefer
