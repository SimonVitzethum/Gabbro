module

public import Grammatik.Logik.Vertraege.Pruefer.Control.Arguments
public import Grammatik.Logik.Vertraege.Pruefer.Control.Results
public import Grammatik.Logik.Vertraege.Pruefer.Control.Snapshots

@[expose] public section

namespace Gabbro.Grammatik.Vertraege.Pruefer

open Invarianten Invarianten.Frag Invarianten.Elim Invarianten.Elim.Korrekt Invarianten.VC
open Invarianten.Frag.Symbolic Symbolic

variable {D : Deklaration} {S : SperrInv D} {program : Programm D}

/-- The call rule quantifies normal answers and written observations. Immutable
    arguments and caller locals retain their original realizing valuation. -/
def callOutcomesAt {context : Context A next} (policy : CallPolicy program context)
    (budget : Nat) (f : D.Fn) (args : SymEnv D Nat (D.params f)) (argsBounded : args.Bounded next)
    (caller : SymEnv D Nat Γ) (callerBounded : caller.Bounded next)
    (snapshot : Option (Snapshot.Region D next))
    (target : Env D Γ → ErgVal D (D.erg f) → A → Runtime program (fun _ => []) S → World D → Prop)
    (failure : Env D Γ → Fin (D.gruende f) → A → Runtime program (fun _ => []) S → World D → Prop)
    (compile : ResultCompiler context caller (D.erg f) target)
    (compileFailure : ∀ reason, Except Frag.Refusal (Certificate context (fun valuation item runtime world =>
      ∀ actual, caller.Realizes valuation world actual → failure actual reason item runtime world)))
    (shared : Option (SharedResult context caller (D.erg f) target) := none) :
    Except Frag.Refusal (Certificate context (fun valuation item runtime world => ∀ actual,
      caller.Realizes valuation world actual → ∀ supplied, args.Realizes valuation world supplied →
      Snapshot.Realizes (Snapshot.regionStart snapshot) (Snapshot.regionNames snapshot) valuation world →
      ∀ allowed, HandlerSafe (policy.semantic item) runtime allowed →
      match runtime.calls f world supplied with
      | .ok after value => target actual value item runtime after
      | .why after reason => failure actual reason item runtime after
      | .logik error => allowed error
      | .hardware _ => True)) := do
  let pre ← policy.encode next (Nat.le_refl next) f args argsBounded
  let normal ← resultCondition args argsBounded caller callerBounded budget (D.erg f)
    (program.ensures f) target compile shared snapshot
  let failures ← allCertificates context (List.finRange (D.gruende f))
    (fun reason valuation item runtime world => ∀ actual, caller.Realizes valuation world actual →
      ∀ after, failure actual reason item runtime after)
    (fun reason => do
      let tail ← compileFailure reason
      return {
        formula := havocFormula (fun _ => true) tail.formula
        sound := fun valuation item present runtime world valid actual realized after =>
          tail.sound valuation item present runtime after
            (havocFormula_sound (fun _ => true) tail.formula valuation world after valid
              (fun _ impossible => Bool.noConfusion impossible)) actual
            ((caller.realizes_world actual valuation world after).mp realized) })
  return {
    formula := .and pre.val (.and (havocFormula (writtenObservation f) normal.formula) failures.formula)
    sound := fun valuation item present runtime world valid actual realized supplied suppliedRealized frozen allowed safe => by
      have obligation := (pre.property valuation item present world supplied suppliedRealized).mp valid.1
      have required := (policy.semantic item).requires f world supplied obligation
      cases reply : runtime.calls f world supplied with
      | ok after value =>
          have transferred := havocFormula_sound (writtenObservation f) normal.formula valuation world after valid.2.1
            (fun key unchanged => frame_observation f world after (runtime.evidence.frame f world supplied after value reply) key unchanged)
          exact normal.sound valuation item present runtime after transferred world supplied suppliedRealized frozen
            actual ((caller.realizes_world actual valuation world after).mp realized) value
            (safe.1.1 f world supplied required after value reply)
      | why after reason =>
          exact failures.sound valuation item present runtime world valid.2.2 reason
            (List.mem_finRange reason) actual realized after
      | logik error => exact safe.2 f world supplied obligation error reply
      | hardware error => trivial }

/-- Freeze the callee's entry observations before universally havocing its
    post-state. Nested and recursive calls allocate disjoint immutable intervals. -/
def callOutcomesCondition {context : Context A next} (policy : CallPolicy program context)
    (budget : Nat) (f : D.Fn) (args : SymEnv D Nat (D.params f)) (argsBounded : args.Bounded next)
    (caller : SymEnv D Nat Γ) (callerBounded : caller.Bounded next)
    (target : Env D Γ → ErgVal D (D.erg f) → A → Runtime program (fun _ => []) S → World D → Prop)
    (failure : Env D Γ → Fin (D.gruende f) → A → Runtime program (fun _ => []) S → World D → Prop)
    (compile : ResultCompiler context caller (D.erg f) target)
    (compileFailure : ∀ reason, Except Frag.Refusal (Certificate context (fun valuation item runtime world =>
      ∀ actual, caller.Realizes valuation world actual → failure actual reason item runtime world)))
    (shared : Option (SharedResult context caller (D.erg f) target) := none) :
    Except Frag.Refusal (Certificate context (fun valuation item runtime world => ∀ actual,
      caller.Realizes valuation world actual → ∀ supplied, args.Realizes valuation world supplied →
      ∀ allowed, HandlerSafe (policy.semantic item) runtime allowed →
      match runtime.calls f world supplied with
      | .ok after value => target actual value item runtime after
      | .why after reason => failure actual reason item runtime after
      | .logik error => allowed error
      | .hardware _ => True)) := do
  let plan ← snapshotPlan (program.ensures f)
  match plan with
  | none => do
      let checked ← callOutcomesAt policy budget f args argsBounded caller callerBounded none
        target failure compile compileFailure shared
      return checked.map (fun _ _ _ _ ready actual realized supplied suppliedRealized allowed safe =>
        ready actual realized supplied suppliedRealized trivial allowed safe)
  | some names => do
      let more := next + names.length
      have larger : next ≤ more := Nat.le_add_right _ _
      let region : Snapshot.Region D more := ⟨next, names, Nat.le_refl _⟩
      let checked ← callOutcomesAt (policy.weaken larger) budget f args (args.bounded_mono argsBounded larger)
        caller (caller.bounded_mono callerBounded larger) (some region) target failure
        (fun last beyond result resultBounded => compile last (Nat.le_trans larger beyond) result resultBounded)
        (fun reason => do
          let failed ← compileFailure reason
          return failed.weaken larger)
        (shared.map (fun pre => pre.weaken larger))
      return {
        formula := snapshotFormula next names checked.formula
        sound := fun valuation item present runtime world valid actual realized supplied suppliedRealized allowed safe => by
          let chosen := Snapshot.extend next names valuation world
          have agree : ∀ key, key < next → valuation key = chosen key := fun key before =>
            (Snapshot.extend_preserves names next valuation world key (Or.inl before)).symm
          have locals := (caller.realizes_congr next callerBounded valuation chosen agree world world actual).mp realized
          have arguments := (args.realizes_congr next argsBounded valuation chosen agree world world supplied).mp suppliedRealized
          exact checked.sound chosen item ((context.stable valuation chosen item agree).mp present) runtime world
            (snapshotFormula_sound next names checked.formula valuation world valid) actual locals supplied arguments
            (Snapshot.extend_realizes names next valuation world) allowed safe }

def callCondition {context : Context A next} (policy : CallPolicy program context)
    (budget : Nat) (f : D.Fn) (args : SymEnv D Nat (D.params f)) (argsBounded : args.Bounded next)
    (caller : SymEnv D Nat Γ) (callerBounded : caller.Bounded next) (noReasons : D.gruende f = 0)
    (target : Env D Γ → ErgVal D (D.erg f) → A → Runtime program (fun _ => []) S → World D → Prop)
    (compile : ResultCompiler context caller (D.erg f) target)
    (shared : Option (SharedResult context caller (D.erg f) target) := none) :=
  callOutcomesCondition policy budget f args argsBounded caller callerBounded target
    (fun _ _ _ _ _ => False) compile (fun reason => (Fin.cast noReasons reason).elim0) shared

end Gabbro.Grammatik.Vertraege.Pruefer
