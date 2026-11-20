module

public import Grammatik.Logik.Vertraege.Pruefer.Calls

@[expose] public section

namespace Gabbro.Grammatik.Vertraege.Pruefer

open Invarianten Invarianten.Frag Invarianten.Elim Invarianten.VC Invarianten.Frag.Symbolic Symbolic

variable {D : Deklaration} {V : Vertrag D} {S : SperrInv D} {program : Programm D}

/-- Compose an ordinary call binder through the shared symbolic result interface. -/
def bindCallBlockCondition {context : Context A next} (policy : CallPolicy program context)
    (budget : Nat) {l : Bool} {Γ : Ctx} {Λ Λout : List (Res D)}
    (f : D.Fn) (args : Args D Γ Λ (D.params f)) (he : D.erg f = some τ)
    (hp : RufPasst D V (D.signatur f) Λ) (hr : D.gruende f = 0)
    (rest : Block D V l (τ :: Γ) (nach D f Λ) Λout) (symbols : SymEnv D Nat Γ) (bounded : symbols.Bounded next)
    (goals : Symbolic.Goals (program := program) (S := S) context V Γ)
    (compile : ∀ more (larger : next ≤ more) (result : SymEnv D Nat (ErgCtx [] (D.erg f))),
      result.Bounded more → Except Frag.Refusal (Symbolic.BlockCondition policy.semantic rest
        (.cons (resultSymbol he result) symbols) ((goals.weaken larger).shrink τ))) :
    Except Frag.Refusal (Symbolic.BlockCondition policy.semantic
      (.bindCall f args he hp hr rest) symbols goals) := do
  let result := fun (actual : Env D Γ) (value : ErgVal D (D.erg f)) item (runtime : Runtime program (fun _ => []) S) world =>
    ∀ allowed, HandlerSafe (policy.semantic item) runtime allowed →
      runtime.wpB rest ((goals.shrink _).holds item runtime allowed) world (.cons (ergWert he value) actual)
  let pre ← Symbolic.arguments budget args symbols bounded
    (fun actual supplied item runtime world => ∀ allowed, HandlerSafe (policy.semantic item) runtime allowed →
      match runtime.calls f world supplied with
      | .ok after value => result actual value item runtime after
      | .why after reason => False
      | .logik error => allowed error
      | .hardware _ => True)
    (fun more larger supplied suppliedBounded => callCondition (policy.weaken larger) budget f
      supplied suppliedBounded symbols (symbols.bounded_mono bounded larger) hr result
      (fun last beyond result resultBounded => do
        let tail ← compile last (Nat.le_trans larger beyond) result resultBounded
        return tail.map (fun valuation _ _ world ready actual realized value selected =>
          ready (.cons (ergWert he value) actual) ⟨resultSymbol_realizes he result valuation world value selected, realized⟩)))
  return (pre.read Λ args.orte).map (fun valuation item runtime world ready actual realized allowed safe => by
    have ready := ready actual ((symbols.realizes_world actual valuation world (world.lese Λ args.orte)).mp realized) allowed safe
    unfold Runtime.wpB
    dsimp only [execBlockH]
    cases reply : runtime.calls f (world.lese Λ args.orte) (evalArgs (world.lese Λ args.orte) args (world.lese Λ args.orte) actual) with
    | ok after value => rw [reply] at ready; exact (goals.holds_shrink _ item runtime allowed _).mp (ready allowed safe)
    | why after reason => exact (Fin.cast hr reason).elim0
    | logik error => simpa only [reply, Symbolic.Goals.holds] using ready
    | hardware error => trivial)

/-- Compose an ordinary call binder through the shared symbolic result interface. -/
def bindCallEndCondition {context : Context A next} (policy : CallPolicy program context)
    (budget : Nat) {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (f : D.Fn) (args : Args D Γ Λ (D.params f)) (he : D.erg f = some τ)
    (hp : RufPasst D V (D.signatur f) Λ) (hr : D.gruende f = 0)
    (rest : Endblock D V l (τ :: Γ) (nach D f Λ)) (symbols : SymEnv D Nat Γ) (bounded : symbols.Bounded next)
    (goals : Symbolic.Goals (program := program) (S := S) context V Γ)
    (compile : ∀ more (larger : next ≤ more) (result : SymEnv D Nat (ErgCtx [] (D.erg f))),
      result.Bounded more → Except Frag.Refusal (Symbolic.EndCondition policy.semantic rest
        (.cons (resultSymbol he result) symbols) ((goals.weaken larger).shrink τ))) :
    Except Frag.Refusal (Symbolic.EndCondition policy.semantic
      (.bindCall f args he hp hr rest) symbols goals) := do
  let result := fun (actual : Env D Γ) (value : ErgVal D (D.erg f)) item (runtime : Runtime program (fun _ => []) S) world =>
    ∀ allowed, HandlerSafe (policy.semantic item) runtime allowed →
      runtime.wpE rest ((goals.shrink _).endHolds item runtime allowed) world (.cons (ergWert he value) actual)
  let pre ← Symbolic.arguments budget args symbols bounded
    (fun actual supplied item runtime world => ∀ allowed, HandlerSafe (policy.semantic item) runtime allowed →
      match runtime.calls f world supplied with
      | .ok after value => result actual value item runtime after
      | .why after reason => False
      | .logik error => allowed error
      | .hardware _ => True)
    (fun more larger supplied suppliedBounded => callCondition (policy.weaken larger) budget f
      supplied suppliedBounded symbols (symbols.bounded_mono bounded larger) hr result
      (fun last beyond result resultBounded => do
        let tail ← compile last (Nat.le_trans larger beyond) result resultBounded
        return tail.map (fun valuation _ _ world ready actual realized value selected =>
          ready (.cons (ergWert he value) actual) ⟨resultSymbol_realizes he result valuation world value selected, realized⟩)))
  return (pre.read Λ args.orte).map (fun valuation item runtime world ready actual realized allowed safe => by
    have ready := ready actual ((symbols.realizes_world actual valuation world (world.lese Λ args.orte)).mp realized) allowed safe
    unfold Runtime.wpE
    dsimp only [execEndH]
    cases reply : runtime.calls f (world.lese Λ args.orte) (evalArgs (world.lese Λ args.orte) args (world.lese Λ args.orte) actual) with
    | ok after value => rw [reply] at ready; exact (goals.endHolds_shrink _ item runtime allowed _).mp (ready allowed safe)
    | why after reason => exact (Fin.cast hr reason).elim0
    | logik error => simpa only [reply, Symbolic.Goals.endHolds] using ready
    | hardware error => trivial)

/-- A fallible call binder: a value continues with `rest`, a reason runs `failure`. -/
def bindCallElseBlockCondition {context : Context A next} (policy : CallPolicy program context)
    (budget : Nat) {l : Bool} {Γ : Ctx} {Λ Λout : List (Res D)}
    (f : D.Fn) (args : Args D Γ Λ (D.params f)) (he : D.erg f = some τ)
    (hp : RufPasst D V (D.signatur f) Λ) (hr : 0 < D.gruende f)
    (failure : Endblock D V l (.why (D.gruende f) :: Γ) (nach D f Λ))
    (rest : Block D V l (τ :: Γ) (nach D f Λ) Λout) (symbols : SymEnv D Nat Γ) (bounded : symbols.Bounded next)
    (goals : Symbolic.Goals (program := program) (S := S) context V Γ)
    (compile : ∀ more (larger : next ≤ more) (result : SymEnv D Nat (ErgCtx [] (D.erg f))),
      result.Bounded more → Except Frag.Refusal (Symbolic.BlockCondition policy.semantic rest
        (.cons (resultSymbol he result) symbols) ((goals.weaken larger).shrink τ)))
    (compileFailure : ∀ more (larger : next ≤ more) (reason : Fin (D.gruende f)),
      Except Frag.Refusal (Symbolic.EndCondition policy.semantic failure
        (.cons (.known reason) symbols) ((goals.weaken larger).shrink _))) :
    Except Frag.Refusal (Symbolic.BlockCondition policy.semantic
      (.bindCallElse f args he hp hr failure rest) symbols goals) := do
  let result := fun (actual : Env D Γ) (value : ErgVal D (D.erg f)) item (runtime : Runtime program (fun _ => []) S) world =>
    ∀ allowed, HandlerSafe (policy.semantic item) runtime allowed →
      runtime.wpB rest ((goals.shrink _).holds item runtime allowed) world (.cons (ergWert he value) actual)
  let failedResult := fun (actual : Env D Γ) (reason : Fin (D.gruende f)) item (runtime : Runtime program (fun _ => []) S) world =>
    ∀ allowed, HandlerSafe (policy.semantic item) runtime allowed →
      runtime.wpE failure ((goals.shrink _).endHolds item runtime allowed) world (.cons reason actual)
  let pre ← Symbolic.arguments budget args symbols bounded
    (fun actual supplied item runtime world => ∀ allowed, HandlerSafe (policy.semantic item) runtime allowed →
      match runtime.calls f world supplied with
      | .ok after value => result actual value item runtime after
      | .why after reason => failedResult actual reason item runtime after
      | .logik error => allowed error
      | .hardware _ => True)
    (fun more larger supplied suppliedBounded => callOutcomesCondition (policy.weaken larger) budget f
      supplied suppliedBounded symbols (symbols.bounded_mono bounded larger) result failedResult
      (fun last beyond result resultBounded => do
        let tail ← compile last (Nat.le_trans larger beyond) result resultBounded
        return tail.map (fun valuation _ _ world ready actual realized value selected =>
          ready (.cons (ergWert he value) actual) ⟨resultSymbol_realizes he result valuation world value selected, realized⟩))
      (fun reason => do
        let failed ← compileFailure more larger reason
        return failed.map (fun _ _ _ _ ready actual realized => ready (.cons reason actual) ⟨rfl, realized⟩)))
  return (pre.read Λ args.orte).map (fun valuation item runtime world ready actual realized allowed safe => by
    have ready := ready actual ((symbols.realizes_world actual valuation world (world.lese Λ args.orte)).mp realized) allowed safe
    unfold Runtime.wpB
    dsimp only [execBlockH]
    cases reply : runtime.calls f (world.lese Λ args.orte) (evalArgs (world.lese Λ args.orte) args (world.lese Λ args.orte) actual) with
    | ok after value => rw [reply] at ready; exact (goals.holds_shrink _ item runtime allowed _).mp (ready allowed safe)
    | why after reason =>
        rw [reply] at ready
        have failed := ready allowed safe
        cases outcome : execEndH S runtime.oracle runtime.environment runtime.passes runtime.calls failure after (.cons reason actual) <;>
          simpa only [Runtime.wpE, outcome, Symbolic.Goals.holds, Symbolic.Goals.endHolds,
            EndAusgang.schrumpf, EndAusgang.zuAusgang, Symbolic.Goals.shrink, Continuation.shrink] using failed
    | logik error => simpa only [reply, Symbolic.Goals.holds] using ready
    | hardware error => trivial)

/-- A fallible call binder ending a block: a value continues with `rest`, a reason runs `failure`. -/
def bindCallElseEndCondition {context : Context A next} (policy : CallPolicy program context)
    (budget : Nat) {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (f : D.Fn) (args : Args D Γ Λ (D.params f)) (he : D.erg f = some τ)
    (hp : RufPasst D V (D.signatur f) Λ) (hr : 0 < D.gruende f)
    (failure : Endblock D V l (.why (D.gruende f) :: Γ) (nach D f Λ))
    (rest : Endblock D V l (τ :: Γ) (nach D f Λ)) (symbols : SymEnv D Nat Γ) (bounded : symbols.Bounded next)
    (goals : Symbolic.Goals (program := program) (S := S) context V Γ)
    (compile : ∀ more (larger : next ≤ more) (result : SymEnv D Nat (ErgCtx [] (D.erg f))),
      result.Bounded more → Except Frag.Refusal (Symbolic.EndCondition policy.semantic rest
        (.cons (resultSymbol he result) symbols) ((goals.weaken larger).shrink τ)))
    (compileFailure : ∀ more (larger : next ≤ more) (reason : Fin (D.gruende f)),
      Except Frag.Refusal (Symbolic.EndCondition policy.semantic failure
        (.cons (.known reason) symbols) ((goals.weaken larger).shrink _))) :
    Except Frag.Refusal (Symbolic.EndCondition policy.semantic
      (.bindCallElse f args he hp hr failure rest) symbols goals) := do
  let result := fun (actual : Env D Γ) (value : ErgVal D (D.erg f)) item (runtime : Runtime program (fun _ => []) S) world =>
    ∀ allowed, HandlerSafe (policy.semantic item) runtime allowed →
      runtime.wpE rest ((goals.shrink _).endHolds item runtime allowed) world (.cons (ergWert he value) actual)
  let failedResult := fun (actual : Env D Γ) (reason : Fin (D.gruende f)) item (runtime : Runtime program (fun _ => []) S) world =>
    ∀ allowed, HandlerSafe (policy.semantic item) runtime allowed →
      runtime.wpE failure ((goals.shrink _).endHolds item runtime allowed) world (.cons reason actual)
  let pre ← Symbolic.arguments budget args symbols bounded
    (fun actual supplied item runtime world => ∀ allowed, HandlerSafe (policy.semantic item) runtime allowed →
      match runtime.calls f world supplied with
      | .ok after value => result actual value item runtime after
      | .why after reason => failedResult actual reason item runtime after
      | .logik error => allowed error
      | .hardware _ => True)
    (fun more larger supplied suppliedBounded => callOutcomesCondition (policy.weaken larger) budget f
      supplied suppliedBounded symbols (symbols.bounded_mono bounded larger) result failedResult
      (fun last beyond result resultBounded => do
        let tail ← compile last (Nat.le_trans larger beyond) result resultBounded
        return tail.map (fun valuation _ _ world ready actual realized value selected =>
          ready (.cons (ergWert he value) actual) ⟨resultSymbol_realizes he result valuation world value selected, realized⟩))
      (fun reason => do
        let failed ← compileFailure more larger reason
        return failed.map (fun _ _ _ _ ready actual realized => ready (.cons reason actual) ⟨rfl, realized⟩)))
  return (pre.read Λ args.orte).map (fun valuation item runtime world ready actual realized allowed safe => by
    have ready := ready actual ((symbols.realizes_world actual valuation world (world.lese Λ args.orte)).mp realized) allowed safe
    unfold Runtime.wpE
    dsimp only [execEndH]
    cases reply : runtime.calls f (world.lese Λ args.orte) (evalArgs (world.lese Λ args.orte) args (world.lese Λ args.orte) actual) with
    | ok after value => rw [reply] at ready; exact (goals.endHolds_shrink _ item runtime allowed _).mp (ready allowed safe)
    | why after reason => rw [reply] at ready; exact (goals.endHolds_shrink _ item runtime allowed _).mp (ready allowed safe)
    | logik error => simpa only [reply, Symbolic.Goals.endHolds] using ready
    | hardware error => trivial)

end Gabbro.Grammatik.Vertraege.Pruefer
