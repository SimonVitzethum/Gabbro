module

public import Grammatik.Logik.Vertraege.Pruefer.Indirect.Binding

@[expose] public section

/-! # Fallible calls through a function pointer: a value continues, a reason runs the `else` -/

namespace Gabbro.Grammatik.Vertraege.Pruefer

open Invarianten Invarianten.Frag Invarianten.Elim Invarianten.Elim.Korrekt Invarianten.VC
open Invarianten.Frag.Symbolic Symbolic

variable {D : Deklaration} {V : Vertrag D} {S : SperrInv D} {program : Programm D}

/-- `p(args); else (e) { failure }`: a normal return continues, a reason runs `failure`. -/
def callIndElseCondition {context : Context A next} (policy : CallPolicy program context)
    (budget : Nat) {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {n : Nat}
    (p : Expr D Γ Λ (.fnptr n)) (args : Args D Γ Λ (D.sigNr n).params) (he : (D.sigNr n).erg = some τ)
    (hp : RufPasst D V (D.sigNr n) Λ) (hr : 0 < (D.sigNr n).gruende)
    (failure : Endblock D V l (.why (D.sigNr n).gruende :: Γ) (nachSig D (D.sigNr n) Λ))
    (symbols : SymEnv D Nat Γ) (bounded : symbols.Bounded next)
    (goals : Symbolic.Goals (program := program) (S := S) context V Γ)
    (compileFailure : ∀ more (larger : next ≤ more) (reason : Fin (D.sigNr n).gruende),
      Except Frag.Refusal (Symbolic.EndCondition policy.semantic failure
        (.cons (.known reason) symbols) ((goals.weaken larger).shrink _))) :
    Except Frag.Refusal (Symbolic.StatementCondition policy.semantic
      (.callIndElse p args he hp hr failure) symbols goals) := do
  let failedResult := fun (actual : Env D Γ) (reason : Fin (D.sigNr n).gruende) item
      (runtime : Runtime program (fun _ => []) S) world =>
    ∀ allowed, HandlerSafe (policy.semantic item) runtime allowed →
      runtime.wpE failure ((goals.shrink _).endHolds item runtime allowed) world (.cons reason actual)
  let pre ← Symbolic.arguments budget args symbols bounded
    (fun actual supplied item runtime world => ∀ allowed, HandlerSafe (policy.semantic item) runtime allowed →
      ∀ f (hf : D.passt f n = true),
      match runtime.calls f world (umsig hf supplied) with
      | .ok after _ => goals.normal.holds item runtime after actual
      | .why after reason => failedResult actual (grundSig hf reason) item runtime after
      | .logik error => allowed error
      | .hardware _ => True)
    (fun more larger supplied suppliedBounded => do
      let normal ← goals.normal.encode more larger symbols (symbols.bounded_mono bounded larger)
      indirectOutcomes (policy.weaken larger) budget n supplied suppliedBounded symbols
        (symbols.bounded_mono bounded larger)
        (fun actual _ item runtime world => goals.normal.holds item runtime world actual) failedResult
        (fun _ beyond _ _ => .ok ((normal.weaken beyond).map
          (fun _ _ _ _ ready actual realized _ _ => ready actual realized)))
        (fun reason => do
          let failed ← compileFailure more larger reason
          return failed.map (fun _ _ _ _ ready actual realized => ready (.cons reason actual) ⟨rfl, realized⟩))
        (some (normal.map (fun _ _ _ _ ready actual realized _ => ready actual realized))))
  return (pre.read Λ (p.orte ++ args.orte)).map (fun valuation item runtime world ready actual realized allowed safe => by
    have ready := ready actual ((symbols.realizes_world actual valuation world
      (world.lese Λ (p.orte ++ args.orte))).mp realized) allowed safe
    unfold Runtime.wpS
    dsimp only [execStmtH, indSonst]
    generalize eval (world.lese Λ (p.orte ++ args.orte)) p (world.lese Λ (p.orte ++ args.orte)) actual = pointer at ⊢
    obtain ⟨f, hf⟩ := pointer
    dsimp only
    have ready := ready f hf
    cases reply : runtime.calls f (world.lese Λ (p.orte ++ args.orte))
      (umsig hf (evalArgs (world.lese Λ (p.orte ++ args.orte)) args (world.lese Λ (p.orte ++ args.orte)) actual)) with
    | ok after value => simpa only [reply, Symbolic.Goals.holds] using ready
    | why after reason =>
        rw [reply] at ready
        dsimp only
        have failed := ready allowed safe
        cases outcome : execEndH S runtime.oracle runtime.environment runtime.passes runtime.calls failure after
            (.cons (grundSig hf reason) actual) <;>
          simpa only [Runtime.wpE, outcome, Symbolic.Goals.holds, Symbolic.Goals.endHolds,
            EndAusgang.schrumpf, EndAusgang.zuAusgang, Symbolic.Goals.shrink, Continuation.shrink] using failed
    | logik error => simpa only [reply, Symbolic.Goals.holds] using ready
    | hardware error => trivial)

/-- `let x = p(args) else (e) { failure }; rest`: every conforming target, both outcomes. -/
def bindCallIndElseBlockCondition {context : Context A next} (policy : CallPolicy program context)
    (budget : Nat) {l : Bool} {Γ : Ctx} {Λ Λout : List (Res D)} {n : Nat}
    (p : Expr D Γ Λ (.fnptr n)) (args : Args D Γ Λ (D.sigNr n).params) (he : (D.sigNr n).erg = some τ)
    (hp : RufPasst D V (D.sigNr n) Λ) (hr : 0 < (D.sigNr n).gruende)
    (failure : Endblock D V l (.why (D.sigNr n).gruende :: Γ) (nachSig D (D.sigNr n) Λ))
    (rest : Block D V l (τ :: Γ) (nachSig D (D.sigNr n) Λ) Λout) (symbols : SymEnv D Nat Γ)
    (bounded : symbols.Bounded next) (goals : Symbolic.Goals (program := program) (S := S) context V Γ)
    (compile : ∀ more (larger : next ≤ more) (result : SymEnv D Nat (ErgCtx [] (D.sigNr n).erg)),
      result.Bounded more → Except Frag.Refusal (Symbolic.BlockCondition policy.semantic rest
        (.cons (resultSymbol he result) symbols) ((goals.weaken larger).shrink τ)))
    (compileFailure : ∀ more (larger : next ≤ more) (reason : Fin (D.sigNr n).gruende),
      Except Frag.Refusal (Symbolic.EndCondition policy.semantic failure
        (.cons (.known reason) symbols) ((goals.weaken larger).shrink _))) :
    Except Frag.Refusal (Symbolic.BlockCondition policy.semantic
      (.bindCallIndElse p args he hp hr failure rest) symbols goals) := do
  let result := fun (actual : Env D Γ) (value : ErgVal D (D.sigNr n).erg) item
      (runtime : Runtime program (fun _ => []) S) world =>
    ∀ allowed, HandlerSafe (policy.semantic item) runtime allowed →
      runtime.wpB rest ((goals.shrink _).holds item runtime allowed) world (.cons (ergWert he value) actual)
  let failedResult := fun (actual : Env D Γ) (reason : Fin (D.sigNr n).gruende) item
      (runtime : Runtime program (fun _ => []) S) world =>
    ∀ allowed, HandlerSafe (policy.semantic item) runtime allowed →
      runtime.wpE failure ((goals.shrink _).endHolds item runtime allowed) world (.cons reason actual)
  let pre ← Symbolic.arguments budget args symbols bounded
    (fun actual supplied item runtime world => ∀ allowed, HandlerSafe (policy.semantic item) runtime allowed →
      ∀ f (hf : D.passt f n = true),
      match runtime.calls f world (umsig hf supplied) with
      | .ok after value => result actual (ptrResult hf value) item runtime after
      | .why after reason => failedResult actual (grundSig hf reason) item runtime after
      | .logik error => allowed error
      | .hardware _ => True)
    (fun more larger supplied suppliedBounded =>
      indirectOutcomes (policy.weaken larger) budget n supplied suppliedBounded symbols
        (symbols.bounded_mono bounded larger) result failedResult
        (fun last beyond result resultBounded => do
          let tail ← compile last (Nat.le_trans larger beyond) result resultBounded
          return tail.map (fun valuation _ _ world ready actual realized value selected =>
            ready (.cons (ergWert he value) actual)
              ⟨resultSymbol_realizes he result valuation world value selected, realized⟩))
        (fun reason => do
          let failed ← compileFailure more larger reason
          return failed.map (fun _ _ _ _ ready actual realized => ready (.cons reason actual) ⟨rfl, realized⟩)))
  return (pre.read Λ (p.orte ++ args.orte)).map (fun valuation item runtime world ready actual realized allowed safe => by
    have ready := ready actual ((symbols.realizes_world actual valuation world
      (world.lese Λ (p.orte ++ args.orte))).mp realized) allowed safe
    unfold Runtime.wpB
    dsimp only [execBlockH, indSonst]
    generalize eval (world.lese Λ (p.orte ++ args.orte)) p (world.lese Λ (p.orte ++ args.orte)) actual = pointer at ⊢
    obtain ⟨f, hf⟩ := pointer
    dsimp only
    have ready := ready f hf
    cases reply : runtime.calls f (world.lese Λ (p.orte ++ args.orte))
      (umsig hf (evalArgs (world.lese Λ (p.orte ++ args.orte)) args (world.lese Λ (p.orte ++ args.orte)) actual)) with
    | ok after value =>
        rw [reply] at ready
        dsimp only
        rw [ergWert_ptrResult hf he value]
        exact (goals.holds_shrink _ item runtime allowed _).mp (ready allowed safe)
    | why after reason =>
        rw [reply] at ready
        dsimp only
        have failed := ready allowed safe
        cases outcome : execEndH S runtime.oracle runtime.environment runtime.passes runtime.calls failure after
            (.cons (grundSig hf reason) actual) <;>
          simpa only [Runtime.wpE, outcome, Symbolic.Goals.holds, Symbolic.Goals.endHolds,
            EndAusgang.schrumpf, EndAusgang.zuAusgang, Symbolic.Goals.shrink, Continuation.shrink] using failed
    | logik error => simpa only [reply, Symbolic.Goals.holds] using ready
    | hardware error => trivial)

/-- `let x = p(args) else (e) { failure };` ending a block: every conforming target, both outcomes. -/
def bindCallIndElseEndCondition {context : Context A next} (policy : CallPolicy program context)
    (budget : Nat) {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {n : Nat}
    (p : Expr D Γ Λ (.fnptr n)) (args : Args D Γ Λ (D.sigNr n).params) (he : (D.sigNr n).erg = some τ)
    (hp : RufPasst D V (D.sigNr n) Λ) (hr : 0 < (D.sigNr n).gruende)
    (failure : Endblock D V l (.why (D.sigNr n).gruende :: Γ) (nachSig D (D.sigNr n) Λ))
    (rest : Endblock D V l (τ :: Γ) (nachSig D (D.sigNr n) Λ)) (symbols : SymEnv D Nat Γ)
    (bounded : symbols.Bounded next) (goals : Symbolic.Goals (program := program) (S := S) context V Γ)
    (compile : ∀ more (larger : next ≤ more) (result : SymEnv D Nat (ErgCtx [] (D.sigNr n).erg)),
      result.Bounded more → Except Frag.Refusal (Symbolic.EndCondition policy.semantic rest
        (.cons (resultSymbol he result) symbols) ((goals.weaken larger).shrink τ)))
    (compileFailure : ∀ more (larger : next ≤ more) (reason : Fin (D.sigNr n).gruende),
      Except Frag.Refusal (Symbolic.EndCondition policy.semantic failure
        (.cons (.known reason) symbols) ((goals.weaken larger).shrink _))) :
    Except Frag.Refusal (Symbolic.EndCondition policy.semantic
      (.bindCallIndElse p args he hp hr failure rest) symbols goals) := do
  let result := fun (actual : Env D Γ) (value : ErgVal D (D.sigNr n).erg) item
      (runtime : Runtime program (fun _ => []) S) world =>
    ∀ allowed, HandlerSafe (policy.semantic item) runtime allowed →
      runtime.wpE rest ((goals.shrink _).endHolds item runtime allowed) world (.cons (ergWert he value) actual)
  let failedResult := fun (actual : Env D Γ) (reason : Fin (D.sigNr n).gruende) item
      (runtime : Runtime program (fun _ => []) S) world =>
    ∀ allowed, HandlerSafe (policy.semantic item) runtime allowed →
      runtime.wpE failure ((goals.shrink _).endHolds item runtime allowed) world (.cons reason actual)
  let pre ← Symbolic.arguments budget args symbols bounded
    (fun actual supplied item runtime world => ∀ allowed, HandlerSafe (policy.semantic item) runtime allowed →
      ∀ f (hf : D.passt f n = true),
      match runtime.calls f world (umsig hf supplied) with
      | .ok after value => result actual (ptrResult hf value) item runtime after
      | .why after reason => failedResult actual (grundSig hf reason) item runtime after
      | .logik error => allowed error
      | .hardware _ => True)
    (fun more larger supplied suppliedBounded =>
      indirectOutcomes (policy.weaken larger) budget n supplied suppliedBounded symbols
        (symbols.bounded_mono bounded larger) result failedResult
        (fun last beyond result resultBounded => do
          let tail ← compile last (Nat.le_trans larger beyond) result resultBounded
          return tail.map (fun valuation _ _ world ready actual realized value selected =>
            ready (.cons (ergWert he value) actual)
              ⟨resultSymbol_realizes he result valuation world value selected, realized⟩))
        (fun reason => do
          let failed ← compileFailure more larger reason
          return failed.map (fun _ _ _ _ ready actual realized => ready (.cons reason actual) ⟨rfl, realized⟩)))
  return (pre.read Λ (p.orte ++ args.orte)).map (fun valuation item runtime world ready actual realized allowed safe => by
    have ready := ready actual ((symbols.realizes_world actual valuation world
      (world.lese Λ (p.orte ++ args.orte))).mp realized) allowed safe
    unfold Runtime.wpE
    dsimp only [execEndH, indSonstE]
    generalize eval (world.lese Λ (p.orte ++ args.orte)) p (world.lese Λ (p.orte ++ args.orte)) actual = pointer at ⊢
    obtain ⟨f, hf⟩ := pointer
    dsimp only
    have ready := ready f hf
    cases reply : runtime.calls f (world.lese Λ (p.orte ++ args.orte))
      (umsig hf (evalArgs (world.lese Λ (p.orte ++ args.orte)) args (world.lese Λ (p.orte ++ args.orte)) actual)) with
    | ok after value =>
        rw [reply] at ready
        dsimp only
        rw [ergWert_ptrResult hf he value]
        exact (goals.endHolds_shrink _ item runtime allowed _).mp (ready allowed safe)
    | why after reason =>
        rw [reply] at ready
        dsimp only
        exact (goals.endHolds_shrink _ item runtime allowed _).mp (ready allowed safe)
    | logik error => simpa only [reply, Symbolic.Goals.endHolds] using ready
    | hardware error => trivial)

end Gabbro.Grammatik.Vertraege.Pruefer
