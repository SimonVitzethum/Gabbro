module

public import Grammatik.Logik.Vertraege.Pruefer.Indirect.Basic

@[expose] public section

/-! # Binding the answer of a call through a function pointer -/

namespace Gabbro.Grammatik.Vertraege.Pruefer

open Invarianten Invarianten.Frag Invarianten.Elim Invarianten.Elim.Korrekt Invarianten.VC
open Invarianten.Frag.Symbolic Symbolic

variable {D : Deklaration} {V : Vertrag D} {S : SperrInv D} {program : Programm D}

/-- `let x = p(args); rest`: every conforming target, its answer bound at the interface type. -/
def bindCallIndBlockCondition {context : Context A next} (policy : CallPolicy program context)
    (budget : Nat) {l : Bool} {Γ : Ctx} {Λ Λout : List (Res D)} {n : Nat}
    (p : Expr D Γ Λ (.fnptr n)) (args : Args D Γ Λ (D.sigNr n).params) (he : (D.sigNr n).erg = some τ)
    (hp : RufPasst D V (D.sigNr n) Λ) (hr : (D.sigNr n).gruende = 0)
    (rest : Block D V l (τ :: Γ) (nachSig D (D.sigNr n) Λ) Λout) (symbols : SymEnv D Nat Γ)
    (bounded : symbols.Bounded next) (goals : Symbolic.Goals (program := program) (S := S) context V Γ)
    (compile : ∀ more (larger : next ≤ more) (result : SymEnv D Nat (ErgCtx [] (D.sigNr n).erg)),
      result.Bounded more → Except Frag.Refusal (Symbolic.BlockCondition policy.semantic rest
        (.cons (resultSymbol he result) symbols) ((goals.weaken larger).shrink τ))) :
    Except Frag.Refusal (Symbolic.BlockCondition policy.semantic
      (.bindCallInd p args he hp hr rest) symbols goals) := do
  let result := fun (actual : Env D Γ) (value : ErgVal D (D.sigNr n).erg) item
      (runtime : Runtime program (fun _ => []) S) world =>
    ∀ allowed, HandlerSafe (policy.semantic item) runtime allowed →
      runtime.wpB rest ((goals.shrink _).holds item runtime allowed) world (.cons (ergWert he value) actual)
  let pre ← Symbolic.arguments budget args symbols bounded
    (fun actual supplied item runtime world => ∀ allowed, HandlerSafe (policy.semantic item) runtime allowed →
      ∀ f (hf : D.passt f n = true),
      match runtime.calls f world (umsig hf supplied) with
      | .ok after value => result actual (ptrResult hf value) item runtime after
      | .why _ _ => False
      | .logik error => allowed error
      | .hardware _ => True)
    (fun more larger supplied suppliedBounded =>
      indirectCondition (policy.weaken larger) budget n supplied suppliedBounded symbols
        (symbols.bounded_mono bounded larger) hr result
        (fun last beyond result resultBounded => do
          let tail ← compile last (Nat.le_trans larger beyond) result resultBounded
          return tail.map (fun valuation _ _ world ready actual realized value selected =>
            ready (.cons (ergWert he value) actual)
              ⟨resultSymbol_realizes he result valuation world value selected, realized⟩)))
  return (pre.read Λ (p.orte ++ args.orte)).map (fun valuation item runtime world ready actual realized allowed safe => by
    have ready := ready actual ((symbols.realizes_world actual valuation world
      (world.lese Λ (p.orte ++ args.orte))).mp realized) allowed safe
    unfold Runtime.wpB
    dsimp only [execBlockH]
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
    | why after reason => exact keinGrundSig hf hr reason
    | logik error => simpa only [reply, Symbolic.Goals.holds] using ready
    | hardware error => trivial)

/-- `let x = p(args);` ending a block: every conforming target, its answer bound at the interface type. -/
def bindCallIndEndCondition {context : Context A next} (policy : CallPolicy program context)
    (budget : Nat) {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {n : Nat}
    (p : Expr D Γ Λ (.fnptr n)) (args : Args D Γ Λ (D.sigNr n).params) (he : (D.sigNr n).erg = some τ)
    (hp : RufPasst D V (D.sigNr n) Λ) (hr : (D.sigNr n).gruende = 0)
    (rest : Endblock D V l (τ :: Γ) (nachSig D (D.sigNr n) Λ)) (symbols : SymEnv D Nat Γ)
    (bounded : symbols.Bounded next) (goals : Symbolic.Goals (program := program) (S := S) context V Γ)
    (compile : ∀ more (larger : next ≤ more) (result : SymEnv D Nat (ErgCtx [] (D.sigNr n).erg)),
      result.Bounded more → Except Frag.Refusal (Symbolic.EndCondition policy.semantic rest
        (.cons (resultSymbol he result) symbols) ((goals.weaken larger).shrink τ))) :
    Except Frag.Refusal (Symbolic.EndCondition policy.semantic
      (.bindCallInd p args he hp hr rest) symbols goals) := do
  let result := fun (actual : Env D Γ) (value : ErgVal D (D.sigNr n).erg) item
      (runtime : Runtime program (fun _ => []) S) world =>
    ∀ allowed, HandlerSafe (policy.semantic item) runtime allowed →
      runtime.wpE rest ((goals.shrink _).endHolds item runtime allowed) world (.cons (ergWert he value) actual)
  let pre ← Symbolic.arguments budget args symbols bounded
    (fun actual supplied item runtime world => ∀ allowed, HandlerSafe (policy.semantic item) runtime allowed →
      ∀ f (hf : D.passt f n = true),
      match runtime.calls f world (umsig hf supplied) with
      | .ok after value => result actual (ptrResult hf value) item runtime after
      | .why _ _ => False
      | .logik error => allowed error
      | .hardware _ => True)
    (fun more larger supplied suppliedBounded =>
      indirectCondition (policy.weaken larger) budget n supplied suppliedBounded symbols
        (symbols.bounded_mono bounded larger) hr result
        (fun last beyond result resultBounded => do
          let tail ← compile last (Nat.le_trans larger beyond) result resultBounded
          return tail.map (fun valuation _ _ world ready actual realized value selected =>
            ready (.cons (ergWert he value) actual)
              ⟨resultSymbol_realizes he result valuation world value selected, realized⟩)))
  return (pre.read Λ (p.orte ++ args.orte)).map (fun valuation item runtime world ready actual realized allowed safe => by
    have ready := ready actual ((symbols.realizes_world actual valuation world
      (world.lese Λ (p.orte ++ args.orte))).mp realized) allowed safe
    unfold Runtime.wpE
    dsimp only [execEndH]
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
    | why after reason => exact keinGrundSig hf hr reason
    | logik error => simpa only [reply, Symbolic.Goals.endHolds] using ready
    | hardware error => trivial)

end Gabbro.Grammatik.Vertraege.Pruefer
