module

public import Grammatik.Logik.Vertraege.Pruefer.Control.Oracle.Tail

@[expose] public section

namespace Gabbro.Grammatik.Vertraege.Pruefer.Symbolic

open Invarianten Invarianten.Frag Invarianten.Elim Invarianten.Frag.Symbolic

variable {D : Deklaration} {V : Vertrag D} {program : Programm D} {S : SperrInv D}

def bindAxiomEndCondition {context : Context A next} (policy : A → CallObligation program)
    (budget : Nat) {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (he : D.aerg a = (some τ))
    (hw : ∀ t, D.aschreibt a t = true → V.schreibt t = true)
    (hg : ∀ g, D.agschreibt a g = true → V.gschreibt g = true)
    (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
    (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
    (rest : Endblock D V l (ErgCtx Γ (some τ)) Λ) (symbols : SymEnv D Nat Γ) (bounded : symbols.Bounded next)
    (goals : Goals (program := program) (S := S) context V Γ)
    (compile : ∀ more (larger : next ≤ more) (env : SymEnv D Nat (ErgCtx Γ (some τ))), env.Bounded more →
      Except Frag.Refusal (EndCondition policy rest env ((goals.weaken larger).shrinkResult (some τ))))
    : Except Frag.Refusal (EndCondition policy (.bindAxiom a args he hw hg hd hgd rest) symbols goals) := do
  let normal ← oracleEndTail policy symbols bounded budget (some τ) rest goals compile
  return {
    formula := normal.formula
    sound := fun valuation item present runtime world valid actual realized allowed safe => by
      have ready := normal.sound valuation item present runtime world valid actual realized
      unfold VC.Runtime.wpE
      dsimp only [execEndH]
      cases answer : axiomAntwort runtime.oracle a (world.lese Λ args.orte)
        (evalArgs (world.lese Λ args.orte) args (world.lese Λ args.orte) actual) with
      | mk after value =>
          cases value with
          | none => trivial
          | some value =>
              exact (goals.endHolds_shrinkResult (some τ) item runtime allowed _).mp
                (ready after (ergWert he value) allowed safe) }

def bindAxiomElseEndCondition {context : Context A next} (policy : A → CallObligation program)
    (budget : Nat) {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (he : D.aerg a = (some τ))
    (hr : 0 < D.agruende a)
    (hw : ∀ t, D.aschreibt a t = true → V.schreibt t = true)
    (hg : ∀ g, D.agschreibt a g = true → V.gschreibt g = true)
    (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
    (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
    (failure : Endblock D V l (.why (D.agruende a) :: Γ) Λ)
    (rest : Endblock D V l (ErgCtx Γ (some τ)) Λ) (symbols : SymEnv D Nat Γ) (bounded : symbols.Bounded next)
    (goals : Goals (program := program) (S := S) context V Γ)
    (compile : ∀ more (larger : next ≤ more) (env : SymEnv D Nat (ErgCtx Γ (some τ))), env.Bounded more →
      Except Frag.Refusal (EndCondition policy rest env ((goals.weaken larger).shrinkResult (some τ))))
    (compileFailure : ∀ more (larger : next ≤ more) (env : SymEnv D Nat (.why (D.agruende a) :: Γ)), env.Bounded more →
      Except Frag.Refusal (EndCondition policy failure env ((goals.weaken larger).shrinkResult (some (.why (D.agruende a))))))
    : Except Frag.Refusal (EndCondition policy (.bindAxiomElse a args he hr hw hg hd hgd failure rest) symbols goals) := do
  let normal ← oracleEndTail policy symbols bounded budget (some τ) rest goals compile
  let failed ← oracleEndTail policy symbols bounded budget (some (.why (D.agruende a))) failure goals compileFailure
  return {
    formula := .and normal.formula failed.formula
    sound := fun valuation item present runtime world valid actual realized allowed safe => by
      have ready := normal.sound valuation item present runtime world valid.1 actual realized
      have rejected := failed.sound valuation item present runtime world valid.2 actual realized
      unfold VC.Runtime.wpE
      dsimp only [execEndH]
      cases answer : axiomAntwortSonst runtime.oracle a (world.lese Λ args.orte)
        (evalArgs (world.lese Λ args.orte) args (world.lese Λ args.orte) actual) with
      | mk after value =>
          cases value with
          | none => trivial
          | some value =>
              cases value with
              | inl value =>
                  exact (goals.endHolds_shrinkResult (some τ) item runtime allowed _).mp
                    (ready after (ergWert he value) allowed safe)
              | inr reason =>
                  exact (goals.endHolds_shrinkResult (some (.why (D.agruende a))) item runtime allowed _).mp
                    (rejected after reason allowed safe) }

def bindAxiomOptEndCondition {context : Context A next} (policy : A → CallObligation program)
    (budget : Nat) {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (result : Option Ty)
    (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (he : D.aerg a = result)
    (hp : RufPasst D V (D.asignatur a) Λ)
    (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
    (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
    (rest : Endblock D V l (ErgCtx Γ result) (nachSig D (D.asignatur a) Λ)) (symbols : SymEnv D Nat Γ) (bounded : symbols.Bounded next)
    (goals : Goals (program := program) (S := S) context V Γ)
    (compile : ∀ more (larger : next ≤ more) (env : SymEnv D Nat (ErgCtx Γ result)), env.Bounded more →
      Except Frag.Refusal (EndCondition policy rest env ((goals.weaken larger).shrinkResult result)))
    : Except Frag.Refusal (EndCondition policy (.bindAxiomOpt result a args he hp hd hgd rest) symbols goals) := do
  let normal ← oracleEndTail policy symbols bounded budget result rest goals compile
  return {
    formula := normal.formula
    sound := fun valuation item present runtime world valid actual realized allowed safe => by
      have ready := normal.sound valuation item present runtime world valid actual realized
      unfold VC.Runtime.wpE
      dsimp only [execEndH]
      cases answer : axiomAntwort runtime.oracle a (world.lese Λ args.orte)
        (evalArgs (world.lese Λ args.orte) args (world.lese Λ args.orte) actual) with
      | mk after value =>
          cases value with
          | none => trivial
          | some value =>
              exact (goals.endHolds_shrinkResult result item runtime allowed _).mp
                (ready after (he ▸ value) allowed safe) }

def bindAxiomOptElseEndCondition {context : Context A next} (policy : A → CallObligation program)
    (budget : Nat) {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (result : Option Ty)
    (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (he : D.aerg a = result)
    (hp : RufPasst D V (D.asignatur a) Λ)
    (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
    (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
    (hr : 0 < D.agruende a)
    (failure : Endblock D V l (.why (D.agruende a) :: Γ) (nachSig D (D.asignatur a) Λ))
    (rest : Endblock D V l (ErgCtx Γ result) (nachSig D (D.asignatur a) Λ)) (symbols : SymEnv D Nat Γ) (bounded : symbols.Bounded next)
    (goals : Goals (program := program) (S := S) context V Γ)
    (compile : ∀ more (larger : next ≤ more) (env : SymEnv D Nat (ErgCtx Γ result)), env.Bounded more →
      Except Frag.Refusal (EndCondition policy rest env ((goals.weaken larger).shrinkResult result)))
    (compileFailure : ∀ more (larger : next ≤ more) (env : SymEnv D Nat (.why (D.agruende a) :: Γ)), env.Bounded more →
      Except Frag.Refusal (EndCondition policy failure env ((goals.weaken larger).shrinkResult (some (.why (D.agruende a))))))
    : Except Frag.Refusal (EndCondition policy (.bindAxiomOptElse result a args he hp hd hgd hr failure rest) symbols goals) := do
  let normal ← oracleEndTail policy symbols bounded budget result rest goals compile
  let failed ← oracleEndTail policy symbols bounded budget (some (.why (D.agruende a))) failure goals compileFailure
  return {
    formula := .and normal.formula failed.formula
    sound := fun valuation item present runtime world valid actual realized allowed safe => by
      have ready := normal.sound valuation item present runtime world valid.1 actual realized
      have rejected := failed.sound valuation item present runtime world valid.2 actual realized
      unfold VC.Runtime.wpE
      dsimp only [execEndH]
      cases answer : axiomAntwortSonst runtime.oracle a (world.lese Λ args.orte)
        (evalArgs (world.lese Λ args.orte) args (world.lese Λ args.orte) actual) with
      | mk after value =>
          cases value with
          | none => trivial
          | some value =>
              cases value with
              | inl value =>
                  exact (goals.endHolds_shrinkResult result item runtime allowed _).mp
                    (ready after (he ▸ value) allowed safe)
              | inr reason =>
                  exact (goals.endHolds_shrinkResult (some (.why (D.agruende a))) item runtime allowed _).mp
                    (rejected after reason allowed safe) }

end Gabbro.Grammatik.Vertraege.Pruefer.Symbolic
