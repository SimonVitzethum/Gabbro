module

public import Grammatik.Logik.Vertraege.Pruefer.Control.Oracle.Goals

@[expose] public section

namespace Gabbro.Grammatik.Vertraege.Pruefer.Symbolic

open Invarianten Invarianten.Frag.Symbolic

variable {D : Deklaration} {program : Programm D} {S : SperrInv D} {V : Vertrag D}

/-- Compile the actual block continuation on symbolic optional answers. -/
def oracleBlockTail {context : Context A next} (policy : A → CallObligation program)
    {l : Bool} (symbols : SymEnv D Nat Γ) (bounded : symbols.Bounded next) (budget : Nat)
    (result : Option Ty) (rest : Block D V l (ErgCtx Γ result) Λ Λout)
    (goals : Goals (program := program) (S := S) context V Γ)
    (compile : ∀ more (larger : next ≤ more) (env : SymEnv D Nat (ErgCtx Γ result)), env.Bounded more →
      Except Frag.Refusal (BlockCondition policy rest env ((goals.weaken larger).shrinkResult result))) :=
  oracleContinuation symbols bounded budget result {
    holds := fun item runtime world actual => ∀ allowed, HandlerSafe (policy item) runtime allowed →
      runtime.wpB rest ((goals.shrinkResult result).holds item runtime allowed) world actual
    encode := fun more larger env envBounded => do
      let pre ← compile more larger env envBounded
      return pre.map (fun _ _ _ _ ready actual realized allowed safe => by
        cases result <;> exact ready actual realized allowed safe) }

/-- End continuations share the same answer coverage and poststate quantifier. -/
def oracleEndTail {context : Context A next} (policy : A → CallObligation program)
    {l : Bool} (symbols : SymEnv D Nat Γ) (bounded : symbols.Bounded next) (budget : Nat)
    (result : Option Ty) (rest : Endblock D V l (ErgCtx Γ result) Λ)
    (goals : Goals (program := program) (S := S) context V Γ)
    (compile : ∀ more (larger : next ≤ more) (env : SymEnv D Nat (ErgCtx Γ result)), env.Bounded more →
      Except Frag.Refusal (EndCondition policy rest env ((goals.weaken larger).shrinkResult result))) :=
  oracleContinuation symbols bounded budget result {
    holds := fun item runtime world actual => ∀ allowed, HandlerSafe (policy item) runtime allowed →
      runtime.wpE rest ((goals.shrinkResult result).endHolds item runtime allowed) world actual
    encode := fun more larger env envBounded => do
      let pre ← compile more larger env envBounded
      return pre.map (fun _ _ _ _ ready actual realized allowed safe => by
        cases result <;> exact ready actual realized allowed safe) }

end Gabbro.Grammatik.Vertraege.Pruefer.Symbolic
