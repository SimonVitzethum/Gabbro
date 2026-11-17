module

public import Grammatik.Logik.Vertraege.Pruefer.Control.Entry
public import Grammatik.Logik.Invarianten.Frag.Symbolic.Parameters

@[expose] public section

namespace Gabbro.Grammatik.Vertraege.Pruefer.Symbolic

open Invarianten Invarianten.Frag Invarianten.Elim Invarianten.Elim.Korrekt Invarianten.VC
open Invarianten.Frag.Symbolic Invarianten.Pruefer

variable {D : Deklaration}

/-- Universal interface obligations use the same symbolic input coverage as
    function entries. Refusal of an abstraction is never a source countermodel. -/
def checkFormulaForEnvironments (budget : Nat) (Γ : Ctx) (predicate : World D → Env D Γ → Prop)
    (compile : ∀ (symbols : SymEnv D Nat Γ), Except Frag.Refusal
      { formula : LProp (Key D Nat) // ∀ valuation world actual, symbols.Realizes valuation world actual →
        (formula.denote (values valuation world) ↔ predicate world actual) }) :
    Except Frag.Refusal (PLift (∀ world actual, predicate world actual)) := do
  let domain ← parameters (D := D) budget 0 Γ
  let checked ← collect domain.templates
    (fun symbols => ∀ valuation world actual, symbols.Realizes valuation world actual → predicate world actual)
    (fun symbols => do
      let encoded ← compile symbols
      let body : LProp (Key D Nat) := .imp (environmentBounds symbols) encoded.val
      let matrix : LProp (Key D Nat) := .imp (memoryFacts body) body
      if accepted : decideB (close (lower matrix)) (close_closed (lower matrix)) = true then
        return ⟨fun valuation world actual realized => by
          have valid := (lower_denote matrix (values valuation world)).mp
            (close_sound (lower matrix) accepted (values valuation world))
          have facts := memoryFacts_sound body valuation world
          exact (encoded.property valuation world actual realized).mp
            (valid facts (environmentBounds_sound symbols valuation world actual realized))⟩
      else .error (.outsideFragment "interface VC abstraction cannot establish the implication"))
  return ⟨fun world actual => by
    obtain ⟨symbols, member, valuation, realized, _⟩ := domain.cover world actual (fun _ => 0)
    exact checked.down symbols member valuation world actual realized⟩

/-- Parameter/result transports are structural equalities, never value decoding. -/
def checkContractRefinement (budget : Nat) {Γ Γ' : Ctx} {result result' : Option Ty}
    (params : Γ' = Γ) (returns : result' = result)
    (interfacePre : Expr D Γ Λ .bool) (targetPre : Expr D Γ' Λ' .bool)
    (targetPost : Expr D (ErgCtx Γ' result') Θ .bool)
    (interfacePost : Expr D (ErgCtx Γ result) Θ' .bool) :
    Except Frag.Refusal (PLift (
      (∀ old actual, wahr? (eval old interfacePre old actual) = true →
        wahr? (eval old targetPre old (cast (congrArg (Env D) params.symm) actual)) = true) ∧
      (∀ old world actual (value : ErgVal D result'),
        wahr? (eval old targetPost world (ergEnv result' value (cast (congrArg (Env D) params.symm) actual))) = true →
        wahr? (eval old interfacePost world (ergEnv result (cast (congrArg (ErgVal D) returns) value) actual)) = true))) := by
  cases params
  cases returns
  exact do
    let pre ← checkFormulaForEnvironments budget Γ
      (fun world actual => wahr? (eval world interfacePre world actual) = true →
        wahr? (eval world targetPre world actual) = true)
      (fun symbols => do
        let a ← Invarianten.Frag.Symbolic.translate interfacePre symbols
        let b ← Invarianten.Frag.Symbolic.translate targetPre symbols
        return ⟨.imp a.payload b.payload, fun valuation world actual realized =>
          imp_congr (a.bool_iff valuation world actual realized).symm
            (b.bool_iff valuation world actual realized).symm⟩)
    let aIndependent ← currentOnly targetPost
    let bIndependent ← currentOnly interfacePost
    let post ← checkFormulaForEnvironments budget (ErgCtx Γ result)
      (fun world actual => wahr? (eval world targetPost world actual) = true →
        wahr? (eval world interfacePost world actual) = true)
      (fun symbols => do
        let a ← Invarianten.Frag.Symbolic.translate targetPost symbols
        let b ← Invarianten.Frag.Symbolic.translate interfacePost symbols
        return ⟨.imp a.payload b.payload, fun valuation world actual realized =>
          imp_congr (a.bool_iff valuation world actual realized).symm
            (b.bool_iff valuation world actual realized).symm⟩)
    return ⟨⟨pre.down, fun old world actual value valid => by
      rw [aIndependent.down old world] at valid
      rw [bIndependent.down old world]
      exact post.down world (ergEnv result value actual) valid⟩⟩

end Gabbro.Grammatik.Vertraege.Pruefer.Symbolic
