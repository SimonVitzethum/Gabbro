module

public import Grammatik.Logik.Vertraege.Pruefer.Current
public import Grammatik.Logik.Invarianten.Frag.Symbolic.Scope
public import Grammatik.Logik.Invarianten.Frag.Symbolic.Translation
public import Grammatik.Logik.Ruf.Schnittstellen.Vertrag

@[expose] public section

namespace Gabbro.Grammatik.Vertraege.Pruefer

open Invarianten Invarianten.Frag.Symbolic

variable {D : Deklaration} {S : SperrInv D} {program : Programm D}

/-- Semantic handler obligations are independent of their arithmetic encoding. -/
structure CallObligation (program : Programm D) where
  holds : ∀ f, World D → Env D (D.params f) → Prop
  requires : ∀ f world actual, holds f world actual → ReqAmEintritt program f world actual

def requiresObligation (program : Programm D) : CallObligation program where
  holds := ReqAmEintritt program
  requires := fun _ _ _ valid => valid

def HandlerSafe (obligation : CallObligation program)
    (runtime : VC.Runtime program (fun _ => []) S) (allowed : Logik D → Prop) : Prop :=
  RespektiertRahmen program runtime.calls ∧
  ∀ f world actual, obligation.holds f world actual → ∀ error,
    runtime.calls f world actual = .logik error → allowed error

/-- Evidence for calls through a function pointer: every conforming target refines its
    interface (decided by `checkPointers`), and a conforming target's own requires already
    meets the policy's obligation. -/
structure IndirectEvidence (program : Programm D) (semantic : A → CallObligation program) : Prop where
  refined : PtrVerfeinert program
  obliged : ∀ item f n, D.passt f n = true → ∀ world actual,
    ReqAmEintritt program f world actual → (semantic item).holds f world actual

/-- A policy encodes symbolic arguments under frozen realizing entry data. Without
    indirect evidence every call through a function pointer is refused. -/
structure CallPolicy (program : Programm D) (context : Context A next) where
  semantic : A → CallObligation program
  encode : ∀ more (larger : next ≤ more) (f : D.Fn) (symbols : SymEnv D Nat (D.params f)),
    symbols.Bounded more → Except Frag.Refusal { formula : Frag.LProp (Key D Nat) //
      ∀ valuation item, context.holds valuation item → ∀ world actual,
        symbols.Realizes valuation world actual →
        (formula.denote (values valuation world) ↔ (semantic item).holds f world actual) }
  indirect : Option (PLift (IndirectEvidence program semantic)) := none

def CallPolicy.weaken {context : Context A next} (policy : CallPolicy program context)
    (larger : next ≤ more) : CallPolicy program (context.weaken larger) where
  semantic := policy.semantic
  encode := fun last beyond f symbols bounded => policy.encode last (Nat.le_trans larger beyond) f symbols bounded
  indirect := policy.indirect

/-- Entry snapshots strengthen proof data while retaining the actual call and
    decrease obligations of the caller's policy. -/
def CallPolicy.refine {context : Context A next} (policy : CallPolicy program context)
    (larger : next ≤ more) (refined : Context A more)
    (implies : ∀ valuation item, refined.holds valuation item → context.holds valuation item) :
    CallPolicy program refined where
  semantic := policy.semantic
  encode := fun last beyond f symbols bounded => do
    let encoded ← policy.encode last (Nat.le_trans larger beyond) f symbols bounded
    return ⟨encoded.val, fun valuation item present world actual realized =>
      encoded.property valuation item (implies valuation item present) world actual realized⟩
  indirect := policy.indirect

def requiresPolicy (program : Programm D) (context : Context A next)
    (refined : Option (PLift (PtrVerfeinert program)) := none) : CallPolicy program context where
  semantic := fun _ => requiresObligation program
  encode := fun _ _ f symbols _ => do
    let encoded ← Invarianten.Frag.Symbolic.translate (program.requires f) symbols
    return ⟨encoded.payload, fun valuation _ _ world actual realized =>
      (encoded.bool_iff valuation world actual realized).symm⟩
  indirect := refined.map (fun checked => ⟨⟨checked.down, fun _ _ _ _ _ _ required => required⟩⟩)

end Gabbro.Grammatik.Vertraege.Pruefer
