module

public import Grammatik.Logik.Invarianten.Frag.Symbolic.Environment
public import Grammatik.Logik.Invarianten.Frag.Translation

@[expose] public section

namespace Gabbro.Grammatik.Invarianten.Frag.Symbolic

open Elim Elim.Korrekt

def Payload (D : Deklaration) : Ty → Type
  | .int _ _ => LTerm (Key D Nat)
  | .bool => LProp (Key D Nat)
  | .str _ => LTerm (Key D Nat)
  | _ => Empty

def Represents (valuation : Assignment Nat) (world : World D) :
    (τ : Ty) → Payload D τ → Wert D τ → Prop
  | .int _ _, term, value => term.denote (values valuation world) = value.n
  | .bool, formula, value => value = true ↔ formula.denote (values valuation world)
  | .str _, term, value => term.denote (values valuation world) = (value.val.length : Int)
  | _, _, _ => False

structure Encoding (symbols : SymEnv D Nat Γ) (τ : Ty)
    (value : World D → Env D Γ → Wert D τ) where
  payload : Payload D τ
  correct : ∀ valuation world actual, symbols.Realizes valuation world actual →
    Represents valuation world τ payload (value world actual)

theorem Encoding.bool_iff {symbols : SymEnv D Nat Γ} {value : World D → Env D Γ → Wert D .bool}
    (encoded : Encoding symbols .bool value) (valuation : Assignment Nat) (world : World D)
    (actual : Env D Γ) (realized : symbols.Realizes valuation world actual) :
    wahr? (value world actual) = true ↔ encoded.payload.denote (values valuation world) :=
  encoded.correct valuation world actual realized

def liftPayload (τ : Ty) : Frag.Payload D τ → Payload D τ := by
  cases τ <;> first
    | exact renameTerm Sum.inl
    | exact renameProp Sum.inl
    | exact Empty.elim

theorem liftPayload_represents (τ : Ty) (payload : Frag.Payload D τ)
    (valuation : Assignment Nat) (world : World D) (actual : Wert D τ) :
    Represents valuation world τ (liftPayload τ payload) actual ↔
      Frag.Represents world τ payload actual := by
  cases τ with
  | int lo hi =>
      dsimp only [Frag.Payload, Wert, Val] at payload actual
      change (renameTerm Sum.inl payload).denote _ = actual.n ↔ _
      rw [renameTerm_denote]
      rfl
  | bool =>
      dsimp only [Frag.Payload, Wert, Val] at payload actual
      change (actual = true ↔ (renameProp Sum.inl payload).denote _) ↔ _
      rw [renameProp_denote Sum.inl (fun _ _ same => Sum.inl.inj same)]
      rfl
  | str capacity =>
      dsimp only [Frag.Payload, Wert, Val] at payload actual
      change (renameTerm Sum.inl payload).denote _ = (actual.val.length : Int) ↔ _
      rw [renameTerm_denote]
      rfl
  | _ => cases payload

def ofMemory (symbols : SymEnv D Nat Γ) {value : World D → Wert D τ}
    (encoded : Frag.Encoded D τ value) : Encoding symbols τ (fun world _ => value world) where
  payload := liftPayload τ encoded.payload
  correct := fun valuation world _ _ =>
    (liftPayload_represents τ encoded.payload valuation world _).mpr (encoded.correct world)

/-- Concrete environments use the existing exact scalar translator. They are
    one certified specialization of this interface, including constant folding. -/
def concreteEncoding (expression : Expr D Γ Λ τ) (symbols : SymEnv D Nat Γ) :
    Except Refusal (Encoding symbols τ (fun world actual => eval world expression world actual)) := do
  let some concrete := symbols.concrete?
    | .error (.outsideFragment "expression needs a symbolic scalar encoding")
  let encoded ← Frag.translate expression concrete.val
  return {
    payload := liftPayload τ encoded.payload
    correct := fun valuation world actual realized => by
      rw [concrete.property valuation world actual realized]
      exact (liftPayload_represents τ encoded.payload valuation world _).mpr (encoded.correct world) }

def Encoding.constantIndex {symbols : SymEnv D Nat Γ} {value : World D → Env D Γ → Wert D (.int lo hi)}
    (encoded : Encoding symbols (.int lo hi) value) :
    Except Refusal { index : Int // ∀ valuation world actual,
      symbols.Realizes valuation world actual → (value world actual).n = index } :=
  match found : encoded.payload.constant? with
  | none => .error .crossEntry
  | some index => .ok ⟨index, fun valuation world actual realized =>
      (encoded.correct valuation world actual realized).symm.trans
        (LTerm.constant?_sound found (values valuation world))⟩

def allEncoding (symbols : SymEnv D Nat Γ) (items : List α)
    (predicate : α → World D → Env D Γ → Bool)
    (compile : ∀ item, Except Refusal (Encoding symbols .bool (predicate item))) :
    Except Refusal (Encoding symbols .bool (fun world actual =>
      items.all (fun item => predicate item world actual))) :=
  match items with
  | [] => .ok { payload := .tru, correct := fun _ _ _ _ => ⟨fun _ => trivial, fun _ => rfl⟩ }
  | head :: tail => do
      let first ← compile head
      let rest ← allEncoding symbols tail predicate compile
      return {
        payload := .and first.payload rest.payload
        correct := fun valuation world actual realized =>
          Bool.and_eq_true_iff.trans (and_congr
            (first.bool_iff valuation world actual realized)
            (rest.bool_iff valuation world actual realized)) }

end Gabbro.Grammatik.Invarianten.Frag.Symbolic
