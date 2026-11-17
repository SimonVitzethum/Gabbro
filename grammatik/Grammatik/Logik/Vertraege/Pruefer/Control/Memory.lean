module

public import Grammatik.Logik.Vertraege.Pruefer.Control.Selection

@[expose] public section

namespace Gabbro.Grammatik.Vertraege.Pruefer.Symbolic

open Invarianten Invarianten.Elim Invarianten.Elim.Korrekt Invarianten.Frag.Symbolic

variable {D : Deklaration} {program : Programm D} {S : SperrInv D}

def scalarTerm (symbol : SymValue D Nat τ) :
    { term : Frag.LTerm (Key D Nat) // ∀ valuation world actual,
      symbol.Realizes valuation world actual → term.denote (values valuation world) = Frag.scalarValue τ actual } :=
  match symbol with
  | .known value => ⟨.konst (Frag.scalarValue τ value), fun _ _ _ same => by
      change value = _ at same
      rw [← same]
      rfl⟩
  | .integer term => ⟨renameTerm Sum.inr term, fun valuation world actual realized => by
      rw [renameTerm_denote]
      exact realized⟩
  | .product _ => ⟨.konst 0, fun _ _ _ _ => rfl⟩

theorem values_store_swap (valuation : Frag.Assignment Nat) (world after : World D)
    (next : Nat) (key : Frag.Observation D) (value : Int)
    (stored : Frag.assignment after = (Frag.assignment world).bind key value) :
    values (valuation.bind next value) world ∘ swapKey (.inl key) (.inr next) =
      values (valuation.bind next (Frag.assignment world key)) after := by
  funext name
  cases name with
  | inl memory =>
      by_cases same : memory = key <;>
        simp [Function.comp_apply, swapKey, values, stored, Frag.Assignment.bind, same]
  | inr immutable =>
      by_cases same : immutable = next <;>
        simp [Function.comp_apply, swapKey, values, Frag.Assignment.bind, same]

/-- A store relates its new observation to the actual typed value. Renaming is
    capture-free for arbitrary quantified posts; no Cooper stage is run here. -/
def storeCondition {context : Context A next} (symbols : SymEnv D Nat Γ)
    (bounded : symbols.Bounded next) (symbol : SymValue D Nat τ) (valueBounded : symbol.Bounded next)
    (key : Frag.Observation D) (store : World D → Wert D τ → World D)
    (corresponds : ∀ world value,
      Frag.assignment (store world value) = (Frag.assignment world).bind key (Frag.scalarValue τ value))
    (target : A → VC.Runtime program (fun _ => []) S → World D → Env D Γ → Prop)
    (post : Certificate context (fun valuation item runtime world => ∀ actual,
      symbols.Realizes valuation world actual → target item runtime world actual)) :
    Certificate context (fun valuation item runtime world => ∀ actual,
      symbols.Realizes valuation world actual → ∀ value,
      symbol.Realizes valuation world value → target item runtime (store world value) actual) where
  formula := .all (.inr next) (.imp (.eq (.var (.inr next)) (scalarTerm symbol).val)
    (renameProp (swapKey (.inl key) (.inr next)) post.formula))
  sound := fun valuation item present runtime world valid actual realized value selected => by
    let code := Frag.scalarValue τ value
    let extended := valuation.bind next code
    let future := valuation.bind next (Frag.assignment world key)
    have extendAgrees : ∀ key, key < next → valuation key = extended key := by
      intro key before
      have different : key ≠ next := Nat.ne_of_lt before
      simp only [extended, Frag.Assignment.bind, different, ↓reduceIte]
    have futureAgrees : ∀ key, key < next → valuation key = future key := by
      intro key before
      have different : key ≠ next := Nat.ne_of_lt before
      simp only [future, Frag.Assignment.bind, different, ↓reduceIte]
    have selected' := (symbol.realizes_congr next valueBounded valuation extended extendAgrees world world value).mp selected
    have defined : values extended world (.inr next) = (scalarTerm symbol).val.denote (values extended world) :=
      (bind_same valuation next code).trans ((scalarTerm symbol).property extended world value selected').symm
    have body := valid code
    rw [← values_bind] at body
    have renamed := (renameProp_denote _ (swapKey_injective _ _) post.formula (values extended world)).mp (body defined)
    rw [values_store_swap valuation world (store world value) next key code (corresponds world value)] at renamed
    exact post.sound future item ((context.stable valuation future item futureAgrees).mp present)
      runtime (store world value) renamed actual
      ((symbols.realizes_congr next bounded valuation future futureAgrees world (store world value) actual).mp realized)

end Gabbro.Grammatik.Vertraege.Pruefer.Symbolic
