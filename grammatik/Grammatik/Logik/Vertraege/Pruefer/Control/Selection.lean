module

public import Grammatik.Logik.Vertraege.Pruefer.Control.Binding

@[expose] public section

namespace Gabbro.Grammatik.Vertraege.Pruefer.Symbolic

open Invarianten Invarianten.Elim Invarianten.Elim.Korrekt Invarianten.Frag.Symbolic

variable {D : Deklaration} {program : Programm D} {S : SperrInv D}

abbrev SelectCompiler (context : Context A next) (symbols : SymEnv D Nat Γ) (τ : Ty)
    (target : Env D Γ → Wert D τ → A → VC.Runtime program (fun _ => []) S → World D → Prop) :=
  ∀ more (larger : next ≤ more) (symbol : SymValue D Nat τ), symbol.Bounded more →
    Except Frag.Refusal (Certificate (program := program) (S := S) (context.weaken larger)
      (fun valuation item runtime world => ∀ actual, symbols.Realizes valuation world actual →
        ∀ value, symbol.Realizes valuation world value → target actual value item runtime world))

abbrev SelectionCondition (context : Context A next) (symbols : SymEnv D Nat Γ)
    (expression : Expr D Γ Λ τ)
    (target : Env D Γ → Wert D τ → A → VC.Runtime program (fun _ => []) S → World D → Prop) :=
  Certificate context (fun valuation item runtime world => ∀ actual,
    symbols.Realizes valuation world actual →
    target actual (eval world expression world actual) item runtime world)

def knownValue? (expression : Expr D Γ Λ τ) (symbols : SymEnv D Nat Γ) : Option
    { value : Wert D τ // ∀ valuation world actual, symbols.Realizes valuation world actual →
      eval world expression world actual = value } := do
  let concrete ← symbols.concrete?
  let known ← Frag.constantValue expression concrete.val
  return ⟨known.val, fun valuation world actual realized => by
    rw [concrete.property valuation world actual realized]
    exact known.property world⟩

/-- Only Booleans retain two cases. Even their guard is translated under the
    realizing environment, preserving correlation with prior scalar bindings. -/
def booleanSelection {context : Context A next} (symbols : SymEnv D Nat Γ)
    (expression : Expr D Γ Λ .bool)
    (target : Env D Γ → Wert D .bool → A → VC.Runtime program (fun _ => []) S → World D → Prop)
    (compile : SelectCompiler context symbols .bool target) :
    Except Frag.Refusal (SelectionCondition context symbols expression target) := do
  let yes ← compile next (Nat.le_refl next) (.known true) trivial
  let no ← compile next (Nat.le_refl next) (.known false) trivial
  let encoded := (Invarianten.Frag.Symbolic.translate expression symbols).toOption
  let guard : Frag.LProp (Key D Nat) := match encoded with
    | some term => term.payload
    | none => .tru
  let absent : Frag.LProp (Key D Nat) := match encoded with
    | some term => .not term.payload
    | none => .tru
  return {
    formula := .and (.imp guard yes.formula) (.imp absent no.formula)
    sound := fun valuation item present runtime world valid actual realized => by
      have branches : (guard.denote (values valuation world) → yes.formula.denote (values valuation world)) ∧
          (absent.denote (values valuation world) → no.formula.denote (values valuation world)) := valid
      cases answer : eval world expression world actual with
      | true =>
          have guarded : guard.denote (values valuation world) := by
            dsimp only [guard]
            cases encoded with
            | none => trivial
            | some term => exact (term.bool_iff valuation world actual realized).mp answer
          have ready := yes.sound valuation item present runtime world (branches.1 guarded)
          simpa only [answer] using ready actual realized true rfl
      | false =>
          have guarded : absent.denote (values valuation world) := by
            dsimp only [absent]
            cases encoded with
            | none => trivial
            | some term =>
                intro positive
                have impossible := (term.bool_iff valuation world actual realized).mpr positive
                rw [answer] at impossible
                exact Bool.noConfusion impossible
          have ready := no.sound valuation item present runtime world (branches.2 guarded)
          simpa only [answer] using ready actual realized false rfl }

def freshIntegerSelection {context : Context A next} (symbols : SymEnv D Nat Γ)
    (bounded : symbols.Bounded next) (expression : Expr D Γ Λ (.int lo hi))
    (target : Env D Γ → Wert D (.int lo hi) → A → VC.Runtime program (fun _ => []) S → World D → Prop)
    (compile : SelectCompiler context symbols (.int lo hi) target) :
    Except Frag.Refusal (SelectionCondition context symbols expression target) :=
  integerSelection symbols bounded expression target (do
    let pre ← compile (next + 1) (Nat.le_succ next) (.integer (.var next))
      (fun key member => by
        have same := List.mem_singleton.mp member
        subst key
        exact Nat.lt_succ_self next)
    return pre.map (fun _ _ _ _ ready actual realized value selected =>
      ready actual realized value selected))

/-- A scalar continuation is compiled once on its symbolic input. Integer
    intervals never reach the finite domain API. -/
def selectValue {context : Context A next} (symbols : SymEnv D Nat Γ)
    (bounded : symbols.Bounded next) (expression : Expr D Γ Λ τ)
    (target : Env D Γ → Wert D τ → A → VC.Runtime program (fun _ => []) S → World D → Prop)
    (compile : SelectCompiler context symbols τ target) :
    Except Frag.Refusal (SelectionCondition context symbols expression target) :=
  match valueView? expression symbols with
  | some view => do
      let pre ← compile next (Nat.le_refl next) view.symbol (view.bounded next bounded)
      return pre.map (fun valuation _ _ world ready actual realized =>
        ready actual realized (eval world expression world actual)
          (view.realizes valuation world world actual realized))
  | none =>
    match knownValue? expression symbols with
    | some known => do
        let pre ← compile next (Nat.le_refl next) (.known known.val) trivial
        return pre.map (fun valuation _ _ world ready actual realized =>
          ready actual realized (eval world expression world actual)
            (known.property valuation world actual realized).symm)
    | none =>
      match τ, expression, target, compile with
      | .int lo hi, expression, target, compile =>
          match (Invarianten.Frag.Symbolic.translate expression symbols).toOption with
          | some encoded =>
              match constant : encoded.payload.constant? with
              | some number => do
                  let pre ← compile next (Nat.le_refl next) (.integer (.konst number))
                    (fun _ impossible => False.elim (List.not_mem_nil impossible))
                  return pre.map (fun valuation _ _ world ready actual realized => by
                    apply ready actual realized (eval world expression world actual)
                    change number = (eval world expression world actual).n
                    exact (Frag.LTerm.constant?_sound constant (values valuation world)).symm.trans
                      (encoded.correct valuation world actual realized))
              | none => freshIntegerSelection symbols bounded expression target compile
          | none => freshIntegerSelection symbols bounded expression target compile
      | .bool, expression, target, compile => booleanSelection symbols expression target compile
      | .ptr capability, expression, target, compile => do
          let pre ← compile next (Nat.le_refl next) (.known ()) trivial
          return pre.map (fun _ _ _ _ ready actual realized => by
            apply ready actual realized (eval _ expression _ actual)
            cases eval _ expression _ actual
            rfl)
      | _, _, _, _ => .error (.unsupported "local observation needs a finite decoded type")

end Gabbro.Grammatik.Vertraege.Pruefer.Symbolic
