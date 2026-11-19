module

public import Grammatik.Logik.Vertraege.Pruefer.Control.Memory
public import Grammatik.Logik.Vertraege.Pruefer.Control.Havoc
public import Grammatik.Logik.Invarianten.Frag.Symbolic.Parameters

@[expose] public section

namespace Gabbro.Grammatik.Vertraege.Pruefer.Symbolic

open Invarianten Invarianten.Frag Invarianten.Elim Invarianten.Elim.Korrekt Invarianten.Frag.Symbolic
open Invarianten.Modell

variable {D : Deklaration} {program : Programm D} {S : SperrInv D}

def exactArgument (expression : Expr D Γ Λ τ) (symbols : SymEnv D Nat Γ) (bounded : symbols.Bounded next) :
    Option { symbol : SymValue D Nat τ // symbol.Bounded next ∧ ∀ valuation world actual,
      symbols.Realizes valuation world actual → symbol.Realizes valuation world (eval world expression world actual) } :=
  match valueView? expression symbols with
  | some view => some ⟨view.symbol, view.bounded next bounded,
      fun valuation world actual realized => view.realizes valuation world world actual realized⟩
  | none => do
      let known ← knownValue? expression symbols
      return ⟨.known known.val, trivial, fun valuation world actual realized =>
        (known.property valuation world actual realized).symm⟩


def exactArguments (code : Args D Γ Λ params) (symbols : SymEnv D Nat Γ) (bounded : symbols.Bounded next) :
    Option { args : SymEnv D Nat params // args.Bounded next ∧ ∀ valuation world actual,
      symbols.Realizes valuation world actual → args.Realizes valuation world (evalArgs world code world actual) } :=
  match params, code with
  | [], .nil => some ⟨.nil, trivial, fun _ _ _ _ => trivial⟩
  | _ :: _, .cons head tail => do
      let first ← exactArgument head symbols bounded
      let rest ← exactArguments tail symbols bounded
      return ⟨.cons first.val rest.val, ⟨first.property.1, rest.property.1⟩,
        fun valuation world actual realized =>
          ⟨first.property.2 valuation world actual realized, rest.property.2 valuation world actual realized⟩⟩

def argumentRelation (expression : Expr D Γ Λ τ) (symbols : SymEnv D Nat Γ)
    (argument : SymValue D Nat τ) : LProp (Key D Nat) :=
  match τ with
  | .int _ _ => match scalarTerm? argument with
      | some term => (evaluationRelation expression symbols term.val).val
      | none => .tru
  | .bool => match (encodeValue argument).toOption, (Invarianten.Frag.Symbolic.translate expression symbols).toOption with
      | some encoded, some source => .and (.imp encoded.val source.payload) (.imp source.payload encoded.val)
      | _, _ => .tru
  | _ => .tru

theorem argumentRelation_sound (expression : Expr D Γ Λ τ) (symbols : SymEnv D Nat Γ)
    (argument : SymValue D Nat τ) (valuation : Assignment Nat) (world : World D) (actual : Env D Γ)
    (realized : symbols.Realizes valuation world actual)
    (selected : argument.Realizes valuation world (eval world expression world actual)) :
    (argumentRelation expression symbols argument).denote (values valuation world) := by
  cases τ with
  | int lo hi =>
      dsimp only [argumentRelation]
      cases scalarTerm? argument with
      | none => trivial
      | some term =>
          exact (evaluationRelation expression symbols term.val).property valuation world actual realized
            (term.property valuation world _ selected)
  | bool =>
      dsimp only [argumentRelation]
      cases encoded : (encodeValue argument).toOption with
      | none => trivial
      | some value =>
          cases source : (Invarianten.Frag.Symbolic.translate expression symbols).toOption with
          | none => trivial
          | some term =>
              have formal := value.property valuation world _ selected
              have original := term.bool_iff valuation world actual realized
              exact ⟨fun valid => original.mp (formal.mpr valid), fun valid => formal.mp (original.mpr valid)⟩
  | _ => trivial

def argumentRelations (code : Args D Γ Λ params) (symbols : SymEnv D Nat Γ)
    (arguments : SymEnv D Nat params) : LProp (Key D Nat) :=
  match params, code, arguments with
  | [], .nil, .nil => .tru
  | _ :: _, .cons head tail, .cons value rest =>
      .and (argumentRelation head symbols value) (argumentRelations tail symbols rest)

theorem argumentRelations_sound (code : Args D Γ Λ params) (symbols : SymEnv D Nat Γ)
    (arguments : SymEnv D Nat params) (valuation : Assignment Nat) (world : World D) (actual : Env D Γ)
    (realized : symbols.Realizes valuation world actual)
    (selected : arguments.Realizes valuation world (evalArgs world code world actual)) :
    (argumentRelations code symbols arguments).denote (values valuation world) :=
  match params, code, arguments with
  | [], .nil, .nil => trivial
  | _ :: _, .cons head tail, .cons value rest =>
      ⟨argumentRelation_sound head symbols value valuation world actual realized selected.1,
        argumentRelations_sound tail symbols rest valuation world actual realized selected.2⟩
termination_by sizeOf code

def argumentKeys (start finish : Nat) : List (Key D Nat) :=
  (List.range (finish - start)).map (fun offset => .inr (start + offset))

theorem outside_argumentKeys (start finish key : Nat) (absent : (Sum.inr key : Key D Nat) ∉ argumentKeys start finish) :
    key < start ∨ finish ≤ key := by
  by_cases before : key < start
  · exact Or.inl before
  · by_cases after : finish ≤ key
    · exact Or.inr after
    · apply False.elim
      apply absent
      apply List.mem_map.mpr
      refine ⟨key - start, List.mem_range.mpr (by omega), ?_⟩
      have same : start + (key - start) = key := by omega
      rw [same]

def arguments {context : Context A next} (budget : Nat) (code : Args D Γ Λ params)
    (symbols : SymEnv D Nat Γ) (bounded : symbols.Bounded next)
    (target : Env D Γ → Env D params → A → VC.Runtime program (fun _ => []) S → World D → Prop)
    (compile : ∀ more (larger : next ≤ more) (args : SymEnv D Nat params), args.Bounded more →
      Except Frag.Refusal (Certificate (context.weaken larger) (fun valuation item runtime world => ∀ actual,
        symbols.Realizes valuation world actual → ∀ supplied,
        args.Realizes valuation world supplied → target actual supplied item runtime world))) :
    Except Frag.Refusal (Certificate context (fun valuation item runtime world => ∀ actual,
      symbols.Realizes valuation world actual → target actual (evalArgs world code world actual) item runtime world)) :=
  match exactArguments code symbols bounded with
  | some exact => do
      let tail ← compile next (Nat.le_refl next) exact.val exact.property.1
      return tail.map (fun valuation _ _ world ready actual realized =>
        ready actual realized _ (exact.property.2 valuation world actual realized))
  | none => do
      let domain ← parameters (D := D) budget next params
      let branches ← allCertificates context domain.templates.attach
        (fun args valuation item runtime world => ∀ extended,
          (∀ key, key < next ∨ domain.next ≤ key → extended key = valuation key) →
          ∀ actual, symbols.Realizes extended world actual →
          args.val.Realizes extended world (evalArgs world code world actual) →
          target actual (evalArgs world code world actual) item runtime world)
        (fun entry => do
          let args := entry.val
          let tail ← compile domain.next domain.ordered args (domain.bounded args entry.property)
          return {
            formula := universalClosure (argumentKeys next domain.next)
              (.imp (.and (environmentBounds args) (argumentRelations code symbols args)) tail.formula)
            sound := fun valuation item present runtime world valid extended agrees actual realized selected => by
              have ready := closure_transfer (argumentKeys next domain.next)
                (.imp (.and (environmentBounds args) (argumentRelations code symbols args)) tail.formula)
                (values valuation world) (values extended world) valid (by
                  intro key _ absent
                  cases key with
                  | inl memory => rfl
                  | inr key => exact (agrees key (outside_argumentKeys next domain.next key absent)).symm)
              have guarded := ready ⟨environmentBounds_sound args extended world _ selected,
                argumentRelations_sound code symbols args extended world actual realized selected⟩
              have frozen := (context.stable valuation extended item
                (fun key before => (agrees key (Or.inl before)).symm)).mp present
              exact tail.sound extended item frozen runtime world guarded actual realized _ selected })
      return {
        formula := branches.formula
        sound := fun valuation item present runtime world valid actual realized => by
          obtain ⟨args, member, chosen, selected, preserved⟩ := domain.cover world (evalArgs world code world actual) valuation
          let extended : Assignment Nat := fun key => if key < domain.next then chosen key else valuation key
          have selected' : args.Realizes extended world (evalArgs world code world actual) :=
            (args.realizes_congr domain.next (domain.bounded args member) chosen extended
              (fun key before => by simp only [extended, before, ↓reduceIte]) world world _).mp selected
          have agrees : ∀ key, key < next ∨ domain.next ≤ key → extended key = valuation key := by
            intro key outside
            rcases outside with before | after
            · have within : key < domain.next := Nat.lt_of_lt_of_le before domain.ordered
              simpa only [extended, within, ↓reduceIte] using preserved key before
            · have outside : ¬ key < domain.next := Nat.not_lt.mpr after
              simp only [extended, outside, ↓reduceIte]
          have current := (symbols.realizes_congr next bounded valuation extended
            (fun key before => (agrees key (Or.inl before)).symm) world world actual).mp realized
          exact branches.sound valuation item present runtime world valid ⟨args, member⟩
            (List.mem_attach _ _) extended agrees actual current selected' }

end Gabbro.Grammatik.Vertraege.Pruefer.Symbolic
