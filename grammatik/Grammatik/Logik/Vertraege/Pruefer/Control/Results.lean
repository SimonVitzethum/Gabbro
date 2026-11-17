module

public import Grammatik.Logik.Vertraege.Pruefer.Control.Selection

@[expose] public section

namespace Gabbro.Grammatik.Vertraege.Pruefer.Symbolic

open Invarianten Invarianten.Elim Invarianten.Elim.Korrekt Invarianten.Frag.Symbolic

variable {D : Deklaration} {program : Programm D} {S : SperrInv D}

abbrev ResultCompiler (context : Context A next) (caller : SymEnv D Nat Θ) (result : Option Ty)
    (target : Env D Θ → ErgVal D result → A → VC.Runtime program (fun _ => []) S → World D → Prop) :=
  ∀ more (larger : next ≤ more) (symbols : SymEnv D Nat (ErgCtx [] result)), symbols.Bounded more →
    Except Frag.Refusal (Certificate (program := program) (S := S) (context.weaken larger)
      (fun valuation item runtime world => ∀ actual, caller.Realizes valuation world actual → ∀ value,
        symbols.Realizes valuation world (ergEnv result value .nil) → target actual value item runtime world))

/-- A shared result continuation already covers every typed answer. It needs
    no result observation when a literal true ensures contributes no relation. -/
abbrev SharedResult (context : Context A next) (caller : SymEnv D Nat Θ) (result : Option Ty)
    (target : Env D Θ → ErgVal D result → A → VC.Runtime program (fun _ => []) S → World D → Prop) :=
  Certificate context (fun valuation item runtime world => ∀ actual,
    caller.Realizes valuation world actual → ∀ value, target actual value item runtime world)

def resultCondition {context : Context A next} (args : SymEnv D Nat Γ) (bounded : args.Bounded next)
    (caller : SymEnv D Nat Θ) (callerBounded : caller.Bounded next)
    (budget : Nat) (result : Option Ty) (postcondition : Expr D (ErgCtx Γ result) Λ .bool)
    (target : Env D Θ → ErgVal D result → A → VC.Runtime program (fun _ => []) S → World D → Prop)
    (compile : ResultCompiler context caller result target)
    (shared : Option (SharedResult context caller result target) := none) :
    Except Frag.Refusal (Certificate context (fun valuation item runtime world => ∀ old actual,
      args.Realizes valuation old actual → ∀ locals, caller.Realizes valuation world locals → ∀ value,
      wahr? (eval old postcondition world (ergEnv result value actual)) = true → target locals value item runtime world)) :=
  match postcondition, shared with
  | .tru, some pre => .ok {
      formula := pre.formula
      sound := fun valuation item present runtime world valid _ _ _ locals realized value _ =>
        pre.sound valuation item present runtime world valid locals realized value }
  | postcondition, _ => match result, postcondition, target, compile with
    | none, postcondition, target, compile => do
        let independent ← currentOnly postcondition
        let post ← Invarianten.Frag.Symbolic.translate postcondition args
        let tail ← compile next (Nat.le_refl next) .nil trivial
        return {
          formula := .imp post.payload tail.formula
          sound := fun valuation item present runtime world valid old actual realized locals localRealized value promised => by
            rw [independent.down old world (ergEnv none value actual)] at promised
            have current := (args.realizes_world actual valuation old world).mp realized
            have encoded := (post.bool_iff valuation world actual current).mp promised
            exact tail.sound valuation item present runtime world (valid encoded) locals localRealized value trivial }
    | some (.int lo hi), postcondition, target, compile => do
        let independent ← currentOnly postcondition
        let resultSymbols : SymEnv D Nat (ErgCtx [] (some (.int lo hi))) :=
          .cons (.integer (.var next)) .nil
        let resultBounded : resultSymbols.Bounded (next + 1) :=
          ⟨fun key member => by
            have same := List.mem_singleton.mp member
            subst key
            exact Nat.lt_succ_self next, trivial⟩
        let post ← Invarianten.Frag.Symbolic.translate postcondition (.cons (.integer (.var next)) args)
        let tail ← compile (next + 1) (Nat.le_succ next) resultSymbols resultBounded
        let bounds : Frag.LProp (Key D Nat) := .and
          (.le (.konst lo) (.var (.inr next))) (.le (.var (.inr next)) (.konst hi))
        return {
          formula := .all (.inr next) (.imp (.and bounds post.payload) tail.formula)
          sound := fun valuation item present runtime world valid old actual realized locals localRealized value promised => by
            let extended := valuation.bind next value.n
            have agree : ∀ key, key < next → valuation key = extended key := by
              intro key before
              have different : key ≠ next := Nat.ne_of_lt before
              simp only [extended, Frag.Assignment.bind, different, ↓reduceIte]
            have present' := (context.stable valuation extended item agree).mp present
            have current := (args.realizes_congr next bounded valuation extended agree old world actual).mp realized
            have localCurrent := (caller.realizes_congr next callerBounded valuation extended agree world world locals).mp localRealized
            have valueRealized : (SymValue.integer (.var next) : SymValue D Nat (.int lo hi)).Realizes
                extended world value := bind_same valuation next value.n
            rw [independent.down old world (ergEnv (some (.int lo hi)) value actual)] at promised
            have encoded := (post.bool_iff extended world (.cons value actual) ⟨valueRealized, current⟩).mp promised
            have range : bounds.denote (values extended world) := by
              change lo ≤ extended next ∧ extended next ≤ hi
              dsimp only [extended]
              rw [bind_same]
              exact ⟨value.lo_le, value.le_hi⟩
            have ready := valid value.n
            rw [← values_bind] at ready
            exact tail.sound extended item present' runtime world (ready ⟨range, encoded⟩)
              locals localCurrent value ⟨valueRealized, trivial⟩ }
    | some kind, postcondition, target, compile => do
        let independent ← currentOnly postcondition
        let domain ← VC.localDomain (D := D) budget kind
        let branches ← allCertificates context domain.values
          (fun value valuation item runtime world => ∀ old actual, args.Realizes valuation old actual →
            ∀ locals, caller.Realizes valuation world locals →
            wahr? (eval old postcondition world (.cons value actual)) = true → target locals value item runtime world)
          (fun value => do
            let post ← Invarianten.Frag.Symbolic.translate postcondition (.cons (.known value) args)
            let tail ← compile next (Nat.le_refl next) (.cons (.known value) .nil) ⟨trivial, trivial⟩
            return {
              formula := .imp post.payload tail.formula
              sound := fun valuation item present runtime world valid old actual realized locals localRealized promised => by
                have current := (args.realizes_world actual valuation old world).mp realized
                rw [independent.down old world (.cons value actual)] at promised
                have encoded := (post.bool_iff valuation world (.cons value actual) ⟨rfl, current⟩).mp promised
                exact tail.sound valuation item present runtime world (valid encoded) locals localRealized value ⟨rfl, trivial⟩ })
        return branches.map (fun _ _ _ _ ready old actual realized locals localRealized value promised =>
          ready value (domain.complete value) old actual realized locals localRealized promised)

  def resultSymbol {result : Option Ty} {τ : Ty} (same : result = some τ)
      (symbols : SymEnv D Nat (ErgCtx [] result)) : SymValue D Nat τ := by
    subst same
    exact symbols.get .here

  theorem resultSymbol_realizes {result : Option Ty} {τ : Ty} (same : result = some τ)
      (symbols : SymEnv D Nat (ErgCtx [] result)) (valuation : Frag.Assignment Nat) (world : World D)
      (value : ErgVal D result) (realized : symbols.Realizes valuation world (ergEnv result value .nil)) :
      (resultSymbol same symbols).Realizes valuation world (ergWert same value) := by
    subst same
    exact symbols.realizes_get _ valuation world .here realized

  theorem resultSymbol_bounded {result : Option Ty} {τ : Ty} (same : result = some τ)
      (symbols : SymEnv D Nat (ErgCtx [] result)) (bounded : symbols.Bounded next) :
      (resultSymbol same symbols).Bounded next := by
    subst same
    exact symbols.bounded_get next bounded .here

  end Gabbro.Grammatik.Vertraege.Pruefer.Symbolic
