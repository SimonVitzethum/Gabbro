module

public import Grammatik.Logik.Vertraege.Pruefer.Control.Arguments

@[expose] public section

namespace Gabbro.Grammatik.Vertraege.Pruefer.Symbolic

open Invarianten.Modell
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

/-- Compound answers use the same complete typed environment coverage as
    parameters. Only finite constructor choices produce separate branches. -/
def componentResultCondition {context : Context A next}
    (args : SymEnv D Nat Γ) (bounded : args.Bounded next)
    (caller : SymEnv D Nat Θ) (callerBounded : caller.Bounded next)
    (budget : Nat) (kind : Ty) (postcondition : Expr D (kind :: Γ) Λ .bool)
    (target : Env D Θ → Wert D kind → A → VC.Runtime program (fun _ => []) S → World D → Prop)
    (compile : ResultCompiler context caller (some kind) target)
    (snapshot : Option (Snapshot.Region D next)) :
    Except Frag.Refusal (Certificate context (fun valuation item runtime world => ∀ old actual,
      args.Realizes valuation old actual →
      Snapshot.Realizes (Snapshot.regionStart snapshot) (Snapshot.regionNames snapshot) valuation old →
      ∀ locals, caller.Realizes valuation world locals → ∀ value,
      wahr? (eval old postcondition world (.cons value actual)) = true → target locals value item runtime world)) := do
  let domain ← parameters (D := D) budget next [kind]
  let branches ← allCertificates context domain.templates.attach
    (fun entry valuation item runtime world => ∀ extended,
      (∀ key, key < next ∨ domain.next ≤ key → extended key = valuation key) →
      ∀ old actual, args.Realizes extended old actual →
      Snapshot.Realizes (Snapshot.regionStart snapshot) (Snapshot.regionNames snapshot) extended old →
      ∀ locals, caller.Realizes extended world locals → ∀ value,
      entry.val.Realizes extended world (.cons value .nil) →
      wahr? (eval old postcondition world (.cons value actual)) = true → target locals value item runtime world)
    (fun entry => do
      let returned := entry.val
      let post ← translateSnapshot (Snapshot.regionNames snapshot) (Snapshot.regionStart snapshot)
        postcondition (.cons (returned.get .here) args)
      let tail ← compile domain.next domain.ordered returned (domain.bounded returned entry.property)
      return {
        formula := universalClosure (argumentKeys next domain.next)
          (.imp (.and (environmentBounds returned) post.payload) tail.formula)
        sound := fun valuation item present runtime world valid extended agrees old actual realized frozen
            locals localRealized value selected promised => by
          have ready := closure_transfer (argumentKeys next domain.next)
            (.imp (.and (environmentBounds returned) post.payload) tail.formula)
            (values valuation world) (values extended world) valid (by
              intro key _ absent
              cases key with
              | inl memory => rfl
              | inr key => exact (agrees key (outside_argumentKeys next domain.next key absent)).symm)
          have current := (args.realizes_world actual extended old world).mp realized
          have head := returned.realizes_get (.cons value .nil) extended world .here selected
          have encoded := (post.bool_iff extended old world (.cons value actual) frozen ⟨head, current⟩).mp promised
          have present' := (context.stable valuation extended item
            (fun key before => (agrees key (Or.inl before)).symm)).mp present
          exact tail.sound extended item present' runtime world
            (ready ⟨environmentBounds_sound returned extended world _ selected, encoded⟩)
            locals localRealized value selected })
  return {
    formula := branches.formula
    sound := fun valuation item present runtime world valid old actual realized frozen locals localRealized value promised => by
      obtain ⟨returned, member, chosen, selected, preserved⟩ := domain.cover world (.cons value .nil) valuation
      let extended : Frag.Assignment Nat := fun key => if key < domain.next then chosen key else valuation key
      have selected' : returned.Realizes extended world (.cons value .nil) :=
        (returned.realizes_congr domain.next (domain.bounded returned member) chosen extended
          (fun key before => by simp only [extended, before, ↓reduceIte]) world world _).mp selected
      have agrees : ∀ key, key < next ∨ domain.next ≤ key → extended key = valuation key := by
        intro key outside
        rcases outside with before | after
        · have within : key < domain.next := Nat.lt_of_lt_of_le before domain.ordered
          simpa only [extended, within, ↓reduceIte] using preserved key before
        · have outside : ¬ key < domain.next := Nat.not_lt.mpr after
          simp only [extended, outside, ↓reduceIte]
      have preservedPrefix : ∀ key, key < next → valuation key = extended key :=
        fun key before => (agrees key (Or.inl before)).symm
      have oldArgs := (args.realizes_congr next bounded valuation extended preservedPrefix old old actual).mp realized
      have oldSnapshot := (Snapshot.region_realizes_congr snapshot valuation extended old preservedPrefix).mp frozen
      have current := (caller.realizes_congr next callerBounded valuation extended preservedPrefix world world locals).mp localRealized
      exact branches.sound valuation item present runtime world valid ⟨returned, member⟩ (List.mem_attach _ _)
        extended agrees old actual oldArgs oldSnapshot locals current value selected' promised }

def resultCondition {context : Context A next} (args : SymEnv D Nat Γ) (bounded : args.Bounded next)
    (caller : SymEnv D Nat Θ) (callerBounded : caller.Bounded next)
    (budget : Nat) (result : Option Ty) (postcondition : Expr D (ErgCtx Γ result) Λ .bool)
    (target : Env D Θ → ErgVal D result → A → VC.Runtime program (fun _ => []) S → World D → Prop)
    (compile : ResultCompiler context caller result target)
    (shared : Option (SharedResult context caller result target) := none)
    (snapshot : Option (Snapshot.Region D next) := none) :
    Except Frag.Refusal (Certificate context (fun valuation item runtime world => ∀ old actual,
      args.Realizes valuation old actual →
      Snapshot.Realizes (Snapshot.regionStart snapshot) (Snapshot.regionNames snapshot) valuation old →
      ∀ locals, caller.Realizes valuation world locals → ∀ value,
      wahr? (eval old postcondition world (ergEnv result value actual)) = true → target locals value item runtime world)) :=
  match postcondition, shared with
  | .tru, some pre => .ok {
      formula := pre.formula
      sound := fun valuation item present runtime world valid _ _ _ _ locals realized value _ =>
        pre.sound valuation item present runtime world valid locals realized value }
  | postcondition, _ => match result, postcondition, target, compile with
    | none, postcondition, target, compile => do
        let post ← translateSnapshot (Snapshot.regionNames snapshot) (Snapshot.regionStart snapshot) postcondition args
        let tail ← compile next (Nat.le_refl next) .nil trivial
        return {
          formula := .imp post.payload tail.formula
          sound := fun valuation item present runtime world valid old actual realized frozen locals localRealized value promised => by
            have current := (args.realizes_world actual valuation old world).mp realized
            have encoded := (post.bool_iff valuation old world actual frozen current).mp promised
            exact tail.sound valuation item present runtime world (valid encoded) locals localRealized value trivial }
    | some (.int lo hi), postcondition, target, compile => do
        let resultSymbols : SymEnv D Nat (ErgCtx [] (some (.int lo hi))) :=
          .cons (.integer (.var next)) .nil
        let resultBounded : resultSymbols.Bounded (next + 1) :=
          ⟨fun key member => by
            have same := List.mem_singleton.mp member
            subst key
            exact Nat.lt_succ_self next, trivial⟩
        let post ← translateSnapshot (Snapshot.regionNames snapshot) (Snapshot.regionStart snapshot)
          postcondition (.cons (.integer (.var next)) args)
        let tail ← compile (next + 1) (Nat.le_succ next) resultSymbols resultBounded
        let bounds : Frag.LProp (Key D Nat) := .and
          (.le (.konst lo) (.var (.inr next))) (.le (.var (.inr next)) (.konst hi))
        return {
          formula := .all (.inr next) (.imp (.and bounds post.payload) tail.formula)
          sound := fun valuation item present runtime world valid old actual realized frozen locals localRealized value promised => by
            let extended := valuation.bind next value.n
            have agree : ∀ key, key < next → valuation key = extended key := by
              intro key before
              have different : key ≠ next := Nat.ne_of_lt before
              simp only [extended, Frag.Assignment.bind, different, ↓reduceIte]
            have present' := (context.stable valuation extended item agree).mp present
            have frozen' := (Snapshot.region_realizes_congr snapshot valuation extended old agree).mp frozen
            have current := (args.realizes_congr next bounded valuation extended agree old world actual).mp realized
            have localCurrent := (caller.realizes_congr next callerBounded valuation extended agree world world locals).mp localRealized
            have valueRealized : (SymValue.integer (.var next) : SymValue D Nat (.int lo hi)).Realizes
                extended world value := bind_same valuation next value.n
            have encoded := (post.bool_iff extended old world (.cons value actual) frozen' ⟨valueRealized, current⟩).mp promised
            have range : bounds.denote (values extended world) := by
              change lo ≤ extended next ∧ extended next ≤ hi
              dsimp only [extended]
              rw [bind_same]
              exact ⟨value.lo_le, value.le_hi⟩
            have ready := valid value.n
            rw [← values_bind] at ready
            exact tail.sound extended item present' runtime world (ready ⟨range, encoded⟩)
              locals localCurrent value ⟨valueRealized, trivial⟩ }
    | some (.prod name fields), postcondition, target, compile =>
        componentResultCondition args bounded caller callerBounded budget (.prod name fields)
          postcondition target compile snapshot
    | some kind, postcondition, target, compile =>
      match VC.localDomain (D := D) budget kind with
      | .error _ => do
        -- No complete domain within the budget: the continuation is certified for an unobserved result,
        -- without using the postcondition, so it holds for every result.
        let tail ← compile next (Nat.le_refl next) (.cons .unobserved .nil) ⟨trivial, trivial⟩
        return {
          formula := tail.formula
          sound := fun valuation item present runtime world valid _ _ _ _ locals localRealized value _ =>
            tail.sound valuation item present runtime world valid locals localRealized value ⟨trivial, trivial⟩ }
      | .ok domain => do
        let branches ← allCertificates context domain.values
          (fun value valuation item runtime world => ∀ old actual, args.Realizes valuation old actual →
            Snapshot.Realizes (Snapshot.regionStart snapshot) (Snapshot.regionNames snapshot) valuation old →
            ∀ locals, caller.Realizes valuation world locals →
            wahr? (eval old postcondition world (.cons value actual)) = true → target locals value item runtime world)
          (fun value => do
            let post ← translateSnapshot (Snapshot.regionNames snapshot) (Snapshot.regionStart snapshot)
              postcondition (.cons (.known value) args)
            let tail ← compile next (Nat.le_refl next) (.cons (.known value) .nil) ⟨trivial, trivial⟩
            return {
              formula := .imp post.payload tail.formula
              sound := fun valuation item present runtime world valid old actual realized frozen locals localRealized promised => by
                have current := (args.realizes_world actual valuation old world).mp realized
                have encoded := (post.bool_iff valuation old world (.cons value actual) frozen ⟨rfl, current⟩).mp promised
                exact tail.sound valuation item present runtime world (valid encoded) locals localRealized value ⟨rfl, trivial⟩ })
        return branches.map (fun _ _ _ _ ready old actual realized frozen locals localRealized value promised =>
          ready value (domain.complete value) old actual realized frozen locals localRealized promised)

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
