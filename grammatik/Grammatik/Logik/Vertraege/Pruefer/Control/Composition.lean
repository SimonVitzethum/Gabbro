module

public import Grammatik.Logik.Vertraege.Pruefer.Control.Selection

@[expose] public section

namespace Gabbro.Grammatik.Vertraege.Pruefer.Symbolic

open Invarianten Invarianten.Frag.Symbolic

variable {D : Deklaration} {V : Vertrag D} {program : Programm D} {S : SperrInv D}

def returnCondition {context : Context A next} (symbols : SymEnv D Nat Γ)
    (bounded : symbols.Bounded next) (result : Option Ty) (expression : ErgExpr D Γ Λ result)
    (post : Continuation (program := program) (S := S) context (ErgCtx [] result)) :
    Except Frag.Refusal (Certificate context (fun valuation item runtime world => ∀ actual,
      symbols.Realizes valuation world actual →
      post.holds item runtime world (ergEnv result (evalErg world expression world actual) .nil))) :=
  match result, expression, post with
  | none, .empty, post => do
      let pre ← post.encode next (Nat.le_refl next) .nil trivial
      return pre.map (fun _ _ _ _ ready _ _ => ready .nil trivial)
  | some _, .val expression, post =>
      selectValue symbols bounded expression
        (fun _ value item runtime world => post.holds item runtime world (.cons value .nil))
        (fun more larger symbol valueBounded => do
          let pre ← post.encode more larger (.cons symbol .nil) ⟨valueBounded, trivial⟩
          return pre.map (fun _ _ _ _ ready _ _ value selected => ready (.cons value .nil) ⟨selected, trivial⟩))

def retEndCondition (policy : A → CallObligation program) {context : Context A next}
    {l : Bool} (symbols : SymEnv D Nat Γ) (bounded : symbols.Bounded next)
    (expression : ErgExpr D Γ Λ V.erg) (inventory : Λ.Perm V.ende)
    (goals : Goals (program := program) (S := S) context V Γ) :
    Except Frag.Refusal (EndCondition policy (.ret expression inventory : Endblock D V l Γ Λ) symbols goals) := do
  let pre ← returnCondition symbols bounded V.erg expression goals.returned
  return (pre.read Λ expression.orte).map (fun valuation item runtime world ready actual realized _ _ => by
    have current := (symbols.realizes_world actual valuation world (world.lese Λ expression.orte)).mp realized
    unfold VC.Runtime.wpE
    simp only [execEndH, Goals.endHolds]
    exact ready actual current)

/-- The same certified scalar selection composes with the actual block WP.
    Scope shrinkage is proved against execBlockH, including early exits. -/
def bindBlockCondition (policy : A → CallObligation program) {context : Context A next}
    {l : Bool} (symbols : SymEnv D Nat Γ) (bounded : symbols.Bounded next)
    (expression : Expr D Γ Λ τ) (rest : Block D V l (τ :: Γ) Λ Λ')
    (goals : Goals (program := program) (S := S) context V Γ)
    (compile : ∀ more (larger : next ≤ more) (symbol : SymValue D Nat τ), symbol.Bounded more →
      Except Frag.Refusal (BlockCondition policy rest (.cons symbol symbols) ((goals.weaken larger).shrink τ))) :
    Except Frag.Refusal (BlockCondition policy (.bind expression rest) symbols goals) := do
  let pre ← selectValue symbols bounded expression
    (fun actual value item runtime world => ∀ allowed, HandlerSafe (policy item) runtime allowed →
      runtime.wpB rest ((goals.shrink τ).holds item runtime allowed) world (.cons value actual))
    (fun more larger symbol valueBounded => do
      let pre ← compile more larger symbol valueBounded
      return pre.map (fun _ _ _ _ ready actual realized value selected =>
        ready (.cons value actual) ⟨selected, realized⟩))
  return (pre.read Λ expression.orte).map (fun valuation item runtime world ready actual realized allowed safe => by
    have current := (symbols.realizes_world actual valuation world (world.lese Λ expression.orte)).mp realized
    have tail := ready actual current allowed safe
    unfold VC.Runtime.wpB at tail ⊢
    simp only [execBlockH]
    exact (goals.holds_shrink τ item runtime allowed _).mp tail)

/-- End blocks use the identical symbolic selection and the model's own
    end-output shrink operation. No second syntax walker is introduced. -/
def bindEndCondition (policy : A → CallObligation program) {context : Context A next}
    {l : Bool} (symbols : SymEnv D Nat Γ) (bounded : symbols.Bounded next)
    (expression : Expr D Γ Λ τ) (rest : Endblock D V l (τ :: Γ) Λ)
    (goals : Goals (program := program) (S := S) context V Γ)
    (compile : ∀ more (larger : next ≤ more) (symbol : SymValue D Nat τ), symbol.Bounded more →
      Except Frag.Refusal (EndCondition policy rest (.cons symbol symbols) ((goals.weaken larger).shrink τ))) :
    Except Frag.Refusal (EndCondition policy (.bind expression rest) symbols goals) := do
  let pre ← selectValue symbols bounded expression
    (fun actual value item runtime world => ∀ allowed, HandlerSafe (policy item) runtime allowed →
      runtime.wpE rest ((goals.shrink τ).endHolds item runtime allowed) world (.cons value actual))
    (fun more larger symbol valueBounded => do
      let pre ← compile more larger symbol valueBounded
      return pre.map (fun _ _ _ _ ready actual realized value selected =>
        ready (.cons value actual) ⟨selected, realized⟩))
  return (pre.read Λ expression.orte).map (fun valuation item runtime world ready actual realized allowed safe => by
    have current := (symbols.realizes_world actual valuation world (world.lese Λ expression.orte)).mp realized
    have tail := ready actual current allowed safe
    unfold VC.Runtime.wpE at tail ⊢
    simp only [execEndH]
    exact (goals.endHolds_shrink τ item runtime allowed _).mp tail)

/-- One certificate per value of a complete finite list, conjoined: every case is required, so the actual value is
    covered whichever it is. Used for dispatch over finite payloads (`onOption`). -/
def everyValue {context : Context A next} {α : Type}
    (target : α → Frag.Assignment Nat → A → VC.Runtime program (fun _ => []) S → World D → Prop)
    (compile : ∀ value, Except Frag.Refusal (Certificate context (target value))) :
    (values : List α) →
    Except Frag.Refusal (Certificate context (fun valuation item runtime world =>
      ∀ value ∈ values, target value valuation item runtime world))
  | [] => .ok
      { formula := .tru
        sound := fun _ _ _ _ _ _ _ member => absurd member List.not_mem_nil }
  | value :: rest => do
      let head ← compile value
      let tail ← everyValue target compile rest
      return {
        formula := .and head.formula tail.formula
        sound := fun valuation item present runtime world valid current member => by
          have parts : head.formula.denote (values valuation world) ∧
              tail.formula.denote (values valuation world) := valid
          rcases List.mem_cons.mp member with same | member
          · rw [same]
            exact head.sound valuation item present runtime world parts.1
          · exact tail.sound valuation item present runtime world parts.2 current member }

theorem freshKeyBounded (next : Nat) :
    (SymValue.integer (.var next) : SymValue D Nat (.int lo hi)).Bounded (next + 1) := fun key member => by
  have same := List.mem_singleton.mp member
  subst key
  exact Nat.lt_succ_self next

/-- `match` on an option of unknown value: the `Some` block is certified ONCE for a fresh index observation bounded
    by the option's range (no enumeration of the indices), the `None` block once; whichever the actual value is, its
    block's certificate applies. -/
def symbolicOptionCondition (policy : A → CallObligation program) {context : Context A next} {l : Bool}
    {Γ : Ctx} {Λ Λ' : List (Res D)} {count : Int}
    (symbols : SymEnv D Nat Γ) (bounded : symbols.Bounded next) (expression : Expr D Γ Λ (.opt count))
    (present : Block D V l (Ty.index count :: Γ) Λ Λ') (absent : Block D V l Γ Λ Λ')
    (goals : Goals (program := program) (S := S) context V Γ)
    (absentCase : BlockCondition policy absent symbols goals)
    (presentCase : BlockCondition (context := context.weaken (Nat.le_succ next)) policy present
      (.cons (.integer (.var next)) symbols) ((goals.weaken (Nat.le_succ next)).shrink (Ty.index count))) :
    StatementCondition policy (.onOption expression present absent) symbols goals :=
  let bounds : Frag.LProp (Key D Nat) := .and
    (.le (.konst 0) (.var (.inr next))) (.le (.var (.inr next)) (.konst (count - 1)))
  let both : Certificate context (fun valuation item (runtime : VC.Runtime program (fun _ => []) S) world =>
      (∀ index : Wert D (Ty.index count), ∀ actual, symbols.Realizes valuation world actual → ∀ allowed,
        HandlerSafe (policy item) runtime allowed →
        runtime.wpB present ((goals.shrink (Ty.index count)).holds item runtime allowed) world (.cons index actual)) ∧
      (∀ actual, symbols.Realizes valuation world actual → ∀ allowed, HandlerSafe (policy item) runtime allowed →
        runtime.wpB absent (goals.holds item runtime allowed) world actual)) :=
    { formula := .and (.all (.inr next) (.imp bounds presentCase.formula)) absentCase.formula
      sound := fun valuation item ready runtime world valid =>
        ⟨fun index actual realized allowed safe => by
          let extended := valuation.bind next index.n
          have agree : ∀ key, key < next → valuation key = extended key := by
            intro key inside
            have different : key ≠ next := Nat.ne_of_lt inside
            simp only [extended, Frag.Assignment.bind, different, ↓reduceIte]
          have ready' := (context.stable valuation extended item agree).mp ready
          have realized' := (symbols.realizes_congr next bounded valuation extended agree world world actual).mp realized
          have fresh : values extended world (.inr next) = index.n := Invarianten.Elim.Korrekt.bind_same valuation next index.n
          have withinBounds : bounds.denote (values extended world) := by
            change 0 ≤ values extended world (.inr next) ∧ values extended world (.inr next) ≤ count - 1
            rw [fresh]
            exact ⟨index.lo_le, index.le_hi⟩
          have body := valid.1 index.n
          rw [← values_bind] at body
          exact presentCase.sound extended item ready' runtime world (body withinBounds) (.cons index actual)
            ⟨Invarianten.Elim.Korrekt.bind_same valuation next index.n, realized'⟩ allowed safe,
         absentCase.sound valuation item ready runtime world valid.2⟩ }
  (both.read Λ expression.orte).map (fun valuation item runtime world ready actual realized allowed safe => by
    have current := (symbols.realizes_world actual valuation world (world.lese Λ expression.orte)).mp realized
    unfold VC.Runtime.wpS
    simp only [execStmtH]
    cases selected : eval (world.lese Λ expression.orte) expression (world.lese Λ expression.orte) actual with
    | some index =>
        have case := ready.1 index actual current allowed safe
        unfold VC.Runtime.wpB at case
        exact (goals.holds_shrink (Ty.index count) item runtime allowed _).mp case
    | none =>
        have case := ready.2 actual current allowed safe
        unfold VC.Runtime.wpB at case
        exact case)

/-- `match` on an option whose value the environment already determines: only the selected block is certified. -/
def knownOptionCondition (policy : A → CallObligation program) {context : Context A next} {l : Bool}
    {Γ : Ctx} {Λ Λ' : List (Res D)} {count : Int}
    (symbols : SymEnv D Nat Γ) (expression : Expr D Γ Λ (.opt count))
    (present : Block D V l (Ty.index count :: Γ) Λ Λ') (absent : Block D V l Γ Λ Λ')
    (goals : Goals (program := program) (S := S) context V Γ)
    (known : { value : Wert D (.opt count) // ∀ valuation world actual, symbols.Realizes valuation world actual →
      eval world expression world actual = value })
    (absentCase : Unit → Except Frag.Refusal (BlockCondition policy absent symbols goals))
    (presentCase : ∀ index, Except Frag.Refusal
      (BlockCondition policy present (.cons (.known index) symbols) (goals.shrink (Ty.index count)))) :
    Except Frag.Refusal (StatementCondition policy (.onOption expression present absent) symbols goals) :=
  match selected : known.val with
  | some index => do
      let pre ← presentCase index
      return (pre.read Λ expression.orte).map (fun valuation item runtime world ready actual realized allowed safe => by
        have current := (symbols.realizes_world actual valuation world (world.lese Λ expression.orte)).mp realized
        have case := ready (.cons index actual) ⟨rfl, current⟩ allowed safe
        unfold VC.Runtime.wpS
        simp only [execStmtH]
        rw [known.property valuation _ actual current, selected]
        unfold VC.Runtime.wpB at case
        exact (goals.holds_shrink (Ty.index count) item runtime allowed _).mp case)
  | none => do
      let pre ← absentCase ()
      return (pre.read Λ expression.orte).map (fun valuation item runtime world ready actual realized allowed safe => by
        have current := (symbols.realizes_world actual valuation world (world.lese Λ expression.orte)).mp realized
        have case := ready actual current allowed safe
        unfold VC.Runtime.wpS
        simp only [execStmtH]
        rw [known.property valuation _ actual current, selected]
        unfold VC.Runtime.wpB at case
        exact case)

/-- `match` on an option: the selected block when the value is known, otherwise the `Some` block once over a fresh
    bounded index and the absent block. -/
def optionDispatch (policy : A → CallObligation program) {context : Context A next} {l : Bool}
    {Γ : Ctx} {Λ Λ' : List (Res D)} {count : Int}
    (symbols : SymEnv D Nat Γ) (expression : Expr D Γ Λ (.opt count))
    (present : Block D V l (Ty.index count :: Γ) Λ Λ') (absent : Block D V l Γ Λ Λ')
    (goals : Goals (program := program) (S := S) context V Γ)
    (absentCase : Unit → Except Frag.Refusal (BlockCondition policy absent symbols goals))
    (presentCase : ∀ index, Except Frag.Refusal
      (BlockCondition policy present (.cons (.known index) symbols) (goals.shrink (Ty.index count))))
    (bounded : symbols.Bounded next)
    (presentSymbolic : Unit → Except Frag.Refusal
      (BlockCondition (context := context.weaken (Nat.le_succ next)) policy present
        (.cons (.integer (.var next)) symbols) ((goals.weaken (Nat.le_succ next)).shrink (Ty.index count)))) :
    Except Frag.Refusal (StatementCondition policy (.onOption expression present absent) symbols goals) :=
  match knownValue? expression symbols with
  | some known => knownOptionCondition policy symbols expression present absent goals known absentCase presentCase
  | none => do
      let missing ← absentCase ()
      let some ← presentSymbolic ()
      return symbolicOptionCondition policy symbols bounded expression present absent goals missing some

/-- What the arms of a tagged dispatch must certify: for every value of the tagged type, the arm it selects. -/
abbrev TagTarget (policy : A → CallObligation program) {context : Context A next} {l : Bool}
    {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option Ty)}
    (arms : Arms D V l Γ Λ Λ' cs) (symbols : SymEnv D Nat Γ)
    (goals : Goals (program := program) (S := S) context V Γ) :
    Frag.Assignment Nat → A → VC.Runtime program (fun _ => []) S → World D → Prop :=
  fun valuation item runtime world => ∀ actual, symbols.Realizes valuation world actual → ∀ allowed,
    HandlerSafe (policy item) runtime allowed → ∀ value : Wert D (.sum cs),
      goals.holds item runtime allowed
        (execArmsH S runtime.oracle runtime.environment runtime.passes runtime.calls arms value world actual)

def tagNil (policy : A → CallObligation program) {context : Context A next} {l : Bool}
    {Γ : Ctx} {Λ : List (Res D)} (symbols : SymEnv D Nat Γ)
    (goals : Goals (program := program) (S := S) context V Γ) :
    Certificate context (TagTarget policy (.nil : Arms D V l Γ Λ Λ []) symbols goals) where
  formula := .tru
  sound := fun _ _ _ _ _ _ _ _ _ _ value => value.1.elim0

/-- An arm without payload: its block is certified once. -/
def tagNone (policy : A → CallObligation program) {context : Context A next} {l : Bool}
    {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option Ty)}
    {first : Block D V l (ArmCtx Γ none) Λ Λ'} {rest : Arms D V l Γ Λ Λ' cs}
    (symbols : SymEnv D Nat Γ) (goals : Goals (program := program) (S := S) context V Γ)
    (head : BlockCondition policy (show Block D V l Γ Λ Λ' from first) symbols goals)
    (tail : Certificate context (TagTarget policy rest symbols goals)) :
    Certificate context (TagTarget policy (Arms.cons first rest) symbols goals) where
  formula := .and head.formula tail.formula
  sound := fun valuation item present runtime world valid actual realized allowed safe value => by
    have parts : head.formula.denote (values valuation world) ∧ tail.formula.denote (values valuation world) := valid
    match value with
    | ⟨⟨0, _⟩, _⟩ =>
        exact head.sound valuation item present runtime world parts.1 actual realized allowed safe
    | ⟨⟨i + 1, bound⟩, payload⟩ =>
        exact tail.sound valuation item present runtime world parts.2 actual realized allowed safe
          ⟨⟨i, Nat.lt_of_succ_lt_succ bound⟩, payload⟩

/-- An arm with a payload of type `τ`: its block is certified for every payload of the complete domain. -/
def tagSome (policy : A → CallObligation program) {context : Context A next} {l : Bool}
    {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option Ty)} {τ : Ty}
    {first : Block D V l (ArmCtx Γ (some τ)) Λ Λ'} {rest : Arms D V l Γ Λ Λ' cs}
    (symbols : SymEnv D Nat Γ) (goals : Goals (program := program) (S := S) context V Γ)
    (domain : Invarianten.VC.LocalDomain D τ)
    (head : Certificate context (fun valuation item (runtime : VC.Runtime program (fun _ => []) S) world =>
      ∀ payload ∈ domain.values, ∀ actual, symbols.Realizes valuation world actual → ∀ allowed,
        HandlerSafe (policy item) runtime allowed →
        runtime.wpB (show Block D V l (τ :: Γ) Λ Λ' from first) ((goals.shrink τ).holds item runtime allowed) world
          (.cons payload actual)))
    (tail : Certificate context (TagTarget policy rest symbols goals)) :
    Certificate context (TagTarget policy (Arms.cons first rest) symbols goals) where
  formula := .and head.formula tail.formula
  sound := fun valuation item present runtime world valid actual realized allowed safe value => by
    have parts : head.formula.denote (values valuation world) ∧ tail.formula.denote (values valuation world) := valid
    match value with
    | ⟨⟨0, _⟩, payload⟩ =>
        have case := head.sound valuation item present runtime world parts.1 payload (domain.complete payload)
          actual realized allowed safe
        unfold VC.Runtime.wpB at case
        exact (goals.holds_shrink τ item runtime allowed _).mp case
    | ⟨⟨i + 1, bound⟩, payload⟩ =>
        exact tail.sound valuation item present runtime world parts.2 actual realized allowed safe
          ⟨⟨i, Nat.lt_of_succ_lt_succ bound⟩, payload⟩

/-- An arm with a payload of type `τ` whose domain is not enumerated: its block is certified once for an
    unobserved payload, so it holds for every payload. -/
def tagSomeUnobserved (policy : A → CallObligation program) {context : Context A next} {l : Bool}
    {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option Ty)} {τ : Ty}
    {first : Block D V l (ArmCtx Γ (some τ)) Λ Λ'} {rest : Arms D V l Γ Λ Λ' cs}
    (symbols : SymEnv D Nat Γ) (goals : Goals (program := program) (S := S) context V Γ)
    (head : BlockCondition policy (show Block D V l (τ :: Γ) Λ Λ' from first) (.cons .unobserved symbols)
      (goals.shrink τ))
    (tail : Certificate context (TagTarget policy rest symbols goals)) :
    Certificate context (TagTarget policy (Arms.cons first rest) symbols goals) where
  formula := .and head.formula tail.formula
  sound := fun valuation item present runtime world valid actual realized allowed safe value => by
    have parts : head.formula.denote (values valuation world) ∧ tail.formula.denote (values valuation world) := valid
    match value with
    | ⟨⟨0, _⟩, payload⟩ =>
        have case := head.sound valuation item present runtime world parts.1 (.cons payload actual)
          ⟨trivial, realized⟩ allowed safe
        unfold VC.Runtime.wpB at case
        exact (goals.holds_shrink τ item runtime allowed _).mp case
    | ⟨⟨i + 1, bound⟩, payload⟩ =>
        exact tail.sound valuation item present runtime world parts.2 actual realized allowed safe
          ⟨⟨i, Nat.lt_of_succ_lt_succ bound⟩, payload⟩

/-- The arm with a payload, from one block certificate per payload of the complete domain. -/
def tagSomeCases (policy : A → CallObligation program) {context : Context A next} {l : Bool}
    {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option Ty)} {τ : Ty}
    {first : Block D V l (ArmCtx Γ (some τ)) Λ Λ'} {rest : Arms D V l Γ Λ Λ' cs}
    (symbols : SymEnv D Nat Γ) (goals : Goals (program := program) (S := S) context V Γ)
    (domain : Invarianten.VC.LocalDomain D τ)
    (tail : Certificate context (TagTarget policy rest symbols goals))
    (compile : ∀ payload, Except Frag.Refusal
      (BlockCondition policy (show Block D V l (τ :: Γ) Λ Λ' from first) (.cons (.known payload) symbols)
        (goals.shrink τ))) :
    Except Frag.Refusal (Certificate context (TagTarget policy (Arms.cons first rest) symbols goals)) := do
  let head ← everyValue
    (fun payload valuation item (runtime : VC.Runtime program (fun _ => []) S) world =>
      ∀ actual, symbols.Realizes valuation world actual → ∀ allowed, HandlerSafe (policy item) runtime allowed →
        runtime.wpB (show Block D V l (τ :: Γ) Λ Λ' from first) ((goals.shrink τ).holds item runtime allowed) world
          (.cons payload actual))
    (fun payload => do
      let pre ← compile payload
      return pre.map (fun _ _ _ _ ready actual realized allowed safe =>
        ready (.cons payload actual) ⟨rfl, realized⟩ allowed safe))
    domain.values
  return tagSome policy symbols goals domain head tail

/-- An arm with a payload: every payload of the complete domain when it fits the budget, otherwise once for an
    unobserved payload. -/
def tagSomeDispatch (policy : A → CallObligation program) {context : Context A next} {l : Bool}
    {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option Ty)} {τ : Ty}
    {first : Block D V l (ArmCtx Γ (some τ)) Λ Λ'} {rest : Arms D V l Γ Λ Λ' cs}
    (symbols : SymEnv D Nat Γ) (goals : Goals (program := program) (S := S) context V Γ) (expansion : Nat)
    (tail : Certificate context (TagTarget policy rest symbols goals))
    (compileKnown : ∀ payload, Except Frag.Refusal
      (BlockCondition policy (show Block D V l (τ :: Γ) Λ Λ' from first) (.cons (.known payload) symbols)
        (goals.shrink τ)))
    (compileUnobserved : Unit → Except Frag.Refusal
      (BlockCondition policy (show Block D V l (τ :: Γ) Λ Λ' from first) (.cons .unobserved symbols)
        (goals.shrink τ))) :
    Except Frag.Refusal (Certificate context (TagTarget policy (Arms.cons first rest) symbols goals)) :=
  match Invarianten.VC.finiteDomain (D := D) expansion τ with
  | .ok domain => tagSomeCases policy symbols goals domain tail compileKnown
  | .error _ => do
      let head ← compileUnobserved ()
      return tagSomeUnobserved policy symbols goals head tail

end Gabbro.Grammatik.Vertraege.Pruefer.Symbolic
