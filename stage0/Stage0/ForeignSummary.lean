module

public import Grammatik.Logik.Vertraege.Pruefer.Unit
public import Grammatik.Logik.Invarianten.Frag.Symbolic.Current
public import Grammatik.Logik.Ruf.FremdRuf.T5
public import Grammatik.Parser.Elab.UebersetzeAllg3.Measures.Export

@[expose] public section

namespace Gabbro.Stage0

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze Gabbro.Grammatik.Parser.UebersetzeAllg

variable {D : Deklaration} {params : Ctx} {result : Option Ty}

/-- An executable result predicate denotes exactly the projection of the
    original typed contract post over its entry world and arguments. -/
structure ResultSummary (post : Expr D (ErgCtx params result) [] .bool) where
  expression : Expr D (ErgCtx [] result) [] .bool
  exactPost : ∀ world value, eval world expression world (ergEnv result value .nil) = true ↔
    ∃ (old : World D) (arguments : Env D params),
      eval old post world (ergEnv result value arguments) = true

mutual
/-- Construct a typed value for projection, including an empty aggregate
    even when its element type is uninhabited. -/
def summaryValue : (ty : Ty) → Option (Wert D ty)
  | .int lo hi => einpassen (D := D) (fun _ => none) (.int lo hi) lo
  | .bool => some false
  | .opt _ => some none
  | .ptr _ => some ()
  | .ref _ => some (Val.vonZelle 0)
  | .why 0 => none
  | .why (n + 1) => some ⟨0, Nat.zero_lt_succ n⟩
  | .str n => some ⟨[], Nat.zero_le n⟩
  | .arr _ 0 => some Fin.elim0
  | .arr ty (n + 1) => (summaryValue ty).map (fun value => fun _ : Fin (n + 1) => value)
  | .prod _ fields => summaryFields fields
  | _ => none
termination_by ty => sizeOf ty

def summaryFields : (fields : List Ty) → Option (ProdVal D.Fn D.passt fields)
  | [] => some ()
  | ty :: rest => do
    let value ← summaryValue ty
    let tail ← summaryFields rest
    return (value, tail)
termination_by fields => sizeOf fields
end

/-- A true post projects to true only if the original argument context
    has a value. Every constructed environment retains its declared types. -/
def summaryArguments : (params : Ctx) → Option (Env D params)
  | [] => some .nil
  | ty :: rest => do
    let value ← summaryValue ty
    return .cons value (← summaryArguments rest)

/-- The projected expression has the result as its only local. Its
    denotation agrees for every argument environment and entry world. -/
structure ResultOnly {returnType ty : Ty} (source : Expr D (returnType :: params) [] ty) where
  term : Expr D [returnType] [] ty
  exactValue : ∀ old world value arguments,
    eval old source world (.cons value arguments) = eval world term world (.cons value .nil)

def checkResultOnly {returnType ty : Ty} (source : Expr D (returnType :: params) [] ty) :
    Except String (ResultOnly source) :=
  match source with
  | .var .here => .ok ⟨.var .here, fun _ _ _ _ => rfl⟩
  | .lit n => .ok ⟨.lit n, fun _ _ _ _ => rfl⟩
  | .fls => .ok ⟨.fls, fun _ _ _ _ => rfl⟩
  | .tru => .ok ⟨.tru, fun _ _ _ _ => rfl⟩
  | .glob g allowed => .ok ⟨.glob g allowed, fun _ _ _ _ => rfl⟩
  | .strLit bytes fits => .ok ⟨.strLit bytes fits, fun _ _ _ _ => rfl⟩
  | .widen lo hi expr => do
    let pureExpr ← checkResultOnly expr
    return ⟨.widen lo hi pureExpr.term, fun old world value args => by
      simp only [eval, pureExpr.exactValue old world value args] <;> rfl⟩
  | .add lhs rhs => do
    let a ← checkResultOnly lhs
    let b ← checkResultOnly rhs
    return ⟨.add a.term b.term, fun old world value args => by
      simp only [eval, a.exactValue old world value args, b.exactValue old world value args] <;> rfl⟩
  | .sub lhs rhs => do
    let a ← checkResultOnly lhs
    let b ← checkResultOnly rhs
    return ⟨.sub a.term b.term, fun old world value args => by
      simp only [eval, a.exactValue old world value args, b.exactValue old world value args] <;> rfl⟩
  | .mul lhs rhs => do
    let a ← checkResultOnly lhs
    let b ← checkResultOnly rhs
    return ⟨.mul a.term b.term, fun old world value args => by
      simp only [eval, a.exactValue old world value args, b.exactValue old world value args] <;> rfl⟩
  | .neg operand => do
    let projected ← checkResultOnly operand
    return ⟨.neg projected.term, fun old world value args => by
      simp only [eval, projected.exactValue old world value args] <;> rfl⟩
  | .lt lhs rhs => do
    let a ← checkResultOnly lhs
    let b ← checkResultOnly rhs
    return ⟨.lt a.term b.term, fun old world value args => by
      simp only [eval, a.exactValue old world value args, b.exactValue old world value args] <;> rfl⟩
  | .le lhs rhs => do
    let a ← checkResultOnly lhs
    let b ← checkResultOnly rhs
    return ⟨.le a.term b.term, fun old world value args => by
      simp only [eval, a.exactValue old world value args, b.exactValue old world value args] <;> rfl⟩
  | .eq lhs rhs => do
    let a ← checkResultOnly lhs
    let b ← checkResultOnly rhs
    return ⟨.eq a.term b.term, fun old world value args => by
      simp only [eval, a.exactValue old world value args, b.exactValue old world value args] <;> rfl⟩
  | .and lhs rhs => do
    let a ← checkResultOnly lhs
    let b ← checkResultOnly rhs
    return ⟨.and a.term b.term, fun old world value args => by
      simp only [eval, a.exactValue old world value args, b.exactValue old world value args] <;> rfl⟩
  | .or lhs rhs => do
    let a ← checkResultOnly lhs
    let b ← checkResultOnly rhs
    return ⟨.or a.term b.term, fun old world value args => by
      simp only [eval, a.exactValue old world value args, b.exactValue old world value args] <;> rfl⟩
  | .not expr => do
    let pureExpr ← checkResultOnly expr
    return ⟨.not pureExpr.term, fun old world value args => by
      simp only [eval, pureExpr.exactValue old world value args] <;> rfl⟩
  | .prodGet operand field => do
    let projected ← checkResultOnly operand
    return ⟨.prodGet projected.term field, fun old world value args => by
      simp only [eval, projected.exactValue old world value args] <;> rfl⟩
  | .arrGet operand index => do
    let projected ← checkResultOnly operand
    let selected ← checkResultOnly index
    return ⟨.arrGet projected.term selected.term, fun old world value args => by
      simp only [eval, projected.exactValue old world value args, selected.exactValue old world value args] <;> rfl⟩
  | .strLen operand => do
    let projected ← checkResultOnly operand
    return ⟨.strLen projected.term, fun old world value args => by
      simp only [eval, projected.exactValue old world value args] <;> rfl⟩
  | .strGet operand index => do
    let projected ← checkResultOnly operand
    let selected ← checkResultOnly index
    return ⟨.strGet projected.term selected.term, fun old world value args => by
      simp only [eval, projected.exactValue old world value args, selected.exactValue old world value args] <;> rfl⟩
  | .strEq lhs rhs => do
    let a ← checkResultOnly lhs
    let b ← checkResultOnly rhs
    return ⟨.strEq a.term b.term, fun old world value args => by
      simp only [eval, a.exactValue old world value args, b.exactValue old world value args] <;> rfl⟩
  | _ => .error "foreign post summary: unsupported operation, argument or entry-memory read"

/-- A field of a result record is still the same typed field in the
    projected contract. The proof covers every parameter context. -/
theorem resultFieldProjection_erfuellbar {name : Nat} {fields : List Ty} {part : Ty}
    (field : FieldAt fields part) :
    let source : Expr D (.prod name fields :: params) [] part := .prodGet (.var .here) field
    (checkResultOnly source).toOption.map (·.term) = some (.prodGet (.var .here) field) := by
  simp only [checkResultOnly, bind, Except.bind, pure, Except.pure, Except.toOption, Option.map_some]

/-- A parameterless post in the current-world fragment already has the
    required result context. The old world is irrelevant by the expression
    checker's proof, and the only argument environment is empty. -/
def checkResultSummary (params : Ctx) (result : Option Ty)
    (post : Expr D (ErgCtx params result) [] .bool) :
    Except String (ResultSummary post) :=
  match params, result, post with
  | _, _, .fls => .ok ⟨.fls, fun _ _ => by
    constructor
    · intro impossible
      cases impossible
    · rintro ⟨_, _, impossible⟩
      cases impossible⟩
  | [], _, expression => do
    let current ← (Vertraege.Pruefer.currentOnly expression).mapError
      (fun refusal => "foreign post summary: " ++ refusal.message)
    pure ⟨expression, fun world value => by
      constructor
      · intro holds
        exact ⟨world, .nil, holds⟩
      · rintro ⟨old, arguments, holds⟩
        cases arguments
        exact (current.down old world _).symm ▸ holds⟩
  | first :: rest, _, .tru => do
    let some arguments := summaryArguments (D := D) (first :: rest)
      | .error "foreign post summary needs an inhabited argument context"
    pure ⟨.tru, fun world _ => ⟨fun _ => ⟨world, arguments, rfl⟩, fun _ => rfl⟩⟩
  | first :: rest, some _, expression => do
    let projected ← checkResultOnly expression
    let some args := summaryArguments (D := D) (first :: rest)
      | .error "foreign post summary needs an inhabited argument context"
    pure ⟨projected.term, fun world value => by
      constructor
      · intro holds
        exact ⟨world, args, (projected.exactValue world world value args).trans holds⟩
      · rintro ⟨old, arguments, holds⟩
        exact (projected.exactValue old world value arguments).symm.trans holds⟩
  | _ :: _, none, _ => .error "foreign post summary needs argument projection"

/-- The model checker's source expressions and exact post projection
    come from the same canonical foreign contracts. -/
structure ForeignSummary (P : Programm D) where
  predicates : AxEns D
  sources : Vertraege.Pruefer.AxiomSources predicates
  exactPost : ∀ item world value, predicates item world value = true ↔
    ∃ old arguments, AxNach P.axVertrag item old arguments world value

def checkForeignSummary (u : UProg) (P : Programm (declOf u)) : Except String (ForeignSummary P) := do
  let entries ← Gabbro.Grammatik.Parser.Measures.collect u.axs.length
    (fun a => ResultSummary (P.axVertrag a).post)
    (fun a => checkResultSummary ((declOf u).aparams a) ((declOf u).aerg a) (P.axVertrag a).post)
  let predicate : AxEns (declOf u) := fun a world value =>
    eval world (entries a).expression world (ergEnv ((declOf u).aerg a) value .nil)
  pure {
    predicates := predicate
    sources := {
      items := List.finRange u.axs.length
      complete := List.mem_finRange
      resources := fun _ => []
      expression := fun a => (entries a).expression
      correct := fun _ _ _ => rfl }
    exactPost := fun a => (entries a).exactPost }

end Gabbro.Stage0
