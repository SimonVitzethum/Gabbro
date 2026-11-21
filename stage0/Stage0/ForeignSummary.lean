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

/-- A true post projects to true only if the original argument context
    has a value. Construct the typed environment for the common gate inputs. -/
def summaryArguments : (params : Ctx) → Option (Env D params)
  | [] => some .nil
  | .int lo hi :: rest => do
    let value ← einpassen (D := D) (fun _ => none) (.int lo hi) lo
    return .cons value (← summaryArguments rest)
  | .bool :: rest => (summaryArguments rest).map (.cons false)
  | .opt _ :: rest => (summaryArguments rest).map (.cons none)
  | .ptr _ :: rest => (summaryArguments rest).map (.cons ())
  | .ref _ :: rest => (summaryArguments rest).map (.cons (Val.vonZelle 0))
  | _ :: _ => none

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
  | .widen lo hi expr => do
    let pureExpr ← checkResultOnly expr
    return ⟨.widen lo hi pureExpr.term, fun old world value args => by
      simp only [eval, pureExpr.exactValue old world value args]⟩
  | .add lhs rhs => do
    let a ← checkResultOnly lhs
    let b ← checkResultOnly rhs
    return ⟨.add a.term b.term, fun old world value args => by
      simp only [eval, a.exactValue old world value args, b.exactValue old world value args]⟩
  | .sub lhs rhs => do
    let a ← checkResultOnly lhs
    let b ← checkResultOnly rhs
    return ⟨.sub a.term b.term, fun old world value args => by
      simp only [eval, a.exactValue old world value args, b.exactValue old world value args]⟩
  | .lt lhs rhs => do
    let a ← checkResultOnly lhs
    let b ← checkResultOnly rhs
    return ⟨.lt a.term b.term, fun old world value args => by
      simp only [eval, a.exactValue old world value args, b.exactValue old world value args]⟩
  | .le lhs rhs => do
    let a ← checkResultOnly lhs
    let b ← checkResultOnly rhs
    return ⟨.le a.term b.term, fun old world value args => by
      simp only [eval, a.exactValue old world value args, b.exactValue old world value args]⟩
  | .eq lhs rhs => do
    let a ← checkResultOnly lhs
    let b ← checkResultOnly rhs
    return ⟨.eq a.term b.term, fun old world value args => by
      simp only [eval, a.exactValue old world value args, b.exactValue old world value args]⟩
  | .and lhs rhs => do
    let a ← checkResultOnly lhs
    let b ← checkResultOnly rhs
    return ⟨.and a.term b.term, fun old world value args => by
      simp only [eval, a.exactValue old world value args, b.exactValue old world value args]⟩
  | .or lhs rhs => do
    let a ← checkResultOnly lhs
    let b ← checkResultOnly rhs
    return ⟨.or a.term b.term, fun old world value args => by
      simp only [eval, a.exactValue old world value args, b.exactValue old world value args]⟩
  | .not expr => do
    let pureExpr ← checkResultOnly expr
    return ⟨.not pureExpr.term, fun old world value args => by
      simp only [eval, pureExpr.exactValue old world value args]⟩
  | _ => .error "foreign post summary: unsupported operation, argument or entry-memory read"

/-- A parameterless post in the current-world fragment already has the
    required result context. The old world is irrelevant by the expression
    checker's proof, and the only argument environment is empty. -/
def checkResultSummary (params : Ctx) (result : Option Ty)
    (post : Expr D (ErgCtx params result) [] .bool) :
    Except String (ResultSummary post) :=
  match params, result, post with
  | _, _, .fls => .ok ⟨.fls, fun _ _ => by simp only [eval, Bool.false_eq_true, and_false, exists_false]⟩
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
