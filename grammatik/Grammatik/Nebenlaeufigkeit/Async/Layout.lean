module

public import Grammatik.Nebenlaeufigkeit.Async.Regeln
public import Grammatik.Kern.Syntax.Syntax.Teil2
import Lean.Elab.Tactic.Omega

namespace Gabbro.Grammatik.Async

/-- Input of typed reification, after ordinary name/type resolution. A fresh
    injective name supply is required for each originating declaration. The
    front end still owes that resolution; this is not an admission check. -/
public structure TypeResolution where
  recordName : List Nat → Nat
  namesUnique : ∀ a b, recordName a = recordName b → a = b
  ordinary : Parser.STyp → Ty
  childState : String → Ty
  childResult : String → Ty

/-- The optional field schema is shared by frame layout and slot traversal.
    Annotating the source pair keeps its projection independent of elaboration
    of the dependent product value. -/
@[expose] public def slotTypes (types : TypeResolution)
    (fields : List (String × Parser.STyp)) : List Ty :=
  fields.map fun (field : String × Parser.STyp) =>
    Ty.sum [none, some (types.ordinary field.2)]

@[expose] public def frameFields (types : TypeResolution) (f : AsyncFn) : List Ty :=
  slotTypes types (f.params ++ f.fields)

/-- A local has an explicit uninitialised case. Generating a frame never
    invents an inhabitant of an arbitrary source type. Permissions are NOT
    integers in this record: they remain in the canonical resource index Λ. -/
@[expose] public def frameType (types : TypeResolution) (f : AsyncFn) : Ty :=
  .prod (types.recordName [0]) (frameFields types f)

public theorem frameType_eq (types : TypeResolution) (f : AsyncFn) :
    frameType types f = .prod (types.recordName [0]) (frameFields types f) := rfl

/-- A join's result has both component types, in source order. Paths identify
    nested joins statically; no recursive or dynamically typed runtime node
    is needed. Different declarations need disjoint name supplies at linking. -/
@[expose] public def taskResultType (types : TypeResolution) (path : List Nat) : FutureExpr → Ty
  | .call name _ => types.childResult name
  | .join left right => .prod (types.recordName (3 :: path))
      [taskResultType types (0 :: path) left, taskResultType types (1 :: path) right]

/-- Each child has an active/ready sum. A partial join stores both updated
    children, including the cached Ready side, by value. Its shape is bounded
    by the source FutureExpr, unlike the unrestricted semantic Task type. -/
@[expose] public def taskStorageType (types : TypeResolution) (path : List Nat) : FutureExpr → Ty
  | .call name _ => .sum [some (types.childState name), some (types.childResult name)]
  | .join left right => .sum [some (.prod (types.recordName (4 :: path))
      [taskStorageType types (0 :: path) left, taskStorageType types (1 :: path) right]),
      some (taskResultType types path (.join left right))]

/-- Names here describe code positions, never saved continuations. -/
public inductive Phase where
  | cancelled
  | completed
  | running (tag : Nat)
  | waiting (tag : Nat) (future : FutureExpr)

@[expose] public def commandPhases (tag : Nat) : List Command → List Phase
  | [] => [.running tag]
  | .bind _ _ _ :: rest => .running tag :: commandPhases (tag + 1) rest
  | .await _ future _ :: rest =>
      .running tag :: .waiting tag future :: commandPhases (tag + 1) rest

@[expose] public def phases (f : AsyncFn) : List Phase :=
  .cancelled :: .completed :: commandPhases 0 f.body

/-- Every case carries a typed product, including the empty Cancelled case.
    A completed state retains the result but no frame or child storage. -/
@[expose] public def phaseType (types : TypeResolution) (f : AsyncFn) : Phase → Ty
  | .cancelled => .prod (types.recordName [6]) []
  | .completed => .prod (types.recordName [5]) [types.ordinary f.resultType]
  | .running _ => frameType types f
  | .waiting tag future => .prod (types.recordName [2, tag])
      [frameType types f, taskStorageType types [tag] future]

@[expose] public def stateCases (types : TypeResolution) (f : AsyncFn) : List (Option Ty) :=
  (phases f).map fun phase => some (phaseType types f phase)

/-- A nominal record around the closed phase sum, built ONLY from existing
    Ty forms. Finite case selection makes out-of-range tags unrepresentable. -/
@[expose] public def stateType (types : TypeResolution) (f : AsyncFn) : Ty :=
  .prod (types.recordName [1]) [.sum (stateCases types f)]

/-- Construct a state using the chosen phase's exact payload schema. This
    single constructor serves running, waiting, completed and cancelled
    transitions without runtime casts or a dynamically typed frame. -/
@[expose] public def stateExpr (types : TypeResolution) (f : AsyncFn)
    {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
    (phase : Fin (stateCases types f).length)
    (payload : NutzlastExpr D Γ Λ ((stateCases types f).get phase)) :
    Expr D Γ Λ (stateType types f) :=
  .prod (types.recordName [1])
    (.cons (.case (stateCases types f) phase payload) .nil)

/-- Select a Running case in command order. An await inserts a Waiting
    case before the next command, so the command offset alone is not a tag. -/
@[expose] public def commandRunningIndex (base : Nat) : (body : List Command) →
    (offset : Nat) → offset ≤ body.length →
    {index : Fin (commandPhases base body).length //
      (commandPhases base body).get index = .running (base + offset)}
  | [], 0, _ => ⟨⟨0, Nat.zero_lt_succ _⟩, rfl⟩
  | [], offset + 1, valid => False.elim (Nat.not_succ_le_zero offset valid)
  | .bind _ _ _ :: _, 0, _ => ⟨⟨0, Nat.zero_lt_succ _⟩, rfl⟩
  | .await _ _ _ :: _, 0, _ => ⟨⟨0, Nat.zero_lt_succ _⟩, rfl⟩
  | .bind _ _ _ :: rest, offset + 1, valid =>
    let next := commandRunningIndex (base + 1) rest offset (Nat.le_of_succ_le_succ valid)
    ⟨next.val.succ, by
      have tag : base + 1 + offset = base + (offset + 1) := by omega
      change (commandPhases (base + 1) rest).get next.val = .running (base + (offset + 1))
      exact next.property.trans (congrArg Phase.running tag)⟩
  | .await _ _ _ :: rest, offset + 1, valid =>
    let next := commandRunningIndex (base + 1) rest offset (Nat.le_of_succ_le_succ valid)
    ⟨next.val.succ.succ, by
      have tag : base + 1 + offset = base + (offset + 1) := by omega
      change (commandPhases (base + 1) rest).get next.val = .running (base + (offset + 1))
      exact next.property.trans (congrArg Phase.running tag)⟩
termination_by structural body _ _ => body

/-- Earlier dispatch slots cannot name the same running command. They
    either belong to an earlier command or are its Waiting case. -/
public theorem commandRunningIndex_first (base : Nat) (body : List Command) (offset : Nat)
    (within : offset ≤ body.length) (before : Fin (commandPhases base body).length)
    (earlier : before.val < (commandRunningIndex base body offset within).val.val) :
    (commandPhases base body).get before ≠ .running (base + offset) := by
  induction body generalizing base offset with
  | nil =>
    have empty : offset = 0 := Nat.eq_zero_of_le_zero within
    subst offset
    exact (Nat.not_lt_zero _ earlier).elim
  | cons command rest ih =>
    cases offset with
    | zero =>
      cases command <;> exact (Nat.not_lt_zero _ earlier).elim
    | succ offset =>
      have smaller := Nat.le_of_succ_le_succ within
      have tag : base + 1 + offset = base + (offset + 1) := by omega
      have head : Phase.running base ≠ .running (base + (offset + 1)) := by
        intro same
        injection same with equal
        omega
      cases command with
      | bind =>
        obtain ⟨position, valid⟩ := before
        cases position with
        | zero => exact head
        | succ position =>
          let next : Fin (commandPhases (base + 1) rest).length := ⟨position, Nat.lt_of_succ_lt_succ valid⟩
          have bound : next.val < (commandRunningIndex (base + 1) rest offset smaller).val.val :=
            Nat.lt_of_succ_lt_succ earlier
          have different := ih (base + 1) offset smaller next bound
          change (commandPhases (base + 1) rest).get next ≠ .running (base + (offset + 1))
          rwa [← tag]
      | await =>
        obtain ⟨position, valid⟩ := before
        cases position with
        | zero => exact head
        | succ position =>
          cases position with
          | zero => intro equal; cases equal
          | succ position =>
            let next : Fin (commandPhases (base + 1) rest).length :=
              ⟨position, Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ valid)⟩
            have bound : next.val < (commandRunningIndex (base + 1) rest offset smaller).val.val :=
              Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ earlier)
            have different := ih (base + 1) offset smaller next bound
            change (commandPhases (base + 1) rest).get next ≠ .running (base + (offset + 1))
            rwa [← tag]

@[expose] public def runningCase (types : TypeResolution) (f : AsyncFn)
    (tag : Nat) (within : tag ≤ f.body.length) :
    {index : Fin (stateCases types f).length // (stateCases types f).get index = some (frameType types f)} :=
  let selected := commandRunningIndex 0 f.body tag within
  let phase : Fin (phases f).length := selected.val.succ.succ
  let index : Fin (stateCases types f).length :=
    ⟨phase.val, by simpa only [stateCases, List.length_map] using phase.isLt⟩
  ⟨index, by
    have mapped : (stateCases types f).get index = some (phaseType types f ((phases f).get phase)) :=
      List.getElem_map (fun p => some (phaseType types f p)) (h := index.isLt)
    exact mapped.trans (congrArg (fun p => some (phaseType types f p)) selected.property)⟩

/-- Generate the typed constructor for a resumed frame at a checked
    program position. The payload remains at its declared frame type. -/
@[expose] public def runningExpr (types : TypeResolution) (f : AsyncFn)
    {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)} (tag : Nat) (within : tag ≤ f.body.length)
    (frame : Expr D Γ Λ (frameType types f)) : Expr D Γ Λ (stateType types f) :=
  let selected := runningCase types f tag within
  stateExpr types f selected.val (selected.property.symm ▸ NutzlastExpr.val frame)

@[expose] public def awaitCount : List Command → Nat
  | [] => 0
  | .bind _ _ _ :: rest => awaitCount rest
  | .await _ _ _ :: rest => awaitCount rest + 1

public theorem commandPhases_length (tag : Nat) (body : List Command) :
    (commandPhases tag body).length = body.length + awaitCount body + 1 := by
  induction body generalizing tag with
  | nil => rfl
  | cons command rest ih =>
    cases command <;> simp only [commandPhases, List.length_cons, awaitCount, ih] <;> omega

public theorem stateCases_length (types : TypeResolution) (f : AsyncFn) :
    (stateCases types f).length = f.body.length + awaitCount f.body + 3 := by
  simp only [stateCases, List.length_map, phases, List.length_cons, commandPhases_length]

/-- Cancellation has a real zero-field payload; it cannot retain a child or
    a value that a later destructor would need. Cleanup must precede it. -/
@[expose] public def cancelledIndex (types : TypeResolution) (f : AsyncFn) :
    Fin (stateCases types f).length :=
  ⟨0, (by simp only [stateCases, phases, List.map_cons, List.length_cons]; omega)⟩

@[expose] public def cancelledExpr (types : TypeResolution) (f : AsyncFn)
    {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)} : Expr D Γ Λ (stateType types f) :=
  stateExpr types f (cancelledIndex types f) (.val (.prod (types.recordName [6]) .nil))

@[expose] public def cancelledValue (types : TypeResolution) (f : AsyncFn) (D : Deklaration) :
    Wert D (stateType types f) := (⟨cancelledIndex types f, ()⟩, ())

/-- The dispatch discriminant is a record projection, never a stack address. -/
@[expose] public def stateDiscriminant (types : TypeResolution) (f : AsyncFn)
    {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
    (state : Expr D Γ Λ (stateType types f)) : Expr D Γ Λ (.sum (stateCases types f)) :=
  .prodGet state .head

end Gabbro.Grammatik.Async
