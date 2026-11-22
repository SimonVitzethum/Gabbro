module

public import Grammatik.Nebenlaeufigkeit.Async.Segment.Values

namespace Gabbro.Grammatik.Async.Representation
open Segment

variable {D : Deklaration} {types : TypeResolution}

/-- Dead locals have the absent tag. A live local must exist and materialise
    at its declaration's exact ordinary type; failure is explicit. -/
@[expose] public def encodeSlots (D : Deklaration) (types : TypeResolution)
    (live : List String) (frame : Frame (Value D)) :
    (fields : List (String × Parser.STyp)) →
      Option (ProdVal D.Fn D.passt
        (fields.map fun field => Ty.sum [none, some (types.ordinary field.2)]))
  | [] => some ()
  | (name, sourceType) :: fields => do
      let slot ← if name ∈ live then do
          let value ← frame.values.lookup name
          let value ← valueAt D (types.ordinary sourceType) value
          pure (presentValue D (types.ordinary sourceType) value)
        else some (absentValue D (types.ordinary sourceType))
      let rest ← encodeSlots D types live frame fields
      pure (slot, rest)

/-- Structural frame agreement, independent of the encoder's computation. -/
public inductive SlotsRep (D : Deklaration) (types : TypeResolution)
    (live : List String) (frame : Frame (Value D)) :
    (fields : List (String × Parser.STyp)) →
    ProdVal D.Fn D.passt
      (fields.map fun field => Ty.sum [none, some (types.ordinary field.2)]) → Prop where
  | nil : SlotsRep D types live frame [] ()
  | dead (unused : name ∉ live) (tail : SlotsRep D types live frame fields rest) :
      SlotsRep D types live frame ((name, sourceType) :: fields)
        (absentValue D (types.ordinary sourceType), rest)
  | live (used : name ∈ live) (found : frame.values.lookup name = some value)
      (typed : valueAt D (types.ordinary sourceType) value = some ordinary)
      (tail : SlotsRep D types live frame fields rest) :
      SlotsRep D types live frame ((name, sourceType) :: fields)
        (presentValue D (types.ordinary sourceType) ordinary, rest)

public theorem slotsRep_encoded (types : TypeResolution) (live : List String)
    (frame : Frame (Value D)) (fields : List (String × Parser.STyp))
    (slots : ProdVal D.Fn D.passt
      (fields.map fun field => Ty.sum [none, some (types.ordinary field.2)]))
    (represented : SlotsRep D types live frame fields slots) :
    encodeSlots D types live frame fields = some slots := by
  induction represented <;>
    simp only [encodeSlots, *, ite_true, ite_false, Option.bind_eq_bind,
      Option.bind_some, Option.pure_def] <;> rfl

/-- Generate the ordinary product arguments for the smaller live set.
    Retained slots are projected at their declared types. Dead slots
    use the absent tag, which has no source payload. -/
@[expose] public def trimSlotArgs {Γ : Ctx} {Λ : List (Res D)} (types : TypeResolution)
    (keep : List String) : (fields : List (String × Parser.STyp)) →
    (∀ {τ}, FieldAt (slotTypes types fields) τ → Expr D Γ Λ τ) →
    Args D Γ Λ (slotTypes types fields)
  | [], _ => .nil
  | (name, sourceType) :: rest, project =>
    let type := types.ordinary sourceType
    let argument := if name ∈ keep then project .head
      else Expr.case [none, some type] ⟨0, Nat.zero_lt_succ 1⟩ .empty
    .cons argument (trimSlotArgs types keep rest (fun field => project (.tail field)))

public theorem trimSlotArgs_reads {Γ : Ctx} {Λ : List (Res D)} (types : TypeResolution)
    (keep : List String) (fields : List (String × Parser.STyp))
    (project : ∀ {τ}, FieldAt (slotTypes types fields) τ → Expr D Γ Λ τ)
    (localRead : ∀ {τ} (field : FieldAt (slotTypes types fields) τ), (project field).orte = []) :
    (trimSlotArgs types keep fields project).orte = [] := by
  induction fields with
  | nil => rfl
  | cons field rest ih =>
    obtain ⟨name, sourceType⟩ := field
    have tail := ih (fun field => project (.tail field)) (fun field => localRead (.tail field))
    by_cases live : name ∈ keep
    · simp only [trimSlotArgs, live, ite_true, Args.orte]
      rw [localRead .head, tail, List.nil_append]
    · simp only [trimSlotArgs, live, ite_false, Args.orte, Expr.orte, NutzlastExpr.orte, List.nil_append]
      exact tail

/-- The generated arguments preserve exactly the represented fields
    required by the next phase. The projection function is tied to the
    original typed record by the ordinary expression evaluator. -/
public theorem trimSlotArgs_rep {Γ : Ctx} {Λ : List (Res D)} {oldLive keep : List String}
    {frame : Frame (Value D)}
    (kept : ∀ name ∈ keep, name ∈ oldLive) (entry world : World D) (env : Env D Γ)
    {fields : List (String × Parser.STyp)} {payload : ProdVal D.Fn D.passt (slotTypes types fields)}
    (represented : SlotsRep D types oldLive frame fields payload) :
    ∀ (project : ∀ {τ}, FieldAt (slotTypes types fields) τ → Expr D Γ Λ τ),
      (∀ {τ} (field : FieldAt (slotTypes types fields) τ), eval entry (project field) world env = prodGetW field payload) →
      SlotsRep D types keep frame fields (evalProd entry (trimSlotArgs types keep fields project) world env) := by
  induction represented with
  | nil => exact fun _ _ => .nil
  | @dead name fields rest sourceType unused tail ih =>
    intro project exactField
    have removed : name ∉ keep := fun member => unused (kept name member)
    have following := ih (fun field => project (.tail field)) (fun field => exactField (.tail field))
    simp only [trimSlotArgs, removed, ite_false, evalProd, eval, evalNutz]
    exact .dead removed following
  | @live name value sourceType ordinary fields rest needed found typed tail ih =>
    intro project exactField
    have following := ih (fun field => project (.tail field)) (fun field => exactField (.tail field))
    by_cases retained : name ∈ keep
    · simp only [trimSlotArgs, retained, ite_true, evalProd]
      rw [exactField .head]
      exact .live retained found typed following
    · simp only [trimSlotArgs, retained, ite_false, evalProd, eval, evalNutz]
      exact .dead retained following

/-- Rebuild the canonical frame from its saved local, clearing exactly
    the slots outside the selected live set. -/
@[expose] public def trimFrameExpr {Γ : Ctx} {Λ : List (Res D)} (types : TypeResolution)
    (f : AsyncFn) (keep : List String) (saved : Var Γ (frameType types f)) :
    Expr D Γ Λ (frameType types f) :=
  Expr.prod (types.recordName [0])
    (trimSlotArgs types keep (f.params ++ f.fields) (fun field => Expr.prodGet (.var saved) field))

public theorem trimFrameExpr_rep {Γ : Ctx} {Λ : List (Res D)} {f : AsyncFn}
    {frame : Frame (Value D)} {oldLive keep : List String}
    (saved : Var Γ (frameType types f)) (kept : ∀ name ∈ keep, name ∈ oldLive)
    (entry world : World D) (env : Env D Γ)
    (represented : SlotsRep D types oldLive frame (f.params ++ f.fields) (env.get saved)) :
    let expression : Expr D Γ Λ (frameType types f) := trimFrameExpr types f keep saved
    expression.orte = [] ∧
      SlotsRep D types keep frame (f.params ++ f.fields) (eval entry expression world env) := by
  refine ⟨?_, ?_⟩
  · exact trimSlotArgs_reads types keep (f.params ++ f.fields) (fun field => Expr.prodGet (.var saved) field)
      (fun _ => rfl)
  · exact trimSlotArgs_rep kept entry world env represented (fun field => Expr.prodGet (.var saved) field)
      (fun _ => rfl)

/-- Only source values live AFTER construction are needed while waiting.
    The awaited destination itself is not initialised until Ready. -/
@[expose] public def liveAt (f : AsyncFn) : Phase → List String
  | Phase.running tag => liveBefore f.result (f.body.drop tag)
  | Phase.waiting tag _ =>
      match f.body.drop tag with
      | Command.await name _ _ :: rest => without name (liveBefore f.result rest)
      | _ => []
  | Phase.cancelled | Phase.completed => []

@[expose] public def encodeFrame (D : Deklaration) (types : TypeResolution)
    (f : AsyncFn) (phase : Phase) (frame : Frame (Value D)) :
    Option (Wert D (frameType types f)) :=
  encodeSlots D types (liveAt f phase) frame (f.params ++ f.fields)

/-- This includes live-name coverage, which a tuple computation alone cannot
    check: a missing declaration is not an uninitialised optional field. -/
public structure FrameRep (D : Deklaration) (types : TypeResolution) (f : AsyncFn)
    (phase : Phase) (frame : Frame (Value D)) (value : Wert D (frameType types f)) : Prop where
  slots : SlotsRep D types (liveAt f phase) frame (f.params ++ f.fields) value
  declared : ∀ name ∈ liveAt f phase, name ∈ fieldNames f
  unique : (fieldNames f).Nodup

public theorem frameRep_encoded (types : TypeResolution) (f : AsyncFn)
    (phase : Phase) (frame : Frame (Value D)) (value : Wert D (frameType types f))
    (represented : FrameRep D types f phase frame value) :
    encodeFrame D types f phase frame = some value :=
  slotsRep_encoded types (liveAt f phase) frame (f.params ++ f.fields) value represented.slots

/-- Authority is the ordinary resource inventory, separate from by-value
    storage. The injective declaration numbering cannot alias two owners. -/
public structure Inventory (D : Deklaration) where
  number : D.Marke → Nat
  injective : ∀ a b, number a = number b → a = b
  owned : Phase → List (D.Marke × Nat)
  unique : ∀ phase, ((owned phase).map Prod.fst).Nodup
  resources : Phase → List (Res D)
  exact : ∀ phase, resources phase = savedResources (owned phase)

@[expose] public def MarksRep (inventory : Inventory D) (phase : Phase)
    (state : State (Value D) (Child D types)) : Prop :=
  state.marks = (inventory.owned phase).map (fun owner => inventory.number owner.1)

public theorem inventory_no_locks (inventory : Inventory D) (phase : Phase) (lock : D.Lock) :
    Res.held lock ∉ inventory.resources phase := by
  rw [inventory.exact phase]
  exact savedResources_no_locks (inventory.owned phase) lock

public theorem inventory_unique (inventory : Inventory D) (phase : Phase) :
    (inventory.resources phase).Nodup := by
  rw [inventory.exact phase]
  exact savedResources_unique (inventory.owned phase) (inventory.unique phase)

end Gabbro.Grammatik.Async.Representation
