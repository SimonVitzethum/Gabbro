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

/-- The typed field offset belongs to the declared name even when
    several saved locals have the same ordinary type. -/
public inductive NamedFrameSlot (types : TypeResolution) (name : String) (sourceType : Parser.STyp) :
    (fields : List (String × Parser.STyp)) →
    FieldAt (slotTypes types fields) (.sum [none, some (types.ordinary sourceType)]) → Prop where
  | head : NamedFrameSlot types name sourceType ((name, sourceType) :: rest) .head
  | tail (other : label ≠ name) (slot : NamedFrameSlot types name sourceType rest position) :
      NamedFrameSlot types name sourceType ((label, type) :: rest) (.tail position)

/-- Compute the field address from the very declaration lookup checked
    for the bound value. No caller chooses an offset independently. -/
@[expose] public def frameSlot (types : TypeResolution) (name : String) (sourceType : Parser.STyp) :
    (fields : List (String × Parser.STyp)) → fields.lookup name = some sourceType →
    {pos : FieldAt (slotTypes types fields) (.sum [none, some (types.ordinary sourceType)]) //
      NamedFrameSlot types name sourceType fields pos}
  | [], absent => by cases absent
  | (label, type) :: rest, present =>
    if same : name = label then
      have exactType : type = sourceType := by
        simpa only [List.lookup_cons, same, beq_self_eq_true, ite_true, Option.some.injEq] using present
      by
        subst label
        subst type
        exact ⟨.head, .head⟩
    else
      let selected := frameSlot types name sourceType rest
        (by simpa only [List.lookup_cons, beq_eq_false_iff_ne.mpr same, Bool.false_eq_true, ite_false] using present)
      ⟨.tail selected.val, .tail (Ne.symm same) selected.property⟩

private theorem SlotsRep.save_other_fields {oldLive nextLive : List String} {frame : Frame (Value D)}
    {fields : List (String × Parser.STyp)} {record : ProdVal D.Fn D.passt (slotTypes types fields)}
    (represented : SlotsRep D types oldLive frame fields record)
    (name : String) (value : Value D)
    (absent : name ∉ fields.map Prod.fst)
    (retained : ∀ label, label ≠ name → (label ∈ oldLive ↔ label ∈ nextLive)) :
    SlotsRep D types nextLive (save frame name value) fields record := by
  induction represented with
  | nil => exact .nil
  | @dead label fields rest sourceType unused tail ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at absent
    exact .dead (fun live => unused ((retained label (Ne.symm absent.1)).mpr live)) (ih absent.2)
  | @live label old sourceType ordinary fields rest used found typed tail ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at absent
    have other := Ne.symm absent.1
    exact .live ((retained label other).mp used)
      (by simpa only [save, List.lookup_cons, beq_eq_false_iff_ne.mpr other] using found)
      typed (ih absent.2)

private theorem SlotsRep.save_unobserved {live : List String} {frame : Frame (Value D)}
    {fields : List (String × Parser.STyp)} {record : ProdVal D.Fn D.passt (slotTypes types fields)}
    (represented : SlotsRep D types live frame fields record)
    (name : String) (value : Value D) (unused : name ∉ live) :
    SlotsRep D types live (save frame name value) fields record := by
  induction represented with
  | nil => exact .nil
  | dead absent _ ih => exact .dead absent ih
  | @live label previous sourceType ordinary fields rest needed found typed tail ih =>
    have distinct : label ≠ name := fun equal => unused (equal ▸ needed)
    exact .live needed
      (by simpa only [save, List.lookup_cons, beq_eq_false_iff_ne.mpr distinct] using found) typed ih

/-- Writing the computed named slot preserves the frame relation. The
    other fields retain their previous values and canonical absent tags. -/
public theorem NamedFrameSlot.save_rep {name : String} {sourceType : Parser.STyp}
    {fields : List (String × Parser.STyp)}
    {destination : FieldAt (slotTypes types fields) (.sum [none, some (types.ordinary sourceType)])}
    (named : NamedFrameSlot types name sourceType fields destination)
    {oldLive nextLive : List String} {frame : Frame (Value D)} {value : Value D}
    {ordinary : Wert D (types.ordinary sourceType)}
    (typed : valueAt D (types.ordinary sourceType) value = some ordinary)
    (needed : name ∈ nextLive)
    (retained : ∀ label, label ≠ name → (label ∈ oldLive ↔ label ∈ nextLive))
    (unique : (fields.map Prod.fst).Nodup) :
    ∀ {record : ProdVal D.Fn D.passt (slotTypes types fields)},
      SlotsRep D types oldLive frame fields record →
      SlotsRep D types nextLive (save frame name value) fields
        (prodSetW (F := D.Fn) (passt := D.passt) destination record
          (presentValue D (types.ordinary sourceType) ordinary)) := by
  induction named with
  | head =>
    intro record represented
    simp only [List.map_cons, List.nodup_cons] at unique
    cases represented with
    | dead _ tail =>
      exact .live needed List.lookup_cons_self typed (tail.save_other_fields name value unique.1 retained)
    | live _ _ _ tail =>
      exact .live needed List.lookup_cons_self typed (tail.save_other_fields name value unique.1 retained)
  | tail other slot ih =>
    intro record represented
    simp only [List.map_cons, List.nodup_cons] at unique
    cases represented with
    | dead unused tail => exact .dead (fun live => unused ((retained _ other).mpr live)) (ih unique.2 tail)
    | live used found previous tail =>
      exact .live ((retained _ other).mp used)
        (by simpa only [save, List.lookup_cons, beq_eq_false_iff_ne.mpr other] using found)
        previous (ih unique.2 tail)

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
      rw [localRead .head, List.nil_append]
      exact tail
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

/-- Ordinary G code for a live binding. It evaluates the bound expression
    once, clears dead slots and installs the result at the typed position. -/
@[expose] public def bindFrameBlock {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
    (types : TypeResolution) (f : AsyncFn) (keep : List String)
    (saved : Var Γ (frameType types f))
    (destination : FieldAt (frameFields types f) (.sum [none, some τ]))
    (expression : Expr D Γ Λ τ) : Block D V l Γ Λ Λ :=
  evaluateBlock expression saved
    (saveSlotExpr types f (trimFrameExpr types f keep (.there saved)) destination (.var .here))

/-- Frame maintenance observes only local data. The resulting world is
    the one returned by evaluating the original bound expression. -/
public theorem bindFrameBlock_exec {V : Vertrag D} {l : Bool}
    {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
    (types : TypeResolution) (f : AsyncFn) (keep : List String)
    (saved : Var Γ (frameType types f))
    (destination : FieldAt (frameFields types f) (.sum [none, some τ]))
    (expression : Expr D Γ Λ τ) (oracle : Orakel D) (passes : Nat)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (world : World D) (env : Env D Γ) :
    let answer := evaluateExpression expression world env
    let cleared : Expr D (τ :: Γ) Λ (frameType types f) := trimFrameExpr types f keep (.there saved)
    let updated := prodSetW (F := D.Fn) (passt := D.passt) destination
      (eval answer.2.1 cleared answer.2.1 (.cons answer.1 env)) (presentValue D τ answer.1)
    execBlock oracle passes calls (bindFrameBlock (V := V) (l := l) types f keep saved destination expression) world env =
      .ok answer.2.1 (env.set saved updated) := by
  intro answer cleared updated
  have read : cleared.orte = [] :=
    trimSlotArgs_reads types keep (f.params ++ f.fields) (fun field => Expr.prodGet (.var (.there saved)) field)
      (fun _ => rfl)
  let temporary : Expr D (τ :: Γ) Λ τ := .var .here
  have savedRead : (saveSlotExpr types f cleared destination temporary).orte = [] := by
    simp only [saveSlotExpr, Expr.orte, NutzlastExpr.orte, temporary, List.append_nil]
    exact read
  have noRead (current : World D) : current.lese Λ [] = current := rfl
  have executed := evaluateBlock_exec (V := V) (l := l) oracle passes calls expression saved
    (saveSlotExpr types f cleared destination temporary) world env
  simp only [savedRead, noRead, saveSlotExpr_eval] at executed
  exact executed

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

/-- The actual binding segment constructs the canonical successor frame
    from the declaration's live set and the name resolved by elaboration. -/
public theorem bindFrameBlock_rep {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {f : AsyncFn} {before next : Phase} (destination : String) (sourceType : Parser.STyp)
    (binding : (f.params ++ f.fields).lookup destination = some sourceType)
    (needed : destination ∈ liveAt f next)
    (retained : ∀ name ∈ liveAt f next, name ≠ destination → name ∈ liveAt f before)
    (saved : Var Γ (frameType types f)) (expression : Expr D Γ Λ (types.ordinary sourceType))
    (oracle : Orakel D) (passes : Nat)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (world : World D) (env : Env D Γ) (frame : Frame (Value D))
    (represented : FrameRep D types f before frame (env.get saved)) :
    let keep := without destination (liveAt f next)
    let slot := (frameSlot types destination sourceType (f.params ++ f.fields) binding).val
    let answer := evaluateExpression expression world env
    let result := Value.typed (types.ordinary sourceType) answer.1
    ∃ record, execBlock oracle passes calls
        (bindFrameBlock (V := V) (l := l) types f keep saved slot expression) world env =
        .ok answer.2.1 (env.set saved record) ∧
      FrameRep D types f next (save frame destination result) record := by
  intro keep slot answer result
  have kept (name : String) (member : name ∈ keep) : name ∈ liveAt f before := by
    have present := List.mem_filter.mp (show name ∈ (liveAt f next).filter
      (fun candidate => !(candidate == destination)) from member)
    have distinct : name ≠ destination := by
      intro equal
      subst name
      exact Bool.false_ne_true (by simpa only [beq_self_eq_true, Bool.not_true] using present.2)
    exact retained name present.1 distinct
  have stable (name : String) (other : name ≠ destination) : name ∈ keep ↔ name ∈ liveAt f next := by
    simp only [keep, without, List.mem_filter, beq_eq_false_iff_ne.mpr other, Bool.not_false,
      eq_self, and_true]
  let extended : Env D (types.ordinary sourceType :: Γ) := .cons answer.1 env
  have old : SlotsRep D types (liveAt f before) frame (f.params ++ f.fields)
      (extended.get (.there saved)) := represented.slots
  have trimmed := (trimFrameExpr_rep (Λ := Λ) (.there saved) kept answer.2.1 answer.2.1 extended old).2
  have named : NamedFrameSlot types destination sourceType (f.params ++ f.fields) slot :=
    (frameSlot types destination sourceType (f.params ++ f.fields) binding).property
  have typed : valueAt D (types.ordinary sourceType) result = some answer.1 := valueAt_typed D _ _
  have stored := named.save_rep typed needed stable represented.unique trimmed
  refine ⟨_, bindFrameBlock_exec types f keep saved slot expression oracle passes calls world env,
    ⟨stored, ?_, represented.unique⟩⟩
  intro name live
  by_cases same : name = destination
  · subst name
    obtain ⟨earlier, later, fieldsEq, _⟩ := List.lookup_eq_some_iff.mp binding
    have member : (destination, sourceType) ∈ f.params ++ f.fields := by
      rw [fieldsEq]
      exact List.mem_append_right _ List.mem_cons_self
    exact List.mem_map_of_mem (f := Prod.fst) member
  · exact represented.declared name (retained name live same)

/-- Construct the continuation frame from the bound local and the old
    slots. An unused result has no slot in the continuation. -/
@[expose] public def bindingFrameExpr {Γ : Ctx} {Λ : List (Res D)}
    (types : TypeResolution) (f : AsyncFn) (next : Phase) (destination : String) (sourceType : Parser.STyp)
    (binding : (f.params ++ f.fields).lookup destination = some sourceType)
    (saved : Var Γ (frameType types f)) : Expr D (types.ordinary sourceType :: Γ) Λ (frameType types f) :=
  if destination ∈ liveAt f next then
    saveSlotExpr types f (trimFrameExpr types f (without destination (liveAt f next)) (.there saved))
      (frameSlot types destination sourceType (f.params ++ f.fields) binding).val (.var .here)
  else trimFrameExpr types f (liveAt f next) (.there saved)

public theorem bindingFrameExpr_reads {Γ : Ctx} {Λ : List (Res D)}
    (types : TypeResolution) (f : AsyncFn) (next : Phase) (destination : String) (sourceType : Parser.STyp)
    (binding : (f.params ++ f.fields).lookup destination = some sourceType) (saved : Var Γ (frameType types f)) :
    (bindingFrameExpr (D := D) (Λ := Λ) types f next destination sourceType binding saved).orte = [] := by
  have trimmed (keep : List String) :
      (trimFrameExpr (D := D) (Λ := Λ) types f keep (.there (σ := types.ordinary sourceType) saved)).orte = [] :=
    trimSlotArgs_reads types keep (f.params ++ f.fields)
      (fun field => Expr.prodGet (.var (.there saved)) field) (fun _ => rfl)
  unfold bindingFrameExpr
  split
  · simp only [saveSlotExpr, Expr.orte, NutzlastExpr.orte, List.append_nil]
    exact trimmed _
  · exact trimmed _

/-- Emit the binding segment from its checked declaration. Evaluation is
    preserved even when the result is unused. -/
@[expose] public def lowerBinding {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (types : TypeResolution) (f : AsyncFn) (next : Phase) (destination : String) (sourceType : Parser.STyp)
    (binding : (f.params ++ f.fields).lookup destination = some sourceType)
    (saved : Var Γ (frameType types f)) (expression : Expr D Γ Λ (types.ordinary sourceType)) :
    Block D V l Γ Λ Λ :=
  evaluateBlock expression saved (bindingFrameExpr types f next destination sourceType binding saved)

/-- Every generated binding, including a discarded result, has the exact
    source read transition and restores the canonical live frame. -/
public theorem lowerBinding_rep {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {f : AsyncFn} {before next : Phase} (destination : String) (sourceType : Parser.STyp)
    (binding : (f.params ++ f.fields).lookup destination = some sourceType)
    (retained : ∀ name ∈ liveAt f next, name ≠ destination → name ∈ liveAt f before)
    (saved : Var Γ (frameType types f)) (expression : Expr D Γ Λ (types.ordinary sourceType))
    (oracle : Orakel D) (passes : Nat)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (world : World D) (env : Env D Γ) (frame : Frame (Value D))
    (represented : FrameRep D types f before frame (env.get saved)) :
    let answer := evaluateExpression expression world env
    let result := Value.typed (types.ordinary sourceType) answer.1
    ∃ record, execBlock oracle passes calls
        (lowerBinding (V := V) (l := l) types f next destination sourceType binding saved expression) world env =
          .ok answer.2.1 (env.set saved record) ∧
      FrameRep D types f next (save frame destination result) record := by
  intro answer result
  by_cases needed : destination ∈ liveAt f next
  · simp only [lowerBinding, bindingFrameExpr, if_pos needed]
    exact bindFrameBlock_rep destination sourceType binding needed retained saved expression oracle passes calls
      world env frame represented
  · simp only [lowerBinding, bindingFrameExpr, if_neg needed]
    have kept (name : String) (live : name ∈ liveAt f next) : name ∈ liveAt f before :=
      retained name live (fun equal => needed (equal ▸ live))
    let cleared : Expr D (types.ordinary sourceType :: Γ) Λ (frameType types f) :=
      trimFrameExpr types f (liveAt f next) (.there saved)
    let extended : Env D (types.ordinary sourceType :: Γ) := .cons answer.1 env
    have old : SlotsRep D types (liveAt f before) frame (f.params ++ f.fields)
        (extended.get (.there saved)) := represented.slots
    obtain ⟨read, trimmed⟩ := trimFrameExpr_rep (Λ := Λ) (.there saved) kept answer.2.1 answer.2.1 extended old
    have noRead (current : World D) : current.lese Λ [] = current := rfl
    have executed := evaluateBlock_exec (V := V) (l := l) oracle passes calls expression saved cleared world env
    change cleared.orte = [] at read
    simp only [read, noRead] at executed
    exact ⟨_, executed, ⟨trimmed.save_unobserved destination result needed,
      fun name live => represented.declared name (kept name live), represented.unique⟩⟩

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
