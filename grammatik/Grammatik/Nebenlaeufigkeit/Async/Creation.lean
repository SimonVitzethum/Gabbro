module

public import Grammatik.Nebenlaeufigkeit.Async.Representation.Reachability

namespace Gabbro.Grammatik.Async.Representation

open Segment

variable {D : Deklaration} {Λ : List (Res D)}

@[expose] public def parameterTypes (types : TypeResolution) (parameters : List (String × Parser.STyp)) :
    Ctx :=
  parameters.map (fun parameter => types.ordinary parameter.2)

/-- The source frame starts with the actual entry arguments in declaration
    order. Its initial marks come from the checked ordinary inventory. -/
@[expose] public def initialValues (types : TypeResolution) :
    (parameters : List (String × Parser.STyp)) → Env D (parameterTypes types parameters) →
    List (String × Value D)
  | [], .nil => []
  | (name, type) :: rest, .cons value tail =>
    (name, .typed (types.ordinary type) value) :: initialValues types rest tail

@[expose] public def entryFrame (types : TypeResolution) (f : AsyncFn) (inventory : Inventory D)
    (arguments : Env D (parameterTypes types f.params)) : Frame (Value D) :=
  ⟨initialValues types f.params arguments, (inventory.owned (.running 0)).map (fun owner => inventory.number owner.1)⟩

/-- A checked name and type identify exactly one argument position.
    Its proof follows the same declaration lookup as the Var generator. -/
@[expose] public def inputVar (types : TypeResolution) (name : String) (type : Parser.STyp) :
    (params : List (String × Parser.STyp)) → params.lookup name = some type →
    {slot : Var (parameterTypes types params) (types.ordinary type) //
      ∀ inputs : Env D (parameterTypes types params),
        (initialValues types params inputs).lookup name =
          some (.typed (types.ordinary type) (inputs.get slot))}
  | [], found => by cases found
  | (label, declared) :: rest, found =>
    if same : name = label then by
      subst label
      have typed : declared = type := by
        simpa only [List.lookup_cons, beq_self_eq_true, ite_true, Option.some.injEq] using found
      subst declared
      exact ⟨.here, fun inputs => by
        cases inputs with
        | cons value following =>
          exact List.lookup_cons_self⟩
    else
      let tail := inputVar types name type rest (by
        simpa only [List.lookup_cons, beq_eq_false_iff_ne.mpr same, Bool.false_eq_true, ite_false] using found)
      ⟨.there tail.val, fun inputs => by
        cases inputs with
        | cons value following =>
          simpa only [initialValues, List.lookup_cons, beq_eq_false_iff_ne.mpr same, Bool.false_eq_true, ite_false,
            Env.get] using tail.property following⟩

/-- Generate the ordinary expressions that fill the live input slots.
    A live declaration with no matching input yields an explicit error. -/
@[expose] public def initialSlotArgs (types : TypeResolution) (f : AsyncFn) (inventory : Inventory D) :
    (fields : List (String × Parser.STyp)) →
    Except String {code : Args D (parameterTypes types f.params) Λ (slotTypes types fields) //
      code.orte = [] ∧ ∀ (world : World D) (env : Env D (parameterTypes types f.params)),
        SlotsRep D types (liveAt f (.running 0)) (entryFrame types f inventory env) fields
          (evalProd world code world env)}
  | [] => .ok ⟨.nil, rfl, fun _ _ => .nil⟩
  | (name, type) :: fields => do
    let tail ← initialSlotArgs types f inventory fields
    if used : name ∈ liveAt f (.running 0) then
      if found : f.params.lookup name = some type then
        let selected := inputVar (D := D) types name type f.params found
        let code := Expr.case [none, some (types.ordinary type)] (presentIndex _) (.val (.var selected.val))
        .ok ⟨.cons code tail.val, by
            simp only [Args.orte, Expr.orte, NutzlastExpr.orte, code, tail.property.1, List.nil_append],
          fun world env => .live used (selected.property env) (valueAt_typed D _ _) (tail.property.2 world env)⟩
      else .error "async: a live entry local has no typed input"
    else
      let code := Expr.case [none, some (types.ordinary type)] ⟨0, Nat.zero_lt_succ 1⟩ .empty
      .ok ⟨.cons code tail.val, by
          simp only [Args.orte, Expr.orte, NutzlastExpr.orte, code, tail.property.1, List.nil_append],
        fun world env => .dead used (tail.property.2 world env)⟩

/-- The ordinary constructor produces the actual initial async state.
    Its only data input is the checked canonical argument environment. -/
public structure Constructor (types : TypeResolution) (f : AsyncFn) (inventory : Inventory D)
    (Λ : List (Res D)) where
  code : Expr D (parameterTypes types f.params) Λ (stateType types f)
  readsEmpty : code.orte = []
  represents : ∀ world env, Inv f types inventory (.running 0 (entryFrame types f inventory env))
    (eval world code world env)

@[expose] public def checkConstructor (types : TypeResolution) (f : AsyncFn) (inventory : Inventory D)
    (Λ : List (Res D)) : Except String (Constructor types f inventory Λ) := do
  if unique : (fieldNames f).Nodup then
    if declared : (liveAt f (.running 0)).all (fieldNames f).contains = true then
      let slots ← initialSlotArgs (Λ := Λ) types f inventory (f.params ++ f.fields)
      let frame := Expr.prod (types.recordName [0]) slots.val
      .ok ⟨runningExpr types f 0 (Nat.zero_le _) frame, by
          rw [runningExpr_reads]; exact slots.property.1, by
        intro world env
        rw [runningExpr_eval]
        apply runningValue_inv
        · exact ⟨slots.property.2 world env,
            fun name member => List.contains_iff_mem.mp (List.all_eq_true.mp declared name member), unique⟩
        · rfl⟩
    else .error "async: a live entry name has no declared frame slot"
  else .error "async: duplicate entry frame slot"

end Gabbro.Grammatik.Async.Representation
