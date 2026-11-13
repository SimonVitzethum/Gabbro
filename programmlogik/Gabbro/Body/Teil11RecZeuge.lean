module

public import Gabbro.Body.Teil8
public import Gabbro.Body.Teil10RecRegeln

@[expose] public section

namespace Gabbro.Body

/-- Concrete, mixed-shape construction; the order is observable through projections. -/
theorem eval_recOf_zeuge (s : State) :
    eval s (.recOf [.lit (.int 7), .lit (.bool true)]) =
      some (.record [.int 7, .bool true]) := by
  simp [eval, evalAll]

theorem eval_recGet_zeuge (s : State) :
    eval s (.recGet (.recOf [.lit (.int 7), .lit (.bool true)]) 0) = some (.int 7) := by
  rw [eval_recGet s _ [.int 7, .bool true] 0 (eval_recOf_zeuge s)]
  rfl

theorem eval_recSet_zeuge (s : State) :
    eval s (.recSet (.recOf [.lit (.int 7), .lit (.bool true)]) 0 (.lit (.int 9))) =
      some (.record [.int 9, .bool true]) := by
  simpa only [List.set_cons_zero] using
    eval_recSet s _ (.lit (.int 9)) [.int 7, .bool true] (.int 9) 0
      (eval_recOf_zeuge s) rfl (by decide)

theorem recGet_after_recSet_zeuge (s : State) :
    eval s (.recGet
      (.recSet (.recOf [.lit (.int 7), .lit (.bool true)]) 0 (.lit (.int 9))) 0) =
      some (.int 9) :=
  recGet_after_recSet s _ (.lit (.int 9)) [.int 7, .bool true] (.int 9) 0
    (eval_recOf_zeuge s) rfl (by decide)

theorem recGet_frame_zeuge (s : State) :
    eval s (.recGet
      (.recSet (.recOf [.lit (.int 7), .lit (.bool true)]) 0 (.lit (.int 9))) 1) =
      eval s (.recGet (.recOf [.lit (.int 7), .lit (.bool true)]) 1) :=
  recGet_frame s _ (.lit (.int 9)) [.int 7, .bool true] (.int 9) 0 1
    (eval_recOf_zeuge s) rfl (by decide) (by decide)

theorem recSet_idempotent_zeuge (s : State) :
    eval s (.recSet
      (.recSet (.recOf [.lit (.int 7), .lit (.bool true)]) 0 (.lit (.int 9)))
      0 (.lit (.int 9))) =
      eval s (.recSet (.recOf [.lit (.int 7), .lit (.bool true)]) 0 (.lit (.int 9))) :=
  recSet_idempotent s _ (.lit (.int 9)) [.int 7, .bool true] (.int 9) 0
    (eval_recOf_zeuge s) rfl (by decide)

theorem recSet_recGet_zeuge (s : State) :
    eval s (.recSet (.recOf [.lit (.int 7), .lit (.bool true)]) 1
      (.recGet (.recOf [.lit (.int 7), .lit (.bool true)]) 1)) =
      eval s (.recOf [.lit (.int 7), .lit (.bool true)]) :=
  recSet_recGet s _ [.int 7, .bool true] 1 (eval_recOf_zeuge s) (by decide)

theorem record_ext_zeuge :
    Value.record [.int 7, .bool true] = .record [.int 7, .bool true] :=
  Value.record_ext _ _ (fun _ => rfl)

theorem rec_ext_zeuge (s : State) :
    eval s (.recOf [.lit (.int 7), .lit (.bool true)]) =
      eval s (.lit (.record [.int 7, .bool true])) := by
  apply rec_ext s _ _ [.int 7, .bool true] [.int 7, .bool true]
    (eval_recOf_zeuge s) rfl
  intro idx
  rw [eval_recGet s _ [.int 7, .bool true] idx (eval_recOf_zeuge s),
    eval_recGet s _ [.int 7, .bool true] idx rfl]

/-- Shape witnesses are nonempty, preserve order and include an integer range. -/
theorem hasShape_rec_true_zeuge :
    ∃ vs, Value.record [.int 7, .bool true] = .record vs ∧
      vs.length = [Shape.intIn 0 10, .bool].length ∧
      Value.fieldsHaveShape vs [.intIn 0 10, .bool] = true :=
  Value.hasShape_rec_true _ _ (by decide)

theorem fieldsHaveShape_set_zeuge :
    Value.fieldsHaveShape ([Value.int 7, .bool true].set 0 (.int 9))
      [.intIn 0 10, .bool] = true :=
  Value.fieldsHaveShape_set _ _ 0 (.intIn 0 10) (.int 9)
    (by decide) rfl (by decide)

theorem hasShape_rec_set_zeuge :
    (Value.record ([Value.int 7, .bool true].set 0 (.int 9))).hasShape
      (.record [.intIn 0 10, .bool]) = true :=
  Value.hasShape_rec_set _ _ 0 (.intIn 0 10) (.int 9) (by decide) rfl (by decide)

/-- A real record-typed place, rather than an inconsistent well-formedness premise. -/
def recTyping : Typing := fun _ => some (.record [.intIn 0 10, .bool])
def recWorld : World := fun _ => .record [.int 7, .bool true]

theorem recWorld_wf : WF recTyping recWorld := by
  intro p sh hp
  change some (.record [.intIn 0 10, .bool]) = some sh at hp
  cases hp
  change (Value.record [.int 7, .bool true]).hasShape (.record [.intIn 0 10, .bool]) = true
  decide

theorem WF_rec_zeuge :
    ∃ vs, recWorld (.global "pair") = .record vs ∧
      vs.length = [Shape.intIn 0 10, .bool].length ∧
      Value.fieldsHaveShape vs [.intIn 0 10, .bool] = true :=
  WF_rec recTyping recWorld (.global "pair") _ recWorld_wf rfl

theorem WF_read_rec_zeuge :
    (recWorld (.global "pair")).hasShape (.record [.intIn 0 10, .bool]) = true :=
  WF_read_rec recTyping recWorld (.global "pair") _ recWorld_wf rfl

theorem WF_store_rec_zeuge :
    WF recTyping (store recWorld (.global "pair") (.record [.int 9, .bool false])) :=
  WF_store_rec recTyping recWorld (.global "pair") _ [.int 9, .bool false]
    recWorld_wf rfl rfl (by decide)

theorem shape_rec_zeuge :
    ∃ vs, Value.record [.int 7, .bool true] = .record vs ∧
      vs.length = [Shape.intIn 0 10, .bool].length ∧
      Value.fieldsHaveShape vs [.intIn 0 10, .bool] = true := by
  let s : State := {
    world := recWorld
    local' := fun _ => .record [.int 7, .bool true]
  }
  exact shape_rec s "pair" [.intIn 0 10, .bool] (by decide)

/-- Refusal witnesses: bounds, base shape, failed fields and replacement evaluation. -/
theorem eval_recGet_oob_zeuge (s : State) :
    eval s (.recGet (.recOf [.lit (.int 7), .lit (.bool true)]) 2) = none :=
  eval_recGet_oob s _ [.int 7, .bool true] 2 (eval_recOf_zeuge s) (by decide)

theorem eval_recSet_oob_zeuge (s : State) :
    eval s (.recSet (.recOf [.lit (.int 7), .lit (.bool true)]) 2 (.lit (.int 9))) = none :=
  eval_recSet_oob s _ (.lit (.int 9)) [.int 7, .bool true] 2
    (eval_recOf_zeuge s) (by decide)

theorem rec_invalid_base_zeuge (s : State) :
    eval s (.recGet (.lit (.int 7)) 0) = none ∧
      eval s (.recSet (.lit (.int 7)) 0 (.lit (.int 9))) = none := by
  simp [eval]

theorem rec_failed_field_zeuge (s : State) :
    eval s (.recOf [.un .neg (.lit (.bool true)), .lit (.int 7)]) = none ∧
      eval s (.recSet (.lit (.record [.int 7, .bool true])) 0
        (.un .neg (.lit (.bool true)))) = none := by
  simp [eval, evalAll, unop]

/-- The nested constructor exercises both mutual traversals. -/
theorem rec_nested_zeuge (s : State) :
    eval s (.recOf [.recOf [.lit (.int 7)], .lit (.bool true)]) =
      some (.record [.record [.int 7], .bool true]) ∧
      (Value.record [.record [.int 7], .bool true]).hasShape
        (.record [.record [.intIn 0 10], .bool]) = true := by
  constructor
  · simp [eval, evalAll]
  · decide

/-- All three simp entry points can compute construction, projection and replacement. -/
theorem gabbro_simp_rec_zeuge (s : State) :
    eval s (.recGet (.recSet (.recOf [.lit (.int 7), .lit (.bool true)])
      0 (.lit (.int 9))) 0) = some (.int 9) := by
  gabbro_simp

theorem gabbro_simp_rec_args_zeuge (s : State) :
    eval s (.recGet (.recSet (.recOf [.lit (.int 7), .lit (.bool true)])
      0 (.lit (.int 9))) 0) = some (.int 9) := by
  gabbro_simp []

theorem gabbro_simp_rec_hyps_zeuge (s : State) :
    eval s (.recGet (.recSet (.recOf [.lit (.int 7), .lit (.bool true)])
      0 (.lit (.int 9))) 0) = some (.int 9) := by
  gabbro_simp []

/-- The opener dispatches record shapes to the ordered field-list witness. -/
theorem gabbro_open_rec_zeuge (v : Value) (h : v.hasShape (.record [.int, .bool]) = true) :
    ∃ vs, v = .record vs := by
  gabbro_open h
  exact ⟨_, by assumption⟩

/-- The world-shape automation discovers record reads and opens their witnesses. -/
theorem gabbro_shape_rec_zeuge (s : State) (h : WF recTyping s.world) :
    ∃ vs, s.world (.global "pair") = .record vs := by
  gabbro_shape recTyping
  all_goals (first | assumption | exact ⟨_, by assumption⟩)

/-- Empty records are valid values; both accesses still refuse their only candidate index. -/
theorem rec_empty_zeuge (s : State) :
    eval s (.recOf []) = some (.record []) ∧
      (Value.record []).hasShape (.record []) = true ∧
      eval s (.recGet (.recOf []) 0) = none ∧
      eval s (.recSet (.recOf []) 0 (.lit (.int 9))) = none := by
  simp [eval, evalAll]

/-- Neither a different field count nor a permutation with incompatible shapes is accepted. -/
theorem rec_shape_refusals_zeuge :
    (Value.record [.int 7, .bool true]).hasShape (.record [.int]) = false ∧
      (Value.record [.int 7, .bool true]).hasShape (.record [.bool, .int]) = false := by
  decide

/-- The generic value case splitter also retains the record constructor. -/
theorem gabbro_values_rec_zeuge (s : State) (v : Value)
    (hv : v = .record [.int 7, .bool true]) :
    eval s (.recGet (.lit v) 1) = some (.bool true) := by
  gabbro_values
  all_goals simp_all [eval]

end Gabbro.Body
