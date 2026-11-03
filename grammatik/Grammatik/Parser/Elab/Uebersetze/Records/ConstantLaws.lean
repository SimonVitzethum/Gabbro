module
public import Grammatik.Parser.Elab.Uebersetze.Records.Constants
@[expose] public section

namespace Gabbro.Grammatik.Parser.Uebersetze

/-- Integer-name resolution agrees with the complete canonical reader, even in an arbitrary
    alias environment. Reserved Bool/IEEE spellings cannot be shadowed by integer entries. -/
theorem uTypName_sound (alias : List (String × (Int × Int))) (tabs : List UTab)
    (name : String) (lo hi : Int) (resolved : uTypName alias name = .ok (lo, hi)) :
    uTyp alias tabs [] [] (.atom name) = .ok (.int lo hi) := by
  by_cases hb : name = "bool"
  · subst name; simp only [uTypName, reduceCtorEq] at resolved
  by_cases hs : name = "f32"
  · subst name; simp only [uTypName, reduceCtorEq] at resolved
  by_cases hd : name = "f64"
  · subst name; simp only [uTypName, reduceCtorEq] at resolved
  simp [uTyp, uTypIn, hb, hs, hd, resolved]

/-- Reserved noninteger spellings keep their canonical meaning under every alias scope. -/
theorem uTypName_builtin_refused (alias : List (String × (Int × Int))) :
    uTypName alias "bool" = .error "type is not an integer" ∧
    uTypName alias "f32" = .error "type is not an integer" ∧
    uTypName alias "f64" = .error "type is not an integer" := ⟨rfl, rfl, rfl⟩

/-- Numeric evaluation is independent of the optional leaf adapter and keeps the exact range. -/
theorem uKonstZeile_int (alias : List (String × (Int × Int))) (fns : List UKonstFn)
    (consts : List (String × Int)) (lo hi : Int) (source : SExpr)
    (leaf : Ty → SExpr → Option USide) :
    uKonstZeile alias fns consts (.int lo hi) (.one source) leaf =
      (uKonstWert lo hi fns consts 64 source).map USide.lit := by
  rw [uKonstZeile]

/-- Every nested row receives the same adapter; literal typing still checks its exact length. -/
theorem uKonstZeile_array (alias : List (String × (Int × Int))) (fns : List UKonstFn)
    (consts : List (String × Int)) (element : Ty) (count : Nat) (rows : List SKonstWert)
    (leaf : Ty → SExpr → Option USide) :
    uKonstZeile alias fns consts (.arr element count) (.rows rows) leaf =
      uKonstZeilen alias fns consts element rows leaf := by
  rw [uKonstZeile]

/-- Product leaves are delegated at their complete nominal type, with no scalar fallback. -/
theorem uKonstZeile_product (alias : List (String × (Int × Int))) (fns : List UKonstFn)
    (consts : List (String × Int)) (identity : Nat) (fields : List Ty) (source : SExpr)
    (leaf : Ty → SExpr → Option USide) :
    uKonstZeile alias fns consts (.prod identity fields) (.one source) leaf =
      leaf (.prod identity fields) source := by
  simp [uKonstZeile]

theorem uKonstZeilen_cons (alias : List (String × (Int × Int))) (fns : List UKonstFn)
    (consts : List (String × Int)) (element : Ty) (row : SKonstWert) (rows : List SKonstWert)
    (leaf : Ty → SExpr → Option USide) :
    uKonstZeilen alias fns consts element (row :: rows) leaf =
      (match uKonstZeile alias fns consts element row leaf,
          uKonstZeilen alias fns consts element rows leaf with
       | some head, some tail => some (.arrCons head tail)
       | _, _ => none) := by
  rw [uKonstZeilen]
  rfl

/-- Empty rows keep the canonical nil literal regardless of the element adapter. -/
theorem uKonstZeilen_nil (alias : List (String × (Int × Int))) (fns : List UKonstFn)
    (consts : List (String × Int)) (element : Ty) (leaf : Ty → SExpr → Option USide) :
    uKonstZeilen alias fns consts element [] leaf = some .arrNil := by
  rw [uKonstZeilen]

/-- Retention is proved for arbitrary named schemas and arbitrary leaf adapters. It neither
    assumes nor asserts that an arbitrary adapter is sound: the mandatory literal gate supplies
    typing separately. A successful source declaration cannot disappear through filterMap. -/
theorem uKonstArrays_retains (alias : List (String × (Int × Int))) (fns : List UKonstFn)
    (consts : List (String × Int)) (items : List SItemTief) (named : List (String × Ty))
    (leaf : Ty → SExpr → Option USide) (name : String) (sourceType : STyp) (payload : SKonstWert)
    (ty : Ty) (raw : USide) (member : SItemTief.constT name sourceType payload ∈ items)
    (typed : uTypIn alias [] named [] [] sourceType = .ok ty)
    (evaluated : uKonstZeile alias fns consts ty payload leaf = some raw) :
    (name, USide.typed ty raw) ∈ uKonstArrays alias fns consts items named leaf true := by
  unfold uKonstArrays
  apply List.mem_filterMap.mpr
  refine ⟨SItemTief.constT name sourceType payload, member, ?_⟩
  simp only [Bool.true_or, ↓reduceIte, typed, evaluated, Option.map_some]

/-- Every collected typed literal comes from a real declaration and the actual canonical
    lookup/evaluation, with the same schemas and adapter. Collection cannot invent a binding. -/
theorem uKonstArrays_origin (alias : List (String × (Int × Int))) (fns : List UKonstFn)
    (consts : List (String × Int)) (items : List SItemTief) (named : List (String × Ty))
    (leaf : Ty → SExpr → Option USide) (values : Bool) (name : String) (ty : Ty) (raw : USide)
    (collected : (name, USide.typed ty raw) ∈ uKonstArrays alias fns consts items named leaf values) :
    ∃ sourceType payload,
      SItemTief.constT name sourceType payload ∈ items ∧
      uTypIn alias [] named [] [] sourceType = .ok ty ∧
      uKonstZeile alias fns consts ty payload leaf = some raw := by
  unfold uKonstArrays at collected
  obtain ⟨item, member, produced⟩ := List.mem_filterMap.mp collected
  cases item <;> try { cases produced; done }
  case constT sourceName sourceType payload =>
    change (if values || (fun t : STyp => match t with | .array _ _ => true | _ => false) sourceType then
      match uTypIn alias [] named [] [] sourceType with
      | .ok actual => (uKonstZeile alias fns consts actual payload leaf).map
          (fun value => (sourceName, USide.typed actual value))
      | .error _ => none
      else none) = some (name, USide.typed ty raw) at produced
    by_cases selected : (values || (fun t : STyp => match t with | .array _ _ => true | _ => false) sourceType) = true
    · rw [if_pos selected] at produced
      cases typed : uTypIn alias [] named [] [] sourceType with
      | error error =>
        have impossible : (none : Option (String × USide)) = some (name, USide.typed ty raw) := by
          simpa only [typed] using produced
        cases impossible
      | ok actual =>
        have actualProduced : (uKonstZeile alias fns consts actual payload leaf).map
            (fun value => (sourceName, USide.typed actual value)) =
              some (name, USide.typed ty raw) := by
          simpa only [typed] using produced
        obtain ⟨value, evaluated, equality⟩ := Option.map_eq_some_iff.mp actualProduced
        have same : sourceName = name ∧ actual = ty ∧ value = raw := by
          simpa only [Prod.mk.injEq, USide.typed.injEq] using equality
        obtain ⟨rfl, rfl, rfl⟩ := same
        exact ⟨sourceType, payload, member, typed, evaluated⟩
    · rw [if_neg selected] at produced
      cases produced

/-- The production record adapter routes numeric fields back to the canonical evaluator. -/
theorem uRecordConstant_int (records : List URecord) (alias : List (String × (Int × Int)))
    (fns : List UKonstFn) (consts : List (String × Int)) (lo hi : Int) (source : SExpr) :
    uRecordConstant records alias fns consts (.int lo hi) source =
      (uKonstWert lo hi fns consts 64 source).map USide.lit := by
  simp only [uRecordConstant, uKonstZeile]

/-- The same canonical schema lookup and named-field arranger as production construction. -/
theorem uRecordConstant_product (records : List URecord) (alias : List (String × (Int × Int)))
    (fns : List UKonstFn) (consts : List (String × Int)) (identity : Nat) (fields : List Ty)
    (name : String) (args : List SExpr) :
    uRecordConstant records alias fns consts (.prod identity fields) (.call name args) = (do
      let schema ← (uRecordOf records (.prod identity fields)).toOption
      if !strEq schema.val.name name then none else do
      let values ← uRecordConstantFields records alias fns consts schema.val.fields args
      (uRecordValues schema.val values).toOption) := by
  rw [uRecordConstant]

/-- Boolean fields use exactly the canonical truth literals. -/
theorem uRecordConstant_bool (records : List URecord) (alias : List (String × (Int × Int)))
    (fns : List UKonstFn) (consts : List (String × Int)) (value : Bool) :
    uRecordConstant records alias fns consts .bool (if value then .tru else .fls) =
      some (.truth value) := by
  cases value <;> simp [uRecordConstant]

/-- Constructor argument recursion is over the real labelled source list. -/
theorem uRecordConstantFields_cons (records : List URecord)
    (alias : List (String × (Int × Int))) (fns : List UKonstFn) (consts : List (String × Int))
    (fields : List (String × Ty)) (label : String) (source : SExpr) (rest : List SExpr) :
    uRecordConstantFields records alias fns consts fields (.ext .label [label] [source] :: rest) = (do
      let field ← fields.find? (fun field => strEq field.1 label)
      let side ← uRecordConstant records alias fns consts field.2 source
      let tail ← uRecordConstantFields records alias fns consts fields rest
      pure ((label, side) :: tail)) := by
  rw [uRecordConstantFields]

end Gabbro.Grammatik.Parser.Uebersetze
