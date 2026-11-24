module

public import Core.Ast.Expression.Atoms

@[expose] public section

namespace Gabbro.Core.Ast

open Gabbro.Core.Text

theorem tupleType_injective {a b : List (Ty .value)} (same : tupleType a = tupleType b) :
    a = b := by
  induction a generalizing b with
  | nil => cases b <;> first | rfl | cases same
  | cons head tail ih =>
    cases b with
    | nil => cases same
    | cons other rest =>
      injection same with hhead htail
      rw [hhead, ih htail]

theorem identifierList_injective {a b : List Identifier}
    (same : a.map Subtype.val = b.map Subtype.val) : a = b := by
  induction a generalizing b with
  | nil => cases b <;> first | rfl | cases same
  | cons head tail ih =>
    cases b with
    | nil => cases same
    | cons other rest =>
      injection same with hhead htail
      rw [Subtype.ext hhead, ih htail]

theorem identifierPosition_unique {names : List Identifier}
    (distinct : (names.map Subtype.val).Nodup)
    (atLeft : names[left]? = some name) (atRight : names[right]? = some name) :
    left = right := by
  have inRange := (List.getElem?_eq_some_iff.mp atLeft).1
  have mapped := congrArg (Option.map Subtype.val) (atLeft.trans atRight.symm)
  rw [← List.getElem?_map, ← List.getElem?_map] at mapped
  exact (distinct.getElem?_inj (by simpa only [List.length_map] using inRange)).1 mapped

theorem LabeledItems.lengths (items : LabeledItems scope labels types) :
    labels.length = types.length := by
  induction items with
  | empty => rfl
  | next _ _ _ ih => simp only [List.length_cons, ih]

theorem RecordArguments.unique (a b : RecordArguments labels types actualLabels actualTypes)
    (lengths : actualLabels.length = actualTypes.length) : a = b := by
  have slots : a.slot = b.slot := by
    funext i
    apply Fin.ext
    have read := a.label i
    have inRange : (a.slot i).val < actualLabels.length := by rw [lengths]; exact (a.slot i).isLt
    have found : actualLabels[(a.slot i).val]? = some actualLabels[(a.slot i).val] :=
      List.getElem?_eq_some_iff.2 ⟨inRange, rfl⟩
    exact identifierPosition_unique a.distinct found ((b.label i).symm.trans (read.trans found))
  cases a
  cases b
  cases slots
  rfl

theorem RecordRef.unique (a : RecordRef scope labels types)
    (b : RecordRef scope labels' types') (same : a.name.val = b.name.val) :
    (⟨labels, types, a⟩ : Σ ls ts, RecordRef scope ls ts) = ⟨labels', types', b⟩ := by
  have schema := Local.nameVisible_unique a.schema b.schema a.visible b.visible
    (a.spelled.trans (same.trans b.spelled.symm))
  have sameType := congrArg Sigma.fst schema
  injection sameType with _ hlabels htypes
  cases identifierList_injective hlabels
  cases tupleType_injective htypes
  cases a
  cases b
  cases Subtype.ext same
  cases schema
  rfl

private theorem variantLayout_injective {a b : List (Option (Ty .value))}
    (shape : a.map Option.isSome = b.map Option.isSome)
    (layout : variantLayout a = variantLayout b) : a = b := by
  induction a generalizing b with
  | nil => cases b <;> first | rfl | cases shape
  | cons head tail ih =>
    cases b with
    | nil => cases shape
    | cons other rest =>
      injection shape with htag htags
      injection layout with hvalue hvalues
      have hhead : head = other := by
        cases head <;> cases other <;> first | rfl | cases htag | exact congrArg some hvalue
      rw [hhead, ih htags hvalues]

private theorem Local.label_mem_scope (ref : Local scope type)
    (member : label ∈ type.variantLabels) :
    label ∈ scope.flatMap (fun binding => binding.type.variantLabels) := by
  apply List.mem_flatMap.mpr
  exact ⟨ref.binding, ref.binding_mem, member⟩

private theorem Local.unique_label (a : Local scope type) (b : Local scope type')
    (left : label ∈ type.variantLabels) (right : label ∈ type'.variantLabels)
    (occurrences : (scope.flatMap (fun binding => binding.type.variantLabels)).count label ≤ 1) :
    (⟨type, a⟩ : Σ t, Local scope t) = ⟨type', b⟩ := by
  induction a with
  | here =>
    cases b with
    | here => rfl
    | there b =>
      have head := List.count_pos_iff.mpr left
      have tail := List.count_pos_iff.mpr (b.label_mem_scope right)
      simp only [List.flatMap_cons, List.count_append] at occurrences
      omega
  | there a ih =>
    cases b with
    | here =>
      have head := List.count_pos_iff.mpr right
      have tail := List.count_pos_iff.mpr (a.label_mem_scope left)
      simp only [List.flatMap_cons, List.count_append] at occurrences
      omega
    | there b =>
      simp only [List.flatMap_cons, List.count_append] at occurrences
      cases ih b left right (by omega)
      rfl

theorem VariantRef.unique (a : VariantRef scope labels payloads)
    (b : VariantRef scope labels' payloads') (left : label ∈ labels)
    (right : label ∈ labels') (available : availableCase scope label) :
    (⟨labels, payloads, a⟩ : Σ ls ps, VariantRef scope ls ps) = ⟨labels', payloads', b⟩ := by
  have schema := Local.unique_label a.schema b.schema
    (List.mem_map_of_mem left) (List.mem_map_of_mem right) (Nat.le_of_eq available.1)
  have sameType := congrArg Sigma.fst schema
  injection sameType with hname hlabels htags htypes
  cases identifierList_injective hlabels
  cases variantLayout_injective htags htypes
  cases a
  cases b
  cases Subtype.ext hname
  cases schema
  rfl

end Gabbro.Core.Ast
