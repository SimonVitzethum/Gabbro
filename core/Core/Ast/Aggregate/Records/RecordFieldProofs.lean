module

public import Core.Ast.Aggregate.Records.Fields
public import Core.Ast.Semantik.Formbeweise

/-!
# RecordField

- `Surface.RecordFieldInversionAussage`
- `Surface.RecordFieldSuffixAussage`
- `Surface.RecordFieldDerivationAussage`
- `RecordFieldParseAussage`
- `RecordFieldElaboriertAussage`
- `RecordFieldRealisiertAussage`
- `RecordFieldAnnahmeAussage`
- `RecordFieldIdealAussage`
- `RecordFieldEinheitAussage`
- `RecordFieldImplAussage`
- `RecordFieldErhaltungAussage`
- `RecordFieldRegelSicherAussage`
- `RecordFieldErfuellbarAmAussage`
- `RecordFieldValueAussage`
-/

namespace Gabbro.Core.Ast.Surface

theorem RecordFieldInversion : RecordFieldInversionAussage := by
  intro scope name labels types minimum input type base tree rest field allowed read
  have tupleType_inj : ∀ {a b : List (Ty .value)}, tupleType a = tupleType b → a = b := by
    intro a
    induction a with
    | nil =>
        intro b h
        cases b <;> simp only [tupleType] at h ⊢
    | cons x xs ih =>
        intro b h
        cases b with
        | nil => simp only [tupleType] at h
        | cons y ys =>
            simp only [tupleType] at h
            have hx : x = y := by injection h with h1 _; exact h1
            have hxy : tupleType xs = tupleType ys := by injection h with _ h2; exact h2
            subst y
            exact congrArg (fun l => x :: l) (ih hxy)
  have label_inj : ∀ {a b : List Identifier}, a.map Subtype.val = b.map Subtype.val → a = b := by
    intro a
    induction a with
    | nil =>
        intro b h
        cases b <;> simp at h ⊢
    | cons x xs ih =>
        intro b h
        cases b with
        | nil => simp at h
        | cons y ys =>
            simp only [List.map_cons, List.cons.injEq] at h
            subst y
            exact congrArg (fun l => x :: l) (ih h.2)
  refine ExprTail.rec
    (motive_1 := fun _ _ _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ inputType base0 input0 _ tree0 rest0 _ =>
      inputType = recordValueType name labels types →
      input0 = dot :: .word field.val :: input →
      ∃ i : Fin types.length, ∃ checked : RecordFieldAt labels field i.val,
        ExprTail scope minimum (.recordField base0 field i checked) input tree0 rest0)
    (by trivial)
    (by trivial) (by trivial) (by trivial) (by trivial) (by trivial)
    (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial)
    (by trivial)
    (by
      intro hEq htok
      exfalso
      exact (by
        rename_i blocked
        exact blocked ⟨.projection, .word field.val :: input,
          by simpa only [Infix.token] using htok.symm, allowed⟩))
    (by intro hEq htok; cases hEq)
    (by intro hEq htok; cases hEq)
    (by intro hEq htok; cases hEq)
    (by intro hEq htok; cases hEq)
    (by intro hEq htok; cases hEq)
    (by intro hEq htok; cases hEq)
    (by
      intro hEq htok
      rename_i base' field' index written hle tail _
      injection hEq with hnm hlabs hlayout
      have htys : _ := tupleType_inj hlayout
      have hlbs : _ := label_inj hlabs
      have restEq : .word field.val :: input = .word field'.val :: _ := (List.cons.inj htok).2
      have fld : field = field' := Subtype.ext (List.cons.inj restEq).1
      subst field'
      subst hnm
      exact ⟨index, written, tail⟩) read

theorem RecordFieldSuffix : RecordFieldSuffixAussage := by
  intro scope name labels types minimum input type field base tree rest allowed read
  obtain ⟨i, checked, tail⟩ := RecordFieldInversion (field := field) allowed read
  exact ExprTail.consumes tail

end Gabbro.Core.Ast.Surface

namespace Gabbro.Core.Ast.Semantik

open Maschine Annahme Katalog Waechter

theorem RecordFieldElaboriert : RecordFieldElaboriertAussage := by
  intro scope platform args
  rfl

theorem RecordFieldRealisiert : RecordFieldRealisiertAussage := by
  intro scope platform args s running active live atPc
  exact (recordFieldForm scope).realisiert (fun args => by
    change (((expr 0 args.base).code ++ [Befehl.liesRecordFeld 0 args.name args.labels args.types args.index])[(expr 0 args.base).code.length]? =
      some (.liesRecordFeld 0 args.name args.labels args.types args.index))
    simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero]
  ) platform args s running active live atPc

theorem RecordFieldAnnahme : RecordFieldAnnahmeAussage := by
  intro scope
  exact Quellform.annahme (recordFieldForm scope)

theorem RecordFieldIdeal : RecordFieldIdealAussage := by
  intro scope
  refine ⟨?_, ?_⟩
  · intro args
    change (((expr 0 args.base).code ++ [Befehl.liesRecordFeld 0 args.name args.labels args.types args.index])[(expr 0 args.base).code.length]? =
      some (.liesRecordFeld 0 args.name args.labels args.types args.index))
    simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero]
  · intro args
    exact ⟨((recordFieldForm scope).befehl args).bestimmt, fun _ _ _ _ _ => Iff.rfl⟩

theorem RecordFieldEinheit : RecordFieldEinheitAussage := by
  intro scope platform args
  exact ⟨rfl, ((recordFieldForm scope).befehl args).kommutation⟩

theorem RecordFieldImpl : RecordFieldImplAussage := by
  intro scope args c s w plans u
  rfl

theorem RecordFieldErhaltung : RecordFieldErhaltungAussage := by
  intro scope
  exact Quellform.erhaltung (recordFieldForm scope)
    (fun args => expr_keine_invarianten 0 ((Surface.recordField scope).tree args).2)

theorem RecordFieldRegelSicher : RecordFieldRegelSicherAussage := by
  intro scope platform args
  exact (Quellform.erhaltung (recordFieldForm scope)
    (fun args => expr_keine_invarianten 0 ((Surface.recordField scope).tree args).2)
    platform args).2.2.2

theorem RecordFieldValue : RecordFieldValueAussage := by
  intro scope args frame record h
  change ((Befehl.liesRecordFeld 0 args.name args.labels args.types args.index).auswerten frame).temp 0 =
    some ⟨args.types.get args.index, tupleGet args.types args.index record⟩
  simp [Befehl.auswerten, Rahmen.schreibe, h, wertAls, recordValueType, Option.bind]

end Gabbro.Core.Ast.Semantik
