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
  have invGen : ∀ (inputType : Ty .value) (base0 : Expr scope inputType),
      (eqT : inputType = recordValueType name labels types) →
      ExprTail scope minimum base0 (dot :: .word field.val :: input) tree rest →
      ∃ i : Fin types.length, ∃ checked : RecordFieldAt labels field i.val,
        ExprTail scope minimum (.recordField (eqT ▸ base0) field i checked) input tree rest := by
    intro inputType base0 eqT r
    cases r with
    | stop blocked =>
        exfalso
        exact blocked ⟨.projection, .word field.val :: input, rfl, allowed⟩
    | binary _ _ _ _ => cases eqT
    | div _ _ _ _ => cases eqT
    | compare _ _ _ _ _ => cases eqT
    | logic _ _ _ _ => cases eqT
    | arrayIndex _ _ _ _ _ _ => cases eqT
    | tupleField _ _ _ _ => cases eqT
    | recordField base' field' index written hle tail =>
        rename_i nm' labs' tys'
        injection eqT with hnm hlabs hlayout
        have htys : tys' = types := tupleType_inj hlayout
        have hlbs : labs' = labels := label_inj hlabs
        subst nm'
        subst tys'
        subst labs'
        subst field'
        exact ⟨index, written, tail⟩
  exact invGen _ base rfl read

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
