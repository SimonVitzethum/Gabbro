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

theorem tupleType_inj_aux : ∀ {a b : List (Ty .value)}, tupleType a = tupleType b → a = b := by
  intro a
  induction a with
  | nil =>
      intro b h
      cases b with
      | nil => rfl
      | cons y ys =>
          simp only [tupleType] at h
          cases h
  | cons x xs ih =>
      intro b h
      cases b with
      | nil =>
          simp only [tupleType] at h
          cases h
      | cons y ys =>
          simp only [tupleType] at h
          injection h with h1 h2
          subst y
          exact congrArg (fun l => x :: l) (ih h2)

theorem labelList_inj_aux : ∀ {a b : List Identifier}, a.map Subtype.val = b.map Subtype.val → a = b := by
  intro a
  induction a with
  | nil =>
      intro b h
      cases b with
      | nil => rfl
      | cons y ys => cases h
  | cons x xs ih =>
      intro b h
      cases b with
      | nil => cases h
      | cons y ys =>
          injection h with hy hrest
          have yEq : y = x := Subtype.ext hy.symm
          subst y
          exact congrArg (fun l => x :: l) (ih hrest)

theorem recordFieldInvGen {scope name labels types minimum input type}
    {tree : Expr scope type} {rest} (allowed : minimum ≤ Infix.projection.precedence) :
    ∀ (inputType : Ty .value) (base0 : Expr scope inputType),
      (eqT : inputType = recordValueType name labels types) →
      (word : List Char) →
      ExprTail scope minimum base0 (dot :: .word word :: input) tree rest →
      ∃ (fld : Identifier) (i : Fin types.length) (checked : RecordFieldAt labels fld i.val),
        fld.val = word ∧
        ExprTail scope minimum (.recordField (eqT ▸ base0) fld i checked) input tree rest := by
    intro inputType base0 eqT word r
    generalize htok : (dot :: .word word :: input) = toks at r
    cases r with
    | stop blocked =>
        exfalso
        exact blocked ⟨.projection, .word word :: input,
          by simpa only [Infix.token] using htok.symm, allowed⟩
    | binary op hle _ _ =>
        have head : dot = op.token := (List.cons.inj htok).1
        have eq : (.projection : Infix) = .arith op :=
          Infix.token_injective (by simpa only [Infix.token] using head)
        cases eq
    | div hle _ _ _ =>
        have head : dot = Infix.div.token := (List.cons.inj htok).1
        have eq : (.projection : Infix) = .div :=
          Infix.token_injective (by simpa only [Infix.token] using head)
        cases eq
    | compare op hle _ _ _ =>
        have head : dot = (Infix.compare op).token := (List.cons.inj htok).1
        have eq : (.projection : Infix) = .compare op :=
          Infix.token_injective (by simpa only [Infix.token] using head)
        cases eq
    | logic op hle _ _ =>
        have head : dot = (Infix.logic op).token := (List.cons.inj htok).1
        have eq : (.projection : Infix) = .logic op :=
          Infix.token_injective (by simpa only [Infix.token] using head)
        cases eq
    | arrayIndex _ _ _ hle _ _ =>
        have head : dot = openBracket := (List.cons.inj htok).1
        have eq : (.projection : Infix) = .index :=
          Infix.token_injective (by simpa only [Infix.token] using head)
        cases eq
    | tupleField _ index' hle _ =>
        have restEq : .word word :: input = .natural index'.val :: _ := (List.cons.inj htok).2
        cases (List.cons.inj restEq).1
    | recordField base' field' index written hle tail =>
        rename_i nm' labs' tys' input'
        injection eqT with hnm hlabs hlayout
        have htys : tys' = types := tupleType_inj_aux hlayout
        have hlbs : labs' = labels := labelList_inj_aux hlabs
        have restEq : .word word :: input = .word field'.val :: input' := (List.cons.inj htok).2
        have wf : field'.val = word := by
          injection (List.cons.inj restEq).1 with h
          exact h.symm
        have inputEq : input = input' := (List.cons.inj restEq).2
        subst nm'
        subst tys'
        subst labs'
        subst input'
        exact ⟨field', index, written, wf, tail⟩

theorem RecordFieldInversion : RecordFieldInversionAussage := by
  intro scope name labels types minimum input type base tree rest field allowed read
  obtain ⟨fld, i, checked, hval, tail⟩ := recordFieldInvGen allowed _ base rfl field.val read
  have ef : fld = field := Subtype.ext hval
  subst fld
  exact ⟨i, checked, tail⟩

theorem RecordFieldSuffix : RecordFieldSuffixAussage := by
  intro scope name labels types minimum input type field base tree rest allowed read
  obtain ⟨fld, i, checked, hval, tail⟩ := recordFieldInvGen allowed _ base rfl field read
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
  simp only [Befehl.auswerten, Rahmen.schreibe, recordValueType, wertAls, Option.bind,
    Function.update_self, h, dif_pos]

end Gabbro.Core.Ast.Semantik
