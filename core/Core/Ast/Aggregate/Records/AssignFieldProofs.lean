module

public import Core.Ast.Aggregate.Records.Fields
public import Core.Ast.Semantik.Formbeweise

/-!
# AssignField

- `Surface.AssignFieldInversionAussage`
- `Surface.AssignFieldSuffixAussage`
- `Surface.AssignFieldDerivationAussage`
- `AssignFieldParseAussage`
- `AssignFieldElaboriertAussage`
- `AssignFieldRealisiertAussage`
- `AssignFieldAnnahmeAussage`
- `AssignFieldIdealAussage`
- `AssignFieldEinheitAussage`
- `AssignFieldImplAussage`
- `AssignFieldErhaltungAussage`
- `AssignFieldRegelSicherAussage`
- `AssignFieldErfuellbarAmAussage`
- `AssignFieldFrameAussage`
- `AssignFieldProgramAussage`
-/

namespace Gabbro.Core.Ast.Surface

theorem AssignFieldInversion : AssignFieldInversionAussage := by
  intro scope result name field input tree rest read
  generalize htok : (.word name :: dot :: .word field :: assignment :: input) = toks at read
  cases read with
  | assignField ref visible writable fld index checked fits valueRead =>
      rename_i nm labs tys value input'
      injection htok with hName hTail
      injection hTail with hDot hTail2
      injection hTail2 with hWord hTail3
      injection hTail3 with hAssign hInput
      have hn : name = ref.binding.name.val := by injection hName with h; exact h
      have hf : field = fld.val := by injection hWord with h; exact h
      subst input'
      exact ⟨⟨nm, labs, tys, ref, visible, writable, fld, index, checked, _, value, fits⟩,
        hn.symm, hf.symm, valueRead, rfl⟩
  | assignVar ref visible writable fits valueRead =>
      simp_all [assignment, dot]
  | letBinding letName ordinary value more letTail =>
      simp_all [letKeyword, keyword, dot]
  | ret declared fits valueRead =>
      simp_all [returnKeyword, dot]
  | ite condition first yes more no =>
      simp_all [ifKeyword, dot]
  | retVoid declared =>
      simp_all [returnKeyword, dot]
  | letMutable letName ordinary written valid fits typeRead valueRead =>
      simp_all [letKeyword, keyword, dot]
  | directCall callRead =>
      simp_all [dot]
  | bindDirect letName ordinary written valid typeRead callRead =>
      simp_all [letKeyword, keyword, dot]
  | whileBounded nonnegative overflow bound staticBound conditionRead boundRead bodyRead =>
      simp_all [keyword, dot]
  | forRange letName ordinary body lo hi staticBounds overflow bodyRead =>
      simp_all [keyword, dot]
  | tupleBind checked patternRead annotationRead valueRead =>
      simp_all [letKeyword, dot]
  | letMutableValue letName ordinary valueRead =>
      simp_all [letKeyword, keyword, dot]
  | variantMatch valueRead armsRead =>
      simp_all [keyword, dot]

theorem AssignFieldSuffix : AssignFieldSuffixAussage := by
  intro scope result name field input tree rest read
  obtain ⟨a, hname, hfield, valueRead, htree⟩ := AssignFieldInversion read
  exact (ExprReads.consumes valueRead).trans (List.suffix_cons semicolon)

end Gabbro.Core.Ast.Surface

namespace Gabbro.Core.Ast.Semantik

open Maschine Annahme Katalog Waechter

theorem AssignFieldElaboriert : AssignFieldElaboriertAussage := by
  intro ctx platform args
  rfl

theorem AssignFieldRealisiert : AssignFieldRealisiertAussage := by
  intro ctx platform args s running active live atPc
  exact (assignFieldForm ctx).realisiert (fun args => by
    change (((expr 0 args.value).code ++ [Befehl.setzeRecordFeld 0 args.ref.index args.name args.labels args.types args.index])[(expr 0 args.value).code.length]? =
      some (.setzeRecordFeld 0 args.ref.index args.name args.labels args.types args.index))
    simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero]
  ) platform args s running active live atPc

theorem AssignFieldAnnahme : AssignFieldAnnahmeAussage := by
  intro ctx
  exact Quellform.annahme (assignFieldForm ctx)

theorem AssignFieldIdeal : AssignFieldIdealAussage := by
  intro ctx
  refine ⟨?_, ?_⟩
  · intro args
    change (((expr 0 args.value).code ++ [Befehl.setzeRecordFeld 0 args.ref.index args.name args.labels args.types args.index])[(expr 0 args.value).code.length]? =
      some (.setzeRecordFeld 0 args.ref.index args.name args.labels args.types args.index))
    simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero]
  · intro args
    exact ⟨((assignFieldForm ctx).befehl args).bestimmt, fun _ _ _ _ _ => Iff.rfl⟩

theorem AssignFieldEinheit : AssignFieldEinheitAussage := by
  intro ctx platform args
  exact ⟨rfl, ((assignFieldForm ctx).befehl args).kommutation⟩

theorem AssignFieldImpl : AssignFieldImplAussage := by
  intro ctx args c s w plans u
  rfl

theorem AssignFieldErhaltung : AssignFieldErhaltungAussage := by
  intro ctx
  exact Quellform.erhaltung (assignFieldForm ctx)
    (fun args => stmt_keine_invarianten ((Surface.assignField ctx).tree args).2)

theorem AssignFieldRegelSicher : AssignFieldRegelSicherAussage := by
  intro ctx platform args
  exact (Quellform.erhaltung (assignFieldForm ctx)
    (fun args => stmt_keine_invarianten ((Surface.assignField ctx).tree args).2)
    platform args).2.2.2

theorem AssignFieldFrame : AssignFieldFrameAussage := by
  intro ctx args frame record value hlocal htemp
  change ((Befehl.setzeRecordFeld 0 args.ref.index args.name args.labels args.types args.index).auswerten frame).lokale[args.ref.index]? =
      some (some ⟨recordValueType args.name args.labels args.types,
        tupleSet args.types args.index (Wert.widen args.source (args.types.get args.index) args.fits value)
          (by simpa only [recordValueType, Wert] using record)⟩) ∧
    (∀ i, i ≠ args.ref.index →
      ((Befehl.setzeRecordFeld 0 args.ref.index args.name args.labels args.types args.index).auswerten frame).lokale[i]? = frame.lokale[i]?) ∧
    ((Befehl.setzeRecordFeld 0 args.ref.index args.name args.labels args.types args.index).auswerten frame).pc = frame.pc + 1 ∧
    ((Befehl.setzeRecordFeld 0 args.ref.index args.name args.labels args.types args.index).auswerten frame).temp = frame.temp
  simp only [Befehl.auswerten, Rahmen.schreibe, recordValueType, wertAls, hlocal, htemp, dif_pos,
    List.getElem?_set_self, ne_eq, List.getElem?_set_of_ne, and_self]

end Gabbro.Core.Ast.Semantik
