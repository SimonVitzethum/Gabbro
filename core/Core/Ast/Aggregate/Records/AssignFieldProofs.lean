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
  have noDotExpr : ∀ {t : Ty .value} (tree : Expr scope t) (r : List Gabbro.Core.Text.Token),
      ¬ ExprReads scope 0 (dot :: .word field :: assignment :: input) tree r := by
    intro t tree r rd
    cases rd with
    | atom a tail => cases a
  have noDotCall : ∀ (call : DirectCall scope) (rs : List Gabbro.Core.Text.Token),
      ¬ CallReads scope (dot :: .word field :: assignment :: input) call rs := by
    intro call rs rd
    cases rd
  have noDotPattern : ∀ (pat : TuplePattern) (rs : List Gabbro.Core.Text.Token),
      ¬ TuplePatternReads (dot :: .word field :: assignment :: input) pat rs := by
    intro pat rs rd
    cases rd
  generalize htok : (.word name :: dot :: .word field :: assignment :: input) = toks at read
  cases read with
  | assignField ref visible writable fld index checked fits valueRead =>
      rename_i refName nm labs src input' value
      injection htok with hName hTail
      injection hTail with hDot hTail2
      injection hTail2 with hWord hTail3
      injection hTail3 with hAssign hInput
      have hn : name = ref.binding.name.val := by injection hName with h
      have hf : field = fld.val := by injection hWord with h
      have inputEq : input = input' := hInput
      have valueRead' : ExprReads scope 0 input value (semicolon :: rest) := by
        simpa only [inputEq] using valueRead
      exact ⟨⟨refName, nm, labs, ref, visible, writable, fld, index, checked, src, value, fits⟩,
        hn.symm, hf.symm, valueRead', rfl⟩
  | assignVar => simp_all [letKeyword, keyword, returnKeyword, ifKeyword, assignment, dot, semicolon, noDotExpr, noDotCall, noDotPattern]
  | letBinding => simp_all [letKeyword, keyword, returnKeyword, ifKeyword, assignment, dot, semicolon, noDotExpr, noDotCall, noDotPattern]
  | ret => simp_all [letKeyword, keyword, returnKeyword, ifKeyword, assignment, dot, semicolon, noDotExpr, noDotCall, noDotPattern]
  | ite => simp_all [letKeyword, keyword, returnKeyword, ifKeyword, assignment, dot, semicolon, noDotExpr, noDotCall, noDotPattern]
  | retVoid => simp_all [letKeyword, keyword, returnKeyword, ifKeyword, assignment, dot, semicolon, noDotExpr, noDotCall, noDotPattern]
  | letMutable => simp_all [letKeyword, keyword, returnKeyword, ifKeyword, assignment, dot, semicolon, noDotExpr, noDotCall, noDotPattern]
  | directCall =>
      rename_i call cr
      exfalso
      exact noDotCall call (by simpa only [← htok] using cr)
  | bindDirect => simp_all [letKeyword, keyword, returnKeyword, ifKeyword, assignment, dot, semicolon, noDotExpr, noDotCall, noDotPattern]
  | whileBounded => simp_all [letKeyword, keyword, returnKeyword, ifKeyword, assignment, dot, semicolon, noDotExpr, noDotCall, noDotPattern]
  | forRange => simp_all [letKeyword, keyword, returnKeyword, ifKeyword, assignment, dot, semicolon, noDotExpr, noDotCall, noDotPattern]
  | tupleBind => simp_all [letKeyword, keyword, returnKeyword, ifKeyword, assignment, dot, semicolon, noDotExpr, noDotCall, noDotPattern]
  | letMutableValue => simp_all [letKeyword, keyword, returnKeyword, ifKeyword, assignment, dot, semicolon, noDotExpr, noDotCall, noDotPattern]
  | variantMatch => simp_all [letKeyword, keyword, returnKeyword, ifKeyword, assignment, dot, semicolon, noDotExpr, noDotCall, noDotPattern]

theorem AssignFieldSuffix : AssignFieldSuffixAussage := by
  intro scope result name field input tree rest read
  obtain ⟨a, hname, hfield, valueRead, htree⟩ := AssignFieldInversion read
  exact (List.suffix_cons semicolon rest).trans (ExprReads.consumes valueRead)

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


end Gabbro.Core.Ast.Semantik
