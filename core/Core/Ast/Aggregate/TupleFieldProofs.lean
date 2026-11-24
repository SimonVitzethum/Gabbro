module

public import Core.Ast.Aggregate.Tuples
public import Core.Ast.Aggregate.Records.RecordFieldProofs
public import Core.Ast.Semantik.Formbeweise

/-!
# TupleField

Prove the pinned statements in this file.

- `Surface.TupleFieldInversionAussage`
- `Surface.TupleFieldSuffixAussage`
- `Surface.TupleFieldDerivationAussage`
- `TupleFieldParseAussage`
- `TupleFieldElaboriertAussage`
- `TupleFieldRealisiertAussage`
- `TupleFieldAnnahmeAussage`
- `TupleFieldIdealAussage`
- `TupleFieldEinheitAussage`
- `TupleFieldImplAussage`
- `TupleFieldErhaltungAussage`
- `TupleFieldRegelSicherAussage`
- `TupleFieldErfuellbarAmAussage`
-/

namespace Gabbro.Core.Ast.Surface

open Gabbro.Core.Ast.Semantik (tupleType_inj_aux)

theorem tupleFieldInvGen {scope first second types minimum input type}
    {tree : Expr scope type} {rest} (allowed : minimum ≤ Infix.projection.precedence) :
    ∀ (inputType : Ty .value) (base0 : Expr scope inputType),
      (eqT : inputType = tupleType (first :: second :: types)) →
      (n : Nat) →
      ExprTail scope minimum base0 (dot :: .natural n :: input) tree rest →
      ∃ i : Fin (first :: second :: types).length, i.val = n ∧
        ExprTail scope minimum (.tupleField (eqT ▸ base0) i) input tree rest := by
    intro inputType base0 eqT n r
    generalize htok : (dot :: .natural n :: input) = toks at r
    cases r with
    | stop blocked =>
        exfalso
        exact blocked ⟨.projection, .natural n :: input,
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
    | tupleField base' index' hle tail =>
        rename_i a b ts input'
        have hlists : a :: b :: ts = first :: second :: types :=
          tupleType_inj_aux eqT
        injection hlists with ha htail
        injection htail with hb hts
        subst a
        subst b
        subst ts
        have numEq : .natural index'.val :: input = .natural n :: input' := (List.cons.inj htok).2
        have hidx : index'.val = n := by injection (List.cons.inj numEq).1 with h; exact h
        have inputEq : input = input' := (List.cons.inj numEq).2
        subst input'
        exact ⟨index', hidx, tail⟩
    | recordField _ field' _ _ hle _ =>
        have restEq : .natural n :: input = .word field'.val :: _ := (List.cons.inj htok).2
        cases (List.cons.inj restEq).1

theorem TupleFieldInversion : TupleFieldInversionAussage := by
  intro scope first second types minimum input type base tree rest n allowed read
  exact tupleFieldInvGen allowed _ base rfl n read

theorem TupleFieldSuffix : TupleFieldSuffixAussage := by
  intro scope first second types minimum input type base tree rest n allowed read
  obtain ⟨i, hival, tail⟩ := tupleFieldInvGen allowed _ base rfl n read
  exact ExprTail.consumes tail

end Gabbro.Core.Ast.Surface

namespace Gabbro.Core.Ast.Semantik

open Maschine Annahme Katalog Waechter

theorem TupleFieldElaboriert : TupleFieldElaboriertAussage := by
  intro scope platform args
  rfl

theorem TupleFieldRealisiert : TupleFieldRealisiertAussage := by
  intro scope platform args s running active live atPc
  exact (tupleFieldForm scope).realisiert (fun args => by
    change (((expr 0 args.base).code ++ [Befehl.liesTupelfeld 0 args.types args.index])[(expr 0 args.base).code.length]? =
      some (.liesTupelfeld 0 args.types args.index))
    simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero]
  ) platform args s running active live atPc

theorem TupleFieldAnnahme : TupleFieldAnnahmeAussage := by
  intro scope
  exact Quellform.annahme (tupleFieldForm scope)

theorem TupleFieldIdeal : TupleFieldIdealAussage := by
  intro scope
  refine ⟨?_, ?_⟩
  · intro args
    change (((expr 0 args.base).code ++ [Befehl.liesTupelfeld 0 args.types args.index])[(expr 0 args.base).code.length]? =
      some (.liesTupelfeld 0 args.types args.index))
    simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero]
  · intro args
    exact ⟨((tupleFieldForm scope).befehl args).bestimmt, fun _ _ _ _ _ => Iff.rfl⟩

theorem TupleFieldEinheit : TupleFieldEinheitAussage := by
  intro scope platform args
  exact ⟨rfl, ((tupleFieldForm scope).befehl args).kommutation⟩

theorem TupleFieldImpl : TupleFieldImplAussage := by
  intro scope args c s w plans u
  rfl

theorem TupleFieldErhaltung : TupleFieldErhaltungAussage := by
  intro scope
  exact Quellform.erhaltung (tupleFieldForm scope)
    (fun args => expr_keine_invarianten 0 ((Surface.tupleField scope).tree args).2)

theorem TupleFieldRegelSicher : TupleFieldRegelSicherAussage := by
  intro scope platform args
  exact (Quellform.erhaltung (tupleFieldForm scope)
    (fun args => expr_keine_invarianten 0 ((Surface.tupleField scope).tree args).2)
    platform args).2.2.2

end Gabbro.Core.Ast.Semantik
