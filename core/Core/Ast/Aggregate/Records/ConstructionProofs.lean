module

public import Core.Ast.Aggregate.Records.Construction
public import Core.Ast.Semantik.Formbeweise

/-!
# RecordValue

- `Surface.RecordValueInversionAussage`
- `Surface.RecordValueSuffixAussage`
- `Surface.RecordValueDerivationAussage`
- `RecordValueParseAussage`
- `RecordValueElaboriertAussage`
- `RecordValueRealisiertAussage`
- `RecordValueAnnahmeAussage`
- `RecordValueIdealAussage`
- `RecordValueEinheitAussage`
- `RecordValueImplAussage`
- `RecordValueErhaltungAussage`
- `RecordValueRegelSicherAussage`
- `RecordValueErfuellbarAmAussage`
- `RecordValueSlotsAussage`
-/

namespace Gabbro.Core.Ast.Surface

open Gabbro.Core.Text

theorem recordValue_inversion : RecordValueInversionAussage := by
  intro scope labels types input type ref tree rest read
  generalize hh : Token.word ref.name.val :: openParen :: input = hs at read
  cases read with
  | recordValue ref' args fields fits labelRead =>
      have h2 := List.cons.inj hh
      have hnval0 := h2.1
      have hnval : ref'.name.val = ref.name.val := by
        injection hnval0 with h
        exact h.symm
      have hin := h2.2
      refine ⟨⟨_, _, ref', _, _, args, fields, fits⟩, ?_, ?_, ?_⟩
      · exact Subtype.ext hnval
      · simpa [hin] using labelRead
      · rfl
  | _ =>
      simp at hh

private theorem labeledItems_consumes (scope : Scope) :
    ∀ (labels : List Identifier) (types : List (Ty .value)) (items : LabeledItems scope labels types),
      (∀ {input rest}, LabeledItemsRead scope input items rest → rest <:+ input) ∧
      (∀ {input rest}, LabeledItemsTail scope input items rest → rest <:+ input)
  | _, _, .empty => ⟨
      (by intro input rest read; cases read; exact List.suffix_cons _ _),
      (by intro input rest read; cases read; exact List.suffix_cons _ _)⟩
  | _, _, .next name value tail => ⟨
      (by
        intro input rest read
        cases read with
        | next n valueRead tailRead =>
            obtain ⟨u, hu⟩ := (labeledItems_consumes scope _ _ tail).2 tailRead
            obtain ⟨v, hv⟩ := ExprReads.consumes valueRead
            refine ⟨.word n.val :: colon :: v ++ u, ?_⟩
            rw [hv, hu]
            simp),
      (by
        intro input rest read
        cases read with
        | comma label value' remaining itemRead =>
            obtain ⟨u, hu⟩ :=
              (labeledItems_consumes scope _ _ (LabeledItems.next label value' remaining)).1 itemRead
            exact ⟨comma :: u, by rw [hu]; rfl⟩)⟩

theorem recordValue_suffix : RecordValueSuffixAussage := by
  intro scope input labels types items rest read
  exact (labeledItems_consumes scope labels types items).1 read

private theorem labeledItems_print_reads (scope : Scope) :
    ∀ (labels : List Identifier) (types : List (Ty .value)) (items : LabeledItems scope labels types),
      LabeledItemsRead scope (items.printPieces.map PrintedToken.value ++ [closeParen]) items []
  | _, _, .empty => by
      simp [LabeledItems.printPieces]
      exact .close
  | _, _, .next name value tail => by
      have blocked : ¬ Continues 0 (tail.printTail.map PrintedToken.value ++ [closeParen]) := by
        cases tail with
        | empty =>
            simpa [LabeledItems.printTail] using (noOperatorAtClose (minimum := 0) (more := []))
        | next n v t =>
            have commaToken : printComma.value = comma := by rfl
            simpa [LabeledItems.printTail, commaToken] using (noOperatorAtComma (minimum := 0))
      have valueRead : ExprReads scope 0
          (value.printTokens ++ tail.printTail.map PrintedToken.value ++ [closeParen])
          value (tail.printTail.map PrintedToken.value ++ [closeParen]) := by
        simpa [Expr.printTokens] using (Expr.printReads (scope := scope) (minimum := 0) value blocked)
      have tailRead : LabeledItemsTail scope
          (tail.printTail.map PrintedToken.value ++ [closeParen]) tail [] := by
        cases tail with
        | empty =>
            simp [LabeledItems.printTail]
            exact .close
        | next n v t =>
            simpa [LabeledItems.printTail, LabeledItems.printPieces] using
              (LabeledItemsTail.comma n v t (labeledItems_print_reads scope _ _ (.next n v t)))
      simpa [LabeledItems.printPieces, Expr.printTokens] using
        (LabeledItemsRead.next name valueRead tailRead)

private theorem recordValue_print (scope : Scope) (args : RecordValueArgs scope) :
    (recordValue scope).production args
      (((Category.expression scope).printPieces ((recordValue scope).tree args)).map PrintedToken.value) := by
  refine ⟨args.args.printPieces.map PrintedToken.value ++ [closeParen], ?_, ?_⟩
  · simp [recordValue, RecordValueArgs.expression, Category.printPieces, Expr.printPieces]
  · exact labeledItems_print_reads scope _ _ args.args

theorem recordValue_derivation : RecordValueDerivationAussage := by
  intro scope
  refine ⟨
    (fun args tokens prod => by
      rcases prod with ⟨input, rfl, labelRead⟩
      change ExprReads scope 0 (.word args.ref.name.val :: openParen :: input)
        ((Surface.recordValue scope).tree args).2 []
      exact .atom (AtomReads.recordValue args.ref args.fields args.fits labelRead)
        (.stop noOperatorAtEnd)),
    recordValue_print scope,
    ?_⟩
  let rName : Identifier :=
    ⟨['r'], 'r', [], rfl, Or.inl (Or.inl ⟨by decide, by decide⟩),
      fun _ member => (List.not_mem_nil member).elim⟩
  let sc : Scope := recordBinding rName [] :: []
  let ref : RecordRef sc [] [] :=
    { name := rName
      schema := Local.here
      visible := trivial
      spelled := rfl
      shape := rfl
      distinct := by simp }
  let fields : RecordArguments ([] : List Identifier) ([] : List (Ty .value))
      ([] : List Identifier) ([] : List (Ty .value)) :=
    ⟨rfl, by simp, (fun i => Fin.elim0 i), (fun i => Fin.elim0 i)⟩
  let args : RecordValueArgs sc :=
    ⟨([] : List Identifier), ([] : List (Ty .value)), ref,
      ([] : List Identifier), ([] : List (Ty .value)), .empty, fields, fun i => Fin.elim0 i⟩
  exact Rule.satisfiableOfPrint args (recordValue_print sc args)

end Gabbro.Core.Ast.Surface

namespace Gabbro.Core.Ast.Semantik

open Maschine Annahme Katalog Waechter

private theorem rv_amOrt (scope : Scope) : (recordValueForm scope).RegelAmOrt := by
  intro args
  change (((labeledCode 0 args.args).code ++ [Befehl.baueRecord 0 args.ref.name.val args.labels args.types
    (List.ofFn fun i : Fin args.types.length => (args.fields.slot i).val)])[
    (labeledCode 0 args.args).code.length]? = some
      (.baueRecord 0 args.ref.name.val args.labels args.types
        (List.ofFn fun i : Fin args.types.length => (args.fields.slot i).val)))
  simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero]

theorem recordValue_parse : RecordValueParseAussage := by
  intro scope args text pieces lexed prod
  exact (Surface.recordValue_derivation scope).parse lexed prod

theorem recordValue_elaboriert : RecordValueElaboriertAussage := by
  intro scope platform args
  rfl

theorem recordValue_realisiert : RecordValueRealisiertAussage := by
  intro scope platform args s running active live atPc
  exact (recordValueForm scope).realisiert (rv_amOrt scope) platform args s running active live atPc

theorem recordValue_annahme : RecordValueAnnahmeAussage := by
  intro scope
  exact Quellform.annahme (recordValueForm scope)

theorem recordValue_ideal : RecordValueIdealAussage := by
  intro scope
  refine ⟨rv_amOrt scope, ?_⟩
  intro args
  exact ⟨((recordValueForm scope).befehl args).bestimmt, fun _ _ _ _ _ => Iff.rfl⟩

theorem recordValue_einheit : RecordValueEinheitAussage := by
  intro scope platform args
  exact ⟨rfl, ((recordValueForm scope).befehl args).kommutation⟩

theorem recordValue_impl : RecordValueImplAussage := by
  intro scope args c s w plans u
  rfl

theorem recordValue_erhaltung : RecordValueErhaltungAussage := by
  intro scope
  exact Quellform.erhaltung (recordValueForm scope) (fun args =>
    expr_keine_invarianten 0 ((Surface.recordValue scope).tree args).2)

theorem recordValue_regelSicher : RecordValueRegelSicherAussage := by
  intro scope platform args
  exact (Quellform.erhaltung (recordValueForm scope) (fun a =>
    expr_keine_invarianten 0 ((Surface.recordValue scope).tree a).2) platform args).2.2.2

theorem recordValue_erfuellbar : RecordValueErfuellbarAmAussage := by
  intro platform start
  let rName : Identifier :=
    ⟨['r'], 'r', [], rfl, Or.inl (Or.inl ⟨by decide, by decide⟩),
      fun _ member => (List.not_mem_nil member).elim⟩
  let sc : Scope := recordBinding rName [] :: []
  let ref : RecordRef sc [] [] :=
    { name := rName
      schema := Local.here
      visible := trivial
      spelled := rfl
      shape := rfl
      distinct := by simp }
  let fields : RecordArguments ([] : List Identifier) ([] : List (Ty .value))
      ([] : List Identifier) ([] : List (Ty .value)) :=
    ⟨rfl, by simp, (fun i => Fin.elim0 i), (fun i => Fin.elim0 i)⟩
  let args : Surface.RecordValueArgs sc :=
    ⟨([] : List Identifier), ([] : List (Ty .value)), ref,
      ([] : List Identifier), ([] : List (Ty .value)), .empty, fields, fun i => Fin.elim0 i⟩
  let form := recordValueForm sc
  let E := form.einheit platform args
  let s := (I.start E start).2
  refine ⟨sc, args, form.erfuellbar_aus_erreichbar platform start args s .start
    (form.realisiert (rv_amOrt sc) platform args s rfl rfl rfl rfl) ?_⟩
  intro g guard
  cases guard

end Gabbro.Core.Ast.Semantik
