module

public import Core.Ast.Aggregate.Tuples
public import Core.Ast.Semantik.Formbeweise

/-!
# TupleValue

Prove the pinned statements in this file.

- `Surface.TupleValueInversionAussage`
- `Surface.TupleValueSuffixAussage`
- `Surface.TupleValueDerivationAussage`
- `TupleValueParseAussage`
- `TupleValueElaboriertAussage`
- `TupleValueRealisiertAussage`
- `TupleValueAnnahmeAussage`
- `TupleValueIdealAussage`
- `TupleValueEinheitAussage`
- `TupleValueImplAussage`
- `TupleValueErhaltungAussage`
- `TupleValueRegelSicherAussage`
- `TupleValueErfuellbarAmAussage`
-/

@[expose] public section

namespace Gabbro.Core.Ast.Surface

open Gabbro.Core.Text

private theorem tupleTailBlocked {scope : Scope} {types : List (Ty .value)}
    (items : ExprItems scope types) :
    ¬ Continues 0 (items.printTail.map PrintedToken.value ++ [closeParen]) := by
  match items with
  | .empty =>
      simpa [ExprItems.printTail] using (noOperatorAtClose (minimum := 0) (more := []))
  | .next _ _ =>
      have commaToken : printComma.value = comma := by rfl
      simpa [ExprItems.printTail, commaToken] using (noOperatorAtComma (minimum := 0))

private theorem tupleItemsTail_print (scope : Scope) : (types : List (Ty .value)) →
    (items : ExprItems scope types) →
    ItemsTail scope closeParen (items.printTail.map PrintedToken.value ++ [closeParen]) items []
  | _, .empty => by
      simp only [ExprItems.printTail, List.map_nil, List.nil_append]
      exact .close
  | _, .next head tail => by
      simp only [ExprItems.printTail, List.map_cons, List.map_append, List.map_nil]
      apply ItemsTail.comma (Or.inl (by intro empty; cases empty))
      exact .next (by
        simpa [Expr.printTokens] using Expr.printReads head (tupleTailBlocked tail))
        (tupleItemsTail_print scope _ tail)

theorem tupleValue_inversion : TupleValueInversionAussage := by
  intro scope input type firstType secondInput tree rest first firstRead read
  cases read
  case grouped inner =>
      have same := ExprReads.deterministic firstRead inner
      have bad : comma = closeParen := (List.cons.inj same.2).1
      simp only [comma, closeParen, Token.punctuation.injEq, String.reduceToList,
        List.cons.injEq, Char.reduceEq, false_and] at bad
  case tupleValue fRead sRead =>
      rename_i firstType' firstExpr' secondInput' secondType' secondExpr' more' tailTypes' items' secondSub
      have same := ExprReads.deterministic firstRead fRead
      have listsEq := List.cons.inj same.2
      rw [← listsEq.2] at secondSub
      refine ⟨⟨firstType', secondType', tailTypes', firstExpr', secondExpr', items'⟩,
        more', same.1, secondSub, sRead, rfl⟩
  all_goals contradiction

mutual
  private theorem itemsRead_consumes (scope : Scope) (close : Token) :
      (input : List Token) → (types : List (Ty .value)) → (items : ExprItems scope types) →
      (rest : List Token) → ItemsRead scope close input items rest → rest <:+ input
    | _, _, _, _, .close => List.suffix_cons _ _
    | _, _, _, _, .next headRead tailRead =>
        (itemsTail_consumes scope close _ _ _ _ tailRead).trans (ExprReads.consumes headRead)

  private theorem itemsTail_consumes (scope : Scope) (close : Token) :
      (input : List Token) → (types : List (Ty .value)) → (items : ExprItems scope types) →
      (rest : List Token) → ItemsTail scope close input items rest → rest <:+ input
    | _, _, _, _, .close => List.suffix_cons _ _
    | _, _, _, _, .comma _ itemRead =>
        (itemsRead_consumes scope close _ _ _ _ itemRead).trans (List.suffix_cons _ _)
end

theorem tupleValue_suffix : TupleValueSuffixAussage := by
  intro scope input types items rest read
  exact itemsTail_consumes scope closeParen input types items rest read

private theorem tupleValue_reads (scope : Scope) (args : TupleValueArgs scope) {tokens : List Token}
    (prod : (tupleValue scope).production args tokens) :
    (Category.expression scope).reads tokens ((tupleValue scope).tree args) := by
  rcases prod with ⟨input, secondInput, more, rfl, firstRead, secondRead, tailRead⟩
  change ExprReads scope 0 (openParen :: input) (.tupleValue args.first args.second args.tail) []
  exact .atom (.tupleValue firstRead secondRead tailRead) (.stop noOperatorAtEnd)

private theorem tupleValue_print (scope : Scope) (args : TupleValueArgs scope) :
    (tupleValue scope).production args
      (((Category.expression scope).printPieces ((tupleValue scope).tree args)).map PrintedToken.value) := by
  change ∃ input secondInput more,
      Expr.printTokens (Expr.tupleValue args.first args.second args.tail) = openParen :: input ∧
      ExprReads scope 0 input args.first (comma :: secondInput) ∧
      ExprReads scope 0 secondInput args.second more ∧
      ItemsTail scope closeParen more args.tail []
  let firstTokens := args.first.printTokens
  let secondTokens := args.second.printTokens
  let tailTokens := args.tail.printTail.map PrintedToken.value
  refine ⟨firstTokens ++ [comma] ++ secondTokens ++ tailTokens ++ [closeParen],
    secondTokens ++ tailTokens ++ [closeParen], tailTokens ++ [closeParen], ?_, ?_, ?_, ?_⟩
  · have openTok : printOpen.value = openParen := by rfl
    have commaTok : printComma.value = comma := by rfl
    have closeTok : printClose.value = closeParen := by rfl
    simp only [Expr.printTokens, Expr.printPieces, List.map_append, List.map_cons, List.map_nil,
      firstTokens, secondTokens, tailTokens, openTok, commaTok, closeTok, List.singleton_append,
      List.append_assoc]
    rfl
  · simpa [firstTokens] using
      (Expr.printReads (tree := args.first) (minimum := 0)
        (rest := comma :: (secondTokens ++ tailTokens ++ [closeParen])) noOperatorAtComma)
  · simpa [secondTokens, tailTokens] using
      (Expr.printReads (tree := args.second) (minimum := 0)
        (rest := tailTokens ++ [closeParen]) (tupleTailBlocked args.tail))
  · simpa [tailTokens] using (tupleItemsTail_print scope _ args.tail)

theorem tupleValue_derivation : TupleValueDerivationAussage := by
  intro scope
  refine ⟨fun args tokens prod => tupleValue_reads scope args prod, tupleValue_print scope, ?_⟩
  let args : TupleValueArgs scope := ⟨.int 1 1, .int 2 2, [], .lit 1, .lit 2, .empty⟩
  exact Rule.satisfiableOfPrint args (tupleValue_print scope args)

end Gabbro.Core.Ast.Surface

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog Waechter

theorem tupleValue_am_ort (scope : Scope) : (tupleValueForm scope).RegelAmOrt := by
  intro args
  change ((((expr 0 args.first).anhaengen (expr 1 args.second)).anhaengen
    (itemCode 2 args.tail)).anhaengen (.einzel (.baueTupel 0 args.types))).code[
      (((expr 0 args.first).anhaengen (expr 1 args.second)).anhaengen (itemCode 2 args.tail)).code.length]?
    = some (.baueTupel 0 args.types)
  simp only [Fragment.anhaengen, Fragment.einzel, List.getElem?_append_right (Nat.le_refl _),
    Nat.sub_self, List.getElem?_cons_zero]

theorem tupleValue_elaboriert : TupleValueElaboriertAussage := by
  intro scope platform args
  rfl

theorem tupleValue_realisiert : TupleValueRealisiertAussage := by
  intro scope platform args s running active live atPc
  exact (tupleValueForm scope).realisiert (tupleValue_am_ort scope) platform args s
    running active live atPc

theorem tupleValue_annahme : TupleValueAnnahmeAussage := by
  intro scope
  exact (tupleValueForm scope).annahme

theorem tupleValue_ideal : TupleValueIdealAussage := by
  intro scope
  refine ⟨tupleValue_am_ort scope, ?_⟩
  intro args
  exact ⟨((tupleValueForm scope).befehl args).bestimmt, fun _ _ _ _ _ => Iff.rfl⟩

theorem tupleValue_einheit : TupleValueEinheitAussage := by
  intro scope platform args
  exact ⟨rfl, ((tupleValueForm scope).befehl args).kommutation⟩

theorem tupleValue_impl : TupleValueImplAussage := by
  intro scope args c s w plans u
  rfl

theorem tupleValue_erhaltung : TupleValueErhaltungAussage := by
  intro scope
  exact (tupleValueForm scope).erhaltung (fun args => by
    change (expr 0 (Expr.tupleValue args.first args.second args.tail)).klauseln.invariant = []
    exact expr_keine_invarianten 0 (Expr.tupleValue args.first args.second args.tail))

theorem tupleValue_regelSicher : TupleValueRegelSicherAussage := by
  intro scope platform args
  exact ((tupleValueForm scope).befehl args).sicher ((tupleValueForm scope).fragment args)
    platform (by
      change (expr 0 (Expr.tupleValue args.first args.second args.tail)).klauseln.invariant = []
      exact expr_keine_invarianten 0 (Expr.tupleValue args.first args.second args.tail))

theorem tupleValue_parse : TupleValueParseAussage := by
  intro scope args text pieces lexed prod
  exact (Surface.tupleValue_derivation scope).parse lexed prod

theorem tupleValue_erfuellbar : TupleValueErfuellbarAmAussage := by
  intro platform start
  let args : Surface.TupleValueArgs [] := ⟨.int 1 1, .int 2 2, [], .lit 1, .lit 2, .empty⟩
  let form := tupleValueForm []
  let E := form.einheit platform args
  let s₀ := (I.start E start).2
  let s₁ := (Befehl.literal 0 1).nach eintritt s₀
  let s₂ := (Befehl.literal 1 2).nach eintritt s₁
  have first : E.system.ISchritt eintritt s₀ () [plan] s₁ :=
    ⟨.literal 0 1, rfl, rfl, rfl⟩
  have second : E.system.ISchritt eintritt s₁ () [plan] s₂ :=
    ⟨.literal 1 2, rfl, rfl, rfl⟩
  have reached : E.system.IErreichbar s₀ s₂ :=
    .schritt eintritt () [plan] (.schritt eintritt () [plan] .start first) second
  refine ⟨args, form.erfuellbar_aus_erreichbar platform start args s₂ reached
    (form.realisiert (tupleValue_am_ort []) platform args s₂ rfl rfl rfl rfl) ?_⟩
  intro g guard
  cases guard

end Gabbro.Core.Ast.Semantik
