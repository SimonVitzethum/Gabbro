module

public import Core.Ast.Aggregate.Carrier.Option.Construct
public import Core.Ast.Semantik.Formbeweise

/-!
# Option Construct

Prove the pinned statements in this file.

- `OptionInitializerInversionAussage`
- `OptionInitializerPrintAussage`
- `OptionAbsentAussage`
- `OptionPresentAussage`
- `OptionLetDerivationAussage`
- `OptionReturnDerivationAussage`
- `OptionConstructorParseAussage`
- `OptionConstructorElaboriertAussage`
- `OptionConstructorRealisiertAussage`
- `OptionConstructorAnnahmeAussage`
- `OptionConstructorIdealAussage`
- `OptionConstructorEinheitAussage`
- `OptionConstructorImplAussage`
- `OptionConstructorErhaltungAussage`
- `OptionConstructorRegelSicherAussage`
- `OptionLetErfuellbarAmAussage`
- `OptionReturnErfuellbarAmAussage`
-/

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Annahme Katalog Waechter
open Gabbro.Core.Text

private theorem someToken_ne_none : (.word indexSomeName.val : Token) ≠ .word indexNoneName.val := by
  intro h
  have hw : indexSomeName.val = indexNoneName.val := by
    injection h
  have hs : ("Some".toList : List Char) = "None".toList := by
    simpa [indexSomeName, indexNoneName] using hw
  have hc : ('S' : Char) = 'N' := (List.cons.inj hs).1
  exact (by decide : ('S' : Char) ≠ 'N') hc

private theorem noneToken_ne_some : (.word indexNoneName.val : Token) ≠ .word indexSomeName.val :=
  fun h => someToken_ne_none h.symm

theorem optionInitializerInversion : OptionInitializerInversionAussage := by
  constructor
  · intro scope count input value rest read
    generalize htok : .word indexSomeName.val :: input = toks at read
    cases read with
    | absent =>
        exact (someToken_ne_none (List.cons.inj htok).1).elim
    | present fits exprRead =>
        rename_i lo hi operandInput operand
        refine ⟨lo, hi, operand, fits, operandInput, ?_⟩
        exact ⟨(List.cons.inj htok).2, exprRead, rfl⟩
  · intro scope count input value rest read
    generalize htok : .word indexNoneName.val :: input = toks at read
    cases read with
    | absent =>
        exact ⟨(List.cons.inj htok).2, rfl⟩
    | present fits exprRead =>
        exact (noneToken_ne_some (List.cons.inj htok).1).elim

theorem optionInitializerPrint : OptionInitializerPrintAussage := by
  intro scope count value rest
  cases value with
  | absent =>
      exact OptionInitializerReads.absent
  | present operand fits =>
      have someTok : indexSomeName.print.value = .word indexSomeName.val := by rfl
      have openTok : printOpen.value = openParen := by rfl
      have closeTok : printClose.value = closeParen := by rfl
      apply OptionInitializerReads.present fits
      simpa only [OptionInitializer.printPieces, Expr.printTokens, List.map_append, List.map_cons,
        List.map_nil, someTok, openTok, closeTok, List.cons_append, List.nil_append,
        List.append_assoc] using
        (Expr.printReads (tree := operand) (minimum := 0) (rest := closeParen :: rest) noOperatorAtClose)

private theorem wertAls_indexPresent {count : Nat} {lo hi : Int}
    (fits : Fits (.int lo hi) (indexType count)) (value : Wert (.int lo hi)) :
    wertAls (indexType count) ⟨.int lo hi, value⟩ =
      some (Wert.widen (.int lo hi) (indexType count) fits value) := by
  have fits' : Fits (.int lo hi) (.int 0 ((count : Int) - 1)) := fits
  simp only [indexType, wertAls]
  rw [dif_pos ⟨Int.le_trans fits'.1 value.unten, Int.le_trans value.oben fits'.2⟩]
  dsimp [Wert.widen]

theorem optionAbsent : OptionAbsentAussage := by
  intro scope count slot frame
  dsimp
  simp [optionInstruction, Befehl.auswerten, Rahmen.schreibe, variantActual, variantInject,
    indexOptionPayloads, indexOptionLabels, indexOptionType, variantValueType, indexType,
    indexSomeName, indexNoneName]

theorem optionPresent : OptionPresentAussage := by
  intro scope count lo hi slot operand fits frame value htemp
  dsimp
  have hw := wertAls_indexPresent fits value
  simp [optionInstruction, Befehl.auswerten, Rahmen.schreibe, variantActual, variantInject,
    indexOptionPayloads, indexOptionLabels, indexOptionType, variantValueType, htemp, hw,
    indexSomeName, indexNoneName]

private theorem letOption_prints (ctx : OptionContext) (a : OptionLetArgs ctx) :
    (optionLetForm ctx).produktion.production a
      (((Category.statement ctx.1 ctx.2).printPieces ((optionLetForm ctx).produktion.tree a)).map
        PrintedToken.value) := by
  dsimp [optionLetForm]
  let typePieces := (WrittenType.indexOption a.carrier a.count).printPieces.map PrintedToken.value
  let valPieces := a.value.printPieces.map PrintedToken.value
  refine ⟨typePieces ++ (assignment :: valPieces), valPieces, ?_, ?_, ?_⟩
  · have letTok : letName.print.value = letKeyword := by rfl
    have mutTok : printMut.value = .word "mut".toList := by rfl
    have colonTok : printColon.value = colon := by rfl
    have optTok : printOption.value = keyword "option" := by rfl
    have idxTok : printIndex.value = keyword "index" := by rfl
    have intoTok : printInto.value = keyword "into" := by rfl
    have assignTok : printAssignment.value = assignment := by rfl
    have semiTok : printSemicolon.value = semicolon := by rfl
    have carrierTok : a.carrier.print.value = .word a.carrier.val := by rfl
    simp only [Category.printPieces, Stmt.printPieces, List.map_append, List.map_cons, List.map_nil,
      WrittenType.printPieces, optionLetHead, letTok, mutTok, colonTok, optTok, idxTok, intoTok,
      assignTok, semiTok, carrierTok, List.cons_append, List.append_assoc]
  · exact WrittenType.printReads (.indexOption a.carrier a.count) a.resolved (by
      intro more h
      cases h)
  · exact optionInitializerPrint ctx.1 a.count a.value [semicolon]

private theorem returnOption_prints (ctx : OptionContext) (a : OptionReturnArgs ctx) :
    (optionReturnForm ctx).produktion.production a
      (((Category.statement ctx.1 ctx.2).printPieces ((optionReturnForm ctx).produktion.tree a)).map
        PrintedToken.value) := by
  dsimp [optionReturnForm]
  refine ⟨a.value.printPieces.map PrintedToken.value, ?_, ?_⟩
  · have retTok : returnName.print.value = returnKeyword := by rfl
    have semiTok : printSemicolon.value = semicolon := by rfl
    simp only [Category.printPieces, Stmt.printPieces, List.map_append, List.map_cons, List.map_nil,
      retTok, semiTok, List.cons_append]
  · exact optionInitializerPrint ctx.1 a.count a.value [semicolon]

theorem optionLetDerivation : OptionLetDerivationAussage := by
  intro ctx nonemptyArgs
  rcases nonemptyArgs with ⟨a⟩
  refine ⟨?_, letOption_prints ctx, ?_⟩
  · intro tokens prod
    rcases prod with ⟨input, rhs, rfl, typeRead, initRead⟩
    exact StmtReads.letOption a.mutable a.name a.ordinary a.carrier a.resolved typeRead initRead
  · exact Surface.Rule.satisfiableOfPrint a (letOption_prints ctx a)

theorem optionReturnDerivation : OptionReturnDerivationAussage := by
  intro ctx nonemptyArgs
  rcases nonemptyArgs with ⟨a⟩
  refine ⟨?_, returnOption_prints ctx, ?_⟩
  · intro tokens prod
    rcases prod with ⟨input, rfl, initRead⟩
    exact StmtReads.retOption a.declared initRead
  · exact Surface.Rule.satisfiableOfPrint a (returnOption_prints ctx a)

private theorem letOption_amOrt (ctx : OptionContext) : (optionLetForm ctx).RegelAmOrt := by
  intro a
  change ((((optionOperand 0 a.value).code ++ [optionInstruction 0 a.value]) ++
    [Befehl.bindeWert 0 (indexOptionType a.count) false])[
      (optionOperand 0 a.value).code.length]?) = some (optionInstruction 0 a.value)
  have hlt : (optionOperand 0 a.value).code.length <
      ((optionOperand 0 a.value).code ++ [optionInstruction 0 a.value]).length := by simp
  rw [List.getElem?_append_left hlt]
  simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero]

private theorem returnOption_amOrt (ctx : OptionContext) : (optionReturnForm ctx).RegelAmOrt := by
  intro a
  change ((((optionOperand 0 a.value).code ++ [optionInstruction 0 a.value]) ++
    [Befehl.zurueck 0 (indexOptionType a.count)])[
      (optionOperand 0 a.value).code.length]?) = some (optionInstruction 0 a.value)
  have hlt : (optionOperand 0 a.value).code.length <
      ((optionOperand 0 a.value).code ++ [optionInstruction 0 a.value]).length := by simp
  rw [List.getElem?_append_left hlt]
  simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero]

private theorem letOption_keineInvarianten (ctx : OptionContext) (a : OptionLetArgs ctx) :
    ((optionLetForm ctx).fragment a).klauseln.invariant = [] := by
  change (stmt (Stmt.letOption a.mutable a.name a.ordinary a.carrier a.resolved a.value)).klauseln.invariant = []
  exact stmt_keine_invarianten _

private theorem returnOption_keineInvarianten (ctx : OptionContext) (a : OptionReturnArgs ctx) :
    ((optionReturnForm ctx).fragment a).klauseln.invariant = [] := by
  change (stmt (Stmt.retOption a.declared a.value)).klauseln.invariant = []
  exact stmt_keine_invarianten _

theorem optionConstructorParse : OptionConstructorParseAussage := by
  constructor
  · intro ctx args text pieces lexed prod
    exact (optionLetDerivation ctx ⟨args⟩).parse lexed prod
  · intro ctx args text pieces lexed prod
    exact (optionReturnDerivation ctx ⟨args⟩).parse lexed prod

theorem optionConstructorElaboriert : OptionConstructorElaboriertAussage := by
  constructor
  · intro ctx platform args
    rfl
  · intro ctx platform args
    rfl

theorem optionConstructorRealisiert : OptionConstructorRealisiertAussage := by
  constructor
  · intro ctx platform args s running active live atPc
    exact (optionLetForm ctx).realisiert (letOption_amOrt ctx) platform args s running active live atPc
  · intro ctx platform args s running active live atPc
    exact (optionReturnForm ctx).realisiert (returnOption_amOrt ctx) platform args s running active live atPc

theorem optionConstructorAnnahme : OptionConstructorAnnahmeAussage := by
  constructor
  · intro ctx
    exact (optionLetForm ctx).annahme
  · intro ctx
    exact (optionReturnForm ctx).annahme

theorem optionConstructorIdeal : OptionConstructorIdealAussage := by
  constructor
  · intro ctx
    refine ⟨letOption_amOrt ctx, ?_⟩
    intro args
    exact ⟨((optionLetForm ctx).befehl args).bestimmt, fun _ _ _ _ _ => Iff.rfl⟩
  · intro ctx
    refine ⟨returnOption_amOrt ctx, ?_⟩
    intro args
    exact ⟨((optionReturnForm ctx).befehl args).bestimmt, fun _ _ _ _ _ => Iff.rfl⟩

theorem optionConstructorEinheit : OptionConstructorEinheitAussage := by
  constructor
  · intro ctx platform args
    exact ⟨rfl, ((optionLetForm ctx).befehl args).kommutation⟩
  · intro ctx platform args
    exact ⟨rfl, ((optionReturnForm ctx).befehl args).kommutation⟩

theorem optionConstructorImpl : OptionConstructorImplAussage := by
  constructor
  · intro ctx args c s w plans u
    rfl
  · intro ctx args c s w plans u
    rfl

theorem optionConstructorErhaltung : OptionConstructorErhaltungAussage := by
  constructor
  · intro ctx
    exact (optionLetForm ctx).erhaltung (letOption_keineInvarianten ctx)
  · intro ctx
    exact (optionReturnForm ctx).erhaltung (returnOption_keineInvarianten ctx)

theorem optionConstructorRegelSicher : OptionConstructorRegelSicherAussage := by
  constructor
  · intro ctx platform args
    exact ((optionLetForm ctx).befehl args).sicher ((optionLetForm ctx).fragment args) platform
      (letOption_keineInvarianten ctx args)
  · intro ctx platform args
    exact ((optionReturnForm ctx).befehl args).sicher ((optionReturnForm ctx).fragment args) platform
      (returnOption_keineInvarianten ctx args)

theorem optionLetErfuellbarAm : OptionLetErfuellbarAmAussage := by
  intro platform start
  let carrier : Identifier := keywordName 'c' [] (by decide) (fun _ member => (List.not_mem_nil member).elim)
  let scope : Scope := [⟨carrier, .carrierSchema 0 [] .productEnd false, false, false⟩]
  have resolved : scope.carrierCount carrier = some 0 := by decide
  let name : Identifier := keywordName 'x' [] (by decide) (fun _ member => (List.not_mem_nil member).elim)
  have ordinary : name.val ≠ "mut".toList ∧ ordinaryLocal name := by
    constructor
    · change ('x' :: []) ≠ ('m' :: 'u' :: 't' :: [])
      decide
    · dsimp [ordinaryLocal, ordinaryAtomWord, name]
      decide
  let ctx : OptionContext := (scope, none)
  let a : OptionLetArgs ctx := ⟨false, name, ordinary, carrier, 0, resolved, .absent⟩
  refine ⟨ctx, a, rfl, rfl, ?_⟩
  let form := optionLetForm ctx
  let E := form.einheit platform a
  let s := (I.start E start).2
  exact form.erfuellbar_aus_erreichbar platform start a s .start
    (form.realisiert (letOption_amOrt ctx) platform a s rfl rfl rfl rfl)
    (by intro g guard; cases guard)

theorem optionReturnErfuellbarAm : OptionReturnErfuellbarAmAussage := by
  intro platform start
  let carrier : Identifier := keywordName 'c' [] (by decide) (fun _ member => (List.not_mem_nil member).elim)
  let scope : Scope := [⟨carrier, .carrierSchema 1 [] .productEnd false, false, false⟩]
  have resolved : scope.carrierCount carrier = some 1 := by decide
  let ctx : OptionContext := (scope, some (indexOptionType 1))
  have fits : Fits (.int 0 0) (indexType 1) := by
    change 0 ≤ (0 : Int) ∧ (0 : Int) ≤ (1 : Int) - 1
    decide
  let a : OptionReturnArgs ctx := ⟨1, rfl, .present (Expr.lit 0) fits⟩
  refine ⟨ctx, a, ?_, ?_⟩
  · exact ⟨0, 0, Expr.lit 0, fits, rfl⟩
  · let form := optionReturnForm ctx
    let E := form.einheit platform a
    let s₀ := (I.start E start).2
    let litCmd : Befehl := .literal 0 0
    let s₁ := litCmd.nach eintritt s₀
    have step : E.system.ISchritt eintritt s₀ () [plan] s₁ := ⟨litCmd, rfl, rfl, rfl⟩
    have reached : E.system.IErreichbar s₀ s₁ := .schritt eintritt () [plan] .start step
    exact form.erfuellbar_aus_erreichbar platform start a s₁ reached
      (form.realisiert (returnOption_amOrt ctx) platform a s₁ rfl rfl rfl rfl)
      (by intro g guard; cases guard)

end Gabbro.Core.Ast.Semantik
