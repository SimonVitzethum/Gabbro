module

public import Core.Ast.Aggregate.Carrier.Option.Test
public import Core.Ast.Semantik.Formbeweise

import Init.Omega

/-!
# Option Test

Prove the pinned statements in this file.

- `OptionTestInversionAussage`
- `OptionTestCasesAussage`
- `OptionTestDerivationAussage`
- `OptionTestParseAussage`
- `OptionTestElaboriertAussage`
- `OptionTestRealisiertAussage`
- `OptionTestAnnahmeAussage`
- `OptionTestIdealAussage`
- `OptionTestEinheitAussage`
- `OptionTestImplAussage`
- `OptionTestErhaltungAussage`
- `OptionTestRegelSicherAussage`
- `OptionTestErfuellbarAmAussage`
- `OptionTestInitializedAussage`
-/

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog Gabbro.Core.Text

private theorem optionTestPrint (scope : Scope) (a : OptionTestArgs scope) :
    (optionTestForm scope).produktion.production a
      (((Category.expression scope).printPieces ((optionTestForm scope).produktion.tree a)).map
        PrintedToken.value) := by
  change
    (Expr.optionIsSome a.ref a.visible a.ordinary).printPieces.map PrintedToken.value =
        [.word a.ref.binding.name.val, dot, .word indexIsSomeName.val, openParen, closeParen] ∨
    (Expr.optionIsSome a.ref a.visible a.ordinary).printPieces.map PrintedToken.value =
        openParen :: [.word a.ref.binding.name.val, dot, .word indexIsSomeName.val, openParen,
          closeParen] ++ [closeParen]
  right
  rfl

private theorem optionTest_amOrt (scope : Scope) : (optionTestForm scope).RegelAmOrt := by
  intro args
  change (((Fragment.einzel (Befehl.lesen 0 args.ref.index)).anhaengen
      (Fragment.einzel (Befehl.optionIstBesetzt 0 args.count))).code[1]?) =
    some (Befehl.optionIstBesetzt 0 args.count)
  simp only [Fragment.anhaengen, Fragment.einzel, List.cons_append, List.nil_append,
    List.getElem?_cons_succ, List.getElem?_cons_zero]

private theorem optionTest_keine_invarianten (scope : Scope) (args : OptionTestArgs scope) :
    ((optionTestForm scope).fragment args).klauseln.invariant = [] := by
  change (expr 0 (Expr.optionIsSome args.ref args.visible args.ordinary)).klauseln.invariant = []
  exact expr_keine_invarianten 0 _

private theorem optionIsSomeCast {scope count optTy} (eqT : optTy = indexOptionType count)
    {refT : Local scope optTy} (vis : refT.visible) (ord : ordinaryLocal refT.binding.name) :
    (eqT ▸ refT).visible ∧ ordinaryLocal (eqT ▸ refT).binding.name := by
  subst optTy
  exact ⟨vis, ord⟩

private theorem indexOptionType_inj {a b : Nat} (h : indexOptionType a = indexOptionType b) : a = b := by
  unfold indexOptionType at h
  injection h with hname hlabels hhas hlayout
  simp only [variantLayout, Option.getD] at hlayout
  injection hlayout with hhead htail
  unfold indexType at hhead
  injection hhead with hlo hhi
  omega

private theorem optionIsSomeInvGen {scope count minimum input rest}
    {resultType : Ty .value} {tree : Expr scope resultType}
    {optTy : Ty .value} {refT : Local scope optTy} {vis : refT.visible}
    {ord : ordinaryLocal refT.binding.name}
    (eqT : optTy = indexOptionType count)
    (allowed : minimum ≤ Infix.projection.precedence) :
    ExprTail scope minimum (.variable refT vis ord)
      (dot :: .word indexIsSomeName.val :: openParen :: closeParen :: input) tree rest →
    ExprTail scope minimum (.optionIsSome (eqT ▸ refT) (optionIsSomeCast eqT vis ord).1
      (optionIsSomeCast eqT vis ord).2) input tree rest := by
  intro read
  generalize htok : (dot :: .word indexIsSomeName.val :: openParen :: closeParen :: input) = toks at read
  cases read with
  | stop blocked =>
      exact (blocked ⟨.projection, _, by simpa only [Infix.token] using htok.symm, allowed⟩).elim
  | binary op _ _ _ =>
      have head : dot = op.token := (List.cons.inj htok).1
      have eq : (.projection : Infix) = .arith op :=
        Infix.token_injective (by simpa only [Infix.token] using head)
      cases eq
  | div _ _ _ _ =>
      have head : dot = Infix.div.token := (List.cons.inj htok).1
      have eq : (.projection : Infix) = .div :=
        Infix.token_injective (by simpa only [Infix.token] using head)
      cases eq
  | compare op _ _ _ _ =>
      have head : dot = (Infix.compare op).token := (List.cons.inj htok).1
      have eq : (.projection : Infix) = .compare op :=
        Infix.token_injective (by simpa only [Infix.token] using head)
      cases eq
  | logic op _ _ _ =>
      have head : dot = (Infix.logic op).token := (List.cons.inj htok).1
      have eq : (.projection : Infix) = .logic op :=
        Infix.token_injective (by simpa only [Infix.token] using head)
      cases eq
  | arrayIndex _ _ _ _ _ _ =>
      have head : dot = openBracket := (List.cons.inj htok).1
      have eq : (.projection : Infix) = .index :=
        Infix.token_injective (by simpa only [Infix.token] using head)
      cases eq
  | tupleField _ index' _ _ =>
      have restEq : .word indexIsSomeName.val :: openParen :: closeParen :: input =
          .natural index'.val :: _ := (List.cons.inj htok).2
      cases (List.cons.inj restEq).1
  | recordField _ _ _ _ _ _ =>
      cases eqT
  | textConcat _ _ _ _ =>
      have head : dot = Arith.add.token := (List.cons.inj htok).1
      have eq : (.projection : Infix) = .arith Arith.add :=
        Infix.token_injective (by simpa only [Infix.token] using head)
      cases eq
  | textIndex _ _ _ _ =>
      have head : dot = openBracket := (List.cons.inj htok).1
      have eq : (.projection : Infix) = .index :=
        Infix.token_injective (by simpa only [Infix.token] using head)
      cases eq
  | substring _ _ _ _ _ _ =>
      have head : dot = openBracket := (List.cons.inj htok).1
      have eq : (.projection : Infix) = .index :=
        Infix.token_injective (by simpa only [Infix.token] using head)
      cases eq
  | optionIsSome _ _ _ _ tail =>
      rename_i cnt inp
      cases htok
      have hcnt : cnt = count := indexOptionType_inj eqT
      subst cnt
      exact tail

theorem optionTestInversion : OptionTestInversionAussage := by
  intro scope count minimum input type ref visible ordinary tree rest prec read
  exact optionIsSomeInvGen (refT := ref) (vis := visible) (ord := ordinary) rfl prec read

theorem optionTestCases : OptionTestCasesAussage := by
  intro count slot value frame hframe
  dsimp only
  have hbind : (frame.temp slot).bind (wertAls (indexOptionType count)) = some value := by
    rw [hframe]
    simp only [Option.bind, wertAls, indexOptionType, dif_pos rfl]
    simp
  have hres : ((Befehl.optionIstBesetzt slot count).auswerten frame).temp slot =
      some ⟨.bool, indexOptionPresent value⟩ := by
    rw [Befehl.auswerten, Rahmen.schreibe]
    simp only [Function.update_self]
    rw [hbind]
    rfl
  rw [hres]
  cases value with
  | inl payload =>
      simp only [indexOptionPresent]
      constructor
      · constructor
        · intro _
          exact ⟨payload, rfl⟩
        · intro _
          simp
      · constructor
        · intro h
          cases h
        · intro h
          cases h
  | inr rest =>
      cases rest with
      | inl unit =>
          simp only [indexOptionPresent]
          constructor
          · constructor
            · intro h
              cases h
            · rintro ⟨_, h⟩
              cases h
          · constructor
            · intro _
              cases unit
              rfl
            · intro _
              trivial
      | inr empty => cases empty

theorem optionTestDerivation : OptionTestDerivationAussage := by
  intro scope hne
  obtain ⟨a⟩ := hne
  refine ⟨?_, optionTestPrint scope, ?_⟩
  · intro args tokens production
    change ExprReads scope 0 tokens (Expr.optionIsSome args.ref args.visible args.ordinary) []
    change tokens = [.word args.ref.binding.name.val, dot, .word indexIsSomeName.val, openParen,
        closeParen] ∨
      tokens = openParen :: [.word args.ref.binding.name.val, dot, .word indexIsSomeName.val,
        openParen, closeParen] ++ [closeParen] at production
    rcases production with plain | grouped
    · subst tokens
      exact .atom (.variable args.ref args.visible args.ordinary)
        (ExprTail.optionIsSome args.ref args.visible args.ordinary (by omega) (.stop noOperatorAtEnd))
    · subst tokens
      exact .atom
        (.grouped
          (.atom (.variable args.ref args.visible args.ordinary)
            (ExprTail.optionIsSome args.ref args.visible args.ordinary (by omega)
              (.stop noOperatorAtClose))))
        (.stop noOperatorAtEnd)
  · exact Surface.Rule.satisfiableOfPrint a (optionTestPrint scope a)

theorem optionTestParse : OptionTestParseAussage := by
  intro scope args text pieces lexed production
  exact ((optionTestDerivation scope ⟨args⟩).parse lexed production)

theorem optionTestElaboriert : OptionTestElaboriertAussage := by
  intro scope platform args
  rfl

theorem optionTestRealisiert : OptionTestRealisiertAussage := by
  intro scope platform args s running active live atPc
  exact (optionTestForm scope).realisiert (optionTest_amOrt scope) platform args s
    running active live atPc

theorem optionTestAnnahme : OptionTestAnnahmeAussage := by
  intro scope
  exact Quellform.annahme (optionTestForm scope)

theorem optionTestIdeal : OptionTestIdealAussage := by
  intro scope
  refine ⟨optionTest_amOrt scope, ?_⟩
  intro args
  refine ⟨Befehl.bestimmt _, ?_⟩
  intro c s w plans u
  rfl

theorem optionTestEinheit : OptionTestEinheitAussage := by
  intro scope platform args
  exact ⟨rfl, ((optionTestForm scope).befehl args).kommutation⟩

theorem optionTestImpl : OptionTestImplAussage := by
  intro scope args c s w plans u
  rfl

theorem optionTestErhaltung : OptionTestErhaltungAussage := by
  intro scope
  apply Quellform.erhaltung
  intro args
  exact optionTest_keine_invarianten scope args

theorem optionTestRegelSicher : OptionTestRegelSicherAussage := by
  intro scope platform args
  exact Befehl.sicher ((optionTestForm scope).fragment args) platform
    (optionTest_keine_invarianten scope args) ((optionTestForm scope).befehl args)

theorem optionTestErfuellbarAm : OptionTestErfuellbarAmAussage := by
  intro platform start
  let name : Identifier := keywordName 'x' [] (by decide) (fun _ member => (List.not_mem_nil member).elim)
  let binding : Binding := ⟨name, indexOptionType 0, false, false⟩
  let scope : Scope := [binding]
  let ref : Local scope (indexOptionType 0) := .here
  have visible : ref.visible := by
    dsimp [ref, Local.visible, Ty.valueBinding, Local.nameVisible]
    trivial
  have ordinary : ordinaryLocal ref.binding.name := by
    dsimp [ref, name, ordinaryLocal, ordinaryAtomWord]
    decide
  let a : OptionTestArgs scope := ⟨0, ref, visible, ordinary⟩
  refine ⟨scope, a, ?_⟩
  let form := optionTestForm scope
  let lesen : Befehl := .lesen 0 ref.index
  let s₀ := (I.start (form.einheit platform a) start).2
  let s₁ := lesen.nach eintritt s₀
  have first : (form.einheit platform a).system.ISchritt eintritt s₀ () [plan] s₁ :=
    ⟨lesen, rfl, rfl, rfl⟩
  have reached : (form.einheit platform a).system.IErreichbar s₀ s₁ :=
    .schritt eintritt () [plan] .start first
  refine form.erfuellbar_aus_erreichbar platform start a s₁ reached ?_ ?_
  · exact form.realisiert (optionTest_amOrt scope) platform a s₁ rfl rfl rfl rfl
  · intro g guard
    change (Befehl.optionIstBesetzt 0 0).guard (s₁.lokal eintritt) = some g at guard
    simp only [Befehl.guard] at guard
    cases guard

theorem optionTestInitialized : OptionTestInitializedAussage := by
  intro platform start
  let cname : Identifier := keywordName 'c' [] (by decide) (fun _ member => (List.not_mem_nil member).elim)
  let scope : Scope := [⟨cname, .carrierSchema 0 [] .productEnd false, false, false⟩]
  have resolved : scope.carrierCount cname = some 0 := by
    dsimp [scope, cname]
    decide
  let xname : Identifier := keywordName 'x' [] (by decide) (fun _ member => (List.not_mem_nil member).elim)
  have xOrdinary : xname.val ≠ "mut".toList ∧ ordinaryLocal xname := by
    constructor
    · dsimp [xname]
      decide
    · dsimp [ordinaryLocal, ordinaryAtomWord, xname]
      decide
  let init : OptionInitializer scope 0 := .absent
  let letOpt : Stmt none scope (⟨xname, indexOptionType 0, false, false⟩ :: scope) :=
    .letOption false xname xOrdinary cname resolved init
  let extScope : Scope := ⟨xname, indexOptionType 0, false, false⟩ :: scope
  let ref : Local extScope (indexOptionType 0) := .here
  have refVisible : ref.visible := by
    dsimp [ref, Local.visible, Ty.valueBinding, Local.nameVisible]
    trivial
  have refOrdinary : ordinaryLocal ref.binding.name := by
    dsimp [ref, xname, ordinaryLocal, ordinaryAtomWord]
    decide
  let optExpr : Expr extScope .bool := Expr.optionIsSome ref refVisible refOrdinary
  let yname : Identifier := keywordName 'y' [] (by decide) (fun _ member => (List.not_mem_nil member).elim)
  have yOrdinary : yname.val ≠ "mut".toList := by
    dsimp [yname]
    decide
  let letY : Stmt none extScope (⟨yname, .bool, false, false⟩ :: extScope) :=
    .letValue yname yOrdinary optExpr
  let tree : BracedBlock none scope :=
    .braces (.step letOpt (.step letY .done))
  let E := elaborieren (category := .block scope none) platform tree
  let s₀ := (I.start E start).2
  let s₁ := (optionInstruction 0 init).nach eintritt s₀
  let s₂ := (Befehl.bindeWert 0 (indexOptionType 0) false).nach eintritt s₁
  let s₃ := (Befehl.lesen 0 ref.index).nach eintritt s₂
  have step₀ : E.system.ISchritt eintritt s₀ () [plan] s₁ := ⟨_, rfl, rfl, rfl⟩
  have step₁ : E.system.ISchritt eintritt s₁ () [plan] s₂ := ⟨_, rfl, rfl, rfl⟩
  have step₂ : E.system.ISchritt eintritt s₂ () [plan] s₃ := ⟨_, rfl, rfl, rfl⟩
  have reached : E.system.IErreichbar s₀ s₃ :=
    .schritt eintritt () [plan]
      (.schritt eintritt () [plan] (.schritt eintritt () [plan] .start step₀) step₁) step₂
  let b : Befehl := .optionIstBesetzt 0 0
  refine ⟨scope, tree, Ast.print (category := .block scope none) tree, s₃, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Ast.parse_print (category := .block scope none) tree
  · exact reached
  · change E.system.kopf s₃ eintritt = some (.optionIstBesetzt 0 0)
    rfl
  · change (s₃.lokal eintritt).temp 0 = some ⟨indexOptionType 0, (.inr (.inl PUnit.unit) : Wert (indexOptionType 0))⟩
    rfl
  · exact ⟨b, rfl, rfl, rfl⟩
  · exact ⟨b, rfl, rfl, rfl⟩

end Gabbro.Core.Ast.Semantik
