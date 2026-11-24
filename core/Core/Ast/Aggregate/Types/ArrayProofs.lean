module

public import Core.Ast.Aggregate.Types
public import Core.Ast.Semantik.Formbeweise
public import Core.Ast.ProgramSurface

import Init.Omega

/-!
# Fixed-size array type

- `ArrayTypeInversionAussage`
- `ArrayTypeSuffixAussage`
- `ArrayTypeDerivationAussage`
- `ArrayTypeIndexAussage`
- `ArrayTypeSyntaxErfuellbarAussage`
- `ArrayTypeParseAussage`
- `ArrayTypeElaboriertAussage`
- `ArrayTypeRealisiertAussage`
- `ArrayTypeAnnahmeAussage`
- `ArrayTypeIdealAussage`
- `ArrayTypeEinheitAussage`
- `ArrayTypeImplAussage`
- `ArrayTypeErhaltungAussage`
- `ArrayTypeRegelSicherAussage`
- `ArrayTypeErfuellbarAmAussage`
-/

@[expose] public section

open Gabbro.Core.Text

namespace Gabbro.Core.Ast

theorem arrayTypeInversion : ArrayTypeInversionAussage := by
  intro input type rest read
  cases read with
  | array count bound elementRead boundRead =>
      exact ⟨_, _, bound, _, elementRead, boundRead, rfl⟩

theorem arrayTypeSuffix : ArrayTypeSuffixAussage := by
  intro input type rest read
  obtain ⟨element, count, bound, boundInput, elementRead, boundRead, _⟩ :=
    arrayTypeInversion read
  have closeSuffix : closeBracket :: rest <:+ boundInput := ExprReads.consumes boundRead
  have restSuffix : rest <:+ boundInput := (List.suffix_cons closeBracket rest).trans closeSuffix
  have semicolonSuffix : semicolon :: boundInput <:+ input := TypeReads.consumes elementRead
  have boundSuffix : boundInput <:+ input := (List.suffix_cons semicolon boundInput).trans semicolonSuffix
  exact restSuffix.trans boundSuffix

theorem arrayTypeDerivation : ArrayTypeDerivationAussage := by
  intro element count rest valid
  have closed : ∀ more, semicolon :: (.natural count :: closeBracket :: rest) ≠ keyword "in" :: more := by
    intro more same
    cases same
  have elementRead := WrittenType.printReads element valid closed
  have boundRead : ExprReads [] 0 (.natural count :: closeBracket :: rest)
      (Expr.lit count : Expr [] (.int count count)) (closeBracket :: rest) :=
    .atom .lit (.stop noOperatorAtCloseBracket)
  simpa only [WrittenType.printPieces, List.map_append, List.map_cons, List.map_nil,
    List.append_assoc, List.singleton_append, List.cons_append, List.nil_append,
    printOpenBracket, printSemicolon, printCloseBracket, printInteger,
    printPunctuation, PrintedToken.unquoted,
    (show (Token.punctuation "[".toList : Token) = openBracket by decide),
    (show (Token.punctuation ";".toList : Token) = semicolon by decide),
    (show (Token.punctuation "]".toList : Token) = closeBracket by decide)] using
    (TypeReads.array count (Expr.lit count) elementRead boundRead)

theorem arrayTypeIndex : ArrayTypeIndexAussage := by
  intro element count
  rfl

theorem arrayTypeSyntaxErfuellbar : ArrayTypeSyntaxErfuellbarAussage := by
  let element : WrittenType := .bool
  let count : Nat := 0
  let words := (WrittenType.array element count).printPieces
  obtain ⟨pieces, lexed, aligned⟩ := PrintedToken.renderLexed 0 words
  refine ⟨element, count, PrintedToken.render words, pieces, ?_, lexed, ?_⟩
  · change element.valid
    trivial
  · rw [aligned]
    simpa using (arrayTypeDerivation element count ([] : List Token) (by change element.valid; trivial))

end Gabbro.Core.Ast

namespace Gabbro.Core.Ast.Semantik

open Maschine Annahme Katalog Waechter

private theorem typeRootLookup (p : Fragment) (b : Befehl) :
    (p.anhaengen (.einzel b)).code[p.code.length]? = some b := by
  simp only [Fragment.anhaengen, Fragment.einzel, List.getElem?_append_right (Nat.le_refl _),
    Nat.sub_self, List.getElem?_cons_zero]

private theorem arrayType_am_ort (ctx : Scope × Option (Ty .value)) :
    (typeUseForm ctx arrayTypeUse).RegelAmOrt := by
  intro args
  change (((expr 0 args.val.value).anhaengen
    (.einzel (.bindeWert 0 args.val.written.type false))).code)[(expr 0 args.val.value).code.length]? =
      some (.bindeWert 0 args.val.written.type false)
  exact typeRootLookup _ _

private theorem arrayType_keine_invarianten (ctx : Scope × Option (Ty .value))
    (args : {a : Surface.MutableLocalArgs ctx.1 ctx.2 // arrayTypeUse a.written}) :
    ((typeUseForm ctx arrayTypeUse).fragment args).klauseln.invariant = [] := by
  change (stmt (Stmt.letMutable args.val.name args.val.ordinary args.val.written args.val.valid
    args.val.value args.val.fits)).klauseln.invariant = []
  exact stmt_keine_invarianten _

theorem arrayTypeParse : ArrayTypeParseAussage := by
  intro ctx args text pieces lexed production
  exact (Surface.mutableLocal_entry ctx.1 ctx.2).parse lexed production

theorem arrayTypeElaboriert : ArrayTypeElaboriertAussage := by
  intro ctx platform args
  rfl

theorem arrayTypeRealisiert : ArrayTypeRealisiertAussage := by
  intro ctx platform args s running active live atPc
  exact (typeUseForm ctx arrayTypeUse).realisiert (arrayType_am_ort ctx) platform args s running active live atPc

theorem arrayTypeAnnahme : ArrayTypeAnnahmeAussage := by
  intro ctx
  exact Quellform.annahme (typeUseForm ctx arrayTypeUse)

theorem arrayTypeIdeal : ArrayTypeIdealAussage := by
  intro ctx
  refine ⟨arrayType_am_ort ctx, ?_⟩
  intro args
  refine ⟨Befehl.bestimmt _, ?_⟩
  intro c s w plans u
  rfl

theorem arrayTypeEinheit : ArrayTypeEinheitAussage := by
  intro ctx platform args
  exact ⟨rfl, ((typeUseForm ctx arrayTypeUse).befehl args).kommutation⟩

theorem arrayTypeImpl : ArrayTypeImplAussage := by
  intro ctx args c s w plans u
  rfl

theorem arrayTypeErhaltung : ArrayTypeErhaltungAussage := by
  intro ctx
  apply Quellform.erhaltung
  intro args
  exact arrayType_keine_invarianten ctx args

theorem arrayTypeRegelSicher : ArrayTypeRegelSicherAussage := by
  intro ctx platform args
  exact Befehl.sicher ((typeUseForm ctx arrayTypeUse).fragment args) platform
    (arrayType_keine_invarianten ctx args) ((typeUseForm ctx arrayTypeUse).befehl args)

theorem arrayTypeErfuellbarAm : ArrayTypeErfuellbarAmAussage := by
  intro platform start
  let name : Identifier :=
    ⟨['x'], 'x', [], rfl, Or.inl (Or.inl ⟨by change 97 ≤ 120; omega, by change 120 ≤ 122; omega⟩),
      fun _ member => (List.not_mem_nil member).elim⟩
  have ordinary : ordinaryLocal name := (directName_of_singleton (name := name) rfl).1
  let written : WrittenType := .array .bool 1
  let value : Expr [] written.type :=
    .arrayValue (.next (.trueLit : Expr [] .bool) .empty) rfl (fun i => by
      have bound : i.val < 1 := by simpa using i.isLt
      have ival : i.val = 0 := by omega
      cases i with
      | mk val isLt =>
          simp only at ival
          subst val
          change Fits .bool .bool
          trivial)
  let argsVal : Surface.MutableLocalArgs [] none :=
    ⟨name, ordinary, written, by change written.valid; trivial, written.type, value, by rfl⟩
  let args : {a : Surface.MutableLocalArgs [] none // arrayTypeUse a.written} :=
    ⟨argsVal, by change arrayTypeUse (WrittenType.array .bool 1); simp only [arrayTypeUse]⟩
  let form := typeUseForm ([], none) arrayTypeUse
  let E := form.einheit platform args
  let s₀ := (I.start E start).2
  let s₁ := (Befehl.wahrheitswert 0 true).nach eintritt s₀
  let s₂ := (Befehl.baueArray 0 .bool 1).nach eintritt s₁
  have step1 : E.system.ISchritt eintritt s₀ () [plan] s₁ :=
    ⟨.wahrheitswert 0 true, rfl, rfl, rfl⟩
  have step2 : E.system.ISchritt eintritt s₁ () [plan] s₂ :=
    ⟨.baueArray 0 .bool 1, rfl, rfl, rfl⟩
  have reached : E.system.IErreichbar s₀ s₂ :=
    .schritt eintritt () [plan] (.schritt eintritt () [plan] .start step1) step2
  refine ⟨args, form.erfuellbar_aus_erreichbar platform start args s₂ reached
    (form.realisiert (arrayType_am_ort ([], none)) platform args s₂ rfl rfl rfl rfl) ?_⟩
  intro g guard
  cases guard

end Gabbro.Core.Ast.Semantik
