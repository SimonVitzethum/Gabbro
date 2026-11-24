module

public import Core.Ast.Aggregate.Carrier.Option.Match
public import Core.Ast.Semantik.Formbeweise

/-!
# Option Match

Prove the pinned statements in this file.

- `OptionMatchPayloadAussage`
- `OptionMatchDerivationAussage`
- `OptionMatchParseAussage`
- `OptionMatchElaboriertAussage`
- `OptionMatchRealisiertAussage`
- `OptionMatchAnnahmeAussage`
- `OptionMatchIdealAussage`
- `OptionMatchEinheitAussage`
- `OptionMatchImplAussage`
- `OptionMatchErhaltungAussage`
- `OptionMatchRegelSicherAussage`
- `OptionMatchErfuellbarAmAussage`
-/

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Annahme Katalog Waechter Gabbro.Core.Text

private theorem om_amOrt (ctx : OptionContext) : (optionMatchForm ctx).RegelAmOrt := by
  intro a
  let head := (.waehleVariante 0 a.val.name a.val.labels a.val.payloads
    (variantArms a.val.arms).branches : Befehl)
  let valueCode := (expr 0 a.val.value).code
  let bodyCode := (variantArms a.val.arms).body.code
  change (((valueCode ++ [head]) ++ bodyCode)[valueCode.length]?) = some head
  have hlt : valueCode.length < (valueCode ++ [head]).length := by simp
  rw [List.getElem?_append_left hlt]
  rw [List.getElem?_append_right (Nat.le_refl _)]
  simp

private theorem om_arms_inv (result : Option (Ty .value)) (scope : Scope) (allowed : Bool)
    (labels : List Identifier) (payloads : List (Option (Ty .value)))
    (arms : VariantArms result scope allowed labels payloads) :
    (variantArms arms).body.klauseln.invariant = [] := by
  let rec blockInv {res : Option (Ty .value)} {before after : Scope} (t : Block res before after) :
      (block t).klauseln.invariant = [] :=
    match t with
    | .done => rfl
    | .step first rest => by
        change (stmt first).klauseln.invariant ++ (block rest).klauseln.invariant = []
        rw [stmt_keine_invarianten, blockInv rest]
        rfl
  have bracedInv : ∀ {res : Option (Ty .value)} {before : Scope} (t : BracedBlock res before),
      (bracedBlock t).klauseln.invariant = [] := by
    intro res before t
    rcases t with ⟨body⟩
    change (block body).klauseln.invariant ++ [] = []
    rw [blockInv body]
    rfl
  let rec go {s : Scope} {a : Bool} {l : List Identifier} {p : List (Option (Ty .value))}
      (ar : VariantArms result s a l p) : (variantArms ar).body.klauseln.invariant = [] :=
    match ar with
    | .done => rfl
    | .nullary _ _ body rest => by
        simp [variantArms, MatchCode.prepend, Fragment.anhaengen, Fragment.einzel, bracedInv,
          go rest, Quellklauseln.anhaengen, Quellklauseln.leer]
    | .payload _ _ _ body rest => by
        simp [variantArms, MatchCode.prepend, Fragment.anhaengen, Fragment.einzel, bracedInv,
          go rest, Quellklauseln.anhaengen, Quellklauseln.leer]
    | .wildcard body _ _ => by
        simp [variantArms, bracedInv, Quellklauseln.leer]
  exact go arms

private theorem om_keine_invarianten (ctx : OptionContext) (a : OptionMatchArgs ctx) :
    ((optionMatchForm ctx).fragment a).klauseln.invariant = [] := by
  change ((((expr 0 a.val.value).anhaengen
    (Fragment.einzel (Befehl.waehleVariante 0 a.val.name a.val.labels a.val.payloads
      (variantArms a.val.arms).branches))).anhaengen
      (variantArms a.val.arms).body).klauseln.invariant = [])
  simp [Fragment.anhaengen, Fragment.einzel, Quellklauseln.anhaengen, Quellklauseln.leer,
    expr_keine_invarianten, om_arms_inv]

private theorem om_arms_printReads {result : Option (Ty .value)} {scope : Scope} {allowed : Bool}
    {labels : List Identifier} {payloads : List (Option (Ty .value))}
    (arms : VariantArms result scope allowed labels payloads) (more : List Token) :
    VariantArmsRead result scope allowed
      (arms.printPieces.map PrintedToken.value ++ closeBrace :: more) arms more := by
  let rec go {res : Option (Ty .value)} {s : Scope} {a : Bool} {l : List Identifier}
      {p : List (Option (Ty .value))} (ar : VariantArms res s a l p) (rest : List Token) :
      VariantArmsRead res s a (ar.printPieces.map PrintedToken.value ++ closeBrace :: rest) ar rest := by
    cases ar with
    | done =>
        simp only [VariantArms.printPieces, List.map_nil, List.nil_append]
        exact .done
    | nullary label caseName body tail =>
        simpa [VariantArms.printPieces, Identifier.print, printMatchArrow, matchArrow] using
          (.nullary label caseName
            (BracedBlock.printReads body (tail.printPieces.map PrintedToken.value ++ closeBrace :: rest))
            (go tail rest))
    | payload label binder ord body tail =>
        simpa [VariantArms.printPieces, Identifier.print, printMatchArrow, matchArrow] using
          (.payload label binder ord body
            (BracedBlock.printReads body (tail.printPieces.map PrintedToken.value ++ closeBrace :: rest))
            (go tail rest))
    | wildcard body nonempty shape =>
        simpa [VariantArms.printPieces, Identifier.print, printMatchArrow, matchArrow, discardName] using
          (.wildcard nonempty shape (BracedBlock.printReads body (closeBrace :: rest)))
  exact go arms more

private theorem om_print (ctx : OptionContext) (a : OptionMatchArgs ctx) :
    (optionMatchForm ctx).produktion.production a
      (((Category.statement ctx.1 ctx.2).printPieces ((optionMatchForm ctx).produktion.tree a)).map
        PrintedToken.value) := by
  change ∃ input arms,
    (printMatch :: a.val.value.printPieces ++ [printOpenBrace] ++
      a.val.arms.printPieces ++ [printCloseBrace]).map PrintedToken.value =
        keyword "match" :: input ∧
    ExprReads ctx.1 0 input a.val.value (openBrace :: arms) ∧
    VariantArmsRead ctx.2 ctx.1 false arms a.val.arms []
  refine ⟨a.val.value.printTokens ++
      (openBrace :: a.val.arms.printPieces.map PrintedToken.value ++ [closeBrace]),
    a.val.arms.printPieces.map PrintedToken.value ++ [closeBrace], ?_, ?_, ?_⟩
  · simp [printMatch, printProgramWord, keywordName, Identifier.print, keyword,
      Expr.printTokens, printOpenBrace, printCloseBrace]
  · exact Expr.printReads a.val.value noOperatorAtOpenBrace
  · exact om_arms_printReads a.val.arms []

theorem optionMatchPayload : OptionMatchPayloadAussage := by
  intro count value
  change (∀ index : Wert (indexType count), value = .inl index →
      variantCase (indexOptionPayloads count) value = (0, some ⟨indexType count, index⟩)) ∧
    (value = .inr (.inl PUnit.unit) → variantCase (indexOptionPayloads count) value = (1, none))
  constructor
  · intro index hvalue
    subst value
    simp [indexOptionPayloads, variantCase, variantPayload]
  · intro hvalue
    subst value
    simp [indexOptionPayloads, variantCase, variantPayload]

theorem optionMatchDerivation : OptionMatchDerivationAussage := by
  intro ctx hne
  rcases hne with ⟨a⟩
  refine ⟨?_, ?_, ?_⟩
  · intro a' tokens prod
    change ∃ input arms, tokens = keyword "match" :: input ∧
      ExprReads ctx.1 0 input a'.val.value (openBrace :: arms) ∧
      VariantArmsRead ctx.2 ctx.1 false arms a'.val.arms [] at prod
    rcases prod with ⟨input, arms, same, valueRead, armsRead⟩
    rw [same]
    exact .variantMatch valueRead armsRead
  · intro a'
    exact om_print ctx a'
  · exact Surface.Rule.satisfiableOfPrint a (om_print ctx a)

theorem optionMatchParse : OptionMatchParseAussage := by
  intro ctx a text pieces lexed production
  apply (Category.statement ctx.1 ctx.2).syntax.parse_iff.mpr
  refine ⟨pieces, lexed, ?_⟩
  change ∃ input arms, canonicalTokens pieces = keyword "match" :: input ∧
    ExprReads ctx.1 0 input a.val.value (openBrace :: arms) ∧
    VariantArmsRead ctx.2 ctx.1 false arms a.val.arms [] at production
  rcases production with ⟨input, arms, same, valueRead, armsRead⟩
  rw [same]
  exact .variantMatch valueRead armsRead

theorem optionMatchElaboriert : OptionMatchElaboriertAussage := by
  intro ctx platform a
  rfl

theorem optionMatchRealisiert : OptionMatchRealisiertAussage := by
  intro ctx platform a s running active live atPc
  exact (optionMatchForm ctx).realisiert (om_amOrt ctx) platform a s running active live atPc

theorem optionMatchAnnahme : OptionMatchAnnahmeAussage := by
  intro ctx
  exact Quellform.annahme (optionMatchForm ctx)

theorem optionMatchIdeal : OptionMatchIdealAussage := by
  intro ctx
  constructor
  · exact om_amOrt ctx
  · intro a
    constructor
    · exact ((optionMatchForm ctx).befehl a).bestimmt
    · intro c s w plans u
      rfl

theorem optionMatchEinheit : OptionMatchEinheitAussage := by
  intro ctx platform a
  exact ⟨rfl, ((optionMatchForm ctx).befehl a).kommutation⟩

theorem optionMatchImpl : OptionMatchImplAussage := by
  intro ctx a c s w plans u
  rfl

theorem optionMatchErhaltung : OptionMatchErhaltungAussage := by
  intro ctx
  apply Quellform.erhaltung
  intro a
  exact om_keine_invarianten ctx a

theorem optionMatchRegelSicher : OptionMatchRegelSicherAussage := by
  intro ctx platform a
  exact (optionMatchErhaltung ctx platform a).2.2.2

theorem optionMatchErfuellbarAm : OptionMatchErfuellbarAmAussage := by
  intro platform start
  let count : Nat := 0
  let name : Identifier := keywordName 'o' [] (by decide) (by simp)
  let scope : Scope := [⟨name, indexOptionType count, false, true⟩]
  let ref : Local scope (indexOptionType count) := .here
  have visible : ref.visible := by
    constructor
    · simp [Ty.valueBinding, indexOptionType]
    · trivial
  have ordinary : ordinaryLocal name := by
    simp [ordinaryLocal, ordinaryAtomWord, name, keywordName]
  have refOrdinary : ordinaryLocal ref.binding.name := by
    dsimp [ref, Local.binding]
    exact ordinary
  let value : Expr scope (variantValueType [] indexOptionLabels (indexOptionPayloads count)) :=
    Expr.variable ref visible refOrdinary
  let binder : Identifier := keywordName 'p' [] (by decide) (by simp)
  have binderOrdinary : ordinaryLocal binder := by
    simp [ordinaryLocal, ordinaryAtomWord, binder, keywordName]
  let bodySome : BracedBlock none (payloadBinding binder (indexType count) :: scope) := .braces .done
  let bodyNone : BracedBlock none scope := .braces .done
  have noneCase : indexNoneName.val ≠ ['_'] := by
    simp [indexNoneName]
  let armsNone : VariantArms none scope true [indexNoneName] [none] :=
    .nullary indexNoneName noneCase bodyNone .done
  let arms : VariantArms none scope false indexOptionLabels (indexOptionPayloads count) :=
    .payload indexSomeName binder binderOrdinary bodySome armsNone
  let aVal : Surface.VariantMatchArgs (scope, none) :=
    ⟨[], indexOptionLabels, indexOptionPayloads count, value, arms⟩
  have hshape : ∃ c, aVal.name = [] ∧ aVal.labels = indexOptionLabels ∧
      aVal.payloads = indexOptionPayloads c := ⟨count, rfl, rfl, rfl⟩
  let a : OptionMatchArgs (scope, none) := ⟨aVal, hshape⟩
  refine ⟨(scope, none), a, ?_⟩
  let form := optionMatchForm (scope, none)
  let E := form.einheit platform a
  let s₀ := (I.start E start).2
  let vb : Befehl := .lesen 0 ref.index
  let s₁ := vb.nach eintritt s₀
  have vbhead : kopf (form.fragment a).code s₀ eintritt = some vb := by
    rfl
  have step : E.system.ISchritt eintritt s₀ () [plan] s₁ :=
    ⟨vb, vbhead, rfl, rfl⟩
  have reached : E.system.IErreichbar s₀ s₁ :=
    .schritt eintritt () [plan] .start step
  dsimp [Quellform.ErfuellbarAm]
  refine ⟨Ast.print (category := .statement scope none) (form.produktion.tree a), s₁,
    Ast.parse_print _, rfl, reached, ?_, ?_⟩
  · refine form.realisiert (om_amOrt (scope, none)) platform a s₁ rfl rfl rfl ?_
    rfl
  · intro g guard
    cases guard

end Gabbro.Core.Ast.Semantik
