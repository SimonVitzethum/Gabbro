module

public import Core.Ast.Aggregate.Records.Declarations
public import Core.Ast.Semantik.Formbeweise

/-!
# MutableValue

- `Surface.MutableValueInversionAussage`
- `Surface.MutableValueSuffixAussage`
- `Surface.MutableValueDerivationAussage`
- `MutableValueParseAussage`
- `MutableValueElaboriertAussage`
- `MutableValueRealisiertAussage`
- `MutableValueAnnahmeAussage`
- `MutableValueIdealAussage`
- `MutableValueEinheitAussage`
- `MutableValueImplAussage`
- `MutableValueErhaltungAussage`
- `MutableValueRegelSicherAussage`
- `MutableValueErfuellbarAmAussage`
-/

namespace Gabbro.Core.Ast.Surface

open Gabbro.Core.Text

theorem mutableValue_inversion : MutableValueInversionAussage := by
  intro scope result name input tree rest read
  generalize ht : keyword "mut" = t at read
  generalize hn : Token.word name.val = w at read
  cases read with
  | letMutableValue n ordinary value valueRead =>
      have hnval : n.val = name.val := by
        injection hn with h
        exact h.symm
      refine ⟨⟨n, ordinary, value⟩, ?_, valueRead, ?_⟩
      · exact Subtype.ext hnval
      · rfl
  | tupleBind checked patternRead annotationRead valueRead =>
      cases patternRead
      simp_all [keyword]
  | directCall callRead =>
      cases callRead
      simp_all [keyword]
  | _ => simp_all [keyword]

theorem mutableValue_suffix : MutableValueSuffixAussage := by
  intro scope result name input tree rest read
  obtain ⟨a, hname, valueRead, htree⟩ := mutableValue_inversion read
  exact (List.suffix_cons semicolon rest).trans (ExprReads.consumes valueRead)

private theorem mutableValue_print (ctx : Scope × Option (Ty .value)) (args : MutableValueArgs ctx.1) :
    (mutableValue ctx).production args
      (((Category.statement ctx.1 ctx.2).printPieces ((mutableValue ctx).tree args)).map PrintedToken.value) := by
  refine ⟨args.value.printTokens ++ [semicolon], ?_, ?_⟩
  · simp [Category.printPieces, Stmt.printPieces, Expr.printTokens]
  · simpa [Expr.printTokens] using
      (Expr.printReads (scope := ctx.1) (minimum := 0) args.value noOperatorAtSemicolon)

theorem mutableValue_derivation : MutableValueDerivationAussage := by
  intro ctx
  refine ⟨
    (fun args tokens prod => by
      rcases prod with ⟨input, rfl, valueRead⟩
      exact StmtReads.letMutableValue args.name args.ordinary valueRead),
    mutableValue_print ctx,
    ?_⟩
  let name : Identifier :=
    ⟨['x'], 'x', [], rfl, Or.inl (Or.inl ⟨by change 97 ≤ 120; omega, by change 120 ≤ 122; omega⟩),
      fun _ member => (List.not_mem_nil member).elim⟩
  have ordinary : ordinaryLocal name := by
    constructor
    · change ['x'] ≠ ['t', 'r', 'u', 'e']
      intro same
      cases same
    · change ['x'] ≠ ['f', 'a', 'l', 's', 'e']
      intro same
      cases same
  let args : MutableValueArgs ctx.1 := ⟨name, ordinary, .bool, .trueLit⟩
  exact Rule.satisfiableOfPrint args (mutableValue_print ctx args)

end Gabbro.Core.Ast.Surface

namespace Gabbro.Core.Ast.Semantik

open Maschine Annahme Katalog Waechter

private theorem mv_amOrt (ctx : Scope × Option (Ty .value)) : (mutableValueForm ctx).RegelAmOrt := by
  intro args
  change (((expr 0 args.value).anhaengen (Fragment.einzel (.bindeWert 0 args.type false))).code[
    (expr 0 args.value).code.length]? = some (.bindeWert 0 args.type false))
  simp only [Fragment.anhaengen, Fragment.einzel, List.getElem?_append_right (Nat.le_refl _),
    Nat.sub_self, List.getElem?_cons_zero]

theorem mutableValue_parse : MutableValueParseAussage := by
  intro ctx args text pieces lexed prod
  exact (Surface.mutableValue_derivation ctx).parse lexed prod

theorem mutableValue_elaboriert : MutableValueElaboriertAussage := by
  intro ctx platform args
  rfl

theorem mutableValue_realisiert : MutableValueRealisiertAussage := by
  intro ctx platform args s running active live atPc
  exact (mutableValueForm ctx).realisiert (mv_amOrt ctx) platform args s running active live atPc

theorem mutableValue_annahme : MutableValueAnnahmeAussage := by
  intro ctx
  exact Quellform.annahme (mutableValueForm ctx)

theorem mutableValue_ideal : MutableValueIdealAussage := by
  intro ctx
  refine ⟨mv_amOrt ctx, ?_⟩
  intro args
  exact ⟨((mutableValueForm ctx).befehl args).bestimmt, fun _ _ _ _ _ => Iff.rfl⟩

theorem mutableValue_einheit : MutableValueEinheitAussage := by
  intro ctx platform args
  exact ⟨rfl, ((mutableValueForm ctx).befehl args).kommutation⟩

theorem mutableValue_impl : MutableValueImplAussage := by
  intro ctx args c s w plans u
  rfl

theorem mutableValue_erhaltung : MutableValueErhaltungAussage := by
  intro ctx
  exact Quellform.erhaltung (mutableValueForm ctx) (fun args =>
    stmt_keine_invarianten ((Surface.mutableValue ctx).tree args).2)

theorem mutableValue_regelSicher : MutableValueRegelSicherAussage := by
  intro ctx platform args
  exact (Quellform.erhaltung (mutableValueForm ctx) (fun a =>
    stmt_keine_invarianten ((Surface.mutableValue ctx).tree a).2) platform args).2.2.2

theorem mutableValue_erfuellbar : MutableValueErfuellbarAmAussage := by
  intro platform start
  let name : Identifier :=
    ⟨['x'], 'x', [], rfl, Or.inl (Or.inl ⟨by change 97 ≤ 120; omega, by change 120 ≤ 122; omega⟩),
      fun _ member => (List.not_mem_nil member).elim⟩
  have ordinary : ordinaryLocal name := by
    constructor
    · change ['x'] ≠ ['t', 'r', 'u', 'e']
      intro same
      cases same
    · change ['x'] ≠ ['f', 'a', 'l', 's', 'e']
      intro same
      cases same
  let args : Surface.MutableValueArgs [] := ⟨name, ordinary, .int 1 1, .lit 1⟩
  let form := mutableValueForm ([], none)
  let E := form.einheit platform args
  let s₀ := (I.start E start).2
  let s₁ := (Befehl.literal 0 1).nach eintritt s₀
  have first : E.system.ISchritt eintritt s₀ () [plan] s₁ :=
    ⟨.literal 0 1, rfl, rfl, rfl⟩
  have reached : E.system.IErreichbar s₀ s₁ := .schritt eintritt () [plan] .start first
  refine ⟨args, form.erfuellbar_aus_erreichbar platform start args s₁ reached
    (form.realisiert (mv_amOrt ([], none)) platform args s₁ rfl rfl rfl rfl) ?_⟩
  intro g guard
  cases guard

end Gabbro.Core.Ast.Semantik
