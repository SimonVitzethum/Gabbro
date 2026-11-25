module

public import Core.Ast.Aggregate.Types
public import Core.Ast.Semantik.Formbeweise

/-!
# Tuple type

- `TupleTypeInversionAussage`
- `TupleTypeSuffixAussage`
- `TupleTypeDerivationAussage`
- `TupleTypeIndexAussage`
- `TupleTypeSyntaxErfuellbarAussage`
- `TupleTypeParseAussage`
- `TupleTypeElaboriertAussage`
- `TupleTypeRealisiertAussage`
- `TupleTypeAnnahmeAussage`
- `TupleTypeIdealAussage`
- `TupleTypeEinheitAussage`
- `TupleTypeImplAussage`
- `TupleTypeErhaltungAussage`
- `TupleTypeRegelSicherAussage`
- `TupleTypeErfuellbarAmAussage`
-/

@[expose] public section

namespace Gabbro.Core.Ast

open Gabbro.Core.Text

theorem tupleType_inversion : TupleTypeInversionAussage := by
  intro scope input type rest read
  cases read with
  | tuple firstRead secondRead tailRead => exact ⟨_, _, _, _, _, firstRead, secondRead, tailRead, rfl⟩

private theorem typeItemsTail_consumes : (input : List Token) → (tail : WrittenTypes) → (rest : List Token) →
    TypeItemsTail scope input tail rest → rest <:+ input
  | _, _, _, .close => List.suffix_cons _ _
  | _, _, _, .comma headRead tailRead =>
      (typeItemsTail_consumes _ _ _ tailRead).trans
        ((TypeReads.consumes headRead).trans (List.suffix_cons comma _))

theorem tupleType_suffix : TupleTypeSuffixAussage := by
  intro scope input type rest read
  obtain ⟨_, _, _, secondInput, more, firstRead, secondRead, tailRead, _⟩ := tupleType_inversion read
  exact ((typeItemsTail_consumes more _ rest tailRead).trans (TypeReads.consumes secondRead)).trans
    ((List.suffix_cons comma secondInput).trans (TypeReads.consumes firstRead))

theorem tupleType_index : TupleTypeIndexAussage := by
  intro first second tail
  rfl

private theorem tupleTypeTail_closed (tail : WrittenTypes) (rest : List Token) :
    ∀ more, tail.printTail.map PrintedToken.value ++ closeParen :: rest ≠ keyword "in" :: more := by
  match tail with
  | .empty =>
      intro more same
      simp only [WrittenTypes.printTail, List.map_nil, List.nil_append] at same
      cases same
  | .next _ _ =>
      intro more same
      have commaTok : printComma.value = comma := by rfl
      simp only [WrittenTypes.printTail, List.map_cons, List.map_append, List.map_nil, commaTok] at same
      cases same

private theorem tupleType_printTail : (tail : WrittenTypes) → tail.valid scope → (rest : List Token) →
    TypeItemsTail scope (tail.printTail.map PrintedToken.value ++ closeParen :: rest) tail rest
  | .empty, _, rest => by
      simpa [WrittenTypes.printTail] using (TypeItemsTail.close (rest := rest))
  | .next head tail, valid, rest => by
      simp only [WrittenTypes.printTail, List.map_cons, List.map_append, List.map_nil]
      have commaTok : printComma.value = comma := by rfl
      rw [commaTok]
      apply TypeItemsTail.comma
      · simpa [List.append_assoc] using
          (WrittenType.printReads head valid.1
            (rest := tail.printTail.map PrintedToken.value ++ closeParen :: rest)
            (tupleTypeTail_closed tail rest))
      · exact tupleType_printTail tail valid.2 rest

theorem tupleType_derivation : TupleTypeDerivationAussage := by
  intro scope first second tail rest valid
  let ft := first.printPieces.map PrintedToken.value
  let st := second.printPieces.map PrintedToken.value
  let tt := tail.printTail.map PrintedToken.value
  have openTok : printOpen.value = openParen := by rfl
  have commaTok : printComma.value = comma := by rfl
  have closeTok : printClose.value = closeParen := by rfl
  have printEq : (WrittenType.tuple first second tail).printPieces.map PrintedToken.value =
      openParen :: (ft ++ [comma] ++ st ++ tt ++ [closeParen]) := by
    simp only [WrittenType.printPieces, WrittenTypes.printTail, List.map_append, List.map_cons,
      List.map_nil, ft, st, tt, openTok, commaTok, closeTok, List.singleton_append, List.append_assoc]
    rfl
  rw [printEq]
  simp only [List.cons_append]
  refine TypeReads.tuple (input := ft ++ [comma] ++ st ++ tt ++ [closeParen] ++ rest)
    (secondInput := st ++ tt ++ closeParen :: rest)
    (more := tt ++ closeParen :: rest) ?_ ?_ ?_
  · simpa [ft] using (WrittenType.printReads first valid.1
      (rest := comma :: (st ++ tt ++ closeParen :: rest))
      (by intro more same; cases same))
  · simpa [st] using (WrittenType.printReads second valid.2.1
      (rest := tt ++ closeParen :: rest) (tupleTypeTail_closed tail rest))
  · simpa [tt] using (tupleType_printTail tail valid.2.2 rest)

theorem tupleType_syntax_erfuellbar : TupleTypeSyntaxErfuellbarAussage := by
  let first : WrittenType := .bool
  let second : WrittenType := .bool
  let tail : WrittenTypes := .empty
  let tree := WrittenType.tuple first second tail
  obtain ⟨pieces, lexed, aligned⟩ := PrintedToken.renderLexed 0 tree.printPieces
  refine ⟨first, second, tail, PrintedToken.render tree.printPieces, pieces, ?_, lexed, ?_⟩
  · simpa [tree, first, second, tail, WrittenType.valid, WrittenTypes.valid]
  · rw [aligned]
    exact WrittenType.printReads tree (by simpa [tree, first, second, tail, WrittenType.valid, WrittenTypes.valid])
      (by intro more same; cases same)

end Gabbro.Core.Ast

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog Waechter

theorem tupleTypeUse_am_ort (ctx : Scope × Option (Ty .value)) : (typeUseForm ctx tupleTypeUse).RegelAmOrt := by
  intro args
  change (((expr 0 args.val.value).anhaengen (.einzel (.bindeWert 0 args.val.written.type false))).code[
    (expr 0 args.val.value).code.length]? = some (.bindeWert 0 args.val.written.type false))
  simp only [Fragment.anhaengen, Fragment.einzel, List.getElem?_append_right (Nat.le_refl _),
    Nat.sub_self, List.getElem?_cons_zero]

theorem tupleTypeUse_entry (ctx : Scope × Option (Ty .value)) :
    (typeUseForm ctx tupleTypeUse).produktion.Entry := by
  let base := Surface.mutableLocal_entry ctx.1 ctx.2
  refine ⟨?reads, ?prints, ?erfuellbar⟩
  · intro args tokens prod
    exact base.reads args.val tokens prod
  · intro args
    exact base.prints args.val
  · let name : Identifier :=
      ⟨['x'], 'x', [], rfl, Or.inl (Or.inl (by decide)),
        fun _ member => (List.not_mem_nil member).elim⟩
    have ordinary : ordinaryLocal name := by
      exact (directName_of_singleton (name := name) rfl).1
    let w : WrittenType := .tuple .bool .bool .empty
    let a : Surface.MutableLocalArgs ctx.1 ctx.2 :=
      ⟨name, ordinary, w, by simpa [w, WrittenType.valid, WrittenTypes.valid], tupleType [.bool, .bool],
        .tupleValue .trueLit .falseLit .empty, by simpa [w, Fits, WrittenType.type, WrittenTypes.types, tupleType]⟩
    exact Surface.Rule.satisfiableOfPrint ⟨a, by simpa [a, w, tupleTypeUse]⟩ (base.prints a)

theorem tupleType_parse : TupleTypeParseAussage := by
  intro ctx args text pieces lexed prod
  exact (tupleTypeUse_entry ctx).parse lexed prod

theorem tupleType_elaboriert : TupleTypeElaboriertAussage := by
  intro ctx platform args
  rfl

theorem tupleType_realisiert : TupleTypeRealisiertAussage := by
  intro ctx platform args s running active live atPc
  exact (typeUseForm ctx tupleTypeUse).realisiert (tupleTypeUse_am_ort ctx) platform args s
    running active live atPc

theorem tupleType_annahme : TupleTypeAnnahmeAussage := by
  intro ctx
  exact (typeUseForm ctx tupleTypeUse).annahme

theorem tupleType_ideal : TupleTypeIdealAussage := by
  intro ctx
  refine ⟨tupleTypeUse_am_ort ctx, ?_⟩
  intro args
  exact ⟨(typeUseForm ctx tupleTypeUse).bestimmt args, fun _ _ _ _ _ => Iff.rfl⟩

theorem tupleType_einheit : TupleTypeEinheitAussage := by
  intro ctx platform args
  exact ⟨rfl, ((typeUseForm ctx tupleTypeUse).befehl args).kommutation⟩

theorem tupleType_impl : TupleTypeImplAussage := by
  intro ctx args c s w plans u
  rfl

private theorem tupleTypeUse_keineInvarianten (ctx : Scope × Option (Ty .value))
    (args : {a : Surface.MutableLocalArgs ctx.1 ctx.2 // tupleTypeUse a.written}) :
    ((typeUseForm ctx tupleTypeUse).fragment args).klauseln.invariant = [] := by
  change (stmt (Stmt.letMutable args.val.name args.val.ordinary args.val.written args.val.valid
    args.val.value args.val.fits)).klauseln.invariant = []
  exact stmt_keine_invarianten _

theorem tupleType_erhaltung : TupleTypeErhaltungAussage := by
  intro ctx
  exact (typeUseForm ctx tupleTypeUse).erhaltung (tupleTypeUse_keineInvarianten ctx)

theorem tupleType_regelSicher : TupleTypeRegelSicherAussage := by
  intro ctx platform args
  exact ((typeUseForm ctx tupleTypeUse).befehl args).sicher
    ((typeUseForm ctx tupleTypeUse).fragment args) platform (tupleTypeUse_keineInvarianten ctx args)

theorem tupleType_erfuellbar : TupleTypeErfuellbarAmAussage := by
  intro platform start
  let name : Identifier :=
    ⟨['x'], 'x', [], rfl, Or.inl (Or.inl (by decide)),
      fun _ member => (List.not_mem_nil member).elim⟩
  have ordinary : ordinaryLocal name := by
    exact (directName_of_singleton (name := name) rfl).1
  let w : WrittenType := .tuple .bool .bool .empty
  let a : Surface.MutableLocalArgs [] none :=
    ⟨name, ordinary, w, by simpa [w, WrittenType.valid, WrittenTypes.valid], tupleType [.bool, .bool],
      .tupleValue .trueLit .falseLit .empty,
      by simpa [w, Fits, WrittenType.type, WrittenTypes.types, tupleType]⟩
  let args : {a : Surface.MutableLocalArgs [] none // tupleTypeUse a.written} :=
    ⟨a, by simpa [a, w, tupleTypeUse]⟩
  let form := typeUseForm ([], none) tupleTypeUse
  let E := form.einheit platform args
  let s₀ := (I.start E start).2
  let s₁ := (Befehl.wahrheitswert 0 true).nach eintritt s₀
  let s₂ := (Befehl.wahrheitswert 1 false).nach eintritt s₁
  let s₃ := (Befehl.baueTupel 0 [.bool, .bool]).nach eintritt s₂
  have first : E.system.ISchritt eintritt s₀ () [plan] s₁ :=
    ⟨.wahrheitswert 0 true, rfl, rfl, rfl⟩
  have second : E.system.ISchritt eintritt s₁ () [plan] s₂ :=
    ⟨.wahrheitswert 1 false, rfl, rfl, rfl⟩
  have third : E.system.ISchritt eintritt s₂ () [plan] s₃ :=
    ⟨.baueTupel 0 [.bool, .bool], rfl, rfl, rfl⟩
  have reached : E.system.IErreichbar s₀ s₃ :=
    .schritt eintritt () [plan]
      (.schritt eintritt () [plan] (.schritt eintritt () [plan] .start first) second) third
  refine ⟨args, form.erfuellbar_aus_erreichbar platform start args s₃ reached
    (form.realisiert (tupleTypeUse_am_ort ([], none)) platform args s₃ rfl rfl rfl rfl) ?_⟩
  intro g guard
  cases guard

end Gabbro.Core.Ast.Semantik
