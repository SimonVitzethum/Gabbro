module

public import Core.Ast.Declaration.Readers
import Core.Ast.Declaration.Members
import Core.Ast.Declaration.Effects

@[expose] public section

namespace Gabbro.Core.Ast

open Gabbro.Core.Text

-- Mirror StmtReads.assign_inversion with the written type and const initializer.
theorem DeclReads.constant_inversion
    (read : DeclReads before (keyword "const" :: .word spelling :: colon :: input) tree rest) :
    ∃ (name : Identifier) (ordinary : ordinaryLocal name) (written : WrittenType) (valid : written.valid before)
      (type : Ty .value) (value : Expr before type) (staticValue : value.static) (fits : Fits type written.type) (rhs : List Token),
      name.val = spelling ∧ TypeReads before input written (assignment :: rhs) ∧
      ExprReads before 0 rhs value (semicolon :: rest) ∧
      tree = ⟨_, .constant name ordinary written valid value staticValue fits⟩ := by
  generalize same : (keyword "const" :: Token.word spelling :: colon :: input) = tokens at read
  cases read with
  | constant name ordinary written valid value staticValue fits typeRead exprRead =>
    have tail := List.cons.inj (List.cons.inj same).2
    have nameEq := Token.word.inj tail.1
    cases (List.cons.inj tail.2).2
    exact ⟨name, ordinary, written, valid, _, value, staticValue, fits, _, nameEq.symm, typeRead, exprRead, rfl⟩
  | function => cases same
  | record exported => cases exported <;> cases same
  | tagged exported => cases exported <;> cases same
  | table item =>
    cases item with
    | mk exported => cases exported <;> cases same
  | effectGroup item =>
    cases item with
    | mk exported => cases exported <;> cases same

-- Mirror BlockReads.braced_inversion and keep every header derivation in token order.
theorem DeclReads.function_inversion
    (read : DeclReads before (keyword "fn" :: .word spelling :: openParen :: input) tree rest) :
    ∃ (name : Identifier) (ordinary : directName name) (ps : List (Parameter before))
      (result : Option WrittenType) (valid : ∀ t ∈ result.toList, WrittenType.valid before t)
      (measure : Option (Measure (functionScope before ps)))
      (body : BracedBlock (writtenResult result) (functionScope before ps))
      (distinct : (ps.map (fun p => p.name.val)).Nodup)
      (returns : result.isSome = true → body.returns = true)
      (effects : Option (EffectClause before ps))
      (afterParams afterResult afterEffects afterMeasure : List Token),
      name.val = spelling ∧ ParamsRead before input ps afterParams ∧
      ResultReads before afterParams result afterResult ∧
      EffectClauseReads before ps afterResult effects afterEffects ∧
      MeasureReads (functionScope before ps) afterEffects measure afterMeasure ∧
      BlockReads (writtenResult result) (functionScope before ps) afterMeasure body rest ∧
      tree = ⟨before, .function name ordinary ps result valid measure body distinct returns effects⟩ := by
  generalize same : (keyword "fn" :: .word spelling :: openParen :: input) = tokens at read
  cases read with
  | function name ordinary result valid parameters measure body distinct returns effects
      paramsRead resultRead effectRead measureRead blockRead =>
    simp only [List.cons.injEq, Token.word.injEq] at same
    obtain ⟨_, spellingEq, _, inputEq⟩ := same
    subst input
    exact ⟨name, ordinary, parameters, result, valid, measure, body, distinct, returns,
      effects, _, _, _, _, spellingEq.symm, paramsRead, resultRead, effectRead, measureRead, blockRead, rfl⟩
  | constant => cases same
  | record exported => cases exported <;> cases same
  | tagged exported => cases exported <;> cases same
  | table item =>
    cases item with
    | mk exported => cases exported <;> cases same
  | effectGroup item =>
    cases item with
    | mk exported => cases exported <;> cases same

theorem ResultReads.deterministic (read : ResultReads before input result rest) :
    ∀ {result' rest'}, ResultReads before input result' rest' → result = result' ∧ rest = rest' := by
  cases read with
  | absent closed =>
      intro r' o' read'
      cases read' with
      | absent _ => exact ⟨rfl, rfl⟩
      | typed _ => exact (closed _ rfl).elim
  | typed tr =>
      intro r' o' read'
      cases read' with
      | absent closed => exact (closed _ rfl).elim
      | typed tr' =>
          obtain ⟨weq, oeq⟩ := TypeReads.deterministic tr tr'
          exact ⟨congrArg some weq, oeq⟩

theorem MeasureReads.deterministic (read : MeasureReads scope input measure rest) :
    ∀ {measure' rest'}, MeasureReads scope input measure' rest' → measure = measure' ∧ rest = rest' := by
  cases read with
  | absent closed =>
      intro m' o' read'
      cases read' with
      | absent _ => exact ⟨rfl, rfl⟩
      | present _ _ => exact (closed _ rfl).elim
  | present m exprRead =>
      intro m' o' read'
      cases read' with
      | absent closed => exact (closed _ rfl).elim
      | present m'' exprRead' =>
          cases m with
          | mk lo hi expression lower =>
            cases m'' with
            | mk lo' hi' expression' lower' =>
              obtain ⟨typedEq, oeq⟩ := ExprReads.deterministic exprRead exprRead'
              have fstEq := congrArg (fun p : TypedExpr scope => p.1) typedEq
              injection fstEq with loEq hiEq
              cases loEq
              cases hiEq
              cases typedEq
              exact ⟨rfl, oeq⟩

-- Mirror StmtReads.deterministic, using the header and body derivations in order.
theorem DeclReads.deterministic (left : DeclReads before input a rest)
    (right : DeclReads before input b rest') : a = b ∧ rest = rest' := by
  cases left with
  | constant name ordinary written valid value staticValue fits typeRead exprRead =>
      obtain ⟨name', ordinary', written', valid', type', value', staticValue', fits', rhs',
        nameEq, typeRead', exprRead', treeEq⟩ := DeclReads.constant_inversion right
      have nameFull : name' = name := Subtype.ext nameEq
      subst name'
      obtain ⟨wEq, tailEq⟩ := TypeReads.deterministic typeRead typeRead'
      cases wEq
      injection tailEq with rhsEq
      subst rhs'
      obtain ⟨vEq, restEq⟩ := ExprReads.deterministic exprRead exprRead'
      cases vEq
      injection restEq with hrest
      subst rest'
      exact ⟨treeEq.symm, rfl⟩
  | function name ordinary result valid parameters measure body distinct returns effects
      paramsRead resultRead effectRead measureRead blockRead =>
      obtain ⟨name', ordinary', ps, result', valid', measure', body', distinct', returns', effects',
        afterParams, afterResult, afterEffects, afterMeasure, nameEq, paramsRead', resultRead', effectRead', measureRead',
        blockRead', treeEq⟩ := DeclReads.function_inversion right
      have nameFull : name' = name := Subtype.ext nameEq
      subst name'
      obtain ⟨paramsEq, afterParamsEq⟩ := ParamsRead.deterministic paramsRead paramsRead'
      cases paramsEq
      subst afterParams
      obtain ⟨resultEq, afterResultEq⟩ := resultRead.deterministic resultRead'
      cases resultEq
      subst afterResult
      obtain ⟨effectsEq, afterEffectsEq⟩ := effectRead.deterministic effectRead'
      cases effectsEq
      subst afterEffects
      obtain ⟨measureEq, afterMeasureEq⟩ := measureRead.deterministic measureRead'
      cases measureEq
      subst afterMeasure
      obtain ⟨bodyEq, restEq⟩ := BlockReads.deterministic blockRead blockRead'
      cases bodyEq
      exact ⟨treeEq.symm, restEq⟩

-- Mirror StmtReads.disjoint_closeBrace using the nonempty declaration prefix.
theorem DeclReads.disjoint_end : ¬ DeclReads before [] tree rest := by
  intro read
  generalize h : ([] : List Token) = input at read
  cases read with
  | record exported => cases exported <;> cases h
  | tagged exported => cases exported <;> cases h
  | table item => cases item with | mk exported => cases exported <;> cases h
  | effectGroup item => cases item with | mk exported => cases exported <;> cases h
  | _ => cases h

-- Mirror StmtReads.consumes using the type, expression and block suffixes.
theorem DeclReads.consumes (read : DeclReads before input tree rest) : rest <:+ input := by
  have resultConsumes : ∀ {i : List Token} {r : Option WrittenType} {o : List Token},
      ResultReads before i r o → o <:+ i := by
    intro i r o h
    cases h with
    | absent _ => exact List.suffix_refl _
    | typed tr => exact tr.consumes.trans (List.suffix_cons _ _)
  have measureConsumes : ∀ (scope : Scope) {i : List Token} {m : Option (Measure scope)} {o : List Token},
      MeasureReads scope i m o → o <:+ i := by
    intro scope i m o h
    cases h with
    | absent _ => exact List.suffix_refl _
    | present m exprRead => exact exprRead.consumes.trans (List.suffix_cons _ _)
  cases read with
  | constant _ _ _ _ _ _ _ typeRead exprRead =>
      have h1 := List.suffix_cons semicolon rest
      have h2 := h1.trans exprRead.consumes
      have h3 := h2.trans (List.suffix_cons assignment _)
      have h4 := h3.trans typeRead.consumes
      exact ((h4.trans (List.suffix_cons _ _)).trans (List.suffix_cons _ _)).trans (List.suffix_cons _ _)
  | function _ _ _ _ parameters _ _ _ _ _ paramsRead resultRead effectRead measureRead blockRead =>
      have h1 := blockRead.consumes
      have h2 := h1.trans (measureConsumes (functionScope before parameters) measureRead)
      have h3 := (h2.trans effectRead.consumes).trans (resultConsumes resultRead)
      have h4 := h3.trans paramsRead.consumes
      exact ((h4.trans (List.suffix_cons _ _)).trans (List.suffix_cons _ _)).trans (List.suffix_cons _ _)

  | record exported _ _ _ members =>
    exact ((List.suffix_cons _ _).trans members.consumes).trans
      ((List.suffix_append _ _).trans (List.suffix_append _ _))
  | tagged exported _ _ _ first tail =>
    exact (((List.suffix_cons _ _).trans tail.consumes).trans first.consumes).trans
      ((List.suffix_append _ _).trans (List.suffix_append _ _))
  | table item members =>
    exact ((List.suffix_cons _ _).trans members.consumes).trans (List.suffix_append _ _)
  | effectGroup item effects =>
    exact ((List.suffix_cons _ _).trans
      (EffectListReads.consumes CarrierEffectReads.consumes effects)).trans (List.suffix_append _ _)

-- Mirror BracedBlock.printReads using ParamsRead.printReads for the function header.
theorem Decl.printReads (tree : Decl before after) (rest : List Token) :
    DeclReads before (tree.printPieces.map PrintedToken.value ++ rest) ⟨after, tree⟩ rest := by
  cases tree with
  | constant name ordinary written valid value staticValue fits =>
      simp only [Decl.printPieces, List.map_append, List.map_cons, List.map_nil,
        List.cons_append, List.nil_append, List.append_assoc]
      refine .constant (rhs := value.printPieces.map PrintedToken.value ++ semicolon :: rest)
        name ordinary written valid value staticValue fits ?_ ?_
      · exact WrittenType.printReads written valid (by
          intro more h
          cases h)
      · exact Expr.printReads value noOperatorAtSemicolon
  | function name ordinary parameters result valid measure body distinct returns =>
      cases body with
      | braces items =>
        let afterParams :=
          (resultPieces result).map PrintedToken.value ++
            (measurePieces measure).map PrintedToken.value ++
            (BracedBlock.braces items).printPieces.map PrintedToken.value ++ rest
        let afterResult :=
          (measurePieces measure).map PrintedToken.value ++
            (BracedBlock.braces items).printPieces.map PrintedToken.value ++ rest
        let afterMeasure := (BracedBlock.braces items).printPieces.map PrintedToken.value ++ rest
        have proof : DeclReads before
            (printFn.value :: name.print.value :: printOpen.value ::
              ((commaSeparated (parameters.map Parameter.printPieces)).map PrintedToken.value ++
                printClose.value :: afterParams))
            ⟨before, .function name ordinary parameters result valid measure (BracedBlock.braces items) distinct returns⟩ rest :=
          .function (afterParams := afterParams) (afterResult := afterResult) (afterMeasure := afterMeasure)
            name ordinary result valid parameters measure (BracedBlock.braces items) distinct returns
            (by
              simpa only [List.map_append, List.map_cons, List.map_nil, List.cons_append,
                List.nil_append, List.append_assoc] using
                (ParamsRead.printReads (ps := parameters) (rest := afterParams)))
            (by
              cases result with
              | none =>
                  refine ResultReads.absent ?_
                  intro more h
                  cases measure with
                  | none =>
                      simp only [List.map_append, List.map_cons, List.map_nil, List.nil_append, List.cons_append, List.append_assoc, List.cons.injEq, String.reduceEq, and_false, false_and, afterParams, resultPieces, measurePieces, BracedBlock.printPieces, arrow,
                        keyword, printPunctuation, printProgramWord, Identifier.print, keywordName, printOpenBrace, printDecreases, PrintedToken.unquoted] at h
                      cases h.1
                  | some m0 =>
                      simp only [List.map_append, List.map_cons, List.map_nil, List.nil_append, List.cons_append, List.append_assoc, List.cons.injEq, String.reduceEq, and_false, false_and, afterParams, resultPieces, measurePieces, BracedBlock.printPieces, arrow,
                        keyword, printPunctuation, printProgramWord, Identifier.print, keywordName, printOpenBrace, printDecreases, PrintedToken.unquoted] at h
                      cases h.1
              | some written =>
                  refine ResultReads.typed ?_
                  have hwt := WrittenType.printReads (rest := afterResult) written (valid written (by exact (List.mem_singleton).2 rfl)) (by
                    intro more h
                    cases measure with
                    | none =>
                        simp only [List.map_append, List.map_cons, List.map_nil, List.nil_append, List.cons_append, List.append_assoc, List.cons.injEq, String.reduceEq, and_false, false_and, afterResult, measurePieces, BracedBlock.printPieces, arrow, keyword,
                          printPunctuation, printProgramWord, Identifier.print, keywordName, printOpenBrace, printDecreases, PrintedToken.unquoted] at h
                        cases h.1
                    | some m0 =>
                        simp only [List.map_append, List.map_cons, List.map_nil, List.nil_append, List.cons_append, List.append_assoc, List.cons.injEq, String.reduceEq, and_false, false_and, afterResult, measurePieces, BracedBlock.printPieces, arrow, keyword,
                          printPunctuation, printProgramWord, Identifier.print, keywordName, printOpenBrace, printDecreases, PrintedToken.unquoted] at h
                        cases h.1)
                  rw [← List.append_assoc] at hwt
                  rw [← List.append_assoc] at hwt
                  exact hwt)
            (by
              cases measure with
              | none =>
                  refine MeasureReads.absent ?_
                  intro more h
                  simp only [List.map_append, List.map_cons, List.map_nil, List.nil_append, List.cons_append, List.append_assoc, List.cons.injEq, String.reduceEq, and_false, false_and, afterResult, measurePieces, BracedBlock.printPieces, arrow, keyword,
                    printPunctuation, printProgramWord, Identifier.print, keywordName, printOpenBrace, printDecreases, PrintedToken.unquoted] at h
                  cases h.1
              | some m =>
                  refine MeasureReads.present m ?_
                  have hexpr := Expr.printReads (rest := afterMeasure) m.expression (by
                    simpa [afterMeasure, BracedBlock.printPieces, List.map_append, printOpenBrace,
                      printPunctuation, PrintedToken.unquoted, openBrace] using
                      (noOperatorAtOpenBrace (minimum := 0)
                        (more := items.printItems.map PrintedToken.value ++ printCloseBrace.value :: rest)))
                  rw [← List.append_assoc] at hexpr
                  exact hexpr)
            ((BracedBlock.braces items).printReads rest)
        simpa only [Decl.printPieces, resultPieces, measurePieces, BracedBlock.printPieces,
          afterParams, afterResult, afterMeasure, List.map_append, List.map_cons, List.map_nil,
          List.cons_append, List.nil_append, List.append_assoc] using proof

end Gabbro.Core.Ast
