module

public import Core.Ast.Declaration.Readers
import Core.Ast.Declaration.Members
import Core.Ast.Declaration.EffectReaders

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
  | environment => cases same

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
  | environment => cases same

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

theorem MeasureReads.deterministic (read : MeasureReads scope input selected rest) :
    ∀ {selected' rest'}, MeasureReads scope input selected' rest' → selected = selected' ∧ rest = rest' := by
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

local macro "deny_declaration" equality:ident : tactic =>
  `(tactic|
    (exfalso
     first
     | (cases (List.cons.inj $equality).1; done)
     | cases (List.cons.inj (List.cons.inj $equality).2).1))

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

  | record exported name valid distinct fieldsRead =>
    generalize same : (recordDeclarationPrefix exported ++ [Token.word name.val, assignment, openBrace] ++ _) =
      tokens at right
    cases right with
    | record otherExported otherName otherValid otherDistinct otherFields =>
      cases exported <;> cases otherExported
      · have tail := (List.cons.inj same).2
        have nameEq := Subtype.ext (Token.word.inj (List.cons.inj tail).1)
        cases nameEq
        cases (List.cons.inj (List.cons.inj (List.cons.inj tail).2).2).2
        obtain ⟨rfl, suffix⟩ := fieldsRead.deterministic otherFields
        exact ⟨rfl, (List.cons.inj suffix).2⟩
      · deny_declaration same
      · deny_declaration same
      · have tail := (List.cons.inj (List.cons.inj same).2).2
        have nameEq := Subtype.ext (Token.word.inj (List.cons.inj tail).1)
        cases nameEq
        cases (List.cons.inj (List.cons.inj (List.cons.inj tail).2).2).2
        obtain ⟨rfl, suffix⟩ := fieldsRead.deterministic otherFields
        exact ⟨rfl, (List.cons.inj suffix).2⟩
    | tagged otherExported => cases exported <;> cases otherExported <;> deny_declaration same
    | table item =>
      cases item with | mk otherExported => cases exported <;> cases otherExported <;> deny_declaration same
    | effectGroup item =>
      cases item with | mk otherExported => cases exported <;> cases otherExported <;> deny_declaration same
    | _ => cases exported <;> deny_declaration same
  | tagged exported name valid distinct firstRead tailRead =>
    generalize same : (taggedDeclarationPrefix exported ++ [Token.word name.val, assignment, openBrace] ++ _) =
      tokens at right
    cases right with
    | tagged otherExported otherName _ _ otherFirst otherTail =>
      cases exported <;> cases otherExported
      · have tail := (List.cons.inj (List.cons.inj same).2).2
        cases Subtype.ext (Token.word.inj (List.cons.inj tail).1)
        cases (List.cons.inj (List.cons.inj (List.cons.inj tail).2).2).2
        obtain ⟨rfl, rfl⟩ := firstRead.deterministic otherFirst
        obtain ⟨rfl, suffix⟩ := tailRead.deterministic otherTail
        exact ⟨rfl, (List.cons.inj suffix).2⟩
      · deny_declaration same
      · deny_declaration same
      · have tail := (List.cons.inj (List.cons.inj (List.cons.inj same).2).2).2
        cases Subtype.ext (Token.word.inj (List.cons.inj tail).1)
        cases (List.cons.inj (List.cons.inj (List.cons.inj tail).2).2).2
        obtain ⟨rfl, rfl⟩ := firstRead.deterministic otherFirst
        obtain ⟨rfl, suffix⟩ := tailRead.deterministic otherTail
        exact ⟨rfl, (List.cons.inj suffix).2⟩
    | record otherExported => cases exported <;> cases otherExported <;> deny_declaration same
    | table item =>
      cases item with | mk otherExported => cases exported <;> cases otherExported <;> deny_declaration same
    | effectGroup item =>
      cases item with | mk otherExported => cases exported <;> cases otherExported <;> deny_declaration same
    | _ => cases exported <;> deny_declaration same
  | table item fieldsRead =>
    generalize same : (item.header.map PrintedToken.value ++ _) = tokens at right
    cases item with
    | mk exported name count fields valid distinct =>
      cases right with
      | table other otherFields =>
        cases other with
        | mk otherExported otherName otherCount otherMembers otherValid otherDistinct =>
          cases exported <;> cases otherExported
          · have tail := (List.cons.inj same).2
            cases Subtype.ext (Token.word.inj (List.cons.inj tail).1)
            have countTail := (List.cons.inj (List.cons.inj tail).2).2
            cases Token.natural.inj (List.cons.inj countTail).1
            have fieldsTail := (List.cons.inj (List.cons.inj countTail).2).2
            cases (List.cons.inj (List.cons.inj fieldsTail).2).2
            obtain ⟨rfl, suffix⟩ := fieldsRead.deterministic otherFields
            exact ⟨rfl, (List.cons.inj suffix).2⟩
          · deny_declaration same
          · deny_declaration same
          · have tail := (List.cons.inj (List.cons.inj same).2).2
            cases Subtype.ext (Token.word.inj (List.cons.inj tail).1)
            have countTail := (List.cons.inj (List.cons.inj tail).2).2
            cases Token.natural.inj (List.cons.inj countTail).1
            have fieldsTail := (List.cons.inj (List.cons.inj countTail).2).2
            cases (List.cons.inj (List.cons.inj fieldsTail).2).2
            obtain ⟨rfl, suffix⟩ := fieldsRead.deterministic otherFields
            exact ⟨rfl, (List.cons.inj suffix).2⟩
      | record otherExported => cases exported <;> cases otherExported <;> deny_declaration same
      | tagged otherExported => cases exported <;> cases otherExported <;> deny_declaration same
      | effectGroup other =>
        cases other with | mk otherExported => cases exported <;> cases otherExported <;> deny_declaration same
      | _ => cases exported <;> deny_declaration same
  | effectGroup item itemsRead =>
    generalize same : (item.header.map PrintedToken.value ++ _) = tokens at right
    cases item with
    | mk exported name written resolved checked =>
      cases right with
      | effectGroup other otherRead =>
        cases other with
        | mk otherExported otherName otherWritten otherResolved otherChecked =>
          cases exported <;> cases otherExported
          · have tail := (List.cons.inj same).2
            cases Subtype.ext (Token.word.inj (List.cons.inj tail).1)
            cases (List.cons.inj (List.cons.inj tail).2).2
            obtain ⟨rfl, suffix⟩ := EffectListReads.deterministic (read := CarrierEffectReads)
              CarrierEffectReads.deterministic CarrierEffectReads.not_closeBrace itemsRead otherRead
            cases Option.some.inj (checked.symm.trans otherChecked)
            exact ⟨rfl, (List.cons.inj suffix).2⟩
          · deny_declaration same
          · deny_declaration same
          · have tail := (List.cons.inj (List.cons.inj same).2).2
            cases Subtype.ext (Token.word.inj (List.cons.inj tail).1)
            cases (List.cons.inj (List.cons.inj tail).2).2
            obtain ⟨rfl, suffix⟩ := EffectListReads.deterministic (read := CarrierEffectReads)
              CarrierEffectReads.deterministic CarrierEffectReads.not_closeBrace itemsRead otherRead
            cases Option.some.inj (checked.symm.trans otherChecked)
            exact ⟨rfl, (List.cons.inj suffix).2⟩
      | record otherExported => cases exported <;> cases otherExported <;> deny_declaration same
      | tagged otherExported => cases exported <;> cases otherExported <;> deny_declaration same
      | table other =>
        cases other with | mk otherExported => cases exported <;> cases otherExported <;> deny_declaration same
      | _ => cases exported <;> deny_declaration same

  | environment name abi row =>
    generalize same : (LowLevel.environmentTokens name abi row ++ _) = tokens at right
    cases right with
    | environment otherName otherAbi otherRow =>
      simp only [LowLevel.environmentTokens, List.cons_append, List.nil_append, List.cons.injEq,
        Token.word.injEq, true_and] at same
      obtain ⟨nameEq, abiEq, rowEq, rfl⟩ := same
      cases Subtype.ext nameEq
      cases Katalog.DienstAbi.name_injective (String.toList_injective abiEq)
      cases Katalog.FirmwareZeile.name_injective (String.toList_injective rowEq)
      exact ⟨rfl, rfl⟩
    | record exported => cases exported <;> deny_declaration same
    | tagged exported => cases exported <;> deny_declaration same
    | table item => cases item with | mk exported => cases exported <;> deny_declaration same
    | effectGroup item => cases item with | mk exported => cases exported <;> deny_declaration same
    | _ => deny_declaration same

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

  | record exported name _ _ members =>
    refine ((List.suffix_cons _ _).trans members.consumes).trans ?_
    simpa only [List.append_assoc] using
      (List.suffix_append (recordDeclarationPrefix exported ++ [Token.word name.val, assignment, openBrace]) _)
  | tagged exported name _ _ first tail =>
    refine (((List.suffix_cons _ _).trans tail.consumes).trans first.consumes).trans ?_
    simpa only [List.append_assoc] using
      (List.suffix_append (taggedDeclarationPrefix exported ++ [Token.word name.val, assignment, openBrace]) _)
  | table item members =>
    exact ((List.suffix_cons _ _).trans members.consumes).trans (List.suffix_append _ _)
  | effectGroup item effects =>
    exact ((List.suffix_cons _ _).trans
      (EffectListReads.consumes CarrierEffectReads.consumes effects)).trans (List.suffix_append _ _)

  | environment name abi row => exact List.suffix_append _ _

theorem Decl.printReads (tree : Decl before after) (rest : List Token) :
    DeclReads before (tree.printPieces.map PrintedToken.value ++ rest) ⟨after, tree⟩ rest := by
  have hpConst : printConst.value = keyword "const" := rfl
  have hpName (name : Identifier) : name.print.value = .word name.val := rfl
  have hpColon : printColon.value = colon := rfl
  have hpAssign : printAssignment.value = assignment := rfl
  have hpSemi : printSemicolon.value = semicolon := rfl
  have hpOpen : printOpen.value = openParen := rfl
  have hpOpenBrace : printOpenBrace.value = openBrace := rfl
  have hpCloseBrace : printCloseBrace.value = closeBrace := rfl
  have hpArrow : printArrow.value = arrow := rfl
  have hpFn : printFn.value = keyword "fn" := rfl
  have hpDecreases : printDecreases.value = keyword "decreases" := rfl
  have hpEffects : printEffects.value = keyword "effects" := rfl
  cases tree with
  | constant name ordinary written valid value staticValue fits =>
    let rhs := value.printTokens ++ (semicolon :: rest)
    have writtenRead := written.printReads valid (rest := assignment :: rhs)
      (by intro tail impossible; cases impossible)
    have valueRead := value.printReads (minimum := 0) (rest := semicolon :: rest) noOperatorAtSemicolon
    simpa only [Decl.printPieces, Expr.printTokens, List.map_append, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, List.append_assoc, hpConst, hpName, hpColon, hpAssign, hpSemi, rhs] using
      (DeclReads.constant name ordinary written valid value staticValue fits writtenRead valueRead)
  | function name ordinary parameters result valid measure body distinct returns effects =>
    let afterMeasure := body.printPieces.map PrintedToken.value ++ rest
    let afterEffects := (measurePieces measure).map PrintedToken.value ++ afterMeasure
    let afterResult := (effectClausePieces effects).map PrintedToken.value ++ afterEffects
    let afterParams := (resultPieces result).map PrintedToken.value ++ afterResult
    have bodyHead : ∃ tail, afterMeasure = openBrace :: tail := by
      cases body
      exact ⟨_, rfl⟩
    have measureHead : ∃ head tail, afterEffects = head :: tail ∧
        (head = openBrace ∨ head = keyword "decreases") := by
      cases measure with
      | none =>
        obtain ⟨tail, eq⟩ := bodyHead
        exact ⟨_, tail, eq, Or.inl rfl⟩
      | some m => exact ⟨_, _, rfl, Or.inr rfl⟩
    have resultHead : ∃ head tail, afterResult = head :: tail ∧
        (head = openBrace ∨ head = keyword "decreases" ∨ head = keyword "effects") := by
      cases effects with
      | none =>
        obtain ⟨head, tail, eq, casesHead⟩ := measureHead
        exact ⟨head, tail, eq, casesHead.elim Or.inl (fun eq => Or.inr (Or.inl eq))⟩
      | some clause => exact ⟨_, _, rfl, Or.inr (Or.inr rfl)⟩
    have resultClosed : ∀ head, head = arrow ∨ head = keyword "in" →
        ∀ tail, afterResult ≠ head :: tail := by
      rintro head (rfl | rfl) tail equal <;>
        obtain ⟨_, _, prefixEq, rfl | rfl | rfl⟩ := resultHead <;> rw [prefixEq] at equal <;> cases equal
    have bodyRead := body.printReads rest
    have effectRead := EffectClauseReads.printReads effects (rest := afterEffects) (by
      intro tail same
      obtain ⟨_, _, head, rfl | rfl⟩ := measureHead <;> rw [head] at same <;> cases same)
    have measureRead : MeasureReads (functionScope before parameters) afterEffects measure afterMeasure := by
      cases measure with
      | none =>
        apply MeasureReads.absent
        intro tail same
        obtain ⟨_, head⟩ := bodyHead
        change afterMeasure = keyword "decreases" :: tail at same
        rw [head] at same
        cases same
      | some m =>
        have blocked : ¬ Continues 0 afterMeasure := by
          obtain ⟨_, head⟩ := bodyHead
          rw [head]
          exact noOperatorAtOpenBrace
        simpa only [afterEffects, measurePieces, Expr.printTokens, List.map_cons,
          List.cons_append, hpDecreases] using
          (MeasureReads.present m (m.expression.printReads (minimum := 0) blocked))
    have resultRead : ResultReads before afterParams result afterResult := by
      cases result with
      | none => exact .absent (resultClosed _ (Or.inl rfl))
      | some written =>
        have read := written.printReads (valid written List.mem_cons_self)
          (resultClosed _ (Or.inr rfl))
        simpa only [afterParams, resultPieces, List.map_cons, List.cons_append, hpArrow] using
          (ResultReads.typed read)
    have paramsRead := ParamsRead.printReads (rest := afterParams) parameters
    simpa only [Decl.printPieces, Expr.printTokens, List.map_append, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, List.append_assoc, hpFn, hpName, hpOpen,
      afterMeasure, afterEffects, afterResult, afterParams] using
      (DeclReads.function name ordinary result valid parameters measure body distinct returns effects
        paramsRead resultRead effectRead measureRead bodyRead)
  | record exported name fields valid distinct =>
    have hpHead : (recordDeclarationHead exported).map PrintedToken.value = recordDeclarationPrefix exported := by
      cases exported <;> rfl
    have body := RecordMembersRead.printReads (rest := semicolon :: rest) fields valid
    simpa only [Decl.printPieces, List.map_append, List.map_cons, List.map_nil, List.cons_append,
      List.nil_append, List.append_assoc, hpHead, hpName, hpAssign, hpOpenBrace, hpCloseBrace, hpSemi] using
      (DeclReads.record exported name valid distinct body)
  | tagged exported name first tail valid distinct =>
    have hpHead : (taggedDeclarationHead exported).map PrintedToken.value = taggedDeclarationPrefix exported := by
      cases exported <;> rfl
    obtain ⟨_, firstRead, tailRead⟩ := variantMembers_printReads first tail (rest := semicolon :: rest) valid
    simpa only [Decl.printPieces, List.map_append, List.map_cons, List.map_nil, List.cons_append,
      List.nil_append, List.append_assoc, hpHead, hpName, hpAssign, hpOpenBrace, hpCloseBrace, hpSemi] using
      (DeclReads.tagged exported name valid distinct firstRead tailRead)
  | table item =>
    have body := TableFieldsRead.printReads (rest := closeBrace :: rest) item.fields item.valid
    simpa only [Decl.printPieces, List.map_append, List.map_cons, List.map_nil, List.cons_append,
      List.nil_append, List.append_assoc, hpCloseBrace] using (DeclReads.table item body)
  | effectGroup item =>
    have body := EffectListReads.printReads (read := CarrierEffectReads) (rest := semicolon :: rest)
      item.written WrittenCarrierEffect.printPieces (fun item _ suffix => CarrierEffectReads.printReads item suffix)
    simpa only [Decl.printPieces, List.map_append, List.map_cons, List.map_nil, List.cons_append,
      List.nil_append, List.append_assoc, hpCloseBrace, hpSemi] using (DeclReads.effectGroup item body)
  | environment name abi row =>
    simpa only [Decl.printPieces, LowLevel.environment_printTokens] using
      (DeclReads.environment (before := before) (rest := rest) name abi row)

end Gabbro.Core.Ast
