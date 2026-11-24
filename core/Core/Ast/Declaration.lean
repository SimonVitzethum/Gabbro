module

public import Core.Ast.Block

@[expose] public section

namespace Gabbro.Core.Ast

open Gabbro.Core.Text

abbrev Declaration (before : Scope) := (after : Scope) × Decl before after

inductive ResultReads : List Token → Option WrittenType → List Token → Prop where
  | absent (closed : ∀ tail, rest ≠ arrow :: tail) : ResultReads rest none rest
  | typed : TypeReads input written rest → ResultReads (arrow :: input) (some written) rest

inductive MeasureReads (scope : Scope) : List Token → Option (Measure scope) → List Token → Prop where
  | absent (closed : ∀ tail, rest ≠ keyword "decreases" :: tail) :
      MeasureReads scope rest none rest
  | present (m : Measure scope) : ExprReads scope 0 input m.expression rest →
      MeasureReads scope (keyword "decreases" :: input) (some m) rest

inductive DeclReads (before : Scope) : List Token → Declaration before → List Token → Prop where
  | constant (name : Identifier) (ordinary : ordinaryLocal name) (written : WrittenType) (valid : written.valid)
      (value : Expr before type) (staticValue : value.static) (fits : Fits type written.type) :
      TypeReads input written (assignment :: rhs) →
      ExprReads before 0 rhs value (semicolon :: rest) →
      DeclReads before (keyword "const" :: .word name.val :: colon :: input)
        ⟨_, .constant name ordinary written valid value staticValue fits⟩ rest
  | function (name : Identifier) (ordinary : directName name) (result : Option WrittenType)
      (valid : ∀ t ∈ result.toList, WrittenType.valid t) (parameters : List Parameter)
      (measure : Option (Measure (functionScope before parameters)))
      (body : BracedBlock (writtenResult result) (functionScope before parameters))
      (distinct : (parameters.map (fun p => p.name.val)).Nodup)
      (returns : result.isSome = true → body.returns = true) :
      ParamsRead input parameters afterParams →
      ResultReads afterParams result afterResult →
      MeasureReads (functionScope before parameters) afterResult measure afterMeasure →
      BlockReads (writtenResult result) (functionScope before parameters) afterMeasure body rest →
      DeclReads before (keyword "fn" :: .word name.val :: openParen :: input)
        ⟨before, .function name ordinary parameters result valid measure body distinct returns⟩ rest

def resultPieces : Option WrittenType → List PrintedToken
  | none => []
  | some written => printArrow :: written.printPieces

def measurePieces : Option (Measure scope) → List PrintedToken
  | none => []
  | some m => printDecreases :: m.expression.printPieces

def Decl.printPieces : Decl before after → List PrintedToken
  | .constant name _ written _ value _ _ =>
    [printConst, name.print, printColon] ++ written.printPieces ++ [printAssignment] ++
      value.printPieces ++ [printSemicolon]
  | .function name _ parameters result _ measure body _ _ =>
    [printFn, name.print, printOpen] ++ commaSeparated (parameters.map Parameter.printPieces) ++
      [printClose] ++ resultPieces result ++ measurePieces measure ++ body.printPieces

-- Mirror StmtReads.assign_inversion with the written type and const initializer.
theorem DeclReads.constant_inversion
    (read : DeclReads before (keyword "const" :: .word spelling :: colon :: input) tree rest) :
    ∃ (name : Identifier) (ordinary : ordinaryLocal name) (written : WrittenType) (valid : written.valid)
      (type : Ty .value) (value : Expr before type) (staticValue : value.static) (fits : Fits type written.type) (rhs : List Token),
      name.val = spelling ∧ TypeReads input written (assignment :: rhs) ∧
      ExprReads before 0 rhs value (semicolon :: rest) ∧
      tree = ⟨_, .constant name ordinary written valid value staticValue fits⟩ := by
  cases read with
  | constant name ordinary written valid value staticValue fits typeRead exprRead =>
      refine ⟨name, ordinary, written, valid, _, value, staticValue, fits, _, ?_, typeRead, exprRead, rfl⟩
      rfl

-- Mirror BlockReads.braced_inversion and keep every header derivation in token order.
theorem DeclReads.function_inversion
    (read : DeclReads before (keyword "fn" :: .word spelling :: openParen :: input) tree rest) :
    ∃ (name : Identifier) (ordinary : directName name) (ps : List Parameter)
      (result : Option WrittenType) (valid : ∀ t ∈ result.toList, WrittenType.valid t)
      (measure : Option (Measure (functionScope before ps)))
      (body : BracedBlock (writtenResult result) (functionScope before ps))
      (distinct : (ps.map (fun p => p.name.val)).Nodup)
      (returns : result.isSome = true → body.returns = true)
      (afterParams afterResult afterMeasure : List Token),
      name.val = spelling ∧ ParamsRead input ps afterParams ∧
      ResultReads afterParams result afterResult ∧
      MeasureReads (functionScope before ps) afterResult measure afterMeasure ∧
      BlockReads (writtenResult result) (functionScope before ps) afterMeasure body rest ∧
      tree = ⟨before, .function name ordinary ps result valid measure body distinct returns⟩ := by
  cases read with
  | function name ordinary result valid parameters measure body distinct returns
      paramsRead resultRead measureRead blockRead =>
      refine ⟨name, ordinary, parameters, result, valid, measure, body, distinct, returns,
        _, _, _, ?_, paramsRead, resultRead, measureRead, blockRead, rfl⟩
      rfl

-- Mirror StmtReads.deterministic, using the header and body derivations in order.
theorem DeclReads.deterministic (left : DeclReads before input a rest)
    (right : DeclReads before input b rest') : a = b ∧ rest = rest' := by
  have resultDet : ∀ {i : List Token} {r : Option WrittenType} {o : List Token},
      ResultReads i r o → ∀ {r' o'}, ResultReads i r' o' → r = r' ∧ o = o' := by
    intro i r o read
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
  have measureDet : ∀ {i : List Token} {m : Option (Measure before)} {o : List Token},
      MeasureReads before i m o → ∀ {m' o'}, MeasureReads before i m' o' → m = m' ∧ o = o' := by
    intro i m o read
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
                have fstEq := congrArg (fun p : TypedExpr before => p.1) typedEq
                injection fstEq with loEq hiEq
                cases loEq
                cases hiEq
                cases typedEq
                exact ⟨rfl, oeq⟩
  cases left with
  | constant name ordinary written valid type value staticValue fits typeRead exprRead =>
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
  | function name ordinary result valid parameters measure body distinct returns
      paramsRead resultRead measureRead blockRead =>
      obtain ⟨name', ordinary', ps, result', valid', measure', body', distinct', returns',
        afterParams, afterResult, afterMeasure, nameEq, paramsRead', resultRead', measureRead',
        blockRead', treeEq⟩ := DeclReads.function_inversion right
      have nameFull : name' = name := Subtype.ext nameEq
      subst name'
      obtain ⟨paramsEq, afterParamsEq⟩ := ParamsRead.deterministic paramsRead paramsRead'
      cases paramsEq
      subst afterParams
      obtain ⟨resultEq, afterResultEq⟩ := resultDet resultRead resultRead'
      cases resultEq
      subst afterResult
      obtain ⟨measureEq, afterMeasureEq⟩ := measureDet measureRead measureRead'
      cases measureEq
      subst afterMeasure
      obtain ⟨bodyEq, restEq⟩ := BlockReads.deterministic blockRead blockRead'
      cases bodyEq
      exact ⟨treeEq.symm, restEq⟩

-- Mirror StmtReads.disjoint_closeBrace using the nonempty declaration prefix.
theorem DeclReads.disjoint_end : ¬ DeclReads before [] tree rest := by
  intro read
  cases read

-- Mirror StmtReads.consumes using the type, expression and block suffixes.
theorem DeclReads.consumes (read : DeclReads before input tree rest) : rest <:+ input := by
  have resultConsumes : ∀ {i : List Token} {r : Option WrittenType} {o : List Token},
      ResultReads i r o → o <:+ i := by
    intro i r o h
    cases h with
    | absent _ => exact List.suffix_refl _
    | typed tr => exact tr.consumes.trans (List.suffix_cons _ _)
  have measureConsumes : ∀ {i : List Token} {m : Option (Measure before)} {o : List Token},
      MeasureReads before i m o → o <:+ i := by
    intro i m o h
    cases h with
    | absent _ => exact List.suffix_refl _
    | present m exprRead => exact exprRead.consumes.trans (List.suffix_cons _ _)
  cases read with
  | constant _ _ _ _ _ _ _ typeRead exprRead =>
      exact (((((exprRead.consumes.trans (List.suffix_cons _ _)).trans typeRead.consumes).trans
        (List.suffix_cons _ _)).trans (List.suffix_cons _ _)).trans (List.suffix_cons _ _))
  | function _ _ _ _ _ _ _ _ _ paramsRead resultRead measureRead blockRead =>
      exact ((((((blockRead.consumes.trans measureConsumes).trans resultConsumes).trans
        paramsRead.consumes).trans (List.suffix_cons _ _)).trans (List.suffix_cons _ _)).trans
        (List.suffix_cons _ _))

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
        simp only [Decl.printPieces, resultPieces, measurePieces, BracedBlock.printPieces,
          List.map_append, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
          List.append_assoc]
        refine .function name ordinary result valid parameters measure (.braces items) distinct returns ?_ ?_ ?_ ?_
        · exact ParamsRead.printReads parameters
        · cases result with
          | none =>
              apply ResultReads.absent
              intro more h
              cases measure with
              | none => cases h
              | some m => cases h
          | some written =>
              apply ResultReads.typed
              exact WrittenType.printReads written (valid written (by simp)) (by
                intro more h
                cases measure with
                | none => cases h
                | some m => cases h)
        · cases measure with
          | none =>
              apply MeasureReads.absent
              intro more h
              cases h
          | some m =>
              apply MeasureReads.present
              exact Expr.printReads m.expression (by
                simpa only [BracedBlock.printPieces, List.map_append, List.map_cons, List.map_nil,
                  List.cons_append, List.nil_append, List.append_assoc] using
                  (noOperatorAtOpenBrace (minimum := 0)
                    (more := items.printItems.map PrintedToken.value ++ printCloseBrace.value :: rest)))
        · simpa only [BracedBlock.printPieces, List.map_append, List.map_cons, List.map_nil,
            List.cons_append, List.nil_append, List.append_assoc] using (.braces items).printReads rest

end Gabbro.Core.Ast
