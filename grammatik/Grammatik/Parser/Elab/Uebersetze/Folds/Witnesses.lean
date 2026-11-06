module

public import Grammatik.Parser.Expr.Ausdruck.Teil3
public import Grammatik.Parser.Elab.Uebersetze.Folds.Expressions
public import Grammatik.Parser.Elab.Uebersetze.Folds.Expansion
public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil10
public import Grammatik.Parser.Elab.UebersetzeAllg3.Rest2a
import all Grammatik.Parser.Expr.Ausdruck.Teil1
import all Grammatik.Parser.Expr.Ausdruck.Teil2
import all Grammatik.Parser.Expr.Ausdruck.Teil2a
import all Grammatik.Parser.Expr.Ausdruck.Teil3
import all Grammatik.Parser.Expr.Typ
import all Grammatik.Parser.Elab.Uebersetze.Folds.FloatWitnesses
import all Grammatik.Parser.Elab.Uebersetze.Folds.Expressions
import all Grammatik.Parser.Elab.Uebersetze.Folds.Expansion
import all Grammatik.Parser.Elab.Uebersetze.Folds.FloatExpansion
import all Grammatik.Parser.Elab.Uebersetze.Folds.FloatLiterals
import all Grammatik.Parser.Elab.Uebersetze.Branches
import all Grammatik.Parser.Elab.Uebersetze.LoopHeaders
import all Grammatik.Parser.Elab.Uebersetze.Records.Records
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil3
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil4
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil5
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil5Rest
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil7
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil8
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil9
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil10
import all Grammatik.Parser.Elab.UebersetzeAllg.Teil1
import all Grammatik.Parser.Elab.UebersetzeAllg.Teil2
import all Grammatik.Parser.Elab.UebersetzeAllg.Teil3
import all Grammatik.Parser.Elab.UebersetzeAllg.Teil3Values
import all Grammatik.Parser.Elab.UebersetzeAllg.Teil4
import all Grammatik.Parser.Elab.UebersetzeAllg.Teil5
import all Grammatik.Parser.Elab.UebersetzeAllg3.Body
import all Grammatik.Parser.Elab.UebersetzeAllg3.Ende
import all Grammatik.Parser.Elab.UebersetzeAllg3.Kopf
import all Grammatik.Parser.Elab.UebersetzeAllg3.Seq
import all Grammatik.Parser.Elab.UebersetzeAllg3.Stufe
import all Grammatik.Parser.Elab.UebersetzeAllg3.Struct
import all Grammatik.Parser.Elab.UebersetzeAllg3.Transition
import all Grammatik.Parser.Elab.UebersetzeAllg3.Rest1
import all Grammatik.Parser.Elab.UebersetzeAllg3.Rest2a
import all Grammatik.Parser.Elab.UebersetzeAllg3.Measures.Export
import all Grammatik.Parser.Elab.Generic.Signatures
import all Grammatik.Parser.Elab.Generic.StaticConformance
import all Init.Data.Repr
import all Init.Data.String.Defs
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Extra
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.Modify
import all Init.Data.String.OrderInstances
import all Init.Data.String.Pattern
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.Char
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Pattern.String
import all Init.Data.String.PosRaw
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Stream
import all Init.Data.String.Subslice
import all Init.Data.String.Substring
import all Init.Data.String.TakeDrop
import all Init.Data.String.Termination
import all Init.Data.String.ToSlice

@[expose] public section
namespace Gabbro.Grammatik.Parser.Uebersetze.FoldWitnesses
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2

set_option maxRecDepth 100000
set_option maxHeartbeats 800000

-- Use the actual selected parser/mutual equations, not their complete fuel records.
attribute [local cbv_opaque] parseTyp parseTypNach parseOr parseOrL parseAnd parseAndL
  parseCmp parseBit parseBitL parseAdd parseAddL parseMul parseMulL parseUnary
  parsePrimary parseKopf parseSuffixe parseFold parseQuant parseDomain domPlace parseOrt
  parsePred parsePredOrL parsePredAnd parsePredAndL parsePredNot parsePredAtom uFloatLimit
attribute [local cbv_eval] parseTyp.eq_def parseTypNach.eq_def parseOr.eq_def parseOrL.eq_def
  parseAnd.eq_def parseAndL.eq_def parseCmp.eq_def parseBit.eq_def parseBitL.eq_def
  parseAdd.eq_def parseAddL.eq_def parseMul.eq_def parseMulL.eq_def parseUnary.eq_def
  parsePrimary.eq_def parseKopf.eq_def parseSuffixe.eq_def parseFold.eq_def parseQuant.eq_def
  parseDomain.eq_def domPlace.eq_def parseOrt.eq_def parsePred.eq_def parsePredOrL.eq_def
  parsePredAnd.eq_def parsePredAndL.eq_def parsePredNot.eq_def parsePredAtom.eq_def

def table : UTab :=
  {name := "T", count := 3, cols := [("v", (1, 9)), ("open", (0, 1))], bools := ["open"]}

def context : UCtx :=
  {names := [], kinds := [], types := [], tabs := [table], locks := [], held := [],
   res := none, fname := "sample", alias := [], lits := []}

def value : SExpr := .field (.index (.variable "T") (.variable "k")) "v"

def operands (kind : XKind) : List SExpr :=
  [.variable "T", .tru, value] ++ (if kind == .foldAdd then [] else [.lit 99])

def tokens (word : String) (empty : List Token := []) : List Token :=
  [.wort word, .ident "k", .wort "in", .wort "slots", .wort "of", .ident "T",
   .zeichen ":", .ident "T", .zeichen "[", .ident "k", .zeichen "]", .zeichen ".", .ident "v"] ++
    empty ++ [.ende]

private theorem parsed_add :
    parseTop (tokens "add") = .ok (.ext .foldAdd ["k", "slots"] (operands .foldAdd)) := by cbv
private theorem parsed_min :
    parseTop (tokens "min" [.wort "else", .num 99]) =
      .ok (.ext .foldMin ["k", "slots"] (operands .foldMin)) := by cbv
private theorem parsed_max :
    parseTop (tokens "max" [.wort "else", .num 99]) =
      .ok (.ext .foldMax ["k", "slots"] (operands .foldMax)) := by cbv

public theorem add_parser_zeuge :
    beqTop (parseTop (tokens "add")) (.ok (.ext .foldAdd ["k", "slots"] (operands .foldAdd))) = true := by
  simp only [parsed_add]
  cbv

public theorem min_parser_zeuge :
    beqTop (parseTop (tokens "min" [.wort "else", .num 99]))
      (.ok (.ext .foldMin ["k", "slots"] (operands .foldMin))) = true := by
  simp only [parsed_min]
  cbv

public theorem max_parser_zeuge :
    beqTop (parseTop (tokens "max" [.wort "else", .num 99]))
      (.ok (.ext .foldMax ["k", "slots"] (operands .foldMax))) = true := by
  simp only [parsed_max]
  cbv

-- Each complete triple comes only from its original expansion equation.
private def addExpansion : { actual : List UStmt × UCtx × SExpr //
    expandFold context 0 .foldAdd ["k", "slots"] (operands .foldAdd) = .ok actual } := by
  refine ⟨?_, by cbv <;> exact Eq.refl _⟩
private def minExpansion : { actual : List UStmt × UCtx × SExpr //
    expandFold context 0 .foldMin ["k", "slots"] (operands .foldMin) = .ok actual } := by
  refine ⟨?_, by cbv <;> exact Eq.refl _⟩
private def maxExpansion : { actual : List UStmt × UCtx × SExpr //
    expandFold context 0 .foldMax ["k", "slots"] (operands .foldMax) = .ok actual } := by
  refine ⟨?_, by cbv <;> exact Eq.refl _⟩

public theorem add_expansion_zeuge :
    (expandFold context 0 .foldAdd ["k", "slots"] (operands .foldAdd)).toOption.map (·.1) =
      some [.bindMut "#fold:0:acc" 0 27 (.lit 0),
        .loopBeg "k" "T" .tru, .ifBeg .tru,
        .bind "#fold:0:value" none (.tab "T" "v" (.param "k")),
        .setVar "#fold:0:acc" (.eng (.add (.param "#fold:0:acc") (.param "#fold:0:value")) 0 27),
        .ifElse, .blkEnd, .blkEnd,
        .bind "#fold:0:acc:result" none (.eng (.param "#fold:0:acc") 0 27)] := by
  rw [addExpansion.property] <;> cbv

public theorem min_expansion_zeuge :
    (expandFold context 0 .foldMin ["k", "slots"] (operands .foldMin)).toOption.map
      (fun result => result.2.1.types.head?) = some (some (.int 1 99)) := by
  rw [minExpansion.property] <;> cbv

public theorem max_expansion_zeuge :
    (expandFold context 0 .foldMax ["k", "slots"] (operands .foldMax)).toOption.map
      (fun result => result.2.1.types.head?) = some (some (.int 1 99)) := by
  rw [maxExpansion.property] <;> cbv

/-- The fallback is evaluated after the loop, inside the empty-only branch. -/
def emptyOnly : List UStmt → Bool
  | code => match code.reverse with
    | .bind .. :: .blkEnd :: .ifElse :: .setVar _ (.lit 99) :: .ifBeg (.not (.var _)) :: .blkEnd :: _ => true
    | _ => false

public theorem extrema_empty_only_zeuge :
    (expandFold context 0 .foldMin ["k", "slots"] (operands .foldMin)).toOption.map
      (fun result => emptyOnly result.1) = some true ∧
    (expandFold context 0 .foldMax ["k", "slots"] (operands .foldMax)).toOption.map
      (fun result => emptyOnly result.1) = some true := by
  rw [minExpansion.property, maxExpansion.property] <;> cbv

/-- The filter guards the element read, rather than filtering a completed sum. -/
public theorem filtered_add_zeuge :
    (expandFold context 0 .foldAdd ["k", "slots"]
      [.variable "T", .field (.index (.variable "T") (.variable "k")) "open", value]).toOption.map
      (fun result => result.1[2]?) = some (some (.ifBeg (.tabB "T" "open" (.param "k")))) := by cbv

/-- The unchanged single-function fixture, with its actual statement result. -/
def program (body : List UStmt) : UProg :=
  {tabs := [table], locks := [], fns := [{
    name := "sample"
    params := []
    kinds := []
    res := none
    held := []
    puts := []
    gives := []
    body := body
    ret := .empty }]}

def lowered (kind : XKind) : Bool :=
  match uAnwReihe [table] [] 1000 context
      [.bind false "total" none (.ext kind ["k", "slots"] (operands kind))] with
  | .error _ => false
  | .ok (body, _) =>
    (lowerAllg (program body)).toOption.isSome

private def addStatements : { actual : List UStmt × UCtx //
    uAnwReihe [table] [] 1000 context
      [.bind false "total" none (.ext .foldAdd ["k", "slots"] (operands .foldAdd))] =
        .ok actual } := by
  refine ⟨?_, by cbv <;> exact Eq.refl _⟩
private def minStatements : { actual : List UStmt × UCtx //
    uAnwReihe [table] [] 1000 context
      [.bind false "total" none (.ext .foldMin ["k", "slots"] (operands .foldMin))] =
        .ok actual } := by
  refine ⟨?_, by cbv <;> exact Eq.refl _⟩
private def maxStatements : { actual : List UStmt × UCtx //
    uAnwReihe [table] [] 1000 context
      [.bind false "total" none (.ext .foldMax ["k", "slots"] (operands .foldMax))] =
        .ok actual } := by
  refine ⟨?_, by cbv <;> exact Eq.refl _⟩

-- Reuse the green generic fuel/typed-value selectors and program-assembly proof.
attribute [local cbv_opaque] lowStufe lowSeqL lowStructL
attribute [local cbv_eval] FloatFoldWitnesses.sequence_select FloatFoldWitnesses.structure_select
  lowStufe_seq lowStufe_struct FloatFoldWitnesses.variable_head FloatFoldWitnesses.fit_same

private theorem add_function :
    (lowerFnAt (program addStatements.val.1) ⟨0, by change 0 < 1; decide⟩).toOption.isSome = true := by
  cbv
private theorem min_function :
    (lowerFnAt (program minStatements.val.1) ⟨0, by change 0 < 1; decide⟩).toOption.isSome = true := by
  cbv
private theorem max_function :
    (lowerFnAt (program maxStatements.val.1) ⟨0, by change 0 < 1; decide⟩).toOption.isSome = true := by
  cbv

private theorem lowering_from_statements (kind : XKind)
    (result : { actual : List UStmt × UCtx //
      uAnwReihe [table] [] 1000 context
        [.bind false "total" none (.ext kind ["k", "slots"] (operands kind))] = .ok actual })
    (first : (lowerFnAt (program result.val.1)
      ⟨0, by change 0 < 1; decide⟩).toOption.isSome = true) : lowered kind = true := by
  have singleton (f : Fin (program result.val.1).fns.length) :
      f = ⟨0, by change 0 < 1; decide⟩ := by
    apply Fin.ext
    change f.val = 0
    have bound : f.val < 1 := f.isLt
    omega
  have success : (lowerAllg (program result.val.1)).toOption.isSome = true := by
    apply FloatFoldWitnesses.lowering_phases
    · rfl
    · intro f
      rw [singleton f]
      exact first
    · cbv
    · intro f
      rw [singleton f]
      rfl
  simpa only [lowered, result.property] using success

/-- Each integer form reaches generic machine-G lowering through the real statement path. -/
public theorem add_lowering_zeuge : lowered .foldAdd = true :=
  lowering_from_statements .foldAdd addStatements add_function
public theorem min_lowering_zeuge : lowered .foldMin = true :=
  lowering_from_statements .foldMin minStatements min_function
public theorem max_lowering_zeuge : lowered .foldMax = true :=
  lowering_from_statements .foldMax maxStatements max_function

public theorem missing_min_else_zeuge :
    beqTop (parseTop (tokens "min")) (.error "fold min/max: else is required") = true := by cbv

public theorem missing_max_else_zeuge :
    beqTop (parseTop (tokens "max")) (.error "fold min/max: else is required") = true := by cbv

-- The producer shares this diagnostic across add, and and or folds.
private theorem parsed_add_else :
    parseTop (tokens "add" [.wort "else", .num 99]) =
      .error "fold add/and/or: else is not allowed" := by cbv

public theorem unexpected_add_else_zeuge :
    beqTop (parseTop (tokens "add" [.wort "else", .num 99]))
      (.error "fold add/and/or: else is not allowed") = true := by
  rw [parsed_add_else]
  cbv

public theorem open_domain_refused_zeuge :
    (expandFold {context with tabs := [{table with count := 0, von := some "provider"}]}
      0 .foldAdd ["k", "slots"] (operands .foldAdd)).toOption.isNone = true := by cbv

public theorem second_table_refused_zeuge :
    (expandFold {context with tabs := [table, {table with name := "Other"}]}
      0 .foldAdd ["k", "slots"] [.variable "T", .tru,
        .field (.index (.variable "Other") (.lit 0)) "v"]).toOption.isNone = true := by cbv

public theorem overflow_refused_zeuge :
    (expandFold {context with tabs := [{table with count := 2^64}]}
      0 .foldAdd ["k", "slots"] (operands .foldAdd)).toOption.isNone = true := by cbv

public theorem annotated_overflow_refused_zeuge :
    (expandFoldStmt context (.bind false "total" (some (.range (.atom "u8") (.lit 0) (.lit 9) false))
      (.ext .foldAdd ["k", "slots"] (operands .foldAdd)))).toOption.isNone = true := by cbv

public theorem empty_sum_range_zeuge : foldSumRange 0 (-9, 12) = (0, 0) := by cbv
public theorem signed_sum_range_zeuge : foldSumRange 3 (-9, 12) = (-27, 36) := by cbv

/-- Float folds retain their source expression for ordered native expansion. -/
public theorem float_syntax_zeuge :
    beqTop (parseTop [.wort "add", .ident "k", .wort "in", .wort "slots", .wort "of",
      .ident "T", .zeichen ":", .float "1.0", .ende])
      (.ok (.ext .foldAdd ["k", "slots"] [.variable "T", .tru, .float "1.0"])) = true := by cbv

public theorem float_export_zeuge :
    (expandFold context 0 .foldAdd ["k", "slots"] [.variable "T", .tru, .float "1.0"]).toOption.isSome = true := by cbv

/-- Deferred source typing must not turn a placeholder into a proved zero range. -/
public theorem unknown_local_range_zeuge :
    foldRange {context with
      names := ["x"]
      kinds := [.int]
      types := [.int 0 0]
      unknownRanges := ["x"]} (.param "x") = none := by cbv

public theorem inferred_local_range_zeuge :
    foldRange (foldBindingContext context
      {context with names := ["x"], kinds := [.int], types := [.int 0 0]}
      (.bind "x" none (.lit 7))) (.param "x") = some (7, 7) := by cbv

public theorem deferred_local_range_zeuge :
    foldRange (foldBindingContext context
      {context with names := ["x"], kinds := [.int], types := [.int 0 0]}
      (.bind "x" none (.div (.lit 9) (.lit 3)))) (.param "x") = none := by cbv

end Gabbro.Grammatik.Parser.Uebersetze.FoldWitnesses
