module
public import Grammatik.Parser.Elab.Tuples.Frontend
import Lean.Elab.Tactic.Cbv
import all Init.Control.Except
import all Init.Data.Repr
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Defs
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

namespace Gabbro.Grammatik.Parser.Tuples
attribute [local cbv_eval] strEq_apply_eq_decide
set_option maxRecDepth 100000

private theorem repr_zero : Nat.repr 0 = "0" := by rfl
private theorem repr_one : Nat.repr 1 = "1" := by rfl
private theorem repr_thirty_two : Nat.repr 32 = "32" := by rfl

attribute [local cbv_eval] repr_zero repr_one repr_thirty_two

def byte : STyp := .range (.atom "u32") (.lit 0) (.lit 255) false
def pair : STyp := .tuple [byte, byte]
def generated : String := "#tuple:32,32:0"

def producer : FnSig :=
  { art := "impl"
    name := "make"
    params := []
    res := some pair
    fehler := none
    klauseln := [.effs [.pure]] }

def caller : FnSig :=
  { art := "impl"
    name := "main"
    params := []
    res := some byte
    fehler := none
    klauseln := [.effs [.pure]] }

/-- A returning function, a caller that destructures its result, and positional access. -/
def fixture : List SItemTief :=
  [.fnT producer (.block [] (some (.ret (some (.built "#tuple" [.lit 17, .lit 25]))))),
   .fnT caller (.block
     [.bind false "p" none (.call "make" []),
      .bind false "#tuple-pattern,a,b" none (.variable "p")]
     (some (.ret (some (.field (.variable "p") "1")))))]

def expandedFixture : List SItemTief :=
  [.typeT [] generated [] [] (some pair),
   .fnT { producer with res := some (.atom generated) }
     (.block [] (some (.ret (some (.call generated
       [.ext .label ["_0"] [.lit 17], .ext .label ["_1"] [.lit 25]]))))),
   .fnT caller (.block
     [.bind false "p" none (.call "make" []),
      .bind false "#tuple-local:0" (some (.atom generated)) (.variable "p"),
      .bind false "a" (some byte) (.field (.variable "#tuple-local:0") "_0"),
      .bind false "b" (some byte) (.field (.variable "#tuple-local:0") "_1")]
     (some (.ret (some (.field (.variable "p") "_1")))))]

def context : Context :=
  { items := fixture
    constants := []
    aliases := [] }

private def internedState : State :=
  { records := [⟨generated, [byte, byte],
      [⟨some (.int 0 255), byte, 32⟩, ⟨some (.int 0 255), byte, 32⟩]⟩] }

/-- Compose successful stateful actions without evaluating their implementations again. -/
private theorem run_two {α β : Type} {f : α → ExpandM β} {a b : α} {a' b' : β}
    {s0 s1 s2 : State}
    (ha : (f a).run s0 = .ok (a', s1)) (hb : (f b).run s1 = .ok (b', s2)) :
    ([a, b].mapM f).run s0 = .ok ([a', b'], s2) := by
  simp only [List.mapM_cons, List.mapM_nil, bind_assoc, pure_bind]
  change Except.bind ((f a).run s0) (fun (x, s) =>
    Except.bind ((f b).run s) (fun (y, s) => .ok ([x, y], s))) = _
  simp only [ha, hb, Except.bind]

private theorem prepared_context_raw :
    (let constants := Uebersetze.uConstsRech (Uebersetze.uKonstFns fixture) fixture []
     let aliases := Uebersetze.uAliase constants fixture ++ Uebersetze.uAliasBreiten fixture ++
       constants.map (fun entry => (entry.1, (entry.2, entry.2)))
     let ordinary := fixture.filter fun
       | .typeT _ _ _ _ (some (.tuple _)) => false
       | _ => true
     let sourceTypes := (Uebersetze.uTypes constants aliases [] ordinary).toOption.getD { types := [] }
     ({ items := fixture, constants := constants, aliases := aliases,
        sourceTypes := sourceTypes } : Context)) = context := by
  cbv

private theorem producer_run :
    (expandItem context 100000
      (.fnT producer (.block [] (some (.ret (some (.built "#tuple" [.lit 17, .lit 25]))))))).run {} =
    .ok (.fnT { producer with res := some (.atom generated) }
      (.block [] (some (.ret (some (.call generated
        [.ext .label ["_0"] [.lit 17], .ext .label ["_1"] [.lit 25]]))))), internedState) := by
  cbv

private theorem caller_run :
    (expandItem context 100000 (.fnT caller (.block
      [.bind false "p" none (.call "make" []),
       .bind false "#tuple-pattern,a,b" none (.variable "p")]
      (some (.ret (some (.field (.variable "p") "1"))))))).run internedState =
    .ok (.fnT caller (.block
      [.bind false "p" none (.call "make" []),
       .bind false "#tuple-local:0" (some (.atom generated)) (.variable "p"),
       .bind false "a" (some byte) (.field (.variable "#tuple-local:0") "_0"),
       .bind false "b" (some byte) (.field (.variable "#tuple-local:0") "_1")]
      (some (.ret (some (.field (.variable "p") "_1"))))),
      { internedState with nextLocal := 1 }) := by
  cbv

/-- Small AST evaluation, without lexing a large source or building an entire program witness. -/
private theorem prepared_context : prepareContext fixture = context :=
  prepared_context_raw

theorem tuple_export_zeuge : expand fixture = .ok (expandedFixture, [generated]) := by
  unfold expand
  rewrite [prepared_context]
  dsimp only
  have hrun := run_two (f := expandItem context 100000) producer_run caller_run
  change (fixture.mapM (expandItem context 100000)).run {} = _ at hrun
  rewrite [hrun]
  cbv

theorem tuple_schema_zeuge :
    (Uebersetze.uTypes [] [] [] expandedFixture).map (fun scope =>
      scope.records.map (fun record => (record.name, record.fields))) =
    .ok [(generated, [("_0", Ty.int 0 255), ("_1", Ty.int 0 255)])] := by
  cbv

theorem tuple_position_zeuge :
    Uebersetze.uRecordPosition [("_0", Ty.int 0 255), ("_1", Ty.int 0 255)] "_1" =
      .ok ⟨Ty.int 0 255, FieldAt.tail FieldAt.head⟩ := by
  simp [Uebersetze.uRecordPosition, strEq_eq_schnell, strEqSchnell, Except.map]

theorem tuple_type_parser_zeuge :
    parseTyp 64 [.zeichen "(", .wort "u32", .zeichen ",", .wort "bool", .zeichen ")"] =
      .ok (.tuple [.atom "u32", .atom "bool"], []) := by cbv

theorem tuple_expression_parser_zeuge :
    parseOr 128 [.zeichen "(", .num 17, .zeichen ",", .num 25, .zeichen ")", .zeichen ".", .num 1] =
      .ok (.field (.built "#tuple" [.lit 17, .lit 25]) "1", []) := by cbv

theorem tuple_pattern_parser_zeuge :
    parseStmt 128 [.wort "let", .zeichen "(", .ident "a", .zeichen ",", .ident "_",
      .zeichen ")", .zeichen "=", .ident "p", .zeichen ";"] =
      .ok (.bind false "#tuple-pattern,a,_" none (.variable "p"), []) := by cbv

def state : State :=
  { records := [⟨generated, [byte, byte], []⟩] }

theorem tuple_field_refused_zeuge :
    ((expandExpr context [("p", .atom generated)] none 32 (.field (.variable "p") "2")).run state).map Prod.fst =
      .error "tuple field: index out of range" := by cbv

theorem tuple_arity_refused_zeuge :
    ((destructure context [("p", .atom generated)] 32 ["a", "b", "c"] none (.variable "p")).run state).map Prod.fst =
      .error "tuple pattern: arity mismatch" := by cbv

theorem nested_pattern_refused_zeuge :
    parseTuplePattern [.zeichen "(", .ident "a"] =
      .error "tuple pattern: nested patterns are unsupported" := by
  simp only [parseTuplePattern]

/-- A discarded component adds no field binding, while the tuple value is still bound once. -/
theorem tuple_wildcard_zeuge :
    ((destructure context [("p", .atom generated)] 32 ["a", "_"] none (.variable "p")).run state).map
      (fun (statements, _) => statements.length) = .ok 2 := by cbv

/-- Equal resolved scalar types, including an alias, allocate exactly one record. -/
theorem tuple_intern_zeuge :
    (expand [.typeT [] "Byte" [] [] (some byte),
      .protoT { producer with res := some (.tuple [.atom "Byte", byte]) },
      .protoT { caller with res := some pair }]).map (fun (_, names) => names.length) = .ok 1 := by cbv

end Gabbro.Grammatik.Parser.Tuples
