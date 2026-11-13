module

public import Grammatik.Parser.Elab.Uebersetze.Folds.Expressions
public import Grammatik.Parser.Elab.Uebersetze.Folds.Expansion
public import Grammatik.Parser.Elab.Uebersetze.Folds.FloatLiterals
public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil3
public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil10
public import Grammatik.Parser.Elab.UebersetzeAllg3.Rest2a
public import NativeFloat.Primitives
import Grammatik.Parser.Elab.UebersetzePipeline
import all Grammatik.Parser.Lex.Lexer.Teil1
import all Grammatik.Parser.Elab.Uebersetze.Folds.Expressions
import all Grammatik.Parser.Elab.Uebersetze.Folds.Expansion
import all Grammatik.Parser.Elab.Uebersetze.Folds.FloatExpansion
import all Grammatik.Parser.Elab.Uebersetze.Folds.FloatLiterals
import all Grammatik.Parser.Elab.Uebersetze.Branches
import all Grammatik.Parser.Elab.Uebersetze.Loops.Headers
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
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
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
import all Init.Data.String.ToSlice
import all Init.Data.String.Defs
import all Init.Data.String.Basic
import all Init.Data.String.Extra
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Legacy
import all Init.Data.String.Termination

@[expose] public section
namespace Gabbro.Grammatik.Parser.Uebersetze.FloatFoldWitnesses
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2

set_option maxRecDepth 100000
set_option maxHeartbeats 800000

-- The compiler carries this exact bound; its large integer expansion is not a witness phase.
attribute [local cbv_opaque] uFloatLimit

def table : UTab :=
  {name := "T", count := 3, cols := [("v", (0, 0)), ("open", (0, 1))],
    bools := ["open"], werte := [("v", uFloatTy)]}

def context : UCtx :=
  {names := [], kinds := [], types := [], tabs := [table], locks := [], held := [],
    res := none, fname := "sample", alias := [], lits := []}

def value : SExpr := .field (.index (.variable "T") (.variable "k")) "v"

def operands (kind : XKind) : List SExpr :=
  [.variable "T", .tru, value] ++ (if kind == .foldAdd then [] else [.lit 0])

def expectedAdd : List UStmt :=
  [.floatLit "#fold:0:acc" (0, 1) (-uFloatLimit, 1) (uFloatLimit, 1),
    .loopBeg "k" "T" .tru, .ifBeg .tru,
    .bindW "#fold:0:value" none (.tab "T" "v" (.param "k")),
    .float "#fold:0:next" .add (.param "#fold:0:acc") (.param "#fold:0:value")
      (-uFloatLimit, 1) (uFloatLimit, 1),
    .setVar "#fold:0:acc" (.param "#fold:0:next"), .ifElse, .blkEnd, .blkEnd,
    .bindW "#fold:0:acc:result" (some uFloatTy) (.param "#fold:0:acc")]

/-- Both source spellings retain the existing formatless canonical float type. -/
public theorem f32_type_zeuge :
    uTyp [] [] (spaces := []) (eigner := []) (.atom "f32") = .ok uFloatTy := rfl
public theorem f64_type_zeuge :
    uTyp [] [] (spaces := []) (eigner := []) (.atom "f64") = .ok uFloatTy := rfl

/-- Certify the whole expansion once; later projections never re-run its readers. -/
private def resultContext (ctx : UCtx) : UCtx :=
  uMitLokal ctx "#fold:0:acc:result" .wert uFloatTy ctx.muts

private def domainContext (count : Int) : UCtx :=
  {context with tabs := [{table with count := count}]}

private def iteratorContext (count : Int) : UCtx :=
  {domainContext count with
    names := ["k"], kinds := [.index 0], types := [.index count],
    bits := [0], loops := ["k"]}

section DomainDispatch
attribute [local cbv_opaque] expandFloatFold

-- These certificates stop before the float-code producer, including for an empty domain.
private theorem domain_dispatch (kind : XKind) :
    expandFold context 0 kind ["k", "slots"] (operands kind) =
      expandFloatFold context (iteratorContext 3) 0 kind (.loopBeg "k" "T" .tru) .tru
        (foldPlaces 1000 value) (if kind == .foldAdd then [] else [.lit 0]) := by cbv <;> try simp only [bind_pure]

private theorem filtered_dispatch :
    expandFold context 0 .foldAdd ["k", "slots"]
      [.variable "T", .field (.index (.variable "T") (.variable "k")) "open", value] =
      expandFloatFold context (iteratorContext 3) 0 .foldAdd (.loopBeg "k" "T" .tru)
        (.tabB "T" "open" (.param "k")) (foldPlaces 1000 value) [] := by cbv <;> try simp only [bind_pure]

private theorem empty_dispatch :
    expandFold (domainContext 0) 0 .foldAdd ["k", "slots"] (operands .foldAdd) =
      expandFloatFold (domainContext 0) (iteratorContext 0) 0 .foldAdd
        (.loopBeg "k" "T" .tru) .tru (foldPlaces 1000 value) [] := by cbv <;> try simp only [bind_pure]
end DomainDispatch

private theorem float_leaf (count : Int) (stem : String) (serial : Nat) :
    foldFloatValue 1000 (iteratorContext count) stem serial (foldPlaces 1000 value) =
      .ok ([], serial, .tab "T" "v" (.param "k")) := by cbv

private theorem expanded_add :
    expandFold context 0 .foldAdd ["k", "slots"] (operands .foldAdd) =
      .ok (expectedAdd, resultContext context, .variable "#fold:0:acc:result") := by
  rw [domain_dispatch .foldAdd]
  simp only [expandFloatFold, foldName, float_leaf, bind, Except.bind, pure, Except.pure]
  cbv

/-- Three slots and a real float table read: one loop, left accumulator first,
    one native addition and one assignment per selected slot, starting at +0.0. -/
public theorem add_slot_order_zeuge :
    (expandFold context 0 .foldAdd ["k", "slots"] (operands .foldAdd)).toOption.map (·.1) =
      some expectedAdd := by
  rw [expanded_add]
  rfl

public theorem add_result_type_zeuge :
    (expandFold context 0 .foldAdd ["k", "slots"] (operands .foldAdd)).toOption.map
      (fun expanded => expanded.2.1.types.head?) = some (some uFloatTy) := by
  rw [expanded_add]
  rfl

public theorem filtered_add_slot_order_zeuge :
    (expandFold context 0 .foldAdd ["k", "slots"]
      [.variable "T", .field (.index (.variable "T") (.variable "k")) "open", value]).toOption.map
      (fun expanded => expanded.1[2]?) =
      some (some (.ifBeg (.tabB "T" "open" (.param "k")))) := by
  rw [filtered_dispatch]
  simp only [expandFloatFold, foldName, float_leaf, bind, Except.bind, pure, Except.pure]
  cbv

public theorem empty_add_still_initializes_positive_zero_zeuge :
    (expandFold {context with tabs := [{table with count := 0}]} 0 .foldAdd ["k", "slots"]
      (operands .foldAdd)).toOption.map (fun expanded => expanded.1.head?) =
      some (some (.floatLit "#fold:0:acc" (0, 1) (-uFloatLimit, 1) (uFloatLimit, 1))) := by
  change (expandFold (domainContext 0) 0 .foldAdd ["k", "slots"]
    (operands .foldAdd)).toOption.map (fun expanded => expanded.1.head?) = _
  rw [empty_dispatch]
  simp only [expandFloatFold, foldName, float_leaf, bind, Except.bind, pure, Except.pure]
  cbv

public theorem literal_rational_zeuge : uFloatRational "1.5e-3 rounded" = .ok (15, 10000) := by
  have text : "1.5e-3 rounded".toList =
      ['1', '.', '5', 'e', '-', '3', ' ', 'r', 'o', 'u', 'n', 'd', 'e', 'd'] := by cbv
  simp only [uFloatRational, text]
  cbv

def expectedExtremum (kind : XKind) : List UStmt :=
  [.floatLit "#fold:0:acc" (0, 1) (-uFloatLimit, 1) (uFloatLimit, 1),
    .floatLit "#fold:0:one" (1, 1) (-uFloatLimit, 1) (uFloatLimit, 1),
    .bindB "#fold:0:seen" .fls, .loopBeg "k" "T" .tru, .ifBeg .tru,
    .bindW "#fold:0:value" none (.tab "T" "v" (.param "k")),
    .ifBeg (.or (.not (.var "#fold:0:seen"))
      (.cmp (if kind == .foldMin then "<" else ">") (.param "#fold:0:value") (.param "#fold:0:acc"))),
    .float "#fold:0:next" .mul (.param "#fold:0:value") (.param "#fold:0:one")
      (-uFloatLimit, 1) (uFloatLimit, 1),
    .setVar "#fold:0:acc" (.param "#fold:0:next"), .setVarB "#fold:0:seen" .tru,
    .ifElse, .blkEnd, .ifElse, .blkEnd, .blkEnd,
    .ifBeg (.not (.var "#fold:0:seen")),
    .floatLit "#fold:0:empty:0" (0, 1) (-uFloatLimit, 1) (uFloatLimit, 1),
    .float "#fold:0:next" .mul (.param "#fold:0:empty:0") (.param "#fold:0:one")
      (-uFloatLimit, 1) (uFloatLimit, 1),
    .setVar "#fold:0:acc" (.param "#fold:0:next"), .ifElse, .blkEnd,
    .bindW "#fold:0:acc:result" (some uFloatTy) (.param "#fold:0:acc")]

private theorem expanded_min :
    expandFold context 0 .foldMin ["k", "slots"] (operands .foldMin) =
      .ok (expectedExtremum .foldMin, resultContext context, .variable "#fold:0:acc:result") := by
  rw [domain_dispatch .foldMin]
  simp only [expandFloatFold, foldName, float_leaf, bind, Except.bind, pure, Except.pure]
  cbv

private theorem expanded_max :
    expandFold context 0 .foldMax ["k", "slots"] (operands .foldMax) =
      .ok (expectedExtremum .foldMax, resultContext context, .variable "#fold:0:acc:result") := by
  rw [domain_dispatch .foldMax]
  simp only [expandFloatFold, foldName, float_leaf, bind, Except.bind, pure, Except.pure]
  cbv

public theorem min_order_and_empty_fallback_zeuge :
    (expandFold context 0 .foldMin ["k", "slots"] (operands .foldMin)).toOption.map (·.1) =
      some (expectedExtremum .foldMin) := by
  rw [expanded_min]
  rfl

public theorem max_order_and_empty_fallback_zeuge :
    (expandFold context 0 .foldMax ["k", "slots"] (operands .foldMax)).toOption.map (·.1) =
      some (expectedExtremum .foldMax) := by
  rw [expanded_max]
  rfl

attribute [local cbv_eval] expanded_add expanded_min expanded_max

/-- Exercise the connected generic G block lowering in a continuing branch. -/
def lowered (kind : XKind) : Bool :=
  match uAnwReihe [table] [] 1000 context
      [.cond .tru (.block [.bind false "total" none (.ext kind ["k", "slots"] (operands kind))] none)
        [] none] with
  | .error _ => false
  | .ok (body, _) =>
    let function : UFn := {
      name := "sample"
      params := []
      kinds := []
      res := none
      held := []
      puts := []
      gives := []
      body := body
      ret := .empty }
    (lowerAllg {tabs := [table], locks := [], fns := [function]}).toOption.isSome

/-- The exact continuing branch generated by the unchanged source statement. -/
private def continuingBody (kind : XKind) : List UStmt :=
  [.ifBeg .tru] ++ (if kind == .foldAdd then expectedAdd else expectedExtremum kind) ++
    [.bindW "total" (some uFloatTy) (.param "#fold:0:acc:result"), .ifElse, .blkEnd]

private def fixtureFunction (body : List UStmt) : UFn := {
  name := "sample"
  params := []
  kinds := []
  res := none
  held := []
  puts := []
  gives := []
  body := body
  ret := .empty }

private def fixtureUnit (body : List UStmt) : UProg :=
  {tabs := [table], locks := [], fns := [fixtureFunction body]}

private theorem source_continuing (kind : XKind)
    (numeric : kind = .foldAdd ∨ kind = .foldMin ∨ kind = .foldMax) :
    uAnwReihe [table] [] 1000 context
      [.cond .tru (.block [.bind false "total" none (.ext kind ["k", "slots"] (operands kind))] none)
        [] none] = .ok (continuingBody kind, context) := by
  rcases numeric with rfl | rfl | rfl <;> cbv

/-- Match the actual fuel before selecting one callback from the canonical record. -/
private theorem sequence_select {l : Bool} (unit : UProg) (caller : Fin unit.fns.length)
    (Γ : Ctx) (fn : UFn) (fuel : Nat) (Λ : List (Res (declOf unit)))
    (top : AtTop unit caller Λ) (statements : List UStmt) :
    lowSeqL (l := l) unit caller Γ fn fuel Λ top statements = match fuel with
      | 0 => .error "lower: blocks nested too deep"
      | n + 1 => lowSeqStep unit caller (lowStufe unit caller n) Γ fn Λ top statements := by
  cases fuel <;> rfl

private theorem structure_select {l : Bool} (unit : UProg) (caller : Fin unit.fns.length)
    (Γ : Ctx) (fn : UFn) (fuel : Nat) (Λ : List (Res (declOf unit)))
    (top : AtTop unit caller Λ) (statement : UStmt) (rest : List UStmt) :
    lowStructL (l := l) unit caller Γ fn fuel Λ top statement rest = match fuel with
      | 0 => .error "lower: blocks nested too deep"
      | n + 1 => lowStructStep unit caller (lowStufe unit caller n) Γ fn Λ top statement rest := by
  cases fuel <;> rfl

private theorem variable_head (Γ : Ctx) (ty : Ty) :
    lowVar (ty :: Γ) 0 ty = .ok (.here : Var (ty :: Γ) ty) := by
  unfold lowVar
  rw [dite_eq_left (rfl : ty = ty)]
  rfl

private theorem fit_same {unit : UProg} {Γ : Ctx} {Λ : List (Res (declOf unit))}
    (ty : Ty) (value : Expr (declOf unit) Γ Λ ty) : fitW ty ⟨ty, value⟩ = .ok value := by
  unfold fitW
  rw [dite_eq_left (rfl : ty = ty)]

attribute [local cbv_opaque] lowStufe lowSeqL lowStructL
attribute [local cbv_eval] sequence_select structure_select lowStufe_seq lowStufe_struct
  variable_head fit_same

/-- The certificate stops at the actual function-success constructor, before
    dependent program assembly or the source-measure gate is evaluated. -/
private theorem continuing_function (kind : XKind)
    (numeric : kind = .foldAdd ∨ kind = .foldMin ∨ kind = .foldMax) :
    (lowerFnAt (fixtureUnit (continuingBody kind)) ⟨0, by change 0 < 1; decide⟩).toOption.isSome = true := by
  rcases numeric with rfl | rfl | rfl <;> cbv

private theorem ending_function :
    (lowerFnAt (fixtureUnit expectedAdd) ⟨0, by change 0 < 1; decide⟩).toOption.isSome = true := by
  cbv

private theorem each_success (unit : UProg)
    (success : ∀ f : Fin unit.fns.length, (lowerFnAt unit f).toOption.isSome = true) :
    ∀ fs, lowerEach unit fs = .ok ()
  | [] => rfl
  | f :: fs => by
    rw [lowerEach, except_ok_get (ε := String)
      (α := EnsTy unit f × RumpTy unit f × ReqTy unit f) (x := lowerFnAt unit f) (success f)]
    exact each_success unit success fs

private theorem collect_success : ∀ (n : Nat) (T : Fin n → Type)
    (get : (i : Fin n) → Except String (T i)),
    (∀ i, (get i).toOption.isSome = true) →
      (Measures.collect n T get).toOption.isSome = true
  | 0, _, _, _ => rfl
  | n + 1, T, get, success => by
    have head := except_ok_get (ε := String) (α := T 0) (x := get 0) (success 0)
    have tail := collect_success n (fun i => T i.succ) (fun i => get i.succ) (fun i => success i.succ)
    have tailValue := except_ok_get (ε := String) (α := (i : Fin n) → T i.succ)
      (x := Measures.collect n (fun i => T i.succ) (fun i => get i.succ)) tail
    rw [Measures.collect, head]
    dsimp only [bind, Except.bind]
    rw [tailValue]
    rfl

/-- Preserve every actual assembly gate while keeping its typed program opaque. -/
private theorem lowering_phases (unit : UProg)
    (invariants : lowerInvs unit (List.finRange unit.invs.length) = .ok ())
    (functions : ∀ f : Fin unit.fns.length, (lowerFnAt unit f).toOption.isSome = true)
    (contracts : contractGate unit = true)
    (absent : ∀ f : Fin unit.fns.length, (fnAt unit f).decreases = none) :
    (lowerAllg unit).toOption.isSome = true := by
  have entries := collect_success unit.fns.length (Measures.At unit) (Measures.lowerAt unit)
    (fun f => by
      unfold Measures.lowerAt
      split
      · rfl
      · rename_i source selected
        rw [absent f] at selected
        cases selected)
  have collected := except_ok_get (ε := String)
    (α := (f : Fin unit.fns.length) → Measures.At unit f)
    (x := Measures.collect unit.fns.length (Measures.At unit) (Measures.lowerAt unit)) entries
  have measures : (Measures.lowerMeasures unit).toOption.isSome = true := by
    unfold Measures.lowerMeasures
    rw [collected]
    rfl
  let exported : Measures.Export unit := (Measures.lowerMeasures unit).toOption.get measures
  have measured : Measures.lowerMeasures unit = .ok exported := except_ok_get measures
  have checked (P : Programm (declOf unit)) :
      (Measures.checkedProgram unit P).toOption.isSome = true := by
    have lengths : Measures.cycleLengths unit P exported.mass = true := by
      unfold Measures.cycleLengths
      apply List.all_eq_true.mpr
      intro f _
      apply List.all_eq_true.mpr
      intro g _
      have empty (i : (declOf unit).Fn) : exported.mass i = [] :=
        Measures.lowerMeasures_absent unit exported i (absent i)
      rw [empty f, empty g]
      change (!zykS P (List.finRange unit.fns.length) f g || true) = true
      exact Bool.or_true _
    unfold Measures.checkedProgram
    rw [measured]
    dsimp only
    split
    · rfl
    · contradiction
  have allFunctions := each_success unit functions (List.finRange unit.fns.length)
  unfold lowerAllg
  split
  · rename_i error failed
    rw [invariants] at failed
    cases failed
  · split
    · rename_i error failed
      rw [allFunctions] at failed
      cases failed
    · split
      · exact checked _
      · contradiction

private theorem unit_success (body : List UStmt)
    (first : (lowerFnAt (fixtureUnit body) ⟨0, by change 0 < 1; decide⟩).toOption.isSome = true) :
    (lowerAllg (fixtureUnit body)).toOption.isSome = true := by
  have singleton (f : Fin (fixtureUnit body).fns.length) : f = ⟨0, by change 0 < 1; decide⟩ := by
    apply Fin.ext
    change f.val = 0
    have bound : f.val < 1 := f.isLt
    omega
  apply lowering_phases
  · rfl
  · intro f
    rw [singleton f]
    exact first
  · cbv
  · intro f
    rw [singleton f]
    rfl

private theorem continuing_lowered (kind : XKind)
    (numeric : kind = .foldAdd ∨ kind = .foldMin ∨ kind = .foldMax) : lowered kind = true := by
  unfold lowered
  rw [source_continuing kind numeric]
  exact unit_success (continuingBody kind) (continuing_function kind numeric)

public theorem add_continuing_lowering_zeuge : lowered .foldAdd = true :=
  continuing_lowered .foldAdd (Or.inl rfl)
public theorem min_continuing_lowering_zeuge : lowered .foldMin = true :=
  continuing_lowered .foldMin (Or.inr (Or.inl rfl))
public theorem max_continuing_lowering_zeuge : lowered .foldMax = true :=
  continuing_lowered .foldMax (Or.inr (Or.inr rfl))

/-- Float folds also lower in the final part of a function body. -/
public theorem top_level_endblock_lowering_zeuge :
    (lowerAllg {tabs := [table], locks := [], fns := [
      {name := "sample", params := [], kinds := [], res := none, held := [],
        puts := [], gives := [], body := expectedAdd, ret := .empty}]}).toOption.isSome = true :=
  unit_success expectedAdd ending_function

/-- Native unordered comparisons and signed-zero copies use the same primitives
    as ordinary expressions, without a separate extrema policy. -/
public theorem nan_unordered_zeuge
    (less_reply : Float.hwLt Float.nan (Float.hwOfInt 1) = false) :
    Float.hwLt Float.nan (Float.hwOfInt 1) = false := less_reply

public theorem copy_preserves_negative_zero_zeuge
    (multiply_reply : Float.hwMul (Float.hwOfBits 0x8000000000000000) (Float.hwOfInt 1) =
      Float.hwOfBits 0x8000000000000000) :
    Float.hwMul (Float.hwOfBits 0x8000000000000000) (Float.hwOfInt 1) =
      Float.hwOfBits 0x8000000000000000 := multiply_reply

end Gabbro.Grammatik.Parser.Uebersetze.FloatFoldWitnesses
