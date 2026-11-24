module

public import Core.Ast.Semantik.Runtime.ExpressionValues
public import Core.Ast.Semantik.Runtime.ValueCoercion
import Init.Data.Vector.OfFn

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

namespace ExpressionAggregates

variable {scope : Scope} {env : Umgebung scope} {slot : Nat}

/-- A tuple of source values appears in consecutive temporaries in source order. -/
def TupleTemps (slot : Nat) (types : List (Ty .value)) (values : Wert (tupleType types))
    (frame : Rahmen) : Prop :=
  ∀ i : Fin types.length, TemporaryValue (slot + i.val) (tupleGet types i values) frame

theorem TupleTemps.cons {frame : Rahmen} {value : Wert type} {values : Wert (tupleType types)}
    (head : TemporaryValue slot value frame) (tail : TupleTemps (slot + 1) types values frame) :
    TupleTemps slot (type :: types) (value, values) frame := by
  intro i
  rcases i with ⟨i, bounded⟩
  cases i with
  | zero => exact head
  | succ n =>
    have index : n < types.length := Nat.lt_of_succ_lt_succ bounded
    have shifted : slot + n.succ = slot + 1 + n := by omega
    change TemporaryValue (slot + n.succ) (tupleGet types ⟨n, index⟩ values) frame
    rw [shifted]
    exact tail ⟨n, index⟩

theorem itemsNil : BewachterAusdruck env slot (itemCode slot (ExprItems.empty (scope := scope))).code
    (fun _ => True) (TupleTemps slot [] PUnit.unit) :=
  .leer (fun _ _ i => Fin.elim0 i)

theorem itemsCons {items : ExprItems scope types}
    (first : Ausdruckswert env slot head)
    (remaining : BewachterAusdruck env (slot + 1) (itemCode (slot + 1) items).code
      (fun _ => True) (TupleTemps (slot + 1) types (items.wert env))) :
    BewachterAusdruck env slot (itemCode slot (.next head items)).code (fun _ => True)
      (TupleTemps slot (_ :: types) ((ExprItems.next head items).wert env)) := by
  refine .anhaengen first (remaining.eingang (fun _ _ => trivial)) (Nat.le_succ _) ?_
  intro mid frame prior tail preserve
  exact .cons ((preserve slot (Nat.lt_succ_self _)).trans prior) tail

theorem labeledNil : BewachterAusdruck env slot (labeledCode slot (LabeledItems.empty (scope := scope))).code
    (fun _ => True) (TupleTemps slot [] PUnit.unit) :=
  .leer (fun _ _ i => Fin.elim0 i)

theorem labeledCons {items : LabeledItems scope labels types} (label : Identifier)
    (first : Ausdruckswert env slot head)
    (remaining : BewachterAusdruck env (slot + 1) (labeledCode (slot + 1) items).code
      (fun _ => True) (TupleTemps (slot + 1) types (items.wert env))) :
    BewachterAusdruck env slot (labeledCode slot (.next label head items)).code (fun _ => True)
      (TupleTemps slot (_ :: types) ((LabeledItems.next label head items).wert env)) := by
  refine .anhaengen first (remaining.eingang (fun _ _ => trivial)) (Nat.le_succ _) ?_
  intro mid frame prior tail preserve
  exact .cons ((preserve slot (Nat.lt_succ_self _)).trans prior) tail

private theorem readTuple {frame : Rahmen} {values : Wert (tupleType types)}
    (placed : TupleTemps slot types values frame) :
    liesTupel frame.temp slot types = some values := by
  induction types generalizing slot with
  | nil =>
    cases values
    rfl
  | cons type tail ih =>
    rcases values with ⟨head, rest⟩
    have first : frame.temp slot = some ⟨type, head⟩ := placed 0
    have restPlaced : TupleTemps (slot + 1) tail rest frame := by
      intro i
      have h := placed i.succ
      change TemporaryValue (slot + i.val.succ) (tupleGet tail i rest) frame at h
      have shifted : slot + i.val.succ = slot + 1 + i.val := by omega
      simpa only [shifted] using h
    have next := ih restPlaced
    simp only [liesTupel, first, Option.bind_some, wertAls_selbst head, next, bind, Option.bind, pure]

private theorem readRecord (frame : Rahmen) (types : List (Ty .value)) (slots : Fin types.length → Nat)
    (values : (i : Fin types.length) → Wert (types.get i))
    (placed : ∀ i, (frame.temp (slots i)).bind (wertAls (types.get i)) = some (values i)) :
    liesRecord frame.temp types (List.ofFn slots) = some (tupleOfFn types values) := by
  induction types with
  | nil => rfl
  | cons type tail ih =>
    have next := ih (fun i => slots i.succ) (fun i => values i.succ) (fun i => placed i.succ)
    have head : (frame.temp (slots 0)).bind (wertAls type) = some (values 0) := placed 0
    simp only [List.ofFn_succ, liesRecord, tupleOfFn]
    rw [head, next]
    rfl

theorem arrayValue {items : ExprItems scope types} (principal : arrayElement types = some element)
    (fits : ∀ i : Fin types.length, Fits (types.get i) element)
    (read : BewachterAusdruck env slot (itemCode slot items).code (fun _ => True)
      (TupleTemps slot types (items.wert env))) : Ausdruckswert env slot (.arrayValue items principal fits) := by
  refine BewachterAusdruck.anhaengen read
    (BewachterAusdruck.wert ((Expr.arrayValue items principal fits).wert env) ?_)
    (Nat.le_refl _) (fun _ _ _ found _ => found)
  intro pre post frame position active typed checked placed
  let values := items.wert env
  let widened (i : Fin types.length) :=
    Wert.widen (types.get i) element (fits i) (tupleGet types i values)
  have allRead : (fun i : Fin types.length => (frame.temp (slot + i.val)).bind (wertAls element)) =
      fun i => some (widened i) := by
    funext i
    have known := placed i
    simp only [TemporaryValue] at known
    rw [known, Option.bind_some, wertAls_widen _ _ (fits i)]
  have arrayRead : Vector.ofFnM
      (fun i : Fin types.length => (frame.temp (slot + i.val)).bind (wertAls element)) =
      some (Vector.ofFn widened) := by
    rw [allRead]
    exact Vector.ofFnM_pure
  simp only [Befehl.auswerten, Expr.wert]
  rw [arrayRead]
  rfl

theorem arrayIndex {count : Nat} {lo hi : Int} {array : Expr scope (.array element count)}
    {subscript : Expr scope (.int lo hi)} (lower : 0 ≤ lo) (upper : hi < (count : Int))
    (base : Ausdruckswert env slot array)
    (index : Ausdruckswert env (slot + 1) subscript) :
    Ausdruckswert env slot (Expr.arrayIndex (count := count) (lo := lo) (hi := hi) array subscript lower upper) := by
  refine .zweiOperandenWert base index ((Expr.arrayIndex (count := count) (lo := lo) (hi := hi) array subscript lower upper).wert env) ?_
  intro pre post frame position active typed checked found
  rcases found with ⟨baseValue, indexValue⟩
  simp only [TemporaryValue] at baseValue indexValue
  have nonnegative : ¬ (subscript.wert env).wert < 0 :=
    Int.not_lt_of_ge (Int.le_trans lower (subscript.wert env).unten)
  let index := indexPosition (subscript.wert env) lower upper
  have inside : (subscript.wert env).wert.toNat < count := index.isLt
  simp only [Befehl.auswerten, Rahmen.zahl, baseValue, indexValue, Option.bind_some,
    wertAls_selbst (array.wert env), alsGanzzahl, if_neg nonnegative, dif_pos inside,
    Expr.wert, indexPosition, bind, Option.bind, pure]

theorem tupleValue {items : ExprItems scope types}
    (first : Ausdruckswert env slot a) (second : Ausdruckswert env (slot + 1) b)
    (tail : BewachterAusdruck env (slot + 2) (itemCode (slot + 2) items).code (fun _ => True)
      (TupleTemps (slot + 2) types (items.wert env))) : Ausdruckswert env slot (.tupleValue a b items) := by
  have placed : BewachterAusdruck env slot
      (((expr slot a).code ++ (expr (slot + 1) b).code) ++ (itemCode (slot + 2) items).code)
      (fun _ => True) (TupleTemps slot (_ :: _ :: types) ((Expr.tupleValue a b items).wert env)) := by
    refine .anhaengen (.zweiOperanden first second) (tail.eingang (fun _ _ => trivial)) (by omega) ?_
    intro previous after operands suffix keep
    refine .cons ((keep slot (by omega)).trans operands.1) ?_
    exact .cons ((keep (slot + 1) (by omega)).trans operands.2) suffix
  refine .anhaengen placed (.wert ((Expr.tupleValue a b items).wert env) ?_)
    (Nat.le_refl _) (fun _ _ _ found _ => found)
  intro pre post frame position active typed checked ready
  simp only [Befehl.auswerten, readTuple ready, Option.map_some]

theorem tupleField (read : Ausdruckswert env slot (base : Expr scope (tupleType (first :: second :: types))))
    (index : Fin (first :: second :: types).length) : Ausdruckswert env slot (.tupleField base index) := by
  refine .einOperand read ((Expr.tupleField base index).wert env) ?_
  intro pre post frame position active typed checked ready
  simp only [TemporaryValue] at ready
  simp only [Befehl.auswerten, ready, Option.bind_some, wertAls_selbst (base.wert env), Expr.wert,
    bind, Option.bind, pure]

theorem recordValue (ref : RecordRef scope labels types) (args : LabeledItems scope actualLabels actualTypes)
    (fields : RecordArguments labels types actualLabels actualTypes)
    (fits : ∀ i, Fits (actualTypes.get (fields.slot i)) (types.get i))
    (read : BewachterAusdruck env slot (labeledCode slot args).code (fun _ => True)
      (TupleTemps slot actualTypes (args.wert env))) : Ausdruckswert env slot (.recordValue ref args fields fits) := by
  refine .anhaengen read (.wert ((Expr.recordValue ref args fields fits).wert env) ?_)
    (Nat.le_refl _) (fun _ _ _ found _ => found)
  intro pre post frame position active typed checked ready
  let values := args.wert env
  let sources (i : Fin types.length) := slot + (fields.slot i).val
  let widened (i : Fin types.length) :=
    Wert.widen (actualTypes.get (fields.slot i)) (types.get i) (fits i) (tupleGet actualTypes (fields.slot i) values)
  have placed : ∀ i, (frame.temp (sources i)).bind (wertAls (types.get i)) = some (widened i) := by
    intro i
    have actual := ready (fields.slot i)
    simp only [TemporaryValue] at actual
    simp only [sources, actual, Option.bind_some, widened, values, wertAls_widen _ _ (fits i)]
  simp only [Befehl.auswerten, readRecord frame types sources widened placed,
    Option.map_some, Expr.wert, widened, values, sources] <;> rfl

theorem recordField (read : Ausdruckswert env slot (base : Expr scope (recordValueType name labels types)))
    (field : Identifier) (index : Fin types.length) (written : RecordFieldAt labels field index.val) :
    Ausdruckswert env slot (.recordField base field index written) := by
  refine .einOperand read ((Expr.recordField base field index written).wert env) ?_
  intro pre post frame position active typed checked ready
  simp only [TemporaryValue] at ready
  simp only [Befehl.auswerten, ready, Option.bind_some, wertAls_selbst (base.wert env), Expr.wert,
    bind, Option.bind, pure]

def CaseTemp (slot : Nat) {type : Option (Ty .value)} (value : Wert (type.getD .productEnd))
    (frame : Rahmen) : Prop :=
  variantActual type (frame.temp slot) = some value

theorem caseNullary (parens : Bool) :
    BewachterAusdruck env slot (caseCode slot (CasePayload.nullary (scope := scope) parens)).code
      (fun _ => True) (CaseTemp (type := none) slot PUnit.unit) :=
  .leer (fun _ _ => rfl)

theorem caseValue (read : Ausdruckswert env slot value) :
    BewachterAusdruck env slot (caseCode slot (.value value)).code
      (fun _ => True) (CaseTemp (type := some _) slot (value.wert env)) := by
  intro pre post before position active typed checked input
  obtain ⟨after, trace, known⟩ := read pre post before position active typed checked input
  refine ⟨after, trace, ?_⟩
  simp only [TemporaryValue] at known
  simp only [CaseTemp, variantActual, known, Option.bind_some]
  exact wertAls_selbst (value.wert env)

theorem variantValue (ref : VariantRef scope labels payloads) (label : Identifier)
    (index : Fin payloads.length) (written : labels[index.val]? = some label)
    (ordinary : ordinaryLocal label) (available : availableCase scope label)
    (payload : CasePayload scope (payloads.get index))
    (read : BewachterAusdruck env slot (caseCode slot payload).code (fun _ => True)
      (CaseTemp (type := payloads.get index) slot (payload.wert env))) :
    Ausdruckswert env slot (.variantValue ref label index written ordinary available payload) := by
  refine .anhaengen read (.wert ((Expr.variantValue ref label index written ordinary available payload).wert env) ?_)
    (Nat.le_refl _) (fun _ _ _ found _ => found)
  intro pre post frame position active typed checked ready
  simp only [CaseTemp] at ready
  simp only [Befehl.auswerten, ready, Expr.wert, bind, Option.bind, pure]

end ExpressionAggregates

end Gabbro.Core.Ast.Semantik
