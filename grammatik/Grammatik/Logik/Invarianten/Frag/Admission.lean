module

public import Grammatik.Logik.Invarianten.Frag.Observation

@[expose] public section

namespace Gabbro.Grammatik.Invarianten.Frag

variable {D : Deklaration}

def located (part : String) : Except Refusal α → Except Refusal α
  | .ok value => .ok value
  | .error cause => .error (.within part cause)

/-- A source literal remains a literal under interval widening. In particular a
    bound index and a closed arithmetic expression are NOT literal coefficients. -/
def literalB : Expr D Γ Λ τ → Bool
  | .lit _ => true
  | .widen _ _ body => literalB body
  | _ => false

def boundIndexB : Expr D Γ Λ τ → Bool
  | .var .here => true
  | _ => false

def checkMemoryType : Ty → Except Refusal Unit
  | .int _ _ | .str _ => .ok ()
  | _ => .error (.unsupported "non-integer memory or string contents")

/-- A scalar record (count one) is available outside a slot binder. Otherwise a
    field must belong to the binder's table and use exactly that binder's index.
    No state-dependent indexing or second row can become an opaque QE variable. -/
def localSlotB (scope : Option D.Tab) (table : D.Tab)
    (index : Expr D Γ Λ (.index (D.count table))) : Bool :=
  decide (D.count table = 1) ||
    (scope == some table && boundIndexB index)

/-- Check the WHOLE syntax before expanding any bounded quantifier, including
    predicates over empty tables. Thus an empty domain cannot hide a nonlinear
    term, a nested binder, or an unsupported constructor. -/
def checkShape (scope : Option D.Tab) : Expr D Γ Λ τ → Except Refusal Unit
  | .lit _ | .tru | .fls | .var _ | .strLit _ _ => .ok ()
  | .glob name _ => checkMemoryType (D.gtyp name)
  | .slot table field index _ =>
      if localSlotB scope table index then do
        located "slot.index" (checkShape scope index)
        checkMemoryType (D.typ table field)
      else .error .crossEntry
  | .widen _ _ body => located "widen" (checkShape scope body)
  | .add left right | .sub left right | .lt left right | .le left right | .eq left right
  | .and left right | .or left right | .strCat left right => do
      located "left" (checkShape scope left)
      located "right" (checkShape scope right)
  | .neg body | .not body | .strLen body => located "operand" (checkShape scope body)
  | .mul left right =>
      if literalB left || literalB right then do
        located "mul.left" (checkShape scope left)
        located "mul.right" (checkShape scope right)
      else .error .nonlinear
  | .forallSlots table body _ =>
      if scope.isSome then .error .crossEntry
      else located "forallSlots.body" (checkShape (some table) body)
  | .existsSlots .. => .error (.unsupported "existsSlots: use a universal local slot predicate")
  | .oldG .. | .oldS .. => .error (.unsupported "old: invariants describe one world")
  | .fllt .. | .flle .. => .error (.unsupported "floating comparison")
  | .reaches .. => .error (.unsupported "reaches: maintain a linear counter instead")
  | .count .. => .error (.unsupported "count fold: maintain a scalar counter instead")
  | .thru .. | .thruOwn .. | .slotRef .. => .error (.unsupported "indirect field access")
  | .ptrOf .. | .fnref .. | .refEq .. => .error (.unsupported "capability expression")
  | .div .. | .rem .. | .sdiv .. | .srem .. => .error (.unsupported "division or remainder")
  | .getBytes .. => .error (.unsupported "byte extraction")
  | .band .. | .bor .. | .bxor .. | .shl .. | .shr .. => .error (.unsupported "bit operation")
  | .none .. | .some .. | .istSome .. | .case .. | .why .. =>
      .error (.unsupported "option, tagged value, or reason")
  | .arrNil .. | .arrCons .. | .arrGet .. | .arrSet .. =>
      .error (.unsupported "array value")
  | .strGet .. | .strEq .. | .strLt .. | .strWeit .. =>
      .error (.unsupported "string contents or truncation")
  | .wenn .. | .eng .. => .error (.unsupported "conditional value or narrowing")
  | .intBuiltin1 .. | .intBuiltin2 .. => .error (.unsupported "integer builtin")
  | .prod .. | .prodGet .. | .prodSet .. => .error (.unsupported "product value")

/-- Carrier admission precedes every arithmetic or locality check. -/
def checkCarriers (carriers : List (D.Tab ⊕ D.Glob)) (e : Expr D Γ Λ τ) :
    Except Refusal Unit :=
  if e.orte.all (fun carrier => decide (carrier ∈ carriers)) then
    if e.orte.any (fun carrier => match carrier with
        | .inl _ => false
        | .inr global => D.atomar global) then
      .error .atomicCarrier
    else .ok ()
  else .error .outsideCarriers

theorem checkCarriers_sound (carriers : List (D.Tab ⊕ D.Glob)) (e : Expr D Γ Λ τ)
    (success : checkCarriers carriers e = .ok ()) :
    ∀ carrier ∈ e.orte, carrier ∈ carriers := by
  unfold checkCarriers at success
  split at success
  next accepted =>
    intro carrier member
    exact of_decide_eq_true (List.all_eq_true.mp accepted carrier member)
  next => cases success

end Gabbro.Grammatik.Invarianten.Frag
