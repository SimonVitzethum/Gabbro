module

public import Grammatik.Kern.Syntax.Syntax.Teil2Expr

@[expose] public section

namespace Gabbro.Grammatik.Boundary

variable {D : Deklaration}

/-- Declaration refusals, corresponding to R1/R4/R5/R6 of the entry-check design.
    None of these is a machine outcome or a named environment assumption. -/
inductive Refusal where
  | unbounded
  | liveness
  | floatExact
  | prose
  deriving DecidableEq, Repr

/- The executable entry fragment. Quantification ranges over a declared finite
    table or a literal count; an open table never supplies a quantifier bound.
    No callback, claim string or unobservable device predicate is an expression.
    Native floating comparisons use the existing finite/range value model. -/
mutual

def fragmentB : Expr D Γ Λ τ → Bool
  | .lit _ | .tru | .fls | .var _ | .glob _ _ | .oldG _ _ => true
  | .slot _ _ i _ | .oldS _ _ i _ => fragmentB i
  | .thru p _ _ _ i _ => fragmentB p && fragmentB i
  | .thruOwn p _ _ _ i _ _ _ _ _ _ => fragmentB p && fragmentB i
  | .ptrOf .. | .fnref .. | .none _ | .why .. => true
  | .widen _ _ e | .neg e | .some e | .istSome e | .not e => fragmentB e
  | .add a b | .sub a b | .mul a b
  | .div _ _ a b | .rem _ _ a b | .sdiv _ a b | .srem _ a b
  | .band _ _ a b | .bor _ _ _ _ _ a b | .bxor _ _ _ _ _ a b
  | .shl _ _ _ _ _ a b | .shr _ _ _ _ _ a b
  | .lt a b | .le a b | .eq a b | .fllt a b | .flle a b
  | .and a b | .or a b | .refEq a b => fragmentB a && fragmentB b
  | .getBytes _ _ _ _ i _ _ _ => fragmentB i
  | .forallSlots t body _ | .existsSlots t body _ => !D.offen t && fragmentB body
  | .reaches t _ _ a b _ => !D.offen t && fragmentB a && fragmentB b
  | .slotRef r _ _ _ _ _ => fragmentB r
  | .arrNil | .strLit .. => true
  | .arrCons a rest => fragmentB a && fragmentB rest
  | .arrGet a i => fragmentB a && fragmentB i
  | .arrSet a i v => fragmentB a && fragmentB i && fragmentB v
  | .strLen s | .strWeit _ s => fragmentB s
  | .strCat s t | .strEq s t | .strLt s t => fragmentB s && fragmentB t
  | .strGet s i => fragmentB s && fragmentB i
  | .wenn c a b => fragmentB c && fragmentB a && fragmentB b
  | .eng e _ _ other => fragmentB e && fragmentB other
  | .intBuiltin1 _ a => fragmentB a
  | .intBuiltin2 _ a b => fragmentB a && fragmentB b
  | .count _ body => fragmentB body
  | .prodGet p _ => fragmentB p
  | .case _ _ payload => payloadFragmentB payload
  | .prod _ args => argsFragmentB args
  | .prodSet p _ e => fragmentB p && fragmentB e

def payloadFragmentB : NutzlastExpr D Γ Λ c → Bool
  | .empty => true
  | .val e => fragmentB e

def argsFragmentB : Args D Γ Λ ts → Bool
  | .nil => true
  | .cons e rest => fragmentB e && argsFragmentB rest

end

/-- A checked expression carries its syntactic admission, not a proof that it
    evaluates to true. False predicates are valid checks and take the error arm. -/
structure Check (D : Deklaration) (Γ : Ctx) (Λ : List (Res D)) where
  expression : Expr D Γ Λ .bool
  admitted : fragmentB expression = true

/-- A missing check contributes no predicate work at entry. -/
def Check.trivial : Check D Γ Λ where
  expression := .tru
  admitted := rfl

/-- Conjunctions of true clauses contain no runtime check. This recognizes only
    syntax, without trying to decide general semantic tautologies. -/
def requiredB : Expr D Γ Λ .bool → Bool
  | .tru => false
  | .and left right => requiredB left || requiredB right
  | _ => true

def Check.requiredB (c : Check D Γ Λ) : Bool := Boundary.requiredB c.expression

/-- Admission of a call site: executable checks require its declared error arm.
    The error code itself is supplied by that declaration, never invented here. -/
def callB (c : Check D Γ Λ) (hasErrorArm : Bool) : Bool :=
  !c.requiredB || hasErrorArm

theorem callB_without_arm (c : Check D Γ Λ) (h : c.requiredB = true) :
    callB c false = false := by
  simp only [callB, h, Bool.not_true, Bool.false_or]

theorem callB_with_arm (c : Check D Γ Λ) : callB c true = true := by
  simp only [callB, Bool.or_true]

end Gabbro.Grammatik.Boundary
