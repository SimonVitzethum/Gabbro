module

public import Grammatik.Niedrig.Authority.SimGSaetze
public import Grammatik.Logik.Fortschritt.KostenG.T1.Teil1a

@[expose] public section

namespace Gabbro.Grammatik.LowLevel.Construct

/-!
Pre-constructor semantics for the single G6 cascade. Append these fifteen
constructors at the ends of their existing inductives:
* Ty: addr, viewRef.
* Expr: addrLit, addrOff, narrowAddr, viewGet, arrSlice, strSlice.
* Stmt: viewPut.
* Block and Endblock: bindView, bindCtx, viewRead in each.

bindView carries the RAM/device class; viewGet/viewPut carry the declared
layout/field interpretation. Device reads need viewRead's returning/hardware
channels and cannot be pure expressions. viewRead has a strict/fallible mode,
so it does not need separate constructor names for the two modes. MMU, masks
and interrupt return reuse bindCtx. Firmware/IRQ entry uses entry metadata,
not a new executable constructor. System/Bindung and Klassen are the complete
pre-constructor semantics; Cascade records the final list for G6.

The functions below and in sibling modules consume already evaluated values.
G6 retains operand evaluation, its read tracing, and its scope/call guards.
Pointwise range checks must be lifted over the accepted expression ranges;
they do not authorize an unchecked expression or an escaping view value.

World has no owner ledger. Borrow/return remain the existing ghost protocol,
while writes use the existing G store and its trace. Concrete byte-to-cell
correspondence is a layout duty, not an equality of table indices and addresses.
Context checks consume static mark/stage and source binding data; the actual
Authority/Context and full (thread, activation) frames come from simulation.
Neither this package nor the imported replay claims a new admitted source form.
-/

/-- The same carrier names as Expr.orte; writes are kept separate for the
    future statement/effect walkers. Operand footprints are supplied by G6. -/
structure Footprint (D : Deklaration) where
  reads : List (D.Tab ⊕ D.Glob)
  writes : List (D.Tab ⊕ D.Glob)

def Footprint.empty {D : Deklaration} : Footprint D :=
  { reads := []
    writes := [] }

def Footprint.read {D : Deklaration} (table : D.Tab) : Footprint D :=
  { reads := [.inl table]
    writes := [] }

def Footprint.write {D : Deklaration} (table : D.Tab) : Footprint D :=
  { reads := []
    writes := [.inl table] }

def Footprint.append {D : Deklaration} (a b : Footprint D) : Footprint D :=
  { reads := a.reads ++ b.reads
    writes := a.writes ++ b.writes }

/-- Expression evaluation is pure in G. Its enclosing G step records reads
    with World.lese, using the separately supplied footprint. -/
structure ValueStep (D : Deklaration) (α : Type) where
  value : α
  world : World D

def valueStep {D : Deklaration} {α : Type} (value : α) (world : World D) : ValueStep D α :=
  { value := value
    world := world }

theorem valueStep_frame {D : Deklaration} {α : Type} (value : α) (world : World D)
    (writes : D.Tab → Bool) (globals : D.Glob → Bool) :
    Rahmen writes globals world (valueStep value world).world := Rahmen.refl _ _ _

theorem valueStep_deterministic {D : Deklaration} {α : Type}
    (value : α) (world : World D) {first second : ValueStep D α}
    (hfirst : valueStep value world = first) (hsecond : valueStep value world = second) :
    first = second := hfirst.symm.trans hsecond

theorem valueStep_sim {D : Deklaration} {P I α : Type} {a : Authority D}
    {c : Context D P I} {world : World D} (value : α) (simulation : SimRel a c world) :
    SimRel a c (valueStep value world).world := simulation

/-- Leaves count no expression work. Unary/binary operations and reads count
    one primitive, exactly as kostenExpr; a scope/call has separate overhead. -/
def literalCost : Nat := 0

def unaryCost (operand : Nat) : Nat := 1 + operand

def binaryCost (left right : Nat) : Nat := 1 + left + right

def sliceCost (base first last : Nat) : Nat := 1 + base + first + last

theorem unaryCost_bound (operand : Nat) : operand + 1 ≤ unaryCost operand := by
  unfold unaryCost
  omega

theorem binaryCost_bound (left right : Nat) : left + right + 1 ≤ binaryCost left right := by
  unfold binaryCost
  omega

theorem sliceCost_bound (base first last : Nat) :
    base + first + last + 1 ≤ sliceCost base first last := by
  unfold sliceCost
  omega

end Gabbro.Grammatik.LowLevel.Construct
