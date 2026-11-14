module

public import Grammatik.Niedrig.Konstrukte.Klassen.Simulation

@[expose] public section

namespace Gabbro.Grammatik.LowLevel.Construct

variable {D : Deklaration}

/-- Fields are the EXISTING declared table layout, with an explicit finite
    enumeration certificate. Records and arrays use one interpretation. No
    bit-pattern is coerced to a reference and no new address is manufactured. -/
structure ViewLayout (table : D.Tab) where
  fields : List (D.Feld table)
  complete : ∀ field, field ∈ fields

def TypedViewOk (view : View D) (layout : AdressLayout D)
    (record : ViewLayout view.span.table) (base : Int) (count : Nat)
    (resources : List (Res D)) : Prop :=
  view.rights.read = true ∧
  ViewAccessOk view resources ∧
  ∀ offset ∈ List.range count, ∀ field ∈ record.fields,
    ViewCellOk view layout (base + (offset : Int)) field

instance (view : View D) (layout : AdressLayout D) (record : ViewLayout view.span.table)
    (base : Int) (count : Nat) (resources : List (Res D)) :
    Decidable (TypedViewOk view layout record base count resources) := by
  unfold TypedViewOk
  infer_instance

def typedViewB (view : View D) (layout : AdressLayout D) (record : ViewLayout view.span.table)
    (base : Int) (count : Nat) (resources : List (Res D)) : Bool :=
  decide (TypedViewOk view layout record base count resources)

theorem typedViewB_iff (view : View D) (layout : AdressLayout D)
    (record : ViewLayout view.span.table) (base : Int) (count : Nat) (resources : List (Res D)) :
    typedViewB view layout record base count resources = true ↔
      TypedViewOk view layout record base count resources := by
  simp only [typedViewB, decide_eq_true_eq]

/-- A record is count=1; an array is an indexed family of those records.
    Endianness is already interpreted by the canonical typed store. Raw bytes
    require a separate representation proof before this interface is usable. -/
def typedViewGetStep (view : View D) (layout : AdressLayout D)
    (record : ViewLayout view.span.table) (base : Int) (count : Nat)
    (resources : List (Res D)) (_checked : TypedViewOk view layout record base count resources)
    (world : World D) :
    ValueStep D (Fin count → (field : D.Feld view.span.table) → Wert D (D.typ view.span.table field)) :=
  valueStep (fun offset field => world.slots view.span.table (base + (offset.val : Int)) field) world

theorem typedViewGetStep_field (view : View D) (layout : AdressLayout D)
    (record : ViewLayout view.span.table) (base : Int) (count : Nat)
    (resources : List (Res D)) (checked : TypedViewOk view layout record base count resources)
    (world : World D) (offset : Fin count) (field : D.Feld view.span.table) :
    (typedViewGetStep view layout record base count resources checked world).value offset field =
      world.slots view.span.table (base + (offset.val : Int)) field := rfl

theorem typedViewGetStep_confined {view : View D} {layout : AdressLayout D}
    {record : ViewLayout view.span.table} {base : Int} {count : Nat} {resources : List (Res D)}
    (checked : TypedViewOk view layout record base count resources) (offset : Fin count)
    (field : D.Feld view.span.table) {byte : Adresse}
    (cell : layout.inZelle view.span.table (base + (offset.val : Int)) field byte) : view.Contains byte :=
  viewCell_confined (checked.2.2 offset.val (List.mem_range.mpr offset.isLt)
    field (record.complete field)) cell

theorem typedViewGetStep_sim {P I : Type} {a : Authority D} {c : Context D P I}
    {view : View D} {layout : AdressLayout D} {record : ViewLayout view.span.table}
    {base : Int} {count : Nat} {resources : List (Res D)} {world : World D}
    (checked : TypedViewOk view layout record base count resources)
    (simulation : ClassSimRel a layout c world) :
    ClassSimRel a layout c (typedViewGetStep view layout record base count resources checked world).world :=
  simulation

/-- Typed field writes use viewPutStep and ViewPutOk directly. Aggregate
    construction uses the existing product/array constructors. This footprint
    covers field reads only; G6 adds operand and construction work. -/
def typedViewFootprint (view : View D) (operands : Footprint D) : Footprint D :=
  viewGetFootprint view operands

/-- Sum of field-read primitives only. The enclosing existing product/array
    constructors retain their own costs; this is not their total budget. -/
def typedViewCost (count fields operands : Nat) : Nat := count * fields + operands

end Gabbro.Grammatik.LowLevel.Construct
