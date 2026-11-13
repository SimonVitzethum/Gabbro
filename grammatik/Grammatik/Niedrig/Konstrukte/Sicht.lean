module

public import Grammatik.Niedrig.Konstrukte.SichtTypen

@[expose] public section

namespace Gabbro.Grammatik.LowLevel.Construct

variable {D : Deklaration}

/-- Exactly getBytes' projection and result type, including its byte order.
    Authorization is ViewGetOk plus G6's range/liveness lifting; the simulation
    lemma below establishes preservation only. Device views use mmioReadStep.
    G6 supplies a live view variable and lifts the local check over index ranges.
    This pure expression does not itself record the enclosing step's reads. -/
def viewGetStep (view : View D) (layout : AdressLayout D)
    (field : D.Feld view.span.table) (byteField : D.typ view.span.table field = .int 0 255)
    (index : Int) (length : Nat) (resources : List (Res D))
    (_checked : ViewGetOk view layout field index length resources) (world : World D) :
    ValueStep D (Zahl 0 (256 ^ length - 1)) :=
  let bytes := world.bytesAb view.span.table field byteField length index
  valueStep
    ⟨bytesZuZahl bytes, (bytesZuZahl_bereich bytes).1, by
      have bound := (bytesZuZahl_bereich bytes).2
      rw [World.bytesAb_length] at bound
      exact bound⟩ world

theorem viewGetStep_value (view : View D) (layout : AdressLayout D)
    (field : D.Feld view.span.table) (byteField : D.typ view.span.table field = .int 0 255)
    (index : Int) (length : Nat) (resources : List (Res D))
    (checked : ViewGetOk view layout field index length resources) (world : World D) :
    (viewGetStep view layout field byteField index length resources checked world).value.n =
      bytesZuZahl (world.bytesAb view.span.table field byteField length index) := rfl

theorem viewGetStep_frame (view : View D) (layout : AdressLayout D)
    (field : D.Feld view.span.table) (byteField : D.typ view.span.table field = .int 0 255)
    (index : Int) (length : Nat) (resources : List (Res D))
    (checked : ViewGetOk view layout field index length resources) (world : World D) :
    (viewGetStep view layout field byteField index length resources checked world).world = world := rfl

theorem viewGetStep_confined {view : View D} {layout : AdressLayout D}
    {field : D.Feld view.span.table} {index : Int} {length : Nat} {resources : List (Res D)}
    (checked : ViewGetOk view layout field index length resources)
    (offset : Nat) (member : offset ∈ List.range length) {byte : Adresse}
    (cell : layout.inZelle view.span.table (index + (offset : Int)) field byte) :
    view.Contains byte := viewCell_confined (checked.2.2 offset member) cell

/-- The sole write path is the existing typed carrier store WITH its trace
    event. Byte-level constructors choose integer fields; L3 owns typed views. -/
def viewPutStep (view : View D) (layout : AdressLayout D)
    (field : D.Feld view.span.table) (index : Int) (value : Wert D (D.typ view.span.table field))
    (resources : List (Res D)) (writes : D.Tab → Bool)
    (_checked : ViewPutOk view layout field index resources writes) (world : World D) : World D :=
  world.schreibSlot view.span.table resources index field value

/-- Construct the precise receipt needed by the existing simulation from the
    static arithmetic check and the dynamic live/active/valid invariant. -/
def viewPutReceipt {P I : Type} {a : Authority D} {c : Context D P I}
    (view : View D) (layout : AdressLayout D) (field : D.Feld view.span.table)
    (index : Int) (value : Wert D (D.typ view.span.table field))
    (resources : List (Res D)) (writes : D.Tab → Bool)
    (checked : ViewPutOk view layout field index resources writes) (world : World D)
    (valid : c.Valid a) (live : view ∈ c.views) (active : c.frame = view.borrower) :
    ViewWrite a c layout world (world.storeSlot view.span.table index field value) :=
  { view := view
    live := live
    active := active
    valid := valid
    writable := checked.2.1
    index := index
    field := field
    extent := checked.2.2.2.1
    bytes := fun _ cell => viewCell_confined checked.2.2.2 cell
    value := value
    store := rfl }

theorem viewPutStep_frame (view : View D) (layout : AdressLayout D)
    (field : D.Feld view.span.table) (index : Int) (value : Wert D (D.typ view.span.table field))
    (resources : List (Res D)) (writes : D.Tab → Bool)
    (checked : ViewPutOk view layout field index resources writes) (world : World D)
    (globals : D.Glob → Bool) :
    Rahmen writes globals world (viewPutStep view layout field index value resources writes checked world) :=
  rahmen_storeSlot writes globals world view.span.table index field value checked.1

theorem viewPutStep_other (view : View D) (layout : AdressLayout D)
    (field : D.Feld view.span.table) (index : Int) (value : Wert D (D.typ view.span.table field))
    (resources : List (Res D)) (writes : D.Tab → Bool)
    (checked : ViewPutOk view layout field index resources writes) (world : World D)
    (table : D.Tab) (different : table ≠ view.span.table) (otherIndex : Int) (otherField : D.Feld table) :
    (viewPutStep view layout field index value resources writes checked world).slots table otherIndex otherField =
      world.slots table otherIndex otherField :=
  storeSlot_andere world view.span.table index field value table different otherIndex otherField

theorem viewPutStep_trace (view : View D) (layout : AdressLayout D)
    (field : D.Feld view.span.table) (index : Int) (value : Wert D (D.typ view.span.table field))
    (resources : List (Res D)) (writes : D.Tab → Bool)
    (checked : ViewPutOk view layout field index resources writes) (world : World D) :
    (viewPutStep view layout field index value resources writes checked world).spur =
      .zugriff view.span.table true resources world.haelt :: world.spur := rfl

theorem viewPutStep_gut (view : View D) (layout : AdressLayout D)
    (field : D.Feld view.span.table) (index : Int) (value : Wert D (D.typ view.span.table field))
    (resources : List (Res D)) (writes : D.Tab → Bool)
    (checked : ViewPutOk view layout field index resources writes) (world : World D)
    (globals : D.Glob → Bool) (held : HeldIn resources world.haelt) :
    Gut writes globals world (viewPutStep view layout field index value resources writes checked world) :=
  gut_schreibSlot world view.span.table resources index field value
    checked.1 checked.2.2.1.2.2.1 held

theorem viewPutStep_sim {P I : Type} {a : Authority D} {c : Context D P I}
    (view : View D) (layout : AdressLayout D) (field : D.Feld view.span.table)
    (index : Int) (value : Wert D (D.typ view.span.table field))
    (resources : List (Res D)) (writes : D.Tab → Bool)
    (checked : ViewPutOk view layout field index resources writes) (world : World D)
    (simulation : SimRel a c world) (correct : LayoutOk layout) (realizes : a.Realizes layout)
    (live : view ∈ c.views) (active : c.frame = view.borrower) (held : HeldIn resources world.haelt) :
    SimRel a c (viewPutStep view layout field index value resources writes checked world) :=
  viewwrite_sim simulation correct realizes
    (viewPutReceipt view layout field index value resources writes checked world simulation.valid live active)
    resources checked.2.2.1.2.2.1 held

theorem viewGetStep_sim {P I : Type} {a : Authority D} {c : Context D P I}
    (view : View D) (layout : AdressLayout D)
    (field : D.Feld view.span.table) (byteField : D.typ view.span.table field = .int 0 255)
    (index : Int) (length : Nat) (resources : List (Res D))
    (checked : ViewGetOk view layout field index length resources) (world : World D)
    (simulation : SimRel a c world) (live : view ∈ c.views) (active : c.frame = view.borrower) :
    SimRel a c (viewGetStep view layout field byteField index length resources checked world).world ∧
      view.Valid a ∧ c.frame = view.borrower :=
  ⟨simulation, simulation.valid.2.2.2.1 view live, active⟩

def viewGetFootprint (view : View D) (index : Footprint D) : Footprint D :=
  (Footprint.read view.span.table).append index

def viewPutFootprint (view : View D) (index value : Footprint D) : Footprint D :=
  (index.append value).append (Footprint.write view.span.table)

theorem viewGetFootprint_reads (view : View D) (index : Footprint D) :
    (viewGetFootprint view index).reads = .inl view.span.table :: index.reads := rfl

theorem viewGetFootprint_writes (view : View D) (index : Footprint D) :
    (viewGetFootprint view index).writes = index.writes := rfl

theorem viewPutFootprint_reads (view : View D) (index value : Footprint D) :
    (viewPutFootprint view index value).reads = index.reads ++ value.reads := by
  simp only [viewPutFootprint, Footprint.append, Footprint.write, List.append_nil]

theorem viewPutFootprint_writes (view : View D) (index value : Footprint D) :
    (viewPutFootprint view index value).writes =
      (index.writes ++ value.writes) ++ [.inl view.span.table] := rfl

/-- With a bound view variable (cost zero), these are exactly getBytes and
    assignSlot costs, including all evaluated operand work. -/
def viewGetCost (index : Nat) : Nat := unaryCost index

def viewPutCost (index value : Nat) : Nat := binaryCost index value

theorem viewPutCost_bound (index value : Nat) : 1 ≤ viewPutCost index value := by
  unfold viewPutCost binaryCost
  omega

end Gabbro.Grammatik.LowLevel.Construct
