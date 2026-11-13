module

public import Grammatik.Niedrig.Konstrukte.Adresse

@[expose] public section

namespace Gabbro.Grammatik.LowLevel.Construct

variable {D : Deklaration}

/-- The canonical layout is the backing registry. Check both links: a table's
    declared nominal name and the nominal name of the selected backing. -/
def SpacePairing (span : Span D) (layout : AdressLayout D) : Prop :=
  D.tableSpace span.table = span.space.nominal ∧
  layout.raum span.table = span.space.backing ∧
  layout.nominal span.space.backing = span.space.nominal

instance (span : Span D) (layout : AdressLayout D) : Decidable (SpacePairing span layout) := by
  unfold SpacePairing
  infer_instance

/-- Checker-visible span and scope conditions, including the declaration's
    span-table lookup and nominal/backing pairing in the same premise set.
    No ghost Authority is a syntax field. Rights, alignment, class, mapping
    and epoch checks are retained. -/
def BindViewOk (span : Span D) (layout : AdressLayout D) (epoch start length borrower : Nat)
    (rights : DataRights) (frames : List Nat) : Prop :=
  span.Valid ∧ span.owner ∈ D.eigner span.table ∧ span.epoch = epoch ∧
  span.memoryClass = .ordinaryRam ∧ span.base ≤ start ∧
  start < span.base + span.length ∧ start + length ≤ span.base + span.length ∧
  (rights.read = true ∨ rights.write = true) ∧
  (rights.read = true → span.rights.read = true) ∧
  (rights.write = true → span.rights.write = true) ∧ rights.owner = span.rights.owner ∧
  start % span.alignment = 0 ∧ length % span.alignment = 0 ∧
  span.mapped = true ∧ span.initialized = true ∧ borrower ∉ frames ∧ SpacePairing span layout

instance (span : Span D) (layout : AdressLayout D) (epoch start length borrower : Nat)
    (rights : DataRights) (frames : List Nat) :
    Decidable (BindViewOk span layout epoch start length borrower rights frames) := by
  unfold BindViewOk
  infer_instance

def bindViewB (span : Span D) (layout : AdressLayout D) (epoch start length borrower : Nat)
    (rights : DataRights) (frames : List Nat) : Bool :=
  decide (BindViewOk span layout epoch start length borrower rights frames)

theorem bindViewB_iff (span : Span D) (layout : AdressLayout D) (epoch start length borrower : Nat)
    (rights : DataRights) (frames : List Nat) :
    bindViewB span layout epoch start length borrower rights frames = true ↔
      BindViewOk span layout epoch start length borrower rights frames := by
  simp only [bindViewB, decide_eq_true_eq]

/-- Nominal-to-carrier resolution uses capTab's NOMINAL index (not backing).
    The independent layout check below compares the backing identity. -/
def ViewAccessOk (view : View D) (resources : List (Res D)) : Prop :=
  D.capTab view.span.space.nominal view.span.number = some view.span.table ∧
  view.span.owner ∈ D.eigner view.span.table ∧ darf D view.span.table resources ∧
  view.span.memoryClass = .ordinaryRam

instance (view : View D) (resources : List (Res D)) :
    Decidable (ViewAccessOk view resources) := by
  unfold ViewAccessOk darf
  infer_instance

def viewAccessB (view : View D) (resources : List (Res D)) : Bool :=
  decide (ViewAccessOk view resources)

theorem viewAccessB_iff (view : View D) (resources : List (Res D)) :
    viewAccessB view resources = true ↔ ViewAccessOk view resources := by
  simp only [viewAccessB, decide_eq_true_eq]

/-- A finite, executable arithmetic check implies the ViewWrite.bytes duty.
    Index extent remains explicit, even for a zero-size layout field. -/
def ViewCellOk (view : View D) (layout : AdressLayout D) (index : Int)
    (field : D.Feld view.span.table) : Prop :=
  ImBereich D view.span.table index ∧ layout.raum view.span.table = view.span.space.backing ∧
  view.base ≤ layout.adresse view.span.table index field ∧
  layout.adresse view.span.table index field + layout.groesse view.span.table field ≤
    view.base + view.length ∧ SpacePairing view.span layout

instance (view : View D) (layout : AdressLayout D) (index : Int)
    (field : D.Feld view.span.table) : Decidable (ViewCellOk view layout index field) := by
  unfold ViewCellOk ImBereich
  infer_instance

def viewCellB (view : View D) (layout : AdressLayout D) (index : Int)
    (field : D.Feld view.span.table) : Bool := decide (ViewCellOk view layout index field)

theorem viewCellB_iff (view : View D) (layout : AdressLayout D) (index : Int)
    (field : D.Feld view.span.table) :
    viewCellB view layout index field = true ↔ ViewCellOk view layout index field := by
  simp only [viewCellB, decide_eq_true_eq]

theorem viewCell_confined {view : View D} {layout : AdressLayout D} {index : Int}
    {field : D.Feld view.span.table} (checked : ViewCellOk view layout index field)
    {byte : Adresse} (cell : layout.inZelle view.span.table index field byte) :
    view.Contains byte := by
  obtain ⟨_, backing, low, high, _⟩ := checked
  obtain ⟨identity, cellLow, cellHigh⟩ := cell
  exact ⟨identity.trans backing, by omega, by omega⟩

def ViewGetOk (view : View D) (layout : AdressLayout D)
    (field : D.Feld view.span.table) (index : Int) (length : Nat)
    (resources : List (Res D)) : Prop :=
  view.rights.read = true ∧ ViewAccessOk view resources ∧
  ∀ offset ∈ List.range length, ViewCellOk view layout (index + (offset : Int)) field

instance (view : View D) (layout : AdressLayout D)
    (field : D.Feld view.span.table) (index : Int) (length : Nat)
    (resources : List (Res D)) : Decidable (ViewGetOk view layout field index length resources) := by
  unfold ViewGetOk
  infer_instance

def viewGetB (view : View D) (layout : AdressLayout D)
    (field : D.Feld view.span.table) (index : Int) (length : Nat)
    (resources : List (Res D)) : Bool :=
  decide (ViewGetOk view layout field index length resources)

theorem viewGetB_iff (view : View D) (layout : AdressLayout D)
    (field : D.Feld view.span.table) (index : Int) (length : Nat)
    (resources : List (Res D)) :
    viewGetB view layout field index length resources = true ↔
      ViewGetOk view layout field index length resources := by
  simp only [viewGetB, decide_eq_true_eq]

def ViewPutOk (view : View D) (layout : AdressLayout D)
    (field : D.Feld view.span.table) (index : Int) (resources : List (Res D))
    (writes : D.Tab → Bool) : Prop :=
  writes view.span.table = true ∧ view.rights.write = true ∧
  ViewAccessOk view resources ∧ ViewCellOk view layout index field

instance (view : View D) (layout : AdressLayout D)
    (field : D.Feld view.span.table) (index : Int) (resources : List (Res D))
    (writes : D.Tab → Bool) : Decidable (ViewPutOk view layout field index resources writes) := by
  unfold ViewPutOk
  infer_instance

def viewPutB (view : View D) (layout : AdressLayout D)
    (field : D.Feld view.span.table) (index : Int) (resources : List (Res D))
    (writes : D.Tab → Bool) : Bool :=
  decide (ViewPutOk view layout field index resources writes)

theorem viewPutB_iff (view : View D) (layout : AdressLayout D)
    (field : D.Feld view.span.table) (index : Int) (resources : List (Res D))
    (writes : D.Tab → Bool) :
    viewPutB view layout field index resources writes = true ↔
      ViewPutOk view layout field index resources writes := by
  simp only [viewPutB, decide_eq_true_eq]

end Gabbro.Grammatik.LowLevel.Construct
