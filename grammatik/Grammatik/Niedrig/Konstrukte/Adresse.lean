module

public import Grammatik.Niedrig.Konstrukte.Basis

@[expose] public section

namespace Gabbro.Grammatik.LowLevel.Construct

variable {D : Deklaration}

/-- Raw type indices can be checked before constructing Space. The width
    registry is an argument until G1 adds its defaulted declaration field. -/
def AddrTypeOk (widths : Nat → Nat) (nominal width kind : Nat) : Prop :=
  nominal < D.dataSpaces.length ∧ 0 < width ∧ width ≤ widths nominal ∧ kind ≤ 1

instance (widths : Nat → Nat) (nominal width kind : Nat) :
    Decidable (AddrTypeOk (D := D) widths nominal width kind) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

def addrTypeB (widths : Nat → Nat) (nominal width kind : Nat) : Bool :=
  decide (AddrTypeOk (D := D) widths nominal width kind)

theorem addrTypeB_iff (widths : Nat → Nat) (nominal width kind : Nat) :
    addrTypeB (D := D) widths nominal width kind = true ↔
      AddrTypeOk (D := D) widths nominal width kind := by
  simp only [addrTypeB, decide_eq_true_eq]

def AddrRange (width : Nat) (value : Int) : Prop :=
  0 ≤ value ∧ value ≤ (2 : Int) ^ width - 1

instance (width : Nat) (value : Int) : Decidable (AddrRange width value) :=
  inferInstanceAs (Decidable (_ ∧ _))

def addrRangeB (width : Nat) (value : Int) : Bool := decide (AddrRange width value)

theorem addrRangeB_iff (width : Nat) (value : Int) :
    addrRangeB width value = true ↔ AddrRange width value := by
  simp only [addrRangeB, decide_eq_true_eq]

def AddrOffOk {space : Space D} (base : Address space) (delta : Int) : Prop :=
  AddrRange space.width (base.value.n + delta)

def addrOffB {space : Space D} (base : Address space) (delta : Int) : Bool :=
  addrRangeB space.width (base.value.n + delta)

theorem addrOffB_iff {space : Space D} (base : Address space) (delta : Int) :
    addrOffB base delta = true ↔ AddrOffOk base delta := addrRangeB_iff _ _

def NarrowAddrOk {space : Space D} (base : Address space) (width : Nat) : Prop :=
  0 < width ∧ AddrRange width base.value.n

instance {space : Space D} (base : Address space) (width : Nat) :
    Decidable (NarrowAddrOk base width) := inferInstanceAs (Decidable (_ ∧ _))

def narrowAddrB {space : Space D} (base : Address space) (width : Nat) : Bool :=
  decide (NarrowAddrOk base width)

theorem narrowAddrB_iff {space : Space D} (base : Address space) (width : Nat) :
    narrowAddrB base width = true ↔ NarrowAddrOk base width := by
  simp only [narrowAddrB, decide_eq_true_eq]

/-- Static-proof-only forms: no wrap, saturation, or hidden failure branch. -/
def addrLitStep (space : Space D) (value : Int) (fits : AddrRange space.width value)
    (world : World D) : ValueStep D (Address space) :=
  valueStep ⟨⟨value, fits.1, fits.2⟩⟩ world

def addrOffStep {space : Space D} (base : Address space) (delta : Int)
    (fits : AddrOffOk base delta) (world : World D) : ValueStep D (Address space) :=
  addrLitStep space (base.value.n + delta) fits world

def narrowAddrStep {space : Space D} (base : Address space) (width : Nat)
    (fits : NarrowAddrOk base width) (world : World D) :
    ValueStep D (Address { space with width := width, positiveWidth := fits.1 }) :=
  addrLitStep _ base.value.n fits.2 world

theorem addrLitStep_checked (space : Space D) (value : Int)
    (fits : AddrRange space.width value) (world : World D) :
    address space value = .ok (addrLitStep space value fits world).value := by
  unfold address
  rw [dif_pos (show 0 ≤ value ∧ value ≤ 2 ^ space.width - 1 from fits)]
  rfl

theorem addrOffStep_value {space : Space D} (base : Address space) (delta : Int)
    (fits : AddrOffOk base delta) (world : World D) :
    (addrOffStep base delta fits world).value.value.n = base.value.n + delta := rfl

theorem narrowAddrStep_checked {space : Space D} (base : Address space) (width : Nat)
    (fits : NarrowAddrOk base width) (world : World D) :
    narrowAddress width fits.1 base = .ok (narrowAddrStep base width fits world).value :=
  addrLitStep_checked _ _ fits.2 world

/-- Arithmetic and narrowing preserve both address identities. -/
theorem narrowAddrStep_identity {space : Space D} (base : Address space) (width : Nat)
    (fits : NarrowAddrOk base width) (world : World D) :
    (narrowAddrStep base width fits world).value.location = base.location := rfl

theorem addrLitStep_frame (space : Space D) (value : Int)
    (fits : AddrRange space.width value) (world : World D) :
    (addrLitStep space value fits world).world = world := rfl

theorem addrOffStep_frame {space : Space D} (base : Address space) (delta : Int)
    (fits : AddrOffOk base delta) (world : World D) :
    (addrOffStep base delta fits world).world = world := rfl

theorem narrowAddrStep_frame {space : Space D} (base : Address space) (width : Nat)
    (fits : NarrowAddrOk base width) (world : World D) :
    (narrowAddrStep base width fits world).world = world := rfl

/-- All three address forms add no footprint beyond their operand. Literal
    costs zero; offset and narrowing use unaryCost (a static delta is free). -/
def addressFootprint : Footprint D := .empty

theorem addressFootprint_empty :
    (addressFootprint (D := D)).reads = [] ∧ (addressFootprint (D := D)).writes = [] :=
  ⟨rfl, rfl⟩

end Gabbro.Grammatik.LowLevel.Construct
