module

public import Grammatik.Niedrig.Konstrukte.Klassen.Simulation
public import Grammatik.Kern.Semantik.Semantik.T2.Teil1

@[expose] public section

namespace Gabbro.Grammatik.LowLevel.Construct

variable {D : Deklaration}

/-- Ordering is part of the target-binding request and observable event, never
    silently erased to an ordinary load. Targets must implement this order. -/
inductive MmioOrder where
  | relaxed | acquire | release | sequential
  deriving DecidableEq, Repr

structure MmioRegister (D : Deklaration) (register : D.Reg) where
  table : D.Tab
  backing : Nat
  address : Nat
  bytes : Nat
  littleEndian : Bool
  readOrder : MmioOrder
  writeOrder : MmioOrder

/-- All bytes, exact width, alignment, table and backing identities are checked.
    Register class and rzusage come from D, rather than a duplicate declaration.
    No port, reserved memory or normal-RAM span can pass this check. -/
def MmioViewOk (view : View D) (layout : AdressLayout D) (register : D.Reg)
    (binding : MmioRegister D register) : Prop :=
  view.span.memoryClass = .device ∧ SpacePairing view.span layout ∧
  view.span.table = binding.table ∧ view.span.space.backing = binding.backing ∧
  binding.bytes ∈ [1, 2, 4, 8] ∧ binding.address % binding.bytes = 0 ∧
  view.base ≤ binding.address ∧ binding.address + binding.bytes ≤ view.base + view.length ∧
  D.rtyp register = .int 0 ((2 : Int) ^ (8 * binding.bytes) - 1)

instance (view : View D) (layout : AdressLayout D) (register : D.Reg)
    (binding : MmioRegister D register) : Decidable (MmioViewOk view layout register binding) := by
  unfold MmioViewOk
  infer_instance

def MmioReadOk (view : View D) (layout : AdressLayout D) (register : D.Reg)
    (binding : MmioRegister D register) : Prop :=
  MmioViewOk view layout register binding ∧ view.rights.read = true ∧
  (D.rklasse register).lesbar = true ∧ binding.readOrder ≠ .release

instance (view : View D) (layout : AdressLayout D) (register : D.Reg)
    (binding : MmioRegister D register) : Decidable (MmioReadOk view layout register binding) := by
  unfold MmioReadOk
  infer_instance

def mmioReadB (view : View D) (layout : AdressLayout D) (register : D.Reg)
    (binding : MmioRegister D register) : Bool := decide (MmioReadOk view layout register binding)

theorem mmioReadB_iff (view : View D) (layout : AdressLayout D) (register : D.Reg)
    (binding : MmioRegister D register) :
    mmioReadB view layout register binding = true ↔ MmioReadOk view layout register binding := by
  simp only [mmioReadB, decide_eq_true_eq]

def MmioWriteOk (view : View D) (layout : AdressLayout D) (register : D.Reg)
    (binding : MmioRegister D register) : Prop :=
  MmioViewOk view layout register binding ∧ view.rights.write = true ∧
  (D.rklasse register).schreibbar = true ∧ binding.writeOrder ≠ .acquire

instance (view : View D) (layout : AdressLayout D) (register : D.Reg)
    (binding : MmioRegister D register) : Decidable (MmioWriteOk view layout register binding) := by
  unfold MmioWriteOk
  infer_instance

def mmioWriteB (view : View D) (layout : AdressLayout D) (register : D.Reg)
    (binding : MmioRegister D register) : Bool := decide (MmioWriteOk view layout register binding)

theorem mmioWriteB_iff (view : View D) (layout : AdressLayout D) (register : D.Reg)
    (binding : MmioRegister D register) :
    mmioWriteB view layout register binding = true ↔ MmioWriteOk view layout register binding := by
  simp only [mmioWriteB, decide_eq_true_eq]

/-- One bus transaction, with its width, byte order and required ordering.
    This augments the existing fremd event; it does not assert CPU behaviour. -/
structure MmioEvent (D : Deklaration) where
  register : D.Reg
  write : Bool
  binding : MmioRegister D register
  raw : Int
  order : MmioOrder

structure MmioStep (D : Deklaration) (α : Type) where
  value : α
  world : World D
  event : MmioEvent D

/-- Exact G register decoding. A broken declared promise is a named hardware
    stop for a strict read, and a value-carrying reason for a fallible read.
    Read side effects remain the existing oracle boundary, never RAM writes. -/
def mmioReadStep (oracle : Orakel D) (view : View D) (layout : AdressLayout D)
    (register : D.Reg) (binding : MmioRegister D register)
    (_checked : MmioReadOk view layout register binding) (fallible : Bool) (world : World D) :
    MmioStep D (Except (Hardware D) (Except (Wert D (D.rtyp register)) (Wert D (D.rtyp register)))) :=
  let observed := world.fragt (.inr (.inl register))
  let raw := oracle.regLies register observed
  { value := match einpassen oracle.zeiger (D.rtyp register) raw with
      | none => .error (.register register)
      | some value => if D.rzusage register value then .ok (.ok value)
        else if fallible then .ok (.error value) else .error (.geraet register)
    world := observed
    event := ⟨register, false, binding, raw, binding.readOrder⟩ }

/-- Width is enforced by rtyp, and raw encoding is the existing G encoding.
    Devices are outside World, exactly as for G's regWrite. -/
def mmioWriteStep (oracle : Orakel D) (view : View D) (layout : AdressLayout D)
    (register : D.Reg) (binding : MmioRegister D register)
    (_checked : MmioWriteOk view layout register binding)
    (value : Wert D (D.rtyp register)) (world : World D) : MmioStep D Unit :=
  { value := oracle.regSchreib register (roh value)
    world := world
    event := ⟨register, true, binding, roh value, binding.writeOrder⟩ }

theorem mmioReadStep_confined {view : View D} {layout : AdressLayout D} {register : D.Reg}
    {binding : MmioRegister D register} (checked : MmioReadOk view layout register binding)
    (offset : Nat) (within : offset < binding.bytes) :
    view.Contains (binding.backing, binding.address + offset) := by
  obtain ⟨_, _, _, backing, _, _, low, high, _⟩ := checked.1
  exact ⟨backing.symm, by omega, by omega⟩

theorem mmioReadStep_sim {P I : Type} {a : Authority D} {layout : AdressLayout D}
    {c : Context D P I} {world : World D} (simulation : ClassSimRel a layout c world)
    (oracle : Orakel D) (view : View D) (register : D.Reg) (binding : MmioRegister D register)
    (checked : MmioReadOk view layout register binding) (fallible : Bool) :
    ClassSimRel a layout c (mmioReadStep oracle view layout register binding checked fallible world).world :=
  ⟨simulation.valid, .observe simulation.replay register⟩

theorem mmioWriteStep_sim {P I : Type} {a : Authority D} {layout : AdressLayout D}
    {c : Context D P I} {world : World D} (simulation : ClassSimRel a layout c world)
    (oracle : Orakel D) (view : View D) (register : D.Reg) (binding : MmioRegister D register)
    (checked : MmioWriteOk view layout register binding) (value : Wert D (D.rtyp register)) :
    ClassSimRel a layout c (mmioWriteStep oracle view layout register binding checked value world).world :=
  simulation

/-- Carrier dependence is the existing rtraeger. Transaction ordering is
    retained separately; an empty RAM write footprint never means reorderable. -/
def mmioReadFootprint (register : D.Reg) : Footprint D := ⟨D.rtraeger register, []⟩

def mmioWriteFootprint (operands : Footprint D) : Footprint D := operands

def mmioReadCost (reason rest : Nat) : Nat := 2 + reason + rest

def mmioWriteCost (operand : Nat) : Nat := unaryCost operand

end Gabbro.Grammatik.LowLevel.Construct
