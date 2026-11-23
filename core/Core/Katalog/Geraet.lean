module
public import Core.Katalog.Seiten

@[expose] public section

namespace Gabbro.Core.Katalog

inductive GeratBus where
  | ioPorts
  | mmio
  deriving DecidableEq, Repr

structure Register where
  offset : Nat
  bytes : Nat
  read : Bool
  write : Bool
  deriving DecidableEq, Repr

structure GeraeteDaten where
  bus : GeratBus
  window : Strecke
  registers : List Register
  dma : Bool
  deriving DecidableEq, Repr

/-- The UART layout of each profile. Only the data and status registers are exposed by this row. -/
def Plattform.uart : Plattform → GeraeteDaten
  | .x86_64 => ⟨.ioPorts, ⟨0x3F8, 0x400⟩, [⟨0, 1, true, true⟩, ⟨5, 1, true, false⟩], false⟩
  | .aarch64 => ⟨.mmio, ⟨0x09000000, 0x09001000⟩, [⟨0, 4, true, true⟩, ⟨0x18, 4, true, false⟩], false⟩
  | .riscv64 => ⟨.mmio, ⟨0x10000000, 0x10000100⟩, [⟨0, 1, true, true⟩, ⟨5, 1, true, false⟩], false⟩

/-- The software-visible DMA window of a paravirtual MMIO transport. Mapping and lifecycle are
    supplied by the platform profile and the device authority rule. -/
def Plattform.virtio : Plattform → GeraeteDaten
  | .x86_64 => ⟨.mmio, ⟨0x10000000, 0x10000200⟩, [⟨0x70, 4, true, true⟩, ⟨0x50, 4, false, true⟩], true⟩
  | .aarch64 => ⟨.mmio, ⟨0x0A000000, 0x0A000200⟩, [⟨0x70, 4, true, true⟩, ⟨0x50, 4, false, true⟩], true⟩
  | .riscv64 => ⟨.mmio, ⟨0x10001000, 0x10001200⟩, [⟨0x70, 4, true, true⟩, ⟨0x50, 4, false, true⟩], true⟩

def GeraeteDaten.gut (z : ZielDaten) (d : GeraeteDaten) : Prop :=
  d.window.von < d.window.bis ∧
  d.window.bis ≤ (if d.bus = .ioPorts then 2 ^ 16 else 2 ^ z.physicalBits) ∧
  (d.registers.map Register.offset).Nodup ∧
  ∀ r ∈ d.registers, 0 < r.bytes ∧ r.offset + r.bytes ≤ d.window.bis - d.window.von

theorem geraete_gut (p : Plattform) :
    p.uart.gut p.ziel ∧ p.virtio.gut p.ziel ∧ p.uart.window.getrennt p.virtio.window := by
  cases p <;> unfold GeraeteDaten.gut Strecke.getrennt <;> decide

/-- One exclusive region lent to a device. Its identity is distinct from the physical address. -/
structure Leihe where
  token : Nat
  region : Strecke
  read : Bool
  write : Bool
  deriving DecidableEq, Repr

inductive GeraetePhase where
  | reset
  | ready
  | lending (loan : Leihe)
  deriving DecidableEq, Repr

inductive GeraeteAktion where
  | start
  | lend (loan : Leihe)
  | takeBack (loan : Leihe)
  | reset

/-- Hook for the linear authority and the language's DMA revocation protocol. -/
inductive GeraeteUebergang (d : GeraeteDaten) (z : ZielDaten) :
    GeraetePhase → GeraeteAktion → GeraetePhase → Prop where
  | start : GeraeteUebergang d z .reset .start .ready
  | lend {loan} (enabled : d.dma = true) (pages : loan.region.seiten z) :
      GeraeteUebergang d z .ready (.lend loan) (.lending loan)
  | takeBack (loan) : GeraeteUebergang d z (.lending loan) (.takeBack loan) .ready
  | reset : GeraeteUebergang d z .ready .reset .reset

/-- The transfer identifies its loan and a relative offset. Bytes resolve inside the lent extent. -/
inductive DmaZugriff where
  | read (token offset count : Nat)
  | write (token offset : Nat) (bytes : List UInt8)
  deriving DecidableEq, Repr

def Leihe.erlaubt (loan : Leihe) (access : DmaZugriff) : Prop :=
  match access with
  | .read token offset size =>
    token = loan.token ∧ loan.read = true ∧ 0 < size ∧ loan.region.von + offset + size ≤ loan.region.bis
  | .write token offset bytes =>
    token = loan.token ∧ loan.write = true ∧ 0 < bytes.length ∧
      loan.region.von + offset + bytes.length ≤ loan.region.bis

def dma (d : GeraeteDaten) (phase : GeraetePhase) (loan : Leihe) (access : DmaZugriff) : Prop :=
  d.dma = true ∧ phase = .lending loan ∧ loan.erlaubt access

theorem dma_ohne_leihe (d : GeraeteDaten) (loan : Leihe) (access : DmaZugriff) :
    ¬ dma d .ready loan access :=
  fun proof => nomatch proof.2.1

end Gabbro.Core.Katalog
