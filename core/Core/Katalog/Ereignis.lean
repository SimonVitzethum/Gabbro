module
public import Core.Katalog.Seiten

@[expose] public section

namespace Gabbro.Core.Katalog

/-- Observations of physical core availability. A parked core is still offered hardware opportunities. -/
def kerneSchreiten (anzahl : Nat) (spur : Nat → Option Nat) : Prop :=
  (∀ i k, spur i = some k → k < anzahl) ∧
    ∀ k, k < anzahl → ∀ ab, ∃ i, ab ≤ i ∧ spur i = some k

theorem kerneSchreiten_reihum {anzahl : Nat} (positive : 0 < anzahl) :
    kerneSchreiten anzahl (fun i => some (i % anzahl)) := by
  constructor
  · intro i k assigned
    exact (Option.some.inj assigned) ▸ Nat.mod_lt i positive
  · intro k hk cut
    have later : cut ≤ anzahl * cut :=
      Nat.mul_comm cut anzahl ▸ Nat.le_mul_of_pos_right cut positive
    refine ⟨anzahl * cut + k, Nat.le_trans later (Nat.le_add_right _ _), ?_⟩
    simp only [Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hk]

inductive Unterbrechung where

  | maskierbar (line priority : Nat)
  | nmi
  | machineCheck
  deriving DecidableEq, Repr

structure Maske where
  normale : Bool
  minimum : Nat
  nmiAktiv : Bool
  machineCheckAktiv : Bool
  deriving DecidableEq, Repr

def ZielDaten.unterstuetzt (z : ZielDaten) : Unterbrechung → Prop
  | .maskierbar line priority => line < z.interruptCount ∧ priority < 256
  | .nmi => z.nonmaskable = true
  | .machineCheck => z.machineCheck = true

inductive Eintritt where
  | handler
  | ausstehend
  | shutdown
  deriving DecidableEq, Repr

/-- Delivery after an offered interrupt meets the core's architectural mask state. A pending line and
    an offer are separate: the offer stays recorded even if the line remains pending. -/
def unterbrechungen (m : Maske) : Unterbrechung → Eintritt
  | .maskierbar _ priority =>
    if m.normale || priority < m.minimum then .ausstehend else .handler
  | .nmi => if m.nmiAktiv then .ausstehend else .handler
  | .machineCheck => if m.machineCheckAktiv then .shutdown else .handler

theorem nmi_unabhaengig (m : Maske) :
    unterbrechungen { m with normale := true } .nmi = unterbrechungen m .nmi := rfl

/-- The per-platform counter row: the bound register and the trap line the hardware raises
    when a cycle counter reaches the bound. Every current row carries a 32-bit bound register
    and raises trap line 32 at priority 0, a line every row supports. -/
structure ZaehlerZeile where
  schranke : Nat
  trap : Unterbrechung
  deriving DecidableEq, Repr

/-- The counter row of each platform (a named hardware assumption the program selects, never
    one it writes). -/
def Plattform.zaehlerZeile : Plattform → ZaehlerZeile
  | .x86_64 => ⟨4294967295, .maskierbar 32 0⟩
  | .aarch64 => ⟨4294967295, .maskierbar 32 0⟩
  | .riscv64 => ⟨4294967295, .maskierbar 32 0⟩

/-- Every platform row supports its own trap line. -/
theorem Plattform.zaehlerZeile_unterstuetzt (p : Plattform) :
    p.ziel.unterstuetzt p.zaehlerZeile.trap := by
  cases p <;>
    simp only [Plattform.zaehlerZeile, Plattform.ziel, ZielDaten.unterstuetzt] <;>
    omega

def laderStart {α : Type} (starts : List α) (i : Nat) : Option α := starts[i]?

/-- Byte and entry observations at an image loader's boundary. Entry addresses are image data. -/
structure Ladebild where
  format : Bildformat
  bildBytes : Nat → Option UInt8
  startBytes : Nat → Option UInt8
  eintraege : List Nat
  starts : Nat → Option Nat

def lader (z : ZielDaten) (bild : Ladebild) : Prop :=
  bild.format ∈ z.imageFormats ∧
  (∀ a b, bild.bildBytes a = some b → a < 2 ^ z.physicalBits ∧ bild.startBytes a = some b) ∧
  (∀ entry ∈ bild.eintraege, ∃ byte, bild.bildBytes entry = some byte) ∧
  ∀ i, bild.starts i = laderStart bild.eintraege i

theorem lader_start (h : lader z bild) (i : Nat) : bild.starts i = laderStart bild.eintraege i :=
  h.2.2.2 i

/-- Loader input and observations are separated so an environment cannot choose the image it must load. -/
structure Bild where
  format : Bildformat
  bytes : Nat → Option UInt8
  entries : List Nat

def Bild.gueltig (z : ZielDaten) (b : Bild) : Prop :=
  b.format ∈ z.imageFormats ∧
    (∀ a v, b.bytes a = some v → a < 2 ^ z.physicalBits) ∧
    ∀ entry ∈ b.entries, ∃ byte, b.bytes entry = some byte

structure Ladung where
  bytes : Nat → Option UInt8
  starts : Nat → Option Nat

def Bild.beobachtung (b : Bild) (l : Ladung) : Ladebild :=
  ⟨b.format, b.bytes, l.bytes, b.entries, l.starts⟩

def Bild.lade (b : Bild) : Ladung := ⟨b.bytes, laderStart b.entries⟩

theorem Bild.lader_lade (b : Bild) (h : b.gueltig z) : lader z (b.beobachtung b.lade) :=
  ⟨h.1, fun a v hv => ⟨h.2.1 a v hv, hv⟩, h.2.2, fun _ => rfl⟩

end Gabbro.Core.Katalog
