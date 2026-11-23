module
public import Core.Katalog.Aussen
public import Core.Katalog.Dauerhaft
public import Core.Katalog.Ereignis
public import Core.Katalog.Gleit

@[expose] public section

namespace Gabbro.Core.Katalog

/-- Closed row names. Their meanings are the corresponding catalogue declarations for the selected platform. -/
inductive Zeile where
  | target
  | cores
  | interrupts
  | mmu
  | nativeFloat
  | loader
  | endpoint (e : Endpunkt)
  | persistence
  deriving DecidableEq, Repr

def ZielZeilen : List Zeile := [.target, .cores, .interrupts, .mmu, .nativeFloat, .loader]

def Plattform.endpunkte (p : Plattform) : List Endpunkt :=
  match p with
  | .x86_64 => [.uart, .virtio, .hosted, .cProcess, .bios, .uefi]
  | .aarch64 => [.uart, .virtio, .hosted, .cProcess, .uefi, .psci]
  | .riscv64 => [.uart, .virtio, .hosted, .cProcess, .sbi]

def Plattform.zeilen (p : Plattform) : List Zeile :=
  ZielZeilen ++ .persistence :: p.endpunkte.map Zeile.endpoint

structure Katalog where
  plattform : Plattform
  zeilen : List Zeile
  deriving DecidableEq, Repr

def Plattform.katalog (p : Plattform) : Katalog := ⟨p, p.zeilen⟩

def Katalog.enthaelt (k : Katalog) (r : Zeile) : Prop := r ∈ k.zeilen

instance (k : Katalog) (r : Zeile) : Decidable (k.enthaelt r) :=
  inferInstanceAs (Decidable (r ∈ k.zeilen))

/-- Exactly the platform's approved rows may be selected, with all required base rows.
    The reviewed device windows in a full platform profile are disjoint. -/
def KatalogWohlgeformt (k : Katalog) : Prop :=
  k.zeilen.Nodup ∧
    ZielZeilen ⊆ k.zeilen ∧ k.zeilen ⊆ k.plattform.zeilen ∧
    k.plattform.ziel.gut ∧ k.plattform.systemAbi.gut k.plattform.ziel ∧
    k.plattform.uart.gut k.plattform.ziel ∧ k.plattform.virtio.gut k.plattform.ziel ∧
    k.plattform.uart.window.getrennt k.plattform.virtio.window

theorem Plattform.zeilen_nodup (p : Plattform) : p.zeilen.Nodup := by
  cases p <;> decide

theorem Plattform.katalog_wohlgeformt (p : Plattform) : KatalogWohlgeformt p.katalog :=
  ⟨p.zeilen_nodup, fun _ h => List.mem_append_left _ h, fun _ h => h,
    ziele_gut p, systemAbi_gut p, geraete_gut p⟩

end Gabbro.Core.Katalog
