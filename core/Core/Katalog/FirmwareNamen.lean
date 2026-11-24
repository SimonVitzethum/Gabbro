module

public import Core.Katalog.Auswahl

@[expose] public section

namespace Gabbro.Core.Katalog

/-- Surface row names for the pinned firmware interfaces. The endpoint owns the
    operation table, the ABI, and the commit and answer rules for every service. -/
inductive FirmwareZeile where
  | biosServices
  | uefi210
  | psci
  | sbi
  deriving DecidableEq, Repr

def FirmwareZeile.name : FirmwareZeile → String
  | .biosServices => "bios_services"
  | .uefi210 => "uefi_2_10"
  | .psci => "psci"
  | .sbi => "sbi"

def FirmwareZeile.endpunkt : FirmwareZeile → Endpunkt
  | .biosServices => .bios
  | .uefi210 => .uefi
  | .psci => .psci
  | .sbi => .sbi

def DienstAbi.name : DienstAbi → String
  | .biosInterrupt => "bios_int"
  | .efiX64 => "uefi_x64"
  | .efiAapcs => "uefi_aapcs"
  | .psciSmc => "psci_smc"
  | .sbiEcall => "sbi_ecall"

theorem DienstAbi.name_injective : Function.Injective DienstAbi.name := by
  intro a b same
  cases a <;> cases b <;> simp only [DienstAbi.name, String.reduceEq] at same ⊢

theorem FirmwareZeile.name_injective : Function.Injective FirmwareZeile.name := by
  intro a b same
  cases a <;> cases b <;> simp only [FirmwareZeile.name, String.reduceEq] at same ⊢

def FirmwareZeile.zugelassen (row : FirmwareZeile) (k : Katalog) (abi : DienstAbi) : Prop :=
  k.enthaelt (.endpoint row.endpunkt) ∧ k.plattform.firmwareAbi row.endpunkt = some abi

instance (row : FirmwareZeile) (k : Katalog) (abi : DienstAbi) :
    Decidable (row.zugelassen k abi) :=
  inferInstanceAs (Decidable (_ ∧ _))

end Gabbro.Core.Katalog
