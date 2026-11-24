module

@[expose] public section

namespace Gabbro.Core.Katalog

inductive Plattform where
  | x86_64
  | aarch64
  | riscv64
  deriving DecidableEq, Repr

def Plattform.name : Plattform → String
  | .x86_64 => "x86_64"
  | .aarch64 => "aarch64"
  | .riscv64 => "riscv64"

def Plattform.vonName (name : String) : Option Plattform :=
  ([.x86_64, .aarch64, .riscv64] : List Plattform).find? (fun p => p.name == name)

inductive Seitenformat where
  | x86FourLevel
  | arm4KiB48
  | sv39
  deriving DecidableEq, Repr

inductive InterruptController where
  | localApic
  | gicv3
  | aia
  deriving DecidableEq, Repr

inductive Ankunft where
  | real16
  | translationOff
  | user64
  deriving DecidableEq, Repr

inductive Kernstart where
  | initSipi
  | psci
  | sbiHsm
  deriving DecidableEq, Repr

inductive Bildformat where
  | elf
  | uefi
  | bootSector
  | flash
  deriving DecidableEq, Repr

/-- Architecture, paging and boot configuration of an approved platform profile. -/
structure ZielDaten where
  triple : String
  layout : String
  wbits : Nat
  big : Bool
  registerCount : Nat
  page : Seitenformat
  virtualBits : Nat
  physicalBits : Nat
  pageShift : Nat
  controller : InterruptController
  interruptCount : Nat
  nonmaskable : Bool
  machineCheck : Bool
  coreStart : Kernstart
  arrival : Ankunft
  imageFormats : List Bildformat
  deriving DecidableEq, Repr

def Plattform.ziel : Plattform → ZielDaten
  | .x86_64 =>
    { triple := "x86_64-unknown-linux-gnu"
      layout := "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
      wbits := 64, big := false, registerCount := 16
      page := .x86FourLevel, virtualBits := 48, physicalBits := 52, pageShift := 12
      controller := .localApic, interruptCount := 256, nonmaskable := true, machineCheck := true
      coreStart := .initSipi, arrival := .real16, imageFormats := [.elf, .uefi, .bootSector, .flash] }
  | .aarch64 =>
    { triple := "aarch64-unknown-linux-gnu"
      layout := "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
      wbits := 64, big := false, registerCount := 31
      page := .arm4KiB48, virtualBits := 48, physicalBits := 48, pageShift := 12
      controller := .gicv3, interruptCount := 1020, nonmaskable := false, machineCheck := false
      coreStart := .psci, arrival := .translationOff, imageFormats := [.elf, .uefi, .flash] }
  | .riscv64 =>
    { triple := "riscv64-unknown-linux-gnu"
      layout := "e-m:e-p:64:64-i64:64-i128:128-n32:64-S128"
      wbits := 64, big := false, registerCount := 32
      page := .sv39, virtualBits := 39, physicalBits := 56, pageShift := 12
      controller := .aia, interruptCount := 2048, nonmaskable := false, machineCheck := false
      coreStart := .sbiHsm, arrival := .translationOff, imageFormats := [.elf, .flash] }

def ZielDaten.seitengranule (z : ZielDaten) : Nat := 2 ^ z.pageShift

def ZielDaten.gut (z : ZielDaten) : Prop :=
  z.wbits = 64 ∧ z.big = false ∧ 0 < z.registerCount ∧
  0 < z.pageShift ∧ z.pageShift < z.virtualBits ∧ z.virtualBits ≤ z.wbits ∧
  z.pageShift < z.physicalBits ∧ z.physicalBits ≤ z.wbits ∧
  0 < z.interruptCount ∧ .elf ∈ z.imageFormats

theorem ziele_gut (p : Plattform) : p.ziel.gut := by
  cases p <;>
    simp only [ZielDaten.gut, Plattform.ziel, List.mem_cons_self, true_and, and_true] <;>
    (repeat' apply And.intro) <;> omega

inductive SystemEntry where
  | syscall
  | svc
  | ecall
  deriving DecidableEq, Repr

/-- Register indices of the Linux register convention. The service number is separate from arguments. -/
structure SystemAbi where
  number : Nat
  arguments : List Nat
  result : Nat
  entry : SystemEntry
  deriving DecidableEq, Repr

def Plattform.systemAbi : Plattform → SystemAbi
  | .x86_64 => ⟨0, [7, 6, 2, 10, 8, 9], 0, .syscall⟩
  | .aarch64 => ⟨8, [0, 1, 2, 3, 4, 5], 0, .svc⟩
  | .riscv64 => ⟨17, [10, 11, 12, 13, 14, 15], 10, .ecall⟩

def SystemAbi.gut (abi : SystemAbi) (z : ZielDaten) : Prop :=
  abi.arguments.Nodup ∧ abi.number ∉ abi.arguments ∧
  abi.number < z.registerCount ∧ abi.result < z.registerCount ∧
  ∀ r ∈ abi.arguments, r < z.registerCount

theorem systemAbi_gut (p : Plattform) : p.systemAbi.gut p.ziel := by
  cases p <;>
    simp only [SystemAbi.gut, Plattform.systemAbi, Plattform.ziel, List.forall_mem_cons] <;>
    simp only [List.nodup_cons, List.nodup_nil, List.mem_cons, List.not_mem_nil, Nat.reduceEqDiff,
      false_or, not_false_eq_true, false_imp_iff, imp_true_iff, true_and, and_true] <;>
    (repeat' apply And.intro) <;> omega

end Gabbro.Core.Katalog
