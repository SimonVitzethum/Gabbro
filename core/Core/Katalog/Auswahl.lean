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
  | dauer (id maximum : Nat)
  | zufall (id : Nat)
  deriving DecidableEq, Repr

def ZielZeilen : List Zeile := [.target, .cores, .interrupts, .mmu, .nativeFloat, .loader]

def Plattform.endpunkte (p : Plattform) : List Endpunkt :=
  match p with
  | .x86_64 => [.uart, .virtio, .hosted, .cProcess, .bios, .uefi]
  | .aarch64 => [.uart, .virtio, .hosted, .cProcess, .uefi, .psci]
  | .riscv64 => [.uart, .virtio, .hosted, .cProcess, .sbi]

/-- Approved duration rows, in hardware cycles. The current platforms have no reviewed maxima. -/
def Plattform.dauerZeilen : Plattform → List Zeile
  | .x86_64 | .aarch64 | .riscv64 => []

def Plattform.zeilen (p : Plattform) : List Zeile :=
  ZielZeilen ++ .persistence :: (p.endpunkte.map Zeile.endpoint ++ p.dauerZeilen)

structure Katalog where
  plattform : Plattform
  zeilen : List Zeile
  deriving DecidableEq, Repr

def Plattform.katalog (p : Plattform) : Katalog := ⟨p, p.zeilen⟩

def Katalog.enthaelt (k : Katalog) (r : Zeile) : Prop := r ∈ k.zeilen

instance (k : Katalog) (r : Zeile) : Decidable (k.enthaelt r) :=
  inferInstanceAs (Decidable (r ∈ k.zeilen))

/-- Exactly the platform's approved rows may be selected, with all required base rows.
    Random-source rows (M9P) are selected per program: any `.zufall id` row may appear,
    and the declared draw law behind `id` is fixed by the probability layer
    (`Beobachtung.Wahrscheinlichkeit`), never here. The reviewed device windows in a
    full platform profile are disjoint. -/
def KatalogWohlgeformt (k : Katalog) : Prop :=
  k.zeilen.Nodup ∧
    ZielZeilen ⊆ k.zeilen ∧
    (∀ r ∈ k.zeilen, r ∈ k.plattform.zeilen ∨ ∃ id, r = .zufall id) ∧
    k.plattform.ziel.gut ∧ k.plattform.systemAbi.gut k.plattform.ziel ∧
    k.plattform.uart.gut k.plattform.ziel ∧ k.plattform.virtio.gut k.plattform.ziel ∧
    k.plattform.uart.window.getrennt k.plattform.virtio.window

theorem Plattform.zeilen_nodup (p : Plattform) : p.zeilen.Nodup := by
  cases p <;>
    simp only [Plattform.zeilen, ZielZeilen, Plattform.endpunkte, Plattform.dauerZeilen,
      List.append_nil, List.cons_append, List.nil_append,
      List.map_cons, List.map_nil, List.nodup_cons, List.nodup_nil, List.mem_cons, List.not_mem_nil,
      reduceCtorEq, Zeile.endpoint.injEq, false_or, not_false_eq_true, true_and]

theorem Plattform.katalog_wohlgeformt (p : Plattform) : KatalogWohlgeformt p.katalog :=
  ⟨p.zeilen_nodup, fun _ h => List.mem_append_left _ h, fun _ h => Or.inl h,
    ziele_gut p, systemAbi_gut p, geraete_gut p⟩

/-- Look up a maximum in a selected row. Random-source rows carry no duration maximum.
    Approval of the selection is a separate catalogue rule. -/
def Katalog.dauerMaximum (k : Katalog) (id : Nat) : Option Nat :=
  k.zeilen.findSome? fun
    | .dauer n max => if n = id then some max else none
    | .target | .cores | .interrupts | .mmu | .nativeFloat | .loader | .endpoint _ | .persistence
    | .zufall _ => none

end Gabbro.Core.Katalog
