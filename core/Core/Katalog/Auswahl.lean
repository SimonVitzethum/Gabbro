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

theorem Plattform.dauerZeilen_leer (p : Plattform) : p.dauerZeilen = [] := by
  cases p <;> rfl

/-- Approved random-source rows (M9P): row 0 is the fair coin on every platform.
    The declared draw law behind the id is fixed by the probability layer
    (`Beobachtung.Wahrscheinlichkeit.zufallGesetz`), never by the program: a program
    selects this row by name like every other catalogue row. -/
def Plattform.zufallZeilen : Plattform → List Zeile
  | .x86_64 | .aarch64 | .riscv64 => [.zufall 0]

theorem Plattform.zufallZeilen_inhalt (p : Plattform) : p.zufallZeilen = [.zufall 0] := by
  cases p <;> rfl

def Plattform.zeilen (p : Plattform) : List Zeile :=
  ZielZeilen ++ .persistence :: (p.endpunkte.map Zeile.endpoint ++ p.dauerZeilen ++ p.zufallZeilen)

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
  cases p <;>
    simp only [Plattform.zeilen, ZielZeilen, Plattform.endpunkte, Plattform.dauerZeilen,
      Plattform.zufallZeilen,
      List.append_nil, List.cons_append, List.nil_append,
      List.map_cons, List.map_nil, List.nodup_cons, List.nodup_nil, List.mem_cons, List.not_mem_nil,
      reduceCtorEq, Zeile.endpoint.injEq, Zeile.zufall.injEq,
      false_or, not_false_eq_true, true_and]

theorem Plattform.katalog_wohlgeformt (p : Plattform) : KatalogWohlgeformt p.katalog :=
  ⟨p.zeilen_nodup, fun _ h => List.mem_append_left _ h, fun _ h => h,
    ziele_gut p, systemAbi_gut p, geraete_gut p⟩

/-- Pinned catalogue data (PERFECT-MODEL §4, step M10): the objects a platform row
    declares stable between check and commit. The approved rows declare the `cProcess`
    object 1 stable; every other object stays unstable. -/
def Plattform.stabileObjekte : Plattform → List Objekt
  | .x86_64 => [⟨.cProcess, 1⟩]
  | .aarch64 => [⟨.cProcess, 1⟩]
  | .riscv64 => [⟨.cProcess, 1⟩]

/-- A row declares stability for the object: membership in its pinned stable set. -/
def Plattform.stabilGemeldet (p : Plattform) (o : Objekt) : Prop :=
  o ∈ p.stabileObjekte

/-- The hardware/environment assumption of the row assures stability exactly for the
    objects the row declares stable. -/
def Plattform.stabilZugesichert (p : Plattform) (o : Objekt) : Prop :=
  o ∈ p.stabileObjekte

/-- Look up a maximum in a selected row. Random-source rows carry no duration maximum.
    Approval of the selection is a separate catalogue rule. -/
def Katalog.dauerMaximum (k : Katalog) (id : Nat) : Option Nat :=
  k.zeilen.findSome? fun
    | .dauer n max => if n = id then some max else none
    | .target | .cores | .interrupts | .mmu | .nativeFloat | .loader | .endpoint _ | .persistence
    | .zufall _ => none

end Gabbro.Core.Katalog
