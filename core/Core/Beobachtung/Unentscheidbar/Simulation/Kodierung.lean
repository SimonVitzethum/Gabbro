module

public import Core.Beobachtung.Unentscheidbar.Modell
public import Mathlib.Logic.Encodable.Basic
import Mathlib.Basic.Countable.Basic
import Mathlib.Logic.Equiv.List
import Mathlib.Tactic.DeriveCountable

@[expose] public section

namespace Gabbro.Core.Beobachtung.Unentscheidbar.Simulation

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik
open Gabbro.Core.Katalog

noncomputable section

/-- Unsigned machine words are injections into the naturals; this makes the
    character and command syntax countable without a hand-written Godel tree. -/
instance : Countable UInt32 :=
  (show Function.Injective (fun x : UInt32 => x.toNat) from
    fun a b h => UInt32.toNat_inj.mp h).countable

deriving instance Countable for Char

instance : Countable Identifier := by
  dsimp only [Identifier]
  infer_instance

deriving instance Countable for Arith
deriving instance Countable for Compare
deriving instance Countable for LowLevel.AddressSpace
deriving instance Countable for PtrRecht
deriving instance Countable for CarrierAccess
deriving instance Countable for CarrierEffect
deriving instance Countable for Ty
deriving instance Countable for DienstAbi
deriving instance Countable for FirmwareZeile
deriving instance Countable for WrittenType, WrittenTypes
deriving instance Countable for RegionInitializer
deriving instance Countable for Rufstelle
deriving instance Countable for Befehl

instance : Encodable Arith := Encodable.ofCountable _
instance : Encodable Compare := Encodable.ofCountable _
instance : Encodable LowLevel.AddressSpace := Encodable.ofCountable _
instance : Encodable PtrRecht := Encodable.ofCountable _
instance : Encodable CarrierAccess := Encodable.ofCountable _
instance : Encodable CarrierEffect := Encodable.ofCountable _
instance : Encodable (Ty .value) := Encodable.ofCountable _
instance : Encodable DienstAbi := Encodable.ofCountable _
instance : Encodable FirmwareZeile := Encodable.ofCountable _
instance : Encodable WrittenType := Encodable.ofCountable _
instance : Encodable WrittenTypes := Encodable.ofCountable _
instance : Encodable RegionInitializer := Encodable.ofCountable _
instance : Encodable Rufstelle := Encodable.ofCountable _
instance : Encodable Identifier := Encodable.ofCountable _
instance : Encodable Befehl := Encodable.ofCountable _

end

/-- The Godel numbering of a command program is the Encodable numbering of the
    first-order syntax. No predicate ever inspects a micro-recursive code here. -/
noncomputable def kodiere (p : List Befehl) : ℕ :=
  Encodable.encode p

/-- Decoding is the Encodable inverse; the left inverse is `Encodable.encodek`. -/
noncomputable def dekodiere (n : ℕ) : Option (List Befehl) :=
  Encodable.decode n

theorem dekodiere_links (p : List Befehl) : dekodiere (kodiere p) = some p := by
  exact Encodable.encodek p

/-- The canonical start frame places the input as an exact integer in slot zero.
    All bound maps keep their default `none`, so the frame is open. -/
def startVon (n : ℕ) : Rahmen :=
  { pc := 0
    temp := fun slot => if slot = 0 then some ⟨.int (n : Int) (n : Int), Zahl.literal (n : Int)⟩ else none
    lokale := []
    rueckgabe := none }

theorem start_offen (n : ℕ) : OffenesFragment (startVon n) := by
  intro slot
  rfl

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation
