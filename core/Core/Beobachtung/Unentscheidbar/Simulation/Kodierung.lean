module

public import Core.Beobachtung.Unentscheidbar.Modell
import Mathlib.Tactic.DeriveEncodable
import Mathlib.Logic.Equiv.List

@[expose] public section

namespace Gabbro.Core.Beobachtung.Unentscheidbar.Simulation

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik
open Gabbro.Core.Katalog
open Gabbro.Core.Text

noncomputable section

deriving instance Encodable for Arith
deriving instance Encodable for Compare
deriving instance Encodable for LowLevel.AddressSpace
deriving instance Encodable for PtrRecht
deriving instance Encodable for CarrierAccess
deriving instance Encodable for CarrierEffect
deriving instance Encodable for Ty
deriving instance Encodable for DienstAbi
deriving instance Encodable for FirmwareZeile
deriving instance Encodable for WrittenType, WrittenTypes
deriving instance Encodable for RegionInitializer
deriving instance Encodable for Rufstelle
deriving instance Encodable for Befehl

/-- Names carry a proof of well-spelling; proof irrelevance makes the spelling
    the only data. Decoding re-establishes the proof by classical choice. -/
noncomputable instance encodableIdentifier : Encodable Identifier where
  encode name := Encodable.encode name.val
  decode n :=
    match (Encodable.decode n : Option (List Char)) with
    | none => none
    | some s =>
      if h : ∃ c rest, s = c :: rest ∧ isNameStart c ∧ ∀ a ∈ rest, isNamePart a
        then some ⟨s, h⟩ else none
  encodek := by
    intro name
    change (match (Encodable.decode (Encodable.encode name.val) : Option (List Char)) with
      | none => none
      | some s =>
        if h : ∃ c rest, s = c :: rest ∧ isNameStart c ∧ ∀ a ∈ rest, isNamePart a
          then some ⟨s, h⟩ else none) = some name
    rw [Encodable.encodek]
    change (if h : ∃ c rest, name.val = c :: rest ∧ isNameStart c ∧ ∀ a ∈ rest, isNamePart a
      then some ⟨name.val, h⟩ else none) = some name
    by_cases h : ∃ c rest, name.val = c :: rest ∧ isNameStart c ∧ ∀ a ∈ rest, isNamePart a
    · rw [dif_pos h]
      exact congrArg some (Subtype.ext rfl)
    · rw [dif_neg h]
      exact (h name.property).elim

end

/-- The Godel numbering of a command program is the Encodable numbering of the
    first-order syntax. No predicate ever inspects a micro-recursive code here. -/
def kodiere (p : List Befehl) : ℕ :=
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
