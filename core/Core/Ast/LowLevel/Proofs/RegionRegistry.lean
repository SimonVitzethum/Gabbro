module

public import Core.Ast.LowLevel.Proofs.RegionSatisfiability

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Gabbro.Core.Waechter
open Lean (Name)

/-- Both surface initializers occur in an accepted unit and execute on a live region. -/
def RegionBindJointAussage : Prop :=
  RegionUnitErfuellbarAussage .address ∧
    ∃ written valid, RegionUnitErfuellbarAussage (.view written valid)

theorem regionBind_erfuellbar : RegionBindJointAussage :=
  ⟨regionAddressUnit_erfuellbar, viewUnit_erfuellbar⟩

/-- Extend the pinned statement schema with the existing checked region binding. -/
def regionStmtSchema (constructor : Name) : RegistrySchema constructor :=
  if constructor = ``Stmt.letRegion then
    ⟨.surface, Quellform.statements (Context := PUnit) (fun _ => regionUnitForm)
      RegionBindJointAussage constructor⟩
  else stmtSchema constructor

/-- The emitted region instruction has a checked source origin in the same unit. -/
def regionBefehlSchema (constructor : Name) : RegistrySchema constructor :=
  if constructor = ``Befehl.bindeRegion then
    ⟨.core, Quellform.kernStatements (Context := PUnit) (fun _ => regionUnitForm)
      RegionBindJointAussage constructor⟩
  else befehlSchema constructor

def regionBindProofs : RegistryEntry ``Stmt.letRegion
    ⟨.surface, Quellform.statements (Context := PUnit) (fun _ => regionUnitForm)
      RegionBindJointAussage ``Stmt.letRegion⟩ where
  realization := .surface (fun _ => regionUnit_realized.2.1)
    (fun _ => regionUnit_realized.2.2.1) (fun _ => regionUnit_realized.2.2.2)
  acceptanceRule := fun _ => regionUnitForm.annahme
  idealRule := fun _ => ⟨regionUnit_realized.1, fun args =>
    ⟨regionUnitForm.bestimmt args, (regionUnitForm.befehl args).ideal_privat
      (regionUnitForm.privat args)⟩⟩
  unitsAndCommutation := fun _ _ args => ⟨rfl, (regionUnitForm.befehl args).kommutation⟩
  implementationRule := fun _ args => (regionUnitForm.befehl args).impl_privat
    (regionUnitForm.privat args)
  preservation := fun _ => regionUnitForm.erhaltung (fun _ => fragment_unit_invarianten _)
  jointlySatisfiable := regionBind_erfuellbar

def regionBindStmtEntry : RegistryPacketEntry ``Stmt.letRegion
    (regionStmtSchema ``Stmt.letRegion) RegionBindUnitAussage where
  entry := by
    rw [regionStmtSchema, if_pos rfl]
    exact regionBindProofs
  packetProof := regionBindUnit

def regionBindBefehlEntry : RegistryPacketEntry ``Befehl.bindeRegion
    (regionBefehlSchema ``Befehl.bindeRegion) RegionBindUnitAussage where
  entry := by
    rw [regionBefehlSchema, if_pos rfl]
    exact Quellform.kernEintrag (constructor := ``Befehl.bindeRegion) regionBindProofs
  packetProof := regionBindUnit

/-- The written address type is admitted by the target and occurs in a checked signature. -/
def AddressTypeRegistryAussage : Prop :=
  AddressTypeUnitAussage ∧ AddressTypeUnitErfuellbarAussage

theorem addressTypeRegistryEntry :
    RegistryPacketProof ``WrittenType.address AddressTypeRegistryAussage :=
  ⟨⟨addressTypeUnit, addressTypeUnit_erfuellbar⟩⟩

end Gabbro.Core.Ast.Semantik
