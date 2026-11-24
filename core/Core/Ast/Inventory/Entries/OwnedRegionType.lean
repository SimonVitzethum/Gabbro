module

public import Core.Ast.Inventory.Entries.WrittenTypeStatements
public import Core.Ast.LowLevel.Proofs.RegionSatisfiability

namespace Gabbro.Core.Ast.Semantik

open Gabbro.Core.Text (PrintedToken)
open Waechter

/-- The printed form of the written region type is read as the owned-region type,
    and its checked binding unit supplies the region evidence. -/
private theorem ownedRegionTypeRegistry : OwnedRegionTypeRegistryAussage := by
  refine ⟨?_, regionBindUnit⟩
  intro scope rest
  change TypeReads scope (LowLevel.printOwnedRegion.map PrintedToken.value ++ rest) .ownedRegion rest
  have printed : LowLevel.printOwnedRegion.map PrintedToken.value = LowLevel.ownedRegionTokens := by
    rfl
  rw [printed]
  exact .ownedRegion

public theorem ownedRegionTypeEntry :
    RegistryPacketProof ``WrittenType.ownedRegion OwnedRegionTypeRegistryAussage :=
  ⟨ownedRegionTypeRegistry⟩

end Gabbro.Core.Ast.Semantik
