module

public import Core.Ast.Inventory.Entries.WrittenTypeStatements
public import Core.Ast.LowLevel.Admission
public import Core.Ast.LowLevel.Meaning
public import Core.Ast.Program.WrittenTypes

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Gabbro.Core.Text (PrintedToken)
open Waechter

/-- The printed pointer type parses as the written pointer capability, its
    elaborated type is the capability over the elaborated referent, admission
    is the space width with the admitted referent, a pointer has no direct
    byte view, and `ptr<physical, rw> bool` shows the premises hold jointly.
    Execute rights and owner marks have no grammar arm (no `x`, no `own`);
    there is no integer-to-pointer conversion. -/
def PointerTypeRegistryAussage : Prop :=
  (∀ scope space recht referent rest, (valid : (WrittenType.ptr space recht referent).valid scope) →
    (∀ more, rest ≠ keyword "in" :: more) →
    TypeReads scope ((WrittenType.ptr space recht referent).printPieces.map PrintedToken.value ++ rest)
      (.ptr space recht referent) rest)
  ∧ (∀ space recht referent,
      (WrittenType.ptr space recht referent).type = .ptr space recht referent.type)
  ∧ (∀ platform space recht referent,
      platformType platform (.ptr space recht referent) =
        ((space.width platform).isSome && platformType platform referent))
  ∧ (∀ target space recht referent,
      LowLevel.layout target (.ptr space recht referent) = none)
  ∧ (∃ scope, (WrittenType.ptr .physical .rw .bool).valid scope)

private theorem pointerTypeRegistry : PointerTypeRegistryAussage := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro scope space recht referent rest valid closed
    exact WrittenType.printReads _ valid closed
  · intro space recht referent; rfl
  · intro platform space recht referent; simp only [platformType]
  · intro target space recht referent; rfl
  · exact ⟨[], True.intro⟩

public theorem pointerTypeEntry :
    RegistryPacketProof ``WrittenType.ptr PointerTypeRegistryAussage :=
  ⟨pointerTypeRegistry⟩

/-- A pointer-typed binding runs the same local-type recipe as the other
    written types: the universal `LocalTypeUseAussage` covers the pointer
    case. The simulation and preservation arguments over the
    capability (no integer-to-pointer conversion, access only through the
    named target with the written rights) are open work for the provers. -/
def PointerTypeUseAussage : Prop :=
  LocalTypeUseAussage

end Gabbro.Core.Ast.Semantik
