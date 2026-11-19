module

public import Grammatik.Logik.Vertraege.Getrennt.GetrenntZeuge
public import Grammatik.Speichermodell.Adressen.NamedSpaces

@[expose] public section

namespace Gabbro.Grammatik.CapabilityWitness

open GetrenntZeuge

def writeType : Ty := .ptr (.table 0 (false, true))

/-- A real write through a capability that has no read permission. -/
def writeOnly : Stmt GetrenntZeuge.gD (vertragVon GetrenntZeuge.gD gAendern) false [writeType] [] [] :=
  .assignThru (.var .here) GTab.T rfl GFeld.x idx0 wert5 rfl darfT

def writeEnv : Env GetrenntZeuge.gD [writeType] := .cons () .nil

/-- Read permission cannot be recovered by unifying a write-only parameter with a readable view. -/
theorem write_only_read_refused :
    ∀ space n : Nat, ∀ write : Bool, writeType ≠ .ptr (.table n (true, write) space) := by
  intro space n write h
  cases h

/-- Labels never split one underlying carrier for separation. -/
theorem labelled_alias_refused :
    ¬ ParamGetrenntL GetrenntZeuge.gD [writeType, .ptr (.table 0 (true, false) 1)] := by
  exact leihe_nicht_getrennt (D := GetrenntZeuge.gD) (ps := [writeType, .ptr (.table 0 (true, false) 1)]) ⟨0, by decide⟩ ⟨1, by decide⟩
    (by decide) rfl rfl rfl (t := GTab.T) rfl

def namedPointer : Expr NamedSpaces.declaration [] [] (.ptr (.table 0 (true, true) 1)) :=
  .ptrOf false 0 rfl (true, true)

def namedWorld : World NamedSpaces.declaration := { slots := fun _ _ _ => ⟨0, by decide, by decide⟩, globs := fun _ => false, spur := [] }

end Gabbro.Grammatik.CapabilityWitness
