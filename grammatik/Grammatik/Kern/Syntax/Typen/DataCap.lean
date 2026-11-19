module

public import Grammatik.Kern.Syntax.Typen.DataRights

@[expose] public section

namespace Gabbro.Grammatik

/-- A logical data target. Live byte targets wait for the checked grant-history interface. -/
inductive DataTarget where
  | table (number : Nat)
  deriving DecidableEq, Repr

/-- One data-capability descriptor. Space and owner numbers are declaration references,
    never machine addresses. Ownership is retained separately from access permissions. -/
structure DataCapTy where
  space : Nat
  rights : DataRights
  target : DataTarget
  deriving DecidableEq, Repr

namespace DataCapTy

/-- A plain table view. The two flags are independently readable and writable. -/
@[match_pattern] abbrev table (number : Nat) (access : Bool × Bool) (space : Nat := 0) : DataCapTy :=
  ⟨space, ⟨access.1, access.2, none⟩, .table number⟩

/-- Attenuation preserves identity, space and ownership; it cannot manufacture access. -/
def attenuates (source target : DataCapTy) : Bool :=
  decide (source.space = target.space) && decide (source.target = target.target) &&
  decide (source.rights.owner = target.rights.owner) &&
  (!target.rights.read || source.rights.read) && (!target.rights.write || source.rights.write)

theorem attenuates_sound (source target : DataCapTy) (h : source.attenuates target = true) :
    source.space = target.space ∧ source.target = target.target ∧
    source.rights.owner = target.rights.owner ∧
    (target.rights.read = true → source.rights.read = true) ∧
    (target.rights.write = true → source.rights.write = true) := by
  cases hsR : source.rights.read <;> cases htR : target.rights.read <;>
    cases hsW : source.rights.write <;> cases htW : target.rights.write <;>
    simp_all [attenuates]

/-- Repeated permission restriction preserves the same target, space and owner. -/
theorem attenuates_trans (source middle target : DataCapTy)
    (first : source.attenuates middle = true)
    (second : middle.attenuates target = true) : source.attenuates target = true := by
  obtain ⟨hs, ht, ho, hr, hw⟩ := attenuates_sound source middle first
  obtain ⟨hs₂, ht₂, ho₂, hr₂, hw₂⟩ := attenuates_sound middle target second
  have spaceEq := hs.trans hs₂
  have targetEq := ht.trans ht₂
  have ownerEq := ho.trans ho₂
  cases sr : source.rights.read <;> cases tr : target.rights.read <;>
    cases sw : source.rights.write <;> cases tw : target.rights.write <;>
    simp_all [attenuates]

end DataCapTy
end Gabbro.Grammatik
