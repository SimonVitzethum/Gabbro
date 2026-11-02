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

theorem write_only_zeuge :
    (table 0 (false, true)).rights.read = false ∧
    (table 0 (false, true)).rights.write = true ∧
    attenuates (table 0 (true, true)) (table 0 (false, true)) = true ∧
    attenuates (table 0 (false, true)) (table 0 (true, true)) = false := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem attenuates_sound_zeuge :
    let source := table 7 (true, true) 1
    let target := table 7 (false, true) 1
    source.space = target.space ∧ source.target = target.target ∧ source.rights.owner = target.rights.owner ∧
      (target.rights.read = true → source.rights.read = true) ∧
      (target.rights.write = true → source.rights.write = true) :=
  attenuates_sound _ _ rfl

end DataCapTy
end Gabbro.Grammatik
