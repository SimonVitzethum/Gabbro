module

public import Grammatik.Kern.Syntax.Marken.Owner.Flow

@[expose] public section

namespace Gabbro.Grammatik

/-- A resolved source ghost binder. The name is a binder identity assigned by
    name resolution, not a runtime epoch and not a `Ty` value. -/
structure OwnerBinding (Marke : Type) where
  binder : Nat
  mark : Marke
  stage : Nat
  deriving DecidableEq, Repr

/-- The linear ghost environment, separate from the copyable value environment.
    At most one source binding names any nominal owner, at any stage. -/
abbrev OwnerBindings (Marke : Type) := List (OwnerBinding Marke)

namespace OwnerBindings

variable {Marke : Type} [DecidableEq Marke]

def Valid (bs : OwnerBindings Marke) : Prop :=
  (bs.map OwnerBinding.binder).Nodup ∧ (bs.map OwnerBinding.mark).Nodup

instance (bs : OwnerBindings Marke) : Decidable (Valid bs) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Resource interpretation: ghost bindings do not emit a machine word. -/
def resources {D : Deklaration} (bs : OwnerBindings D.Marke) : List (Res D) :=
  bs.map (fun b => Res.marke b.mark b.stage)

/-- Moving a source variable consumes the old binder before rebinding the
    same nominal identity. A fresh binder cannot overwrite another variable. -/
def move (bs : OwnerBindings Marke) (sourceBinder into : Nat) : Option (OwnerBindings Marke) :=
  match bs.find? (fun b => b.binder == sourceBinder) with
  | none => none
  | some b =>
      let rest := bs.erase b
      if Valid bs ∧ Valid ({ b with binder := into } :: rest) then
        some ({ b with binder := into } :: rest)
      else none

/-- Handoff/loan entry removes the lender's binding. Restoring it requires
    a checked return from the same dynamic frame escrow, not a value copy. -/
def take (bs : OwnerBindings Marke) (binder : Nat) :
    Option (OwnerBinding Marke × OwnerBindings Marke) :=
  match bs.find? (fun b => b.binder == binder) with
  | none => none
  | some b => if Valid bs then some (b, bs.erase b) else none

/-- Receiving a returned owner cannot duplicate either its binder or identity.
    This operation alone does not authorize a return; the machine must supply
    the saved escrow and the `OwnerFlow` outcome for this exact call. -/
def restore (bs : OwnerBindings Marke) (b : OwnerBinding Marke) :
    Option (OwnerBindings Marke) :=
  if Valid (b :: bs) then some (b :: bs) else none

/-- Every interpreted resource has its unique source binding as provenance. -/
theorem resource_from_binding {D : Deklaration} (bs : OwnerBindings D.Marke)
    {m : D.Marke} {s : Nat} (h : Res.marke m s ∈ resources bs) :
    ∃ b ∈ bs, b.mark = m ∧ b.stage = s := by
  obtain ⟨b, hb, he⟩ := List.mem_map.mp h
  cases he
  exact ⟨b, hb, rfl, rfl⟩

/-- Source rename does not change resource identity or stage, including its
    multiplicity. This is an equality of interpretations, not just membership. -/
theorem move_resources {D : Deklaration} {bs bs' : OwnerBindings D.Marke}
    {sourceBinder into : Nat} (h : move bs sourceBinder into = some bs') :
    ∃ b ∈ bs, resources bs' =
      Res.marke b.mark b.stage :: resources (bs.erase b) := by
  unfold move at h
  split at h
  · cases h
  · rename_i b hb
    dsimp only at h
    split at h
    · cases h
      exact ⟨b, List.mem_of_find?_eq_some hb, rfl⟩
    · cases h

/-- Source moves retain binder and nominal-owner uniqueness. -/
theorem move_valid {bs bs' : OwnerBindings Marke} {sourceBinder into : Nat}
    (h : move bs sourceBinder into = some bs') : Valid bs' := by
  unfold move at h
  split at h
  · cases h
  · dsimp only at h
    split at h
    · rename_i hv
      cases h
      exact hv.2
    · cases h

/-- Taking a binding removes one occurrence, preserving both source and resource
    multiplicity. The source cannot retain an independent alias of that owner. -/
theorem take_resources {D : Deklaration} {bs rest : OwnerBindings D.Marke}
    {binder : Nat} {b : OwnerBinding D.Marke} (h : take bs binder = some (b, rest)) :
    List.Perm (resources bs) (Res.marke b.mark b.stage :: resources rest) := by
  unfold take at h
  split at h
  · cases h
  · rename_i entry he
    split at h
    · cases h
      exact (List.perm_cons_erase (List.mem_of_find?_eq_some he)).map
        (fun x => Res.marke x.mark x.stage)
    · cases h

/-- Renaming a ghost variable preserves the complete resource multiset. -/
theorem move_resource_perm {D : Deklaration} {bs bs' : OwnerBindings D.Marke}
    {sourceBinder into : Nat} (h : move bs sourceBinder into = some bs') :
    List.Perm (resources bs) (resources bs') := by
  obtain ⟨b, hb, hr⟩ := move_resources h
  rw [hr]
  exact (List.perm_cons_erase hb).map (fun x => Res.marke x.mark x.stage)

/-- All accepted receives preserve source-name and nominal-owner uniqueness. -/
theorem restore_valid {bs bs' : OwnerBindings Marke} {b : OwnerBinding Marke}
    (h : restore bs b = some bs') : Valid bs' := by
  unfold restore at h
  split at h
  · rename_i hv
    cases h
    exact hv
  · cases h

/-- A failed lookup cannot manufacture an owner binding. -/
theorem take_missing (bs : OwnerBindings Marke) (binder : Nat)
    (h : bs.find? (fun b => b.binder == binder) = none) : take bs binder = none := by
  simp only [take, h]

end OwnerBindings

end Gabbro.Grammatik
