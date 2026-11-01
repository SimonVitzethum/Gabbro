module

public import Grammatik.Kern.Semantik.Semantik
public import Grammatik.Kern.Syntax.Koernung.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}

/-- Every inventory row lands somewhere: admitted, refused with its
    guarantee, or the open volatile row. There is no fourth case -- ruling
    a tenth row means extending this proof, which is the point. -/
theorem ruling_covers (f : InvForm) :
    f.admitted ∨ (∃ g, f.verdict = some g) ∨ f = .volatileReg := by
  cases f with
  | slotPlain => exact Or.inl True.intro
  | globalPlain => exact Or.inl True.intro
  | slotCompound => exact Or.inr (Or.inl ⟨_, rfl⟩)
  | guardedCompound => exact Or.inr (Or.inl ⟨_, rfl⟩)
  | cas => exact Or.inl True.intro
  | relAcq => exact Or.inl True.intro
  | mergeAdd => exact Or.inr (Or.inl ⟨_, rfl⟩)
  | lockOps => exact Or.inl True.intro
  | volatileReg => exact Or.inr (Or.inr rfl)

/-- Admitted rows are single-access: their width fits one atomic event. -/
theorem admitted_width_le_one (f : InvForm) (h : f.admitted) : f.width ≤ 1 := by
  cases f with
  | slotPlain => decide
  | globalPlain => decide
  | slotCompound => simp only [InvForm.admitted] at h
  | guardedCompound => simp only [InvForm.admitted] at h
  | cas => decide
  | relAcq => decide
  | mergeAdd => simp only [InvForm.admitted] at h
  | lockOps => decide
  | volatileReg => simp only [InvForm.admitted] at h

/-- Admitted rows cannot tear: one atomic event covers the whole transfer,
    so every split shows the old or the new bytes. -/
theorem admitted_no_tear (f : InvForm) (h : f.admitted)
    (old new : List Byte) (hlen : old.length = new.length)
    (hold : old.length = f.width) (m : Nat) :
    interrupted old new m = old ∨ interrupted old new m = new := by
  have hw := admitted_width_le_one f h
  have hb : new.length ≤ 1 := by omega
  exact width_le_one_no_tear old new hlen hb m

/-- The discipline premise, in the ruling's words as a proposition: no
    observer sees the middle of the transfer. Exclusive access (lock held,
    no second thread inside) and single-writer-per-cell (each core its own
    cell, the merge loop only reads) both mean exactly this: an interruption
    sits at a boundary -- before the first byte or past the last. -/
def AtBoundary (_old new : List Byte) (m : Nat) : Prop :=
  m = 0 ∨ new.length ≤ m

/-- At a boundary there is no tear, at any width: before the first byte
    shows old, past the last byte shows new. -/
theorem boundary_no_tear (old new : List Byte) (hlen : old.length = new.length)
    (m : Nat) (h : AtBoundary old new m) :
    interrupted old new m = old ∨ interrupted old new m = new := by
  rcases h with rfl | hle
  · left; exact interrupted_zero_eq old new
  · right; exact interrupted_full_eq old new hlen m hle

/-- Refused rows cannot tear UNDER their guarantee: the guarantee is the
    boundary premise (`AtBoundary`), and the boundary rules out the middle
    (`boundary_no_tear`). The verdict equality travels as an explicit
    hypothesis so the theorem is about refused rows, not about any lists. -/
theorem refused_no_tear (f : InvForm) (g : Guarantee)
    (h : f.verdict = some g) (old new : List Byte)
    (hlen : old.length = new.length) (m : Nat) (hd : AtBoundary old new m) :
    interrupted old new m = old ∨ interrupted old new m = new := by
  cases g
  · exact boundary_no_tear old new hlen m hd
  · exact boundary_no_tear old new hlen m hd

/-- World-level readback of an admitted transfer: writing the admitted row's
    bytes over a byte carrier and reading back shows old or new whole.
    The per-byte version holds unconditionally (`prefix_readback_perByte`);
    this is the whole-list version the no-tearing claim needs. -/
theorem admitted_readback_no_tear (σ : World D) (t : D.Tab) (f : D.Feld t)
    (hf : D.typ t f = .int 0 255) (Λ : List (Res D))
    (form : InvForm) (hadm : form.admitted)
    (k : Int) (m : Nat) (old new : List Byte)
    (hold : old = σ.bytesAb t f hf form.width k)
    (hnew : new.length = form.width) :
    ((σ.schreibBytes t f hf Λ k (new.take m)).bytesAb t f hf form.width k) = old ∨
    ((σ.schreibBytes t f hf Λ k (new.take m)).bytesAb t f hf form.width k) = new := by
  rw [schreibBytes_prefix_readback t f hf Λ form.width m k σ old new hold hnew]
  have hlen : old.length = new.length := by rw [hold, World.bytesAb_length]; omega
  have holdw : old.length = form.width := by rw [hold, World.bytesAb_length]
  exact admitted_no_tear form hadm old new hlen holdw m

/-- World-level readback of a refused-but-disciplined transfer: under the
    guarantee the readback is old or new whole, at any width. -/
theorem refused_readback_no_tear (σ : World D) (t : D.Tab) (f : D.Feld t)
    (hf : D.typ t f = .int 0 255) (Λ : List (Res D))
    (form : InvForm) (g : Guarantee) (href : form.verdict = some g)
    (k : Int) (n m : Nat) (old new : List Byte)
    (hold : old = σ.bytesAb t f hf n k)
    (hnew : new.length = n) (hd : AtBoundary old new m) :
    ((σ.schreibBytes t f hf Λ k (new.take m)).bytesAb t f hf n k) = old ∨
    ((σ.schreibBytes t f hf Λ k (new.take m)).bytesAb t f hf n k) = new := by
  rw [schreibBytes_prefix_readback t f hf Λ n m k σ old new hold hnew]
  have hlen : old.length = new.length := by rw [hold, World.bytesAb_length]; omega
  exact refused_no_tear form g href old new hlen m hd

/-- The guarantee is load-bearing: the mid-interruption it rules out (one
    byte of two written) IS the witnessed tear. A discipline that admitted
    the middle would admit the mix. -/
theorem mid_interruption_tears :
    torn [⟨0, by omega, by omega⟩, ⟨0, by omega, by omega⟩]
         [⟨1, by omega, by omega⟩, ⟨1, by omega, by omega⟩]
         (interrupted [⟨0, by omega, by omega⟩, ⟨0, by omega, by omega⟩]
            [⟨1, by omega, by omega⟩, ⟨1, by omega, by omega⟩] 1) := by
  rw [two_byte_tear_is_interruption]
  exact two_byte_tear

/-- **C2 discharged for the measured inventory: no tearing on shared
    carriers under the ruling.** Every inventory row is shared-carrier
    traffic (see `InvForm`); the ruling leaves each row exactly one way
    out: admitted rows show old or new by width, refused rows show old or
    new under their guarantee (no observer sees the middle), and the open
    volatile row gets no claim -- the disjunction says so explicitly
    instead of going silent. -/
theorem shared_inventory_tearing_free (form : InvForm)
    (old new : List Byte) (hlen : old.length = new.length) (m : Nat)
    (h : (form.admitted ∧ old.length = form.width) ∨
         (∃ g, form.verdict = some g ∧ AtBoundary old new m) ∨
         form = .volatileReg) :
    form = .volatileReg ∨
      interrupted old new m = old ∨ interrupted old new m = new := by
  rcases h with ⟨hadm, hlenw⟩ | ⟨g, href, hdisc⟩ | rfl
  · exact Or.inr (admitted_no_tear form hadm old new hlen hlenw m)
  · exact Or.inr (refused_no_tear form g href old new hlen m hdisc)
  · exact Or.inl rfl

#print axioms EreignisAtomar
#print axioms atomar_no_tear
#print axioms schreibBytes_event_count
#print axioms schreibBytes_not_single
#print axioms leseBytes_single_event
#print axioms leseBytes_not_atomic
#print axioms two_byte_tear
#print axioms two_byte_tear_is_interruption
#print axioms ereignisAtomar_gilt
#print axioms width_le_one_no_tear
#print axioms castBytes_cancel
#print axioms schreibSlot_slots_same
#print axioms schreibSlot_slots_other
#print axioms merke_bytesAb
#print axioms storeSlot_bytesAb_other
#print axioms schreibBytes_slots_other
#print axioms oldOrNewPerByte
#print axioms interrupted_length_eq
#print axioms interrupted_zero_eq
#print axioms interrupted_full_eq
#print axioms interrupted_perByte
#print axioms schreibBytes_prefix_readback
#print axioms prefix_readback_perByte
#print axioms prefix_readback_zero
#print axioms prefix_readback_full
#print axioms ruling_covers
#print axioms admitted_width_le_one
#print axioms admitted_no_tear
#print axioms AtBoundary
#print axioms boundary_no_tear
#print axioms refused_no_tear
#print axioms admitted_readback_no_tear
#print axioms refused_readback_no_tear
#print axioms mid_interruption_tears
#print axioms shared_inventory_tearing_free

end Gabbro.Grammatik
