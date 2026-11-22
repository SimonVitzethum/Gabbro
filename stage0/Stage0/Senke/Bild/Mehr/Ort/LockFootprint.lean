module

public import Stage0.Senke.Bild.Mehr.Ort.LockState
public import Stage0.Senke.Bild.Mehr.ImageTransition
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace Gabbro.Stage0.Senke.Faeden

open Gabbro.Grammatik Gabbro.Grammatik.Parser.UebersetzeAllg Runner

def Zelle.carrier {D : Deklaration} : Senke.Zelle D → D.Tab ⊕ D.Glob
  | .glob global => .inr global
  | .elem table .. => .inl table

/-- A protected cell is private only to a thread holding all the
    guards required by its carrier. A cell with no guard is not
    assigned on the basis of the lock state. -/
def protectedCellFootprint {D : Deklaration} (layout : Lay D) (source : RufMaschineG D)
    (thread : Nat) (address : W) : Prop :=
  ∃ cell : Senke.Zelle D, cell.da layout ∧
    cell.adr layout ≤ address.toNat ∧ address.toNat < cell.adr layout + cell.bytes ∧
    (∃ guard, Bewacht (Zelle.carrier cell) guard) ∧
    ∀ guard, Bewacht (Zelle.carrier cell) guard → guard ∈ offen (source.faeden thread).spur

theorem protectedCellFootprint_bounds {D : Deklaration} {layout : Lay D}
    {source : RufMaschineG D} {thread : Nat} {address : W}
    (inLayout : LayIn layout) (owned : protectedCellFootprint layout source thread address) :
    layout.lo ≤ address.toNat ∧ address.toNat < layout.hi := by
  obtain ⟨cell, allocated, first, last, _, _⟩ := owned
  have inside : layout.lo ≤ cell.adr layout ∧ cell.adr layout + cell.bytes ≤ layout.hi := by
    cases cell with
    | glob global => exact inLayout.2.1 global
    | elem table field index => exact inLayout.1 table field index allocated
  exact ⟨inside.1.trans first, last.trans_le inside.2⟩

/-- Distinct allocated cells cannot overlap. If the same cell was
    claimed twice, its physical ticket queue identifies the same owner. -/
theorem ImageTicketStates.protected_exclusive {D : Deklaration} {N : Nat}
    {layout : Lay D} {memory : Mem} {source : RufMaschineG D} {states : D.Lock → Zustand N}
    (locks : ImageTicketStates layout memory source states) (cells : LayDis layout)
    {first second : Nat} {address : W}
    (left : protectedCellFootprint layout source first address)
    (right : protectedCellFootprint layout source second address) : first = second := by
  obtain ⟨cell, existsLeft, lowLeft, highLeft, ⟨guard, guards⟩, firstOwns⟩ := left
  obtain ⟨other, existsRight, lowRight, highRight, _, secondOwns⟩ := right
  have equalCell : cell = other := by
    by_contra different
    rcases cells.spans cell other existsLeft existsRight different with before | after <;> omega
  subst other
  have heldLeft := firstOwns guard guards
  have heldRight := secondOwns guard guards
  have firstInside : first < N := by
    by_contra outside
    exact (locks.owners guard).outside first (Nat.le_of_not_gt outside) heldLeft
  have secondInside : second < N := by
    by_contra outside
    exact (locks.owners guard).outside second (Nat.le_of_not_gt outside) heldRight
  have leftTicket := ((locks.owners guard).inside ⟨first, firstInside⟩).mpr heldLeft
  have rightTicket := ((locks.owners guard).inside ⟨second, secondInside⟩).mpr heldRight
  exact congrArg Fin.val ((locks.protocol guard).ausschluss leftTicket rightTicket)

theorem protectedCellFootprint_lock_disjoint {D : Deklaration} {layout : Lay D}
    {source : RufMaschineG D} {thread : Nat} {address : W} {locked : D.Lock}
    (inLayout : LayIn layout) (synchronized : LaySync layout)
    (owned : protectedCellFootprint layout source thread address) : ¬ LockBytes layout locked address := by
  intro lockByte
  exact (Nat.not_le_of_lt (protectedCellFootprint_bounds inLayout owned).2)
    ((synchronized.1 locked).1.trans lockByte.1)

/-- The image's fixed stack reservation and the currently protected
    cells use the same TSO projection. Other carrier permissions are
    handled by their own source access rules. -/
def imageProtectedFootprint {src : String} {reserve : Nat} {options : Profil.Options}
    (output : Emitted src reserve options) (source : RufMaschineG (declOf output.compiled.unit).mitRuhe)
    (thread : Nat) (address : W) : Prop :=
  imageStackFootprint output thread address ∨
    protectedCellFootprint output.image.Y.withIdle source thread address

theorem imageProtectedFootprint_exclusive {src : String} {reserve : Nat} {options : Profil.Options}
    {output : Emitted src reserve options} {source : RufMaschineG (declOf output.compiled.unit).mitRuhe}
    {N : Nat} {memory : Mem} {states : _ → Zustand N}
    (locks : ImageTicketStates output.image.Y.withIdle memory source states)
    (inLayout : LayIn output.image.Y.withIdle) (cells : LayDis output.image.Y.withIdle)
    {first second : Nat} {address : W}
    (left : imageProtectedFootprint output source first address)
    (right : imageProtectedFootprint output source second address) : first = second := by
  rcases left with left | left <;> rcases right with right | right
  · exact imageStackFootprint_disjoint left right
  · exact ((Nat.not_le_of_lt (imageStackFootprint_before_world left))
      (protectedCellFootprint_bounds inLayout right).1).elim
  · exact ((Nat.not_le_of_lt (imageStackFootprint_before_world right))
      (protectedCellFootprint_bounds inLayout left).1).elim
  · exact locks.protected_exclusive cells left right

end Gabbro.Stage0.Senke.Faeden
