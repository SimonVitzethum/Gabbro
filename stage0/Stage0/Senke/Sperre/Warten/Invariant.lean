/- The word invariant at sequential ticket-lock boundaries. Preservation by
   interfering threads still requires a separate rely relation. -/
module
public import Stage0.Senke.Sperre.Ticket.Paar
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner Runner.IR Runner.Mem

/-- Outstanding tickets and registered waiters, independent of a thread's frame.
    The strict 32-bit bound prevents a full futex comparison cycle among the
    outstanding tickets; the ticket and serving words themselves may wrap. -/
def TicketInvW (T : Nat) (n s w : W) : Prop :=
  (n - s).toNat ≤ T ∧ w.toNat ≤ (n - s).toNat ∧
    w.toNat < 2 ^ 62 ∧ (n - s).toNat < 2 ^ 32

/-- A draw needs room both in the thread bound and in the strict futex bound.
    The former alone is insufficient when T is at least 2^32. -/
theorem TicketInvW.draw {T : Nat} {n s w : W} (h : TicketInvW T n s w)
    (room : (n - s).toNat + 1 ≤ T) (width : (n - s).toNat + 1 < 2 ^ 32) :
    TicketInvW T (n + 1) s w := by
  have eq : n + 1 - s = (n - s) + 1 := by bv_omega
  have count : (n + 1 - s).toNat = (n - s).toNat + 1 := by
    rw [eq, BitVec.toNat_add]
    change ((n - s).toNat + 1) % 2 ^ 64 = (n - s).toNat + 1
    omega
  unfold TicketInvW at h ⊢
  rw [count]
  exact ⟨room, by omega, h.2.2.1, width⟩

/-- Registering a waiter consumes one outstanding non-waiting ticket. -/
theorem TicketInvW.increment {T : Nat} {n s w : W} (h : TicketInvW T n s w)
    (room : w.toNat + 1 ≤ (n - s).toNat) : TicketInvW T n s (w + 1) := by
  obtain ⟨threads, waiters, bound, width⟩ := h
  have count : (w + 1).toNat = w.toNat + 1 := by
    simp only [BitVec.toNat_add]
    change (w.toNat + 1) % 2 ^ 64 = w.toNat + 1
    omega
  unfold TicketInvW
  rw [count]
  exact ⟨threads, room, by omega, width⟩

/-- A returning registered waiter removes its own entry without underflow. -/
theorem TicketInvW.decrement {T : Nat} {n s w : W} (h : TicketInvW T n s w)
    (positive : 0 < w.toNat) : TicketInvW T n s (w - 1) := by
  obtain ⟨threads, waiters, bound, width⟩ := h
  have count : (w - 1).toNat = w.toNat - 1 := by
    rw [BitVec.toNat_sub_of_le (show (1 : W) ≤ w from by
      rw [BitVec.le_def]; change 1 ≤ w.toNat; omega)]
    rfl
  unfold TicketInvW
  rw [count]
  exact ⟨threads, by omega, by omega, width⟩

/-- The giver is one outstanding ticket and is not a registered waiter. -/
theorem TicketInvW.give {T : Nat} {n s w : W} (h : TicketInvW T n s w)
    (holder : w.toNat + 1 ≤ (n - s).toNat) : TicketInvW T n (s + 1) w := by
  obtain ⟨threads, waiters, bound, width⟩ := h
  have eq : n - (s + 1) = (n - s) - 1 := by bv_omega
  have count : (n - (s + 1)).toNat = (n - s).toNat - 1 := by
    rw [eq, BitVec.toNat_sub_of_le (show (1 : W) ≤ n - s from by
      rw [BitVec.le_def]; change 1 ≤ (n - s).toNat; omega)]
    rfl
  unfold TicketInvW
  rw [count]
  exact ⟨by omega, by omega, bound, by omega⟩

/-- The thread bound alone does not preserve the strict 32-bit clause. -/
theorem TicketInvW.draw_width_zeuge :
    TicketInvW (2 ^ 32) 4294967295 0 0 ∧
    ((4294967295 : W) - 0).toNat + 1 ≤ 2 ^ 32 ∧
    ¬ TicketInvW (2 ^ 32) (4294967295 + 1) 0 0 := by
  unfold TicketInvW
  decide

end Gabbro.Stage0.Senke
