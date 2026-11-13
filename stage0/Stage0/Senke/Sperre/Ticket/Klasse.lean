/-
  File:      stage0/Stage0/Senke/Sperre/Ticket/Klasse.lean
  Subject:   The class a statement keeps of a ticket lock (`TicketKlasse`): for the words next `n`, serving `s`
              and waiters `w` read at `a`, `a + 8`, `a + 16` in `m`, the words `n'`, `s'`, `w'` in `m'` are
              readable with `n' - s' = n - s` (BitVec subtraction) and `w' = w`. The difference is what the
              free/mine invariant needs; equal words keep it (`ofLock`).
-/
module
public import Stage0.Senke.Welt.WeltAt
@[expose] public section


namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner Runner.IR Runner.Mem

/-- What a statement keeps of the ticket lock at `a`: its difference and its waiters. -/
def TicketKlasse (m m' : Mem) (a : Nat) : Prop :=
  ∀ n s w, m.rd64 (BitVec.ofNat 64 a) = some n → m.rd64 (BitVec.ofNat 64 (a + 8)) = some s →
    m.rd64 (BitVec.ofNat 64 (a + 16)) = some w →
    ∃ n' s' w', m'.rd64 (BitVec.ofNat 64 a) = some n' ∧ m'.rd64 (BitVec.ofNat 64 (a + 8)) = some s' ∧
      m'.rd64 (BitVec.ofNat 64 (a + 16)) = some w' ∧ n' - s' = n - s ∧ w' = w

theorem TicketKlasse.refl (m : Mem) (a : Nat) : TicketKlasse m m a :=
  fun _ _ _ h1 h2 h3 => ⟨_, _, _, h1, h2, h3, rfl, rfl⟩

theorem TicketKlasse.trans {m1 m2 m3 : Mem} {a : Nat} (h1 : TicketKlasse m1 m2 a)
    (h2 : TicketKlasse m2 m3 a) : TicketKlasse m1 m3 a := fun n s w e1 e2 e3 => by
  obtain ⟨n1, s1, w1, f1, f2, f3, d1, q1⟩ := h1 n s w e1 e2 e3
  obtain ⟨n2, s2, w2, g1, g2, g3, d2, q2⟩ := h2 n1 s1 w1 f1 f2 f3
  exact ⟨n2, s2, w2, g1, g2, g3, by rw [d2, d1], by rw [q2, q1]⟩

/-- Equal words keep the ticket class: the old owner-lock class implies the new one. -/
theorem TicketKlasse.ofLock {m m' : Mem} {a : Nat} (h : LockKlasse m m' a) : TicketKlasse m m' a :=
  fun n s w e1 e2 e3 => by
    have z0 : a + 8 * 0 = a := by omega
    have z1 : a + 8 * 1 = a + 8 := by omega
    have z2 : a + 8 * 2 = a + 16 := by omega
    have e0 := h 0 (by omega)
    have e1' := h 1 (by omega)
    have e2' := h 2 (by omega)
    rw [z0] at e0
    rw [z1] at e1'
    rw [z2] at e2'
    have f0 : m'.rd64 (BitVec.ofNat 64 a) = some n := by rw [e0]; exact e1
    have f1 : m'.rd64 (BitVec.ofNat 64 (a + 8)) = some s := by rw [e1']; exact e2
    have f2 : m'.rd64 (BitVec.ofNat 64 (a + 16)) = some w := by rw [e2']; exact e3
    exact ⟨n, s, w, f0, f1, f2, rfl, rfl⟩

end Gabbro.Stage0.Senke
