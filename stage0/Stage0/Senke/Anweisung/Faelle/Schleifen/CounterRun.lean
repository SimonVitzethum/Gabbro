import Stage0.Senke.Anweisung.Faelle.Schleifen.CounterCall

namespace Gabbro.Stage0.Senke.CounterCallProbe
open Gabbro.Grammatik Runner.IR Runner.Mem FnptrProben
set_option maxRecDepth 100

local instance (m : Runner.Mem) (pc : Runner.W) (o : Nat) (a b c : BitVec 32) :
    Decidable (InsAt m pc o a b c) :=
  if h : m.rd8 pc = some (BitVec.ofNat 8 o) ∧ m.rd32 (pc + 4) = some a ∧
      m.rd32 (pc + 8) = some b ∧ m.rd32 (pc + 12) = some c then
    .isTrue ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩
  else .isFalse (fun h' => h ⟨h'.op, h'.f1, h'.f2, h'.f3⟩)

theorem counter_facts : ∀ j : Fin 2,
    InsAt (loaded ⟨j.val + 1, by omega⟩) 2016 19 6
      (II.f (16 * (code.length + 3 : Nat))) 0 ∧
    InsAt (loaded ⟨j.val + 1, by omega⟩) 2032 4 6 6 5 ∧
    (loaded ⟨j.val + 1, by omega⟩).rd64 (slot 4096 6) = some (BitVec.ofNat 64 (j.val + 1)) ∧
    (loaded ⟨j.val + 1, by omega⟩).rd64 (slot 4096 5) = some 1 := by
  apply allFin
  decide +kernel

theorem counter_overwrite (m : Runner.Mem) (a : Runner.W) (size old new : Nat) :
    write (write m a size old) a size new = write m a size new := by
  cases m
  simp only [Runner.Mem.write]
  congr 1
  funext x
  split <;> rfl

theorem counter_edges : ∀ b : Fin 3, InsAt (loaded b) (2048 + BitVec.ofNat 64 (16 * code.length)) 18
    (II.f (-(16 * (code.length + 2 : Nat)))) 0 0 := by
  apply allFin
  decide +kernel

theorem counter_values (b : Fin 3) :
    (loaded b).rd64 (slot 4096 (BitVec.ofNat 64 6)) = some (BitVec.ofNat 64 b.val) := by
  have small : b.val < 2 ^ 64 := by have := b.isLt; omega
  have h := rd64_write_same (w := BitVec.ofNat 64 b.val) (frame.rd 6 (by decide))
  simpa only [loaded, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small] using h

theorem sentinel_values (b : Fin 3) : (loaded b).rd64 (slot 4096 4) = some 77 := by
  have h := rd64_agree_out (a := 4128)
    (counter_protected (m := memory) (fp := 4096) (counter := 6) (by decide) b.val)
    (by decide) (Or.inl (by decide))
  change (loaded b).rd64 (slot 4096 4) = memory.rd64 (slot 4096 4) at h
  exact h.trans (by decide +kernel)

/-- Positive budgets execute the real test and decrement, then the emitted
    store/call block and backward jump. All interfaces hold in the same memory. -/
theorem positive_counter_zeuge [Kern] (n : Fin 2) :
    ∃ m', Star ⟨2016, 4096⟩ (loaded ⟨n.val + 1, by omega⟩) ⟨2016, 4096⟩ m' ∧
      m'.rd64 (slot 4096 (BitVec.ofNat 64 6)) = some (BitVec.ofNat 64 n.val) ∧
      m'.rd64 (slot 4096 (BitVec.ofNat 64 4)) = some 77 := by
  let before := loaded ⟨n.val + 1, by omega⟩
  let after := loaded ⟨n.val, by omega⟩
  obtain ⟨test, dec, count, unit⟩ := counter_facts n
  have nz := (counter_fuel_step n.val (by have := n.isLt; omega)).1
  have write : before.wr64 (slot 4096 (BitVec.ofNat 64 6)) (BitVec.ofNat 64 (n.val + 1) - 1) = some after := by
    rw [(counter_fuel_step n.val (by have := n.isLt; omega)).2]
    have hw := wr64_some (v := BitVec.ofNat 64 n.val)
      ((loaded_frame ⟨n.val + 1, by omega⟩).wr 6 (by decide))
    have small : n.val < 2 ^ 64 := by have := n.isLt; omega
    simpa only [before, after, loaded, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt small, counter_overwrite] using hw
  have first := Star.one (counter_positive (t := ⟨2016, 4096⟩) test count nz)
  have second := Star.one (counter_decrement (t := ⟨2032, 4096⟩) dec count unit write)
  have edge : InsAt after (2048 + BitVec.ofNat 64 (16 * code.length)) 18
      (II.f (-(16 * (code.length + 2 : Nat)))) 0 0 := by
    exact counter_edges ⟨n.val, by omega⟩
  have stored : after.rd64 (slot 4096 (BitVec.ofNat 64 6)) = some (BitVec.ofNat 64 n.val) := by
    exact counter_values ⟨n.val, by omega⟩
  obtain ⟨m', run, _, _, _, kept, counter⟩ := Reach.counter_backedge
    (body_simulation_at (m := after) (loaded_pre ⟨n.val, by omega⟩)
      (loaded_surroundings ⟨n.val, by omega⟩) (loaded_head ⟨n.val, by omega⟩)
      (loaded_world ⟨n.val, by omega⟩))
    call_win (counter := 6) (Or.inr (by simp)) (by decide) stored edge
    (by unfold CodeFar; decide +kernel)
  refine ⟨m', first.trans (second.trans ?_), counter, ?_⟩
  · change Star ⟨2048, 4096⟩ after ⟨2016, 4096⟩ m'
    have target : (2048 : Runner.W) + BitVec.ofNat 64 (16 * code.length) +
        sx (II.f (-(16 * (code.length + 2 : Nat)))) = 2016 := by decide +kernel
    simpa only [target] using run
  · rw [kept 4 (by simp)]
    exact sentinel_values ⟨n.val, by omega⟩

/-- Budget zero branches directly to the emitted progress exit. -/
theorem zero_counter_zeuge [Kern] : Stops ⟨2016, 4096⟩ (loaded 0) 111 := by
  have test : InsAt (loaded 0) 2016 19 6
      (II.f (16 * (code.length + 3 : Nat))) 0 := by decide +kernel
  have zero : (loaded 0).rd64 (slot 4096 (sx (6 : BitVec 32))) = some 0 := by
    decide +kernel
  apply counter_budget_stop_code test zero (K := 256) (scratch := 8)
  · have h : ∀ k : Fin (stopC 111 8).length,
        InsAt (loaded 0)
          (2016 + sx (II.f (16 * (code.length + 3 : Nat))) + BitVec.ofNat 64 (16 * k.val))
          (stopC 111 8)[k.val].o (II.f (stopC 111 8)[k.val].a)
          (II.f (stopC 111 8)[k.val].b) (II.f (stopC 111 8)[k.val].c) := by
      apply allFin
      decide +kernel
    exact fun k hk => h ⟨k, hk⟩
  · unfold CodeFar
    decide +kernel
  · exact loaded_frame 0
  · decide
  · decide

end Gabbro.Stage0.Senke.CounterCallProbe
