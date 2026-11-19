/- Instruction bounds for the actual counter control flow. -/
module
public import Stage0.Senke.Images.BildLese
public import Stage0.Senke.Anweisung.Faelle.Schleifen.Counted.Teil3
public import Stage0.Senke.Anweisung.Faelle.Schleifen.Runtime.Teil2
@[expose] public section


namespace Gabbro.Stage0.Senke
open Runner Runner.IR
variable [Kern]
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000

/-- Counter induction with terminal body outcomes, including early leave,
    return and a pending hardware request. The body obligation is one actual
    pass after the decrement; continuing passes execute the real backedge.
    A source `next` already reaches the header and executes no backedge.
    `Done` describes the terminal machine state and may include `StopAt`.
    The bound counts S0IR instructions, independently of source passes and
    G steps. This control-flow theorem alone is not a source certificate. -/
theorem counted_counter_loop_exits
    (I : Nat → Mem → Prop) (Done : T → Mem → Prop) (pc fp back : W)
    (counter one jump : BitVec 32) (bodyLimit : Nat)
    (test : ∀ n m, I n m → InsAt m pc 19 counter jump 0)
    (count : ∀ n m, I n m →
      m.rd64 (slot fp (sx counter)) = some (BitVec.ofNat 64 n))
    (decrement : ∀ n m, I (n + 1) m →
      InsAt m (pc + 16) 4 counter counter one)
    (unit : ∀ n m, I n m → m.rd64 (slot fp (sx one)) = some 1)
    (body : ∀ n m, I (n + 1) m → n + 1 < 2 ^ 64 →
      ∃ a b nb, m.wr64 (slot fp (sx counter)) (BitVec.ofNat 64 n) = some a ∧
        nb ≤ bodyLimit ∧
        ((Counted nb ⟨pc + 32, fp⟩ a ⟨back, fp⟩ b ∧
          InsAt b back 18 (BitVec.ofInt 32 (pc.toInt - back.toInt)) 0 0 ∧ I n b) ∨
         (Counted nb ⟨pc + 32, fp⟩ a ⟨pc, fp⟩ b ∧ I n b) ∨
         (∃ u, Counted nb ⟨pc + 32, fp⟩ a u b ∧ Done u b)))
    (edge : back + sx (BitVec.ofInt 32 (pc.toInt - back.toInt)) = pc)
    {budget m} (fits : budget < 2 ^ 64) (start : I budget m) :
    ∃ u b nb, nb ≤ budget * (bodyLimit + 3) + 1 ∧
      Counted nb ⟨pc, fp⟩ m u b ∧
      ((u = ⟨pc + sx jump, fp⟩ ∧ I 0 b) ∨ Done u b) := by
  induction budget generalizing m with
  | zero =>
    refine ⟨⟨pc + sx jump, fp⟩, m, 1, by omega, ?_, Or.inl ⟨rfl, start⟩⟩
    exact .next (counter_zero (test 0 m start) (count 0 m start)) (.refl _ _)
  | succ n ih =>
    obtain ⟨a, b, nb, write, bound, outcome⟩ := body n m start fits
    have first : Counted 1 ⟨pc, fp⟩ m ⟨pc + 16, fp⟩ m :=
      .next (counter_positive (test _ m start) (count _ m start)
        (counter_fuel_step n fits).1) (.refl _ _)
    have write' : m.wr64 (slot fp (sx counter))
        (BitVec.ofNat 64 (n + 1) - 1) = some a := by
      rw [(counter_fuel_step n fits).2]; exact write
    have second : Counted 1 ⟨pc + 16, fp⟩ m ⟨pc + 32, fp⟩ a := by
      have h := counter_decrement (t := ⟨pc + 16, fp⟩)
        (decrement n m start) (count _ m start) (unit _ m start) write'
      have eq : pc + 16 + 16 = pc + 32 := by rw [BitVec.add_assoc]; rfl
      have result := Counted.next h (Counted.refl _ _)
      change Counted 1 ⟨pc + 16, fp⟩ m ⟨pc + 16 + 16, fp⟩ a at result
      rw [eq] at result
      exact result
    rcases outcome with ⟨run, backCode, next⟩ | ⟨run, next⟩ | ⟨u, run, done⟩
    · have last : Counted 1 ⟨back, fp⟩ b ⟨pc, fp⟩ b := by
        have h := run_step (t := ⟨back, fp⟩) backCode (by decide)
          (run_jmp (t := ⟨back, fp⟩) backCode)
        simpa [edge] using Counted.next h (Counted.refl _ _)
      obtain ⟨u, c, nc, hc, rest, done⟩ := ih (by omega) next
      refine ⟨u, c, 1 + 1 + nb + 1 + nc, ?_,
        (((first.trans second).trans run).trans last).trans rest, done⟩
      rw [Nat.succ_mul]
      omega
    · obtain ⟨u, c, nc, hc, rest, done⟩ := ih (by omega) next
      refine ⟨u, c, 1 + 1 + nb + nc, ?_,
        ((first.trans second).trans run).trans rest, done⟩
      rw [Nat.succ_mul]
      omega
    · refine ⟨u, b, 1 + 1 + nb, ?_, (first.trans second).trans run, Or.inr done⟩
      rw [Nat.succ_mul]
      omega

/-- Local body contract for a counter loop. The body starts AFTER the actual
    decrement and ends BEFORE the actual backedge. Its bound includes all
    executed support and callees. Hardware-dependent bodies must discharge
    this contract under explicit hardware hypotheses; no latency is inferred
    from a declaration or from code length. `I` retains code and frame facts. -/
theorem counted_counter_loop
    (I : Nat → Mem → Prop) (pc fp back : W)
    (counter one jump : BitVec 32) (bodyLimit : Nat)
    (test : ∀ n m, I n m → InsAt m pc 19 counter jump 0)
    (count : ∀ n m, I n m →
      m.rd64 (slot fp (sx counter)) = some (BitVec.ofNat 64 n))
    (decrement : ∀ n m, I (n + 1) m →
      InsAt m (pc + 16) 4 counter counter one)
    (unit : ∀ n m, I n m → m.rd64 (slot fp (sx one)) = some 1)
    (body : ∀ n m, I (n + 1) m → n + 1 < 2 ^ 64 →
      ∃ a b nb, m.wr64 (slot fp (sx counter)) (BitVec.ofNat 64 n) = some a ∧
        nb ≤ bodyLimit ∧ Counted nb ⟨pc + 32, fp⟩ a ⟨back, fp⟩ b ∧
        InsAt b back 18 (BitVec.ofInt 32 (pc.toInt - back.toInt)) 0 0 ∧ I n b)
    (edge : back + sx (BitVec.ofInt 32 (pc.toInt - back.toInt)) = pc)
    {budget m} (fits : budget < 2 ^ 64) (start : I budget m) :
    ∃ b nb, nb ≤ budget * (bodyLimit + 3) + 1 ∧
      Counted nb ⟨pc, fp⟩ m ⟨pc + sx jump, fp⟩ b ∧ I 0 b := by
  obtain ⟨u, b, nb, bound, run, done⟩ := counted_counter_loop_exits I (fun _ _ => False)
    pc fp back counter one jump bodyLimit test count decrement unit
    (fun n m he hn => by
      obtain ⟨a, b, nb, write, bound, run, code, next⟩ := body n m he hn
      exact ⟨a, b, nb, write, bound, Or.inl ⟨run, code, next⟩⟩)
    edge fits start
  rcases done with ⟨rfl, final⟩ | impossible
  · exact ⟨b, nb, bound, run, final⟩
  · contradiction

end Gabbro.Stage0.Senke
