/- Instruction bounds for the actual counter control flow. -/
import Stage0.Senke.Ausdruck.FnptrAufrufProben
import Stage0.Senke.Anweisung.Faelle.Schleifen.Counted
import Stage0.Senke.Anweisung.Faelle.Schleifen.Runtime

namespace Gabbro.Stage0.Senke
open Runner Runner.IR
variable [Kern]
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000

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
  induction budget generalizing m with
  | zero =>
    refine ⟨m, 1, by omega, ?_, start⟩
    exact .next (counter_zero (test 0 m start) (count 0 m start)) (.refl _ _)
  | succ n ih =>
    obtain ⟨a, b, nb, write, bound, run, backCode, next⟩ := body n m start fits
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
    have last : Counted 1 ⟨back, fp⟩ b ⟨pc, fp⟩ b := by
      have h := run_step (t := ⟨back, fp⟩) backCode (by decide)
        (run_jmp (t := ⟨back, fp⟩) backCode)
      simpa [edge] using Counted.next h (Counted.refl _ _)
    obtain ⟨c, nc, hc, rest, done⟩ := ih (by omega) next
    refine ⟨c, 1 + 1 + nb + 1 + nc, ?_,
      (((first.trans second).trans run).trans last).trans rest, done⟩
    rw [Nat.succ_mul]
    omega

namespace CountedLoopProbe
open Runner.Mem

/-- The control image emitted for a true invariant and an empty body. Its
    budget immediate is fixed; the theorem below starts at the live header
    and covers every representable remaining runtime budget without unrolling. -/
def image := foreverCode 4 5 6 2 [ci 1 6 1 0] []

open Gabbro.Grammatik in
/-- The image is the accepted statement lowering, not a hand-selected loop. -/
theorem lowering_zeuge :
    lowS (reserved := 2) 2 FnptrProben.addresses FnptrProben.callLayout 4
      ([], 6) [] (0, 0)
      (show Stmt FnptrProben.D (vertragVon FnptrProben.D 2) false [] [] [] from
        .forever () .tru .nil) = some (image, 14) := by
  decide +kernel

def Entry (n : Nat) (m : Mem) : Prop :=
  CodeAt m 0 image ∧ FrameOK m 1024 16 ∧
  m.rd64 (slot 1024 4) = some (BitVec.ofNat 64 n) ∧
  m.rd64 (slot 1024 5) = some 1

omit [Kern] in
theorem far : CodeFar 0 image.length 1024 16 := by
  unfold CodeFar; decide +kernel

/-- All positive passes execute the actual invariant, its branch and the jump
    over the failure tail. The final zero test reaches the emitted budget stop.
    Count = at most 6 instructions/pass + one final test, not CPU cycles. -/
theorem counted_counter_loop_zeuge {n : Nat} {m : Mem}
    (fits : n < 2 ^ 64) (entry : Entry n m) :
    ∃ b nb, nb ≤ n * 6 + 1 ∧
      Counted nb ⟨32, 1024⟩ m ⟨176, 1024⟩ b ∧ Entry 0 b := by
  apply counted_counter_loop Entry 32 1024 160 4 5 144 3
    (fun n m h => h.1 2 (by decide))
    (fun n m h => h.2.2.1)
    (fun n m h => h.1 3 (by decide))
    (fun n m h => h.2.2.2) ?_ (by decide) fits entry
  intro n m h hn
  let a := write m (slot 1024 4) 8 (BitVec.ofNat 64 n).toNat
  have wa : m.wr64 (slot 1024 4) (BitVec.ofNat 64 n) = some a :=
    wr64_some (h.2.1.wr 4 (by decide))
  have aa : Agree 1024 4 16 m a :=
    agree_write h.2.1.room (by decide) (by decide) _
  have ca := h.1.agree aa far
  have fa := h.2.1.agree aa
  let b := write a (slot 1024 6) 8 1
  have ab : Agree 1024 6 16 a b :=
    agree_write fa.room (by decide) (by decide) _
  have cb := ca.agree ab far
  have fb := fa.agree ab
  have literal : CodeAt a 64 [ci 1 6 1 0] := by
    intro k hk
    have : k = 0 := by simpa using hk
    subst k
    exact ca 4 (by decide)
  have c1 : Counted 1 ⟨64, 1024⟩ a ⟨80, 1024⟩ b :=
    const_step_counted literal fa (by decide) (by decide) (by decide)
  have value : b.rd64 (slot 1024 6) = some 1 :=
    rd64_write_same (w := 1) (fa.rd 6 (by decide))
  have c2 : Counted 1 ⟨80, 1024⟩ b ⟨96, 1024⟩ b :=
    .next (counter_positive (cb 5 (by decide)) value (by decide)) (.refl _ _)
  have c3 : Counted 1 ⟨96, 1024⟩ b ⟨160, 1024⟩ b :=
    .next (run_step (cb 6 (by decide)) (by decide)
      (run_jmp (cb 6 (by decide)))) (.refl _ _)
  refine ⟨a, b, 3, wa, by decide, c1.trans (c2.trans c3), cb 10 (by decide),
    cb, fb, ?_, ?_⟩
  · have saved : a.rd64 (slot 1024 4) = some (BitVec.ofNat 64 n) :=
      rd64_write_same (w := BitVec.ofNat 64 n) (h.2.1.rd 4 (by decide))
    exact (agree_rd_low ab fb.room (by decide) (by decide)).trans saved
  · have saved : a.rd64 (slot 1024 5) = some 1 :=
      (Mem.rd64_write_far (slot_far h.2.1.room (by decide : 4 < 16) (by decide : 5 < 16) (by decide))).trans h.2.2.2
    exact (agree_rd_low ab fb.room (by decide) (by decide)).trans saved

def initial : Mem := {
  b := fun a => if a.toNat < 16 * image.length then
    ((image.flatMap encII)[a.toNat]?).getD 0 else if a = 1064 then 1 else 0
  rd := fun _ => true
  wr := fun _ => true }

def loaded (n : Nat) := write initial (slot 1024 4) 8 (BitVec.ofNat 64 n).toNat

omit [Kern] in
 theorem entry_zeuge (n : Nat) : Entry n (loaded n) := by
  have frame : FrameOK initial 1024 16 :=
    ⟨by decide, fun _ _ => rfl, fun _ _ => rfl⟩
  have agree : Agree 1024 4 16 initial (loaded n) :=
    agree_write frame.room (by decide) (by decide) _
  have code : CodeAt initial 0 image := by
    have h : ∀ k : Fin image.length,
        (initial.rd8 (0 + BitVec.ofNat 64 (16 * k.val)) = some (BitVec.ofNat 8 image[k.val].o)) ∧
        initial.rd32 (0 + BitVec.ofNat 64 (16 * k.val) + 4) = some (II.f image[k.val].a) ∧
        initial.rd32 (0 + BitVec.ofNat 64 (16 * k.val) + 8) = some (II.f image[k.val].b) ∧
        initial.rd32 (0 + BitVec.ofNat 64 (16 * k.val) + 12) = some (II.f image[k.val].c) := by
      apply FnptrProben.allFin; decide +kernel
    intro k hk
    obtain ⟨op, a, b, c⟩ := h ⟨k, hk⟩
    exact ⟨op, a, b, c⟩
  refine ⟨code.agree agree far, frame.agree agree,
    rd64_write_same (w := BitVec.ofNat 64 n) (frame.rd 4 (by decide)), ?_⟩
  exact (Mem.rd64_write_far (slot_far frame.room (by decide : 4 < 16)
    (by decide : 5 < 16) (by decide))).trans (by decide +kernel)

/-- A concrete loaded image inhabits the generic induction for arbitrary fuel. -/
theorem whole_loop_zeuge (n : Nat) (fits : n < 2 ^ 64) :
    ∃ b nb, nb ≤ n * 6 + 1 ∧
      Counted nb ⟨32, 1024⟩ (loaded n) ⟨176, 1024⟩ b ∧ Entry 0 b :=
  counted_counter_loop_zeuge fits (entry_zeuge n)

end CountedLoopProbe

end Gabbro.Stage0.Senke
