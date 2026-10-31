/- Exact S0IR instruction counts. A memory request within an instruction is not
   another instruction; kernel execution time is not measured by this relation.
   Source loop fuel and `ZeitAb` (G own steps) are distinct units. -/
import Stage0.Senke.Anweisung.Simulation

namespace Gabbro.Stage0.Senke
open Runner Runner.IR
variable [Kern]

/-- Exactly `n` completed S0IR instructions, using the canonical instruction
    semantics, including instructions executed in callees and nested loops. -/
inductive Counted : Nat → T → Mem → T → Mem → Prop
  | refl (t m) : Counted 0 t m t m
  | next {n t u v m a b} : Run (step t) m u a → Counted n u a v b →
      Counted (n + 1) t m v b

theorem Counted.forget {n t u m a} (h : Counted n t m u a) : Star t m u a := by
  induction h with
  | refl => exact .refl _ _
  | next h _ ih => exact .next h ih

theorem Counted.trans {n k t u v m a b}
    (h : Counted n t m u a) (g : Counted k u a v b) :
    Counted (n + k) t m v b := by
  induction h with
  | refl => simpa using g
  | next h _ ih => simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Counted.next h (ih g)

/-- Existence of a count alone adds no quantitative bound to `Star`. -/
theorem counted_iff_star {t u m a} : (∃ n, Counted n t m u a) ↔ Star t m u a := by
  constructor
  · rintro ⟨n, h⟩; exact h.forget
  · intro h
    induction h with
    | refl => exact ⟨0, .refl _ _⟩
    | next h _ ih => obtain ⟨n, hn⟩ := ih; exact ⟨n + 1, .next h hn⟩

/-- Compose any finite family of actual execution segments. Segment bounds
    must include the invariant, body/callees, header, backedge and exits as
    applicable; no code-length assumption is made for a recursive segment. -/
inductive CountedSegments : List Nat → T → Mem → T → Mem → Prop
  | nil (t m) : CountedSegments [] t m t m
  | cons {ns n t u v m a b} : Counted n t m u a →
      CountedSegments ns u a v b → CountedSegments (n :: ns) t m v b

theorem CountedSegments.exact {ns t u m a} (h : CountedSegments ns t m u a) :
    Counted ns.sum t m u a := by
  induction h with
  | nil => exact .refl _ _
  | cons h _ ih => exact h.trans ih

/-- Bound actual segments from a uniform bound on each segment. Nested
    execution and calls are already included in each segment's exact count. -/
theorem CountedSegments.bound {ns t u m a} (h : CountedSegments ns t m u a)
    {limit : Nat} (hb : ∀ n ∈ ns, n ≤ limit) :
    ∃ n, n ≤ ns.length * limit ∧ Counted n t m u a := by
  refine ⟨ns.sum, ?_, h.exact⟩
  clear h
  induction ns with
  | nil => simp
  | cons n ns ih =>
    have hn := hb n (by simp)
    have ht := ih (fun k hk => hb k (by simp [hk]))
    simp only [List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- Budget induction for exact instruction traces. `I` describes the real
    header state at each remaining budget; the step obligation separates
    header, invariant, body (including callees/nested loops), and backedge.
    Early exits consume at most the same allowance. This combinator does not
    establish those obligations for a lowering. Source passes and G own steps
    are not instruction counts. -/
theorem counted_budget_induction
    (I : Nat → T → Mem → Prop) (Done : T → Mem → Prop)
    (header invariant body backedge exit : Nat)
    (zero : ∀ t m, I 0 t m →
      ∃ n u a, n ≤ exit ∧ Counted n t m u a ∧ Done u a)
    (positive : ∀ k t m, I (k + 1) t m →
      (∃ n u a, n ≤ header + invariant + body + backedge + exit ∧
        Counted n t m u a ∧ Done u a) ∨
      (∃ nh ni nb ne th ti tb u mh mi mb a,
        nh ≤ header ∧ ni ≤ invariant ∧ nb ≤ body ∧ ne ≤ backedge ∧
        Counted nh t m th mh ∧ Counted ni th mh ti mi ∧
        Counted nb ti mi tb mb ∧ Counted ne tb mb u a ∧ I k u a))
    {budget t m} (start : I budget t m) :
    ∃ n u a, n ≤ budget * (header + invariant + body + backedge) + exit ∧
      Counted n t m u a ∧ Done u a := by
  induction budget generalizing t m with
  | zero => simpa using zero t m start
  | succ k ih =>
    rcases positive k t m start with early | more
    · obtain ⟨n, u, a, hn, run, done⟩ := early
      refine ⟨n, u, a, ?_, run, done⟩
      rw [Nat.succ_mul]
      omega
    · obtain ⟨nh, ni, nb, ne, th, ti, tb, u, mh, mi, mb, a,
        hh, hi, hb, he, rh, ri, rb, re, next⟩ := more
      obtain ⟨n, v, b, hn, run, done⟩ := ih next
      refine ⟨nh + ni + nb + ne + n, v, b, ?_,
        (((rh.trans ri).trans rb).trans re).trans run, done⟩
      rw [Nat.succ_mul]
      omega

end Gabbro.Stage0.Senke
