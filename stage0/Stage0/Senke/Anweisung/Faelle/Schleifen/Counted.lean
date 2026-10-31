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

end Gabbro.Stage0.Senke
