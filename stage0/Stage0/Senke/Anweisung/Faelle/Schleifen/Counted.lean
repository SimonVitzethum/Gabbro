/- Exact S0IR instruction counts. A memory request within an instruction is not
   another instruction; kernel execution time is not measured by this relation.
   Source loop fuel and `ZeitAb` (G own steps) are distinct units. -/
import Stage0.Senke.Anweisung.Simulation
import Stage0.Senke.Ausdruck.Gleichungen

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

/-- The real constant instruction has unit S0IR cost; the writable frame and
    immediate checks are exactly those of the existing lowering helper. -/
theorem const_step_counted {m : Runner.Mem} {pc fp : Runner.W} {K j : Nat} {k : Int}
    (hc : CodeAt m pc [ci 1 j k 0]) (hF : FrameOK m fp K) (hj : j < K)
    (hK : K < 2 ^ 31) (hk : lit32 k = true) :
    Counted 1 ⟨pc, fp⟩ m ⟨pc + 16, fp⟩
      (Runner.Mem.write m (slot fp (BitVec.ofNat 64 j)) 8 (BitVec.ofInt 64 k).toNat) :=
  .next (const_instruction hc hF hj hK hk) (.refl _ _)

/-- Quantitative base case derived from the actual accepted `lowE` result,
    rather than an assumed child bound or evaluation of a particular program.
    This does not cover compound expressions, calls, or loop bodies. -/
theorem lowE_lit_counted {D : Gabbro.Grammatik.Deklaration} {L : Lay D}
    {Γ : Gabbro.Grammatik.Ctx} {Λ : List (Gabbro.Grammatik.Res D)}
    {reserved d top K : Nat} {n : Int} {code : List II}
    {m : Runner.Mem} {pc fp : Runner.W}
    (lower : lowE L (reserved := reserved) (Γ := Γ) (Λ := Λ)
      (.lit n) d = some (code, top))
    (codeAt : CodeAt m pc code) (frame : FrameOK m fp K)
    (fits : top ≤ K) (small : K < 2 ^ 31) :
    Counted 1 ⟨pc, fp⟩ m ⟨pc + 16, fp⟩
      (Runner.Mem.write m (slot fp (BitVec.ofNat 64 d)) 8 (BitVec.ofInt 64 n).toNat) := by
  rw [lowE_lit] at lower
  split at lower
  next accepted =>
    cases lower
    exact const_step_counted codeAt frame (by omega) small accepted
  next refused => contradiction


open Gabbro.Grammatik Runner.Mem

/-- The existing expression postcondition with a canonical exact count.
    Frame agreement preserves arbitrary world predicates through `Pre.next`. -/
def CountedOk (n : Nat) (m : Runner.Mem) (pc fp : Runner.W) (K d : Nat)
    (code : List II) (P : Runner.W → Prop) : Prop :=
  ∃ m', Counted n ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * code.length), fp⟩ m' ∧
    Agree fp d K m m' ∧ ∃ w, m'.rd64 (slot fp (BitVec.ofNat 64 d)) = some w ∧ P w

theorem CountedOk.forget {n m pc fp K d code P}
    (h : CountedOk n m pc fp K d code P) : Ok m pc fp K d code P := by
  obtain ⟨m', run, rest⟩ := h
  exact ⟨m', run.forget, rest⟩

theorem counted_ins {m m' : Runner.Mem} {pc fp : Runner.W} {i : II}
    (hc : CodeAt m pc [i]) (ho : i.o < 256)
    (hr : Run (op i.o ⟨pc, fp⟩) m ⟨pc + 16, fp⟩ m') :
    Counted 1 ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * [i].length), fp⟩ m' :=
  .next (run_step (t := ⟨pc, fp⟩) (by simpa using hc 0 (by simp)) ho hr) (.refl _ _)

variable {D : Deklaration} {L : Lay D} {reserved : Nat}

/-- The same child-IH architecture as `bin_ok_keep`, retaining the exact
    child counts. This includes the final real opcode, not just code lengths. -/
theorem bin_counted_keep {m : Runner.Mem} {pc fp : Runner.W} {K d o na nb : Nat} {ca cb : List II} {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop}
    {Pa Pb P : Runner.W → Prop} {g : Runner.W → Runner.W → Option Runner.W}
    (hA : CountedOk na m pc fp K d ca Pa)
    (hB : ∀ m' pc, Agree fp d K m m' → Pre L m' pc fp K (d + 1) cb ρ W reserved → CountedOk nb m' pc fp K (d + 1) cb Pb)
    (hg : ∀ wa wb, Pa wa → Pb wb → ∃ r, g wa wb = some r ∧ P r) (hop : op o = bin g) (ho : o < 256)
    (hK : d + 1 < K) (h : Pre L m pc fp K d (ca ++ cb ++ [ci o d d (d + 1)]) ρ W reserved) :
    CountedOk (na + nb + 1) m pc fp K d (ca ++ cb ++ [ci o d d (d + 1)]) P := by
  have h' : Pre L m pc fp K d (ca ++ (cb ++ [ci o d d (d + 1)])) ρ W reserved := by simpa using h
  obtain ⟨m1, s1, a1, wa, ra, pa⟩ := hA
  have h1 := h'.next a1 (Nat.le_succ d) (by omega)
  obtain ⟨m2, s2, a2, wb, rb, pb⟩ := hB m1 _ a1 h1.left
  have h2 := h1.next (d := d + 1) (d' := d + 1) a2 (Nat.le_refl _) (by omega)
  obtain ⟨r, hr, pr⟩ := hg wa wb pa pb
  have hF2 : FrameOK m2 fp K := h1.frame.agree a2
  obtain ⟨hw, hrd, a3⟩ := wr_slot hF2 (d := d) (by omega) r
  have ra2 : m2.rd64 (slot fp (BitVec.ofNat 64 d)) = some wa := by
    rw [agree_rd_low a2 hF2.room (Nat.lt_succ_self d) (by omega)]; exact ra
  have := h.small
  have hs : sx (II.f (d : Int)) = BitVec.ofNat 64 d := sx_nat (by omega)
  have hs1 : sx (II.f ((d : Int) + 1)) = BitVec.ofNat 64 (d + 1) := by
    have := sx_nat (d := d + 1) (by omega); simpa using this
  have hi := h2.code 0 (by simp)
  simp only [ci, List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero] at hi
  have s3 := counted_ins (fp := fp) (m' := write m2 (slot fp (BitVec.ofNat 64 d)) 8 r.toNat) h2.code ho (by
    simp only [ci]
    rw [hop]
    refine run_bin (t := ⟨_, fp⟩) (m1 := write m2 (slot fp (BitVec.ofNat 64 d)) 8 r.toNat) hi (va := wa)
      (vb := wb) ?_ ?_ hr ?_
    · simpa [ci, hs] using ra2
    · simpa [ci, hs1] using rb
    · simpa [ci, hs] using hw)
  refine ⟨_, (s1.trans s2).trans ?_, (a1.trans (a2.mono (Nat.le_succ d))).trans a3, r, hrd, pr⟩
  have e : pc + BitVec.ofNat 64 (16 * (ca ++ cb ++ [ci o d d (d + 1)]).length) =
      pc + BitVec.ofNat 64 (16 * ca.length) + BitVec.ofNat 64 (16 * cb.length) +
        BitVec.ofNat 64 (16 * [ci o d d (d + 1)].length) := by
    simp only [List.length_append, List.length_singleton, pc_add]
  rw [e]
  exact s3


/-- Constructor-level cost composition for actual `bin2` lowering. Child
    hypotheses are reusable at every memory/PC, as in `lowE_ok`; no whole
    expression execution or whole expression cost is assumed. -/
theorem bin2_counted {Γ : Ctx} {Λ : List (Res D)} {τa τb : Ty}
    {a : Expr D Γ Λ τa} {b : Expr D Γ Λ τb}
    {d o top K na nb : Nat} {code : List II} {fp : Runner.W}
    {ρ : Env D Γ} {W : Runner.Mem → Prop} {Pa Pb P : Runner.W → Prop}
    {g : Runner.W → Runner.W → Option Runner.W}
    (lower : (do let ca ← lowE L (reserved := reserved) a d
                 let cb ← lowE L (reserved := reserved) b (d + 1)
                 pure (bin2 o d ca cb)) = some (code, top))
    (fits : top ≤ K)
    (left : ∀ ca ta, lowE L (reserved := reserved) a d = some (ca, ta) → ta ≤ K →
      ∀ m pc, Pre L m pc fp K d ca ρ W reserved → CountedOk na m pc fp K d ca Pa)
    (right : ∀ cb tb, lowE L (reserved := reserved) b (d + 1) = some (cb, tb) → tb ≤ K →
      ∀ m pc, Pre L m pc fp K (d + 1) cb ρ W reserved → CountedOk nb m pc fp K (d + 1) cb Pb)
    (values : ∀ wa wb, Pa wa → Pb wb → ∃ r, g wa wb = some r ∧ P r)
    (opcode : op o = bin g) (byte : o < 256)
    {m : Runner.Mem} {pc : Runner.W}
    (pre : Pre L m pc fp K d code ρ W reserved) :
    CountedOk (na + nb + 1) m pc fp K d code P := by
  simp only [bind, Option.bind_eq_some_iff] at lower
  obtain ⟨⟨ca, ta⟩, ha, ⟨⟨cb, tb⟩, hb, out⟩⟩ := lower
  cases out
  have fitA : ta ≤ K := Nat.le_trans (Nat.le_max_left _ _) fits
  have fitB : tb ≤ K := Nat.le_trans (Nat.le_max_right _ _) fits
  have room := lowE_top b (d + 1) cb tb hb
  have hp : Pre L m pc fp K d (ca ++ (cb ++ [ci o d d (d + 1)])) ρ W reserved := by
    simpa [bin2, List.append_assoc] using pre
  exact bin_counted_keep (left ca ta ha fitA m pc hp.left)
    (fun m pc _ h => right cb tb hb fitB m pc h) values opcode byte (by omega) pre

/-- A structurally recursive certificate for accepted expression lowering.
    Binary nodes supply only the real lowering equation and the opcode value
    law. Execution and counts are derived recursively from their children. -/
inductive ExprCost (L : Lay D) {Γ : Ctx} {Λ : List (Res D)} (reserved : Nat) :
    {τ : Ty} → Expr D Γ Λ τ → Nat → Nat → (Runner.W → Prop) → Type
  | literal {n : Int} {d : Nat} :
      ExprCost L reserved (.lit n) d 1 (· = BitVec.ofInt 64 n)
  | binary {τ τa τb : Ty} {e : Expr D Γ Λ τ}
      {a : Expr D Γ Λ τa} {b : Expr D Γ Λ τb} {d o na nb : Nat}
      {Pa Pb P : Runner.W → Prop} {g : Runner.W → Runner.W → Option Runner.W}
      (equation : lowE L (reserved := reserved) e d =
        (do let ca ← lowE L (reserved := reserved) a d
            let cb ← lowE L (reserved := reserved) b (d + 1)
            pure (bin2 o d ca cb)))
      (left : ExprCost L reserved a d na Pa)
      (right : ExprCost L reserved b (d + 1) nb Pb)
      (values : ∀ wa wb, Pa wa → Pb wb → ∃ r, g wa wb = some r ∧ P r)
      (opcode : op o = bin g) (byte : o < 256) :
      ExprCost L reserved e d (na + nb + 1) P

/-- The actual addition constructor composes certificates without another
    lowering or execution premise. -/
def ExprCost.add {Γ : Ctx} {Λ : List (Res D)} {l1 h1 l2 h2 : Int}
    {a : Expr D Γ Λ (.int l1 h1)} {b : Expr D Γ Λ (.int l2 h2)}
    {d na nb : Nat} {Pa Pb : Runner.W → Prop}
    (left : ExprCost L reserved a d na Pa)
    (right : ExprCost L reserved b (d + 1) nb Pb) :
    ExprCost L reserved (.add a b) d (na + nb + 1)
      (fun r => ∃ wa wb, Pa wa ∧ Pb wb ∧ r = wa + wb) :=
  .binary (lowE_add L d a b) left right
    (fun wa wb ha hb => ⟨wa + wb, rfl, wa, wb, ha, hb, rfl⟩) rfl (by decide)

/-- Sound for every accepted lowering, layout, environment and stable world
    predicate. No evaluator of a particular source program occurs here. -/
theorem ExprCost.sound {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
    {e : Expr D Γ Λ τ} {d n : Nat} {P : Runner.W → Prop}
    (certificate : ExprCost L reserved e d n P)
    {code : List II} {top K : Nat} {m : Runner.Mem} {pc fp : Runner.W}
    {ρ : Env D Γ} {W : Runner.Mem → Prop}
    (lower : lowE L (reserved := reserved) e d = some (code, top))
    (fits : top ≤ K) (pre : Pre L m pc fp K d code ρ W reserved) :
    CountedOk n m pc fp K d code P := by
  induction certificate generalizing code top K m pc with
  | @literal n' d' =>
    rw [lowE_lit] at lower
    split at lower
    next accepted =>
      cases lower
      obtain ⟨hw, rd, agree⟩ := wr_slot pre.frame (d := d') (by omega) (BitVec.ofInt 64 n')
      exact ⟨_, const_step_counted pre.code pre.frame (by omega) pre.small accepted,
        agree, _, rd, rfl⟩
    next refused => contradiction
  | binary equation left right values opcode byte ihA ihB =>
    rw [equation] at lower
    exact bin2_counted lower fits
      (fun ca ta ha ht m pc hp => ihA ha ht hp)
      (fun cb tb hb ht m pc hp => ihB hb ht hp) values opcode byte pre

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
