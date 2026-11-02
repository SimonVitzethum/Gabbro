/- Exact S0IR instruction counts. A memory request within an instruction is not
   another instruction; kernel execution time is not measured by this relation.
   Source loop fuel and `ZeitAb` (G own steps) are distinct units. -/
module
public import Stage0.Senke.Anweisung.Faelle.Schleifen.Counted.Teil1a

public import Stage0.Senke.Anweisung.Simulation
public import Stage0.Senke.Ausdruck.Gleichungen

@[expose] public section



namespace Gabbro.Stage0.Senke
open Runner Runner.IR
variable [Kern]
open Gabbro.Grammatik Runner.Mem
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


/-- Exact count and scalar value of an actual constant instruction. -/
theorem const_counted_ok {m : Runner.Mem} {pc fp : Runner.W} {K d : Nat}
    {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop} {k : Int}
    (small : lit32 k = true) (fits : d + 1 ≤ K)
    (pre : Pre L m pc fp K d [ci 1 d k 0] ρ W reserved) :
    CountedOk 1 m pc fp K d [ci 1 d k 0] (· = BitVec.ofInt 64 k) := by
  obtain ⟨writable, read, changed⟩ := wr_slot pre.frame (d := d) (by omega) (BitVec.ofInt 64 k)
  exact ⟨_, const_step_counted pre.code pre.frame (by omega) pre.small small,
    changed, _, read, rfl⟩

theorem CountedOk.mono {n m pc fp K d code P Q} (run : CountedOk n m pc fp K d code P)
    (post : ∀ w, P w → Q w) : CountedOk n m pc fp K d code Q := by
  obtain ⟨m', steps, changed, w, read, value⟩ := run
  exact ⟨m', steps, changed, w, read, post w value⟩

/-- The arbitrary-word generator is straight-line code; every emitted instruction
    is counted, including all radix constants and both arithmetic operations. -/
theorem konstWL_counted {m : Runner.Mem} {pc fp : Runner.W} {K d : Nat}
    {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop} (k n : Nat)
    (range : n < 65536 ^ k) (fits : d + 2 ≤ K)
    (pre : Pre L m pc fp K d (konstWL k n d).1 ρ W reserved) :
    CountedOk ((konstWL k n d).1.length) m pc fp K d (konstWL k n d).1
      (· = BitVec.ofNat 64 n) := by
  induction k generalizing n m pc with
  | zero =>
    have zero : n = 0 := by simpa using range
    subst n
    exact const_counted_ok (by decide) (by omega) pre
  | succ k ih =>
    have quotient : n / 65536 < 65536 ^ k := by rw [Nat.pow_succ] at range; omega
    have low : lit32 (n % 65536 : Nat) = true := lit32_nat (by omega)
    have head : ∀ m pc, Pre L m pc fp K d
        (bin2 5 d (konstWL k (n / 65536) d) ([ci 1 (d + 1) 65536 0], d + 2)).1 ρ W reserved →
        CountedOk ((konstWL k (n / 65536) d).1.length + 1 + 1) m pc fp K d
          (bin2 5 d (konstWL k (n / 65536) d) ([ci 1 (d + 1) 65536 0], d + 2)).1
          (· = BitVec.ofNat 64 (n / 65536) * BitVec.ofInt 64 65536) := by
      intro m pc hp
      exact bin_counted_keep (ih _ quotient hp.left.left)
        (fun m pc _ hp => const_counted_ok (by decide) (by omega) hp)
        (fun a b ha hb => ⟨_, rfl, by rw [ha, hb]⟩) rfl (by decide) (by omega) hp
    have run := bin_counted_keep (head m pc pre.left.left)
      (fun m pc _ hp => const_counted_ok low (by omega) hp)
      (P := fun r => r = BitVec.ofNat 64 n) (g := fun a b => some (a + b))
      (by
        intro a b ha hb
        refine ⟨_, rfl, ?_⟩
        rw [ha, hb, BitVec.ofInt_natCast,
          show BitVec.ofInt 64 65536 = BitVec.ofNat 64 65536 from rfl,
          ← BitVec.ofNat_mul, ← BitVec.ofNat_add]
        exact congrArg (BitVec.ofNat 64) (by omega)) rfl (by decide) (by omega) pre
    simpa only [konstWL, bin2, List.length_append, List.length_singleton, Int.natCast_add, Int.natCast_emod, Int.cast_ofNat_Int] using run

theorem wordConst_counted {m : Runner.Mem} {pc fp : Runner.W} {K d : Nat}
    {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop} (w : Runner.W)
    (fits : (wordConst w d).2 ≤ K)
    (pre : Pre L m pc fp K d (wordConst w d).1 ρ W reserved) :
    CountedOk ((wordConst w d).1.length) m pc fp K d (wordConst w d).1 (· = w) := by
  unfold wordConst at fits pre ⊢
  split at fits
  · next small =>
    rw [if_pos small] at pre ⊢
    exact (const_counted_ok small (by omega) pre).mono fun r hr => by
      rw [hr, BitVec.ofInt_toInt]
  · next large =>
    rw [if_neg large] at pre ⊢
    have room : d + 2 ≤ K := by
      simpa [konstWL, bin2, Nat.max_assoc, Nat.max_comm, Nat.max_left_comm] using fits
    exact (konstWL_counted 4 w.toNat (by simpa using w.isLt) room pre).mono fun r hr => by
      simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using hr

/-- Complete literal materialization has exactly the emitted straight-line length,
    with every output limb and nested word preserved, not just the low word. -/
theorem constWords_counted {fp : Runner.W} {K : Nat} {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} (words : List Runner.W) {m : Runner.Mem} {pc : Runner.W} {d : Nat}
    (fits : (constWords words d).2 ≤ K)
    (pre : Pre L m pc fp K d (constWords words d).1 ρ W reserved) :
    ∃ m', Counted ((constWords words d).1.length) ⟨pc, fp⟩ m
        ⟨pc + BitVec.ofNat 64 (16 * (constWords words d).1.length), fp⟩ m' ∧
      Agree fp d K m m' ∧ WordsAt m' fp d words := by
  induction words generalizing m pc d with
  | nil => exact ⟨m, by simpa [constWords] using Counted.refl ⟨pc, fp⟩ m, .refl _ _ _ _, by intro i hi; cases hi⟩
  | cons w ws ih =>
    have headTop := wordConst_top w d
    obtain ⟨m1, run1, changed1, r, read1, value⟩ := wordConst_counted w
      (by simp only [constWords] at fits; omega) pre.left
    subst r
    have next := pre.next changed1 (Nat.le_succ d) (by simp only [constWords] at fits; omega)
    obtain ⟨m2, run2, changed2, output⟩ := ih (d := d + 1)
      (by simp only [constWords] at fits; omega) next
    refine ⟨m2, ?_, changed1.trans (changed2.mono (Nat.le_succ d)), ?_⟩
    · simpa only [constWords, List.length_append, pc_add] using run1.trans run2
    · intro i hi
      cases i with
      | zero =>
        rw [Nat.add_zero, agree_rd_low changed2 (pre.frame.agree changed1).room (by omega)
          (by simp only [constWords] at fits; omega)]
        exact read1
      | succ i =>
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using output i (by simp at hi; omega)

/-- The count uses precisely the selected emitter, including every limb of an
    arbitrary declared literal. Small signed immediates retain cost one. -/
def literalCount (n : Int) (d : Nat) : Nat :=
  if lit32 n then 1 else (constWords (integerEncoding (integerWords n n) n) d).1.length

theorem lowE_literal_counted {Γ : Ctx} {Λ : List (Res D)} {n : Int} {d top K : Nat}
    {code : List II} {m : Runner.Mem} {pc fp : Runner.W} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    (lower : lowE L (reserved := reserved) (Λ := Λ) (Γ := Γ) (.lit n) d = some (code, top))
    (fits : top ≤ K) (pre : Pre L m pc fp K d code ρ W reserved) :
    CountedOk (literalCount n d) m pc fp K d code (· = BitVec.ofInt 64 n) := by
  rw [lowE_lit] at lower
  split at lower
  · next small =>
    cases lower
    simpa only [literalCount, small, ite_true] using const_counted_ok small (by omega) pre
  · next large =>
    have pair := Option.some.inj lower
    have codeEq := congrArg Prod.fst pair
    have topEq := congrArg Prod.snd pair
    dsimp only at codeEq topEq
    subst code
    subst top
    obtain ⟨m', run, changed, output⟩ := constWords_counted
      (integerEncoding (integerWords n n) n) fits pre
    have read := integerEncoding_read_first (n := integerWords n n) (by unfold integerWords; omega) output
    exact ⟨m', by simpa only [literalCount, large, Bool.false_eq_true, ↓reduceIte, encodeWords] using run,
      changed, _, read, rfl⟩

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
      ExprCost L reserved (.lit n) d (literalCount n d) (· = BitVec.ofInt 64 n)
  | truth {d : Nat} : ExprCost L reserved .tru d 1 (· = 1)
  | falsity {d : Nat} : ExprCost L reserved .fls d 1 (· = 0)
  | binary {τ τa τb : Ty} {e : Expr D Γ Λ τ}
      {a : Expr D Γ Λ τa} {b : Expr D Γ Λ τb} {d o na nb : Nat}
      {Pa Pb P : Runner.W → Prop} {g : Runner.W → Runner.W → Option Runner.W}
      (equation : ∀ code top, lowE L (reserved := reserved) e d = some (code, top) →
        (do let ca ← lowE L (reserved := reserved) a d
            let cb ← lowE L (reserved := reserved) b (d + 1)
            pure (bin2 o d ca cb)) = some (code, top))
      (narrow : ∀ code top, lowE L (reserved := reserved) e d = some (code, top) → valueWords τ = 1)
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
    (narrow : valueWords (.int (l1 + l2) (h1 + h2)) = 1)
    (left : ExprCost L reserved a d na Pa)
    (right : ExprCost L reserved b (d + 1) nb Pb) :
    ExprCost L reserved (.add a b) d (na + nb + 1)
      (fun r => ∃ wa wb, Pa wa ∧ Pb wb ∧ r = wa + wb) :=
  .binary (o := 3) (by
    intro code top made
    rw [lowE_add, if_pos narrow] at made
    exact made) (by
    intro code top _
    exact narrow) left right
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
    exact lowE_literal_counted lower fits pre
  | @truth d =>
    rw [lowE_tru] at lower
    cases lower
    obtain ⟨hw, rd, agree⟩ := wr_slot pre.frame (d := d) (by omega) (1 : Runner.W)
    exact ⟨_, const_step_counted pre.code pre.frame (by omega) pre.small (by decide),
      agree, _, rd, rfl⟩
  | @falsity d =>
    rw [lowE_fls] at lower
    cases lower
    obtain ⟨hw, rd, agree⟩ := wr_slot pre.frame (d := d) (by omega) (0 : Runner.W)
    exact ⟨_, const_step_counted pre.code pre.frame (by omega) pre.small (by decide),
      agree, _, rd, rfl⟩
  | binary equation narrow left right values opcode byte ihA ihB =>
    exact bin2_counted (equation code top lower) fits
      (fun ca ta ha ht m pc hp => ihA ha ht hp)
      (fun cb tb hb ht m pc hp => ihB hb ht hp) values opcode byte pre

/-- Accepted non-scalar certificates retain the exact point-literal source and
    its complete emitted count; binary scalar profiles cannot certify a wide value. -/
theorem ExprCost.width_or_literal {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
    {e : Expr D Γ Λ τ} {d n : Nat} {P : Runner.W → Prop}
    (certificate : ExprCost L reserved e d n P) {code : List II} {top : Nat}
    (lower : lowE L (reserved := reserved) e d = some (code, top)) :
    valueWords τ = 1 ∨ ∃ k : Int, τ = .int k k ∧
      HEq e (Expr.lit (D := D) (Γ := Γ) (Λ := Λ) k) ∧ n = literalCount k d := by
  cases certificate with
  | literal => exact .inr ⟨_, rfl, HEq.rfl, rfl⟩
  | truth => exact .inl rfl
  | falsity => exact .inl rfl
  | binary equation narrow left right values opcode byte => exact .inl (narrow _ _ lower)

end Gabbro.Stage0.Senke
