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

/-- The single-instruction literal case. Larger accepted literals use
    `konstWL_counted_ok` and the literal branch of `ExprCost.sound`. -/
theorem lowE_lit_counted {D : Gabbro.Grammatik.Deklaration} {L : Lay D}
    {Γ : Gabbro.Grammatik.Ctx} {Λ : List (Gabbro.Grammatik.Res D)}
    {reserved d top K : Nat} {n : Int} {code : List II}
    {m : Runner.Mem} {pc fp : Runner.W}
    (literal : lit32 n = true)
    (lower : lowE L (reserved := reserved) (Γ := Γ) (Λ := Λ)
      (.lit n) d = some (code, top))
    (codeAt : CodeAt m pc code) (frame : FrameOK m fp K)
    (fits : top ≤ K) (small : K < 2 ^ 31) :
    Counted 1 ⟨pc, fp⟩ m ⟨pc + 16, fp⟩
      (Runner.Mem.write m (slot fp (BitVec.ofNat 64 d)) 8 (BitVec.ofInt 64 n).toNat) := by
  rw [lowE_lit, if_pos literal] at lower
  cases lower
  exact const_step_counted codeAt frame (by omega) small literal


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

theorem sys_counted_frame {m : Runner.Mem} {pc fp : Runner.W} {K nr c s : Nat} (hc : CodeAt m pc (sysC nr c s))
    (hf : CodeFar pc 3 fp K) (hF : FrameOK m fp K) (hs : s + 8 ≤ K) (hK : K < 2 ^ 31) (hcode : c < 2 ^ 31)
    (hnr : nr < 2 ^ 31) :
    ∃ t' m' q, Counted 2 ⟨pc, fp⟩ m t' m' ∧ StopAt t' m' q ∧ q.nr = BitVec.ofNat 64 nr ∧ q.a1 = BitVec.ofNat 64 c ∧ Agree fp s K m m' := by
  have hroom := hF.room
  -- the two constants
  have s1 := const_step_counted (k := (nr : Int)) (codeAt_left (a := [ci 1 s nr 0]) hc) hF (by omega) hK
    (by simp only [lit32, Bool.and_eq_true, decide_eq_true_eq]; omega)
  let m1 := write m (slot fp (BitVec.ofNat 64 s)) 8 (BitVec.ofInt 64 (nr : Int)).toNat
  have a1 : Agree fp s K m m1 := agree_write hroom (Nat.le_refl _) (by omega) _
  have hc1 : CodeAt m1 (pc + 16) [ci 1 ((s + 1 : Nat) : Int) c 0, ci 23 ((s + 7 : Nat) : Int) s 0] := by
    have := (codeAt_right (a := [ci 1 s nr 0]) hc).agree a1 (codeFar_right (n := 1) (k := 2) hf)
    simpa using this
  have hF1 := hF.agree a1
  have s2 := const_step_counted (j := s + 1) (k := c) (codeAt_left (a := [ci 1 ((s + 1 : Nat) : Int) c 0]) hc1) hF1 (by omega) hK
    (by simp only [lit32, Bool.and_eq_true, decide_eq_true_eq]; omega)
  let m2 := write m1 (slot fp (BitVec.ofNat 64 (s + 1))) 8 (BitVec.ofInt 64 c).toNat
  have a2 : Agree fp s K m1 m2 := agree_write hroom (by omega) (by omega) _
  have hc2 : CodeAt m2 (pc + 16 + 16) [ci 23 ((s + 7 : Nat) : Int) s 0] := by
    have := (codeAt_right (a := [ci 1 ((s + 1 : Nat) : Int) c 0]) hc1).agree a2 (by
      have := codeFar_right (n := 2) (k := 1) hf
      simp only [List.length_singleton, Nat.mul_one]
      rw [BitVec.add_assoc, show (16 : Runner.W) + BitVec.ofNat 64 16 = BitVec.ofNat 64 (16 * 2) by decide]
      exact this)
    simpa using this
  have hF2 := hF1.agree a2
  -- the request
  have hi := hc2 0 (by simp)
  simp only [ci, List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero] at hi
  have hsx : sx (II.f (s : Int)) = BitVec.ofNat 64 s := sx_nat (by omega)
  have r0 : m2.rd64 (slot fp (BitVec.ofNat 64 s)) = some (BitVec.ofInt 64 (nr : Int)) := by
    simp only [m2]
    rw [rd64_write_far (slot_far hroom (by omega) (by omega) (by omega))]
    exact rd64_wr64 (wr64_some (hF.wr s (by omega))) (hF.rd s (by omega))
  have r1 : m2.rd64 (slot fp (BitVec.ofNat 64 (s + 1))) = some (BitVec.ofInt 64 c) :=
    rd64_wr64 (wr64_some (hF1.wr _ (by omega))) (hF1.rd _ (by omega))
  have rd : ∀ i, i < 7 → ∃ v, m2.rd64 (slot fp (BitVec.ofNat 64 (s + i))) = some v := fun i hi =>
    ⟨_, by simp only [Runner.Mem.rd64, hF2.rd (s + i) (by omega), ↓reduceIte]; rfl⟩
  obtain ⟨v2, r2⟩ := rd 2 (by decide)
  obtain ⟨v3, r3⟩ := rd 3 (by decide)
  obtain ⟨v4, r4⟩ := rd 4 (by decide)
  obtain ⟨v5, r5⟩ := rd 5 (by decide)
  obtain ⟨v6, r6⟩ := rd 6 (by decide)
  refine ⟨_, m2, ⟨BitVec.ofInt 64 (nr : Int), BitVec.ofInt 64 c, v2, v3, v4, v5, v6⟩, s1.trans s2,
    runTo_sys (t := ⟨pc + 16 + 16, fp⟩) hi (by rw [hsx]; exact r0) ?_ ?_ ?_ ?_ ?_ ?_,
    by rw [BitVec.ofInt_natCast], ?_, a1.trans a2⟩
  · rw [hsx, show (8 : Runner.W) = BitVec.ofNat 64 (8 * 1) by rfl, slot_plus]; exact r1
  · rw [hsx, show (16 : Runner.W) = BitVec.ofNat 64 (8 * 2) by rfl, slot_plus]; exact r2
  · rw [hsx, show (24 : Runner.W) = BitVec.ofNat 64 (8 * 3) by rfl, slot_plus]; exact r3
  · rw [hsx, show (32 : Runner.W) = BitVec.ofNat 64 (8 * 4) by rfl, slot_plus]; exact r4
  · rw [hsx, show (40 : Runner.W) = BitVec.ofNat 64 (8 * 5) by rfl, slot_plus]; exact r5
  · rw [hsx, show (48 : Runner.W) = BitVec.ofNat 64 (8 * 6) by rfl, slot_plus]; exact r6
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofInt, BitVec.toNat_ofNat]
    omega

theorem sys_counted {m : Runner.Mem} {pc fp : Runner.W} {K nr c s : Nat} (hc : CodeAt m pc (sysC nr c s))
    (hf : CodeFar pc 3 fp K) (hF : FrameOK m fp K) (hs : s + 8 ≤ K) (hK : K < 2 ^ 31) (hcode : c < 2 ^ 31)
    (hnr : nr < 2 ^ 31) :
    ∃ t' m' q, Counted 2 ⟨pc, fp⟩ m t' m' ∧ StopAt t' m' q ∧ q.nr = BitVec.ofNat 64 nr ∧ q.a1 = BitVec.ofNat 64 c := by
  obtain ⟨t, m', q, run, stop, nr, arg, _⟩ :=
    sys_counted_frame hc hf hF hs hK hcode hnr
  exact ⟨t, m', q, run, stop, nr, arg⟩

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


/-- Constant materialization retains exact instruction counts and the writable-frame invariant. -/
theorem const_counted_ok {m : Runner.Mem} {pc fp : Runner.W} {K d : Nat}
    {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop} {n : Int}
    (literal : lit32 n = true) (inside : d < K)
    (pre : Pre L m pc fp K d [ci 1 d n 0] ρ W reserved) :
    CountedOk 1 m pc fp K d [ci 1 d n 0] (· = BitVec.ofInt 64 n) := by
  obtain ⟨hw, rd, agree⟩ := wr_slot pre.frame inside (BitVec.ofInt 64 n)
  exact ⟨_, const_step_counted pre.code pre.frame inside pre.small literal,
    agree, _, rd, rfl⟩

/-- The existing base-65536 template executes exactly four instructions per digit. -/
theorem konstWL_counted_ok {fp : Runner.W} {K d : Nat}
    {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop} (k n : Nat)
    (bound : n < 65536 ^ k) (room : d + 2 ≤ K)
    {m : Runner.Mem} {pc : Runner.W}
    (pre : Pre L m pc fp K d (konstWL k n d).1 ρ W reserved) :
    CountedOk (4 * k + 1) m pc fp K d (konstWL k n d).1 (· = BitVec.ofNat 64 n) := by
  induction k generalizing n m pc with
  | zero =>
    have : n = 0 := by simpa using bound
    subst n
    exact const_counted_ok (by decide) (by omega) pre
  | succ k ih =>
    have quotient : n / 65536 < 65536 ^ k := by rw [Nat.pow_succ] at bound; omega
    have digit : lit32 (n % 65536 : Nat) = true := lit32_nat (by omega)
    rw [show 4 * (k + 1) + 1 = (4 * k + 1 + 1 + 1) + 1 + 1 by omega]
    apply bin_counted_keep (na := 4 * k + 3) (nb := 1) (o := 3)
      (Pa := fun w => w = BitVec.ofNat 64 (n / 65536) * BitVec.ofInt 64 65536)
      (Pb := fun w => w = BitVec.ofInt 64 (n % 65536 : Nat))
      (g := fun a b => some (a + b)) ?_ ?_ ?_ rfl (by decide) (by omega) pre
    · apply bin_counted_keep (na := 4 * k + 1) (nb := 1) (o := 5) (ih _ quotient pre.left.left.left.left)
        (fun _ _ _ hp => const_counted_ok (by decide) (by omega) hp)
        (fun a b ha hb => ⟨_, rfl, by rw [ha, hb]⟩) rfl (by decide) (by omega) pre.left.left
    · intro m pc _ hp
      exact const_counted_ok digit (by omega) hp
    · intro a b ha hb
      refine ⟨_, rfl, ?_⟩
      rw [ha, hb, BitVec.ofInt_natCast,
        show BitVec.ofInt 64 65536 = BitVec.ofNat 64 65536 from rfl,
        ← BitVec.ofNat_mul, ← BitVec.ofNat_add]
      exact congrArg (BitVec.ofNat 64) (by omega)

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
      ExprCost L reserved (.lit n) d (if lit32 n then 1 else 17) (· = BitVec.ofInt 64 n)
  | truth {d : Nat} : ExprCost L reserved .tru d 1 (· = 1)
  | falsity {d : Nat} : ExprCost L reserved .fls d 1 (· = 0)
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
      simpa only [accepted, ite_true] using const_counted_ok accepted (by omega) pre
    next large =>
      split at lower
      · cases lower
        have room : d' + 2 ≤ K := by simp only [konstWL, bin2] at fits; omega
        have run := konstWL_counted_ok 4 (BitVec.ofInt 64 n').toNat (BitVec.isLt _) room pre
        simpa only [if_neg large, BitVec.ofNat_toNat, BitVec.setWidth_eq, konstWL, bin2] using run
      · contradiction
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
  | binary equation left right values opcode byte ihA ihB =>
    rw [equation] at lower
    exact bin2_counted lower fits
      (fun ca ta ha ht m pc hp => ihA ha ht hp)
      (fun cb tb hb ht m pc hp => ihB hb ht hp) values opcode byte pre

/-- Quantitative normal block outcome, retaining the same world, environment
    and protected-slot obligations as `Reach`. -/
def CountedReach (n : Nat) (L : Lay D) {Γ : Ctx} (fp : Runner.W)
    (lo K : Nat) (pr : List Nat) (t : T) (m : Runner.Mem)
    (e : Runner.W) (σ : World D) (ρ : Env D Γ) (reserved : Nat := 0) : Prop :=
  ∃ m', Counted n t m ⟨e, fp⟩ m' ∧ AgreeW L fp lo K m m' ∧
    EnvAt L m' fp ρ reserved ∧ WeltAt m' L σ ∧ Keeps fp pr m m'

theorem CountedReach.forget {n Γ fp lo K pr t m e σ ρ reserved}
    (h : CountedReach n L (Γ := Γ) fp lo K pr t m e σ ρ reserved) :
    Reach L fp lo K pr t m e σ ρ reserved := by
  obtain ⟨m', run, rest⟩ := h
  exact ⟨m', run.forget, rest⟩

/-- A counted pending hardware request; no hardware completion is asserted. -/
def CountedStops (n : Nat) (t : T) (m : Mem) (c : Nat) : Prop :=
  ∃ t' m' q, Counted n t m t' m' ∧ StopAt t' m' q ∧
    q.nr = 231 ∧ q.a1 = BitVec.ofNat 64 c

theorem CountedStops.forget {n t m c} (h : CountedStops n t m c) : Stops t m c := by
  obtain ⟨t', m', q, run, rest⟩ := h
  exact ⟨t', m', q, run.forget, rest⟩

/-- Return costs use the caller endpoint and the canonical return ABI. -/
def CountedRetZ (n : Nat) (L : Lay D) (P : Programm D) (f : D.Fn) (σ0 : World D) (ρ0 : Env D (D.params f)) (fp : Runner.W) (K : Nat)
    (rp cfp : Runner.W) (t : T) (m : Runner.Mem) (σ' : World D) (v : ErgVal D (D.erg f)) : Prop :=
  if wahr? (eval σ0 (P.ensures f) (σ'.lese (vertragVon D f).ende (P.ensures f).orte) (ergEnv (D.erg f) v ρ0)) = false
  then CountedStops n t m 102
  else ∃ m', Counted n t m ⟨rp, cfp⟩ m' ∧ AgreeW L fp 2 K m m' ∧
    (∃ w, m'.rd64 (slot fp (BitVec.ofNat 64 2)) = some w ∧ EncErg L (D.erg f) v w ∧ ReturnFlag m' fp (D.params f).length true) ∧ WeltAt m' L σ'

def CountedRetWhy (n : Nat) (L : Lay D) (f : D.Fn) (fp : Runner.W) (K : Nat) (rp cfp : Runner.W)
    (t : T) (m : Runner.Mem) (σ : World D) (r : Fin (D.gruende f)) : Prop :=
  ∃ m', Counted n t m ⟨rp, cfp⟩ m' ∧ AgreeW L fp 2 K m m' ∧
    m'.rd64 (slot fp (BitVec.ofNat 64 2)) = some (BitVec.ofNat 64 r.val) ∧
    ReturnFlag m' fp (D.params f).length false ∧ WeltAt m' L σ

def CountedSim (n : Nat) (L : Lay D) (P : Programm D) (f : D.Fn) (σ0 : World D) (ρ0 : Env D (D.params f)) (rp cfp : Runner.W)
    {l : Bool} {Γ : Ctx} (fp : Runner.W) (lo K : Nat) (pr : List Nat) (t : T) (m : Runner.Mem) (e eL eN : Runner.W) (o : Ausgang (vertragVon D f) l Γ) (reserved : Nat := 0) : Prop :=
  match o with
  | .ok σ' ρ' => CountedReach n L fp lo K pr t m e σ' ρ' reserved
  | .leave _ σ' ρ' => CountedReach n L fp lo K pr t m eL σ' ρ' reserved
  | .next _ σ' ρ' => CountedReach n L fp lo K pr t m eN σ' ρ' reserved
  | .zurueck σ' v => CountedRetZ n L P f σ0 ρ0 fp K rp cfp t m σ' v
  | .logik c => CountedStops n t m (logikCode c)
  | .hardware h => CountedStops n t m (hwCode h)
  | .why σ' r => CountedRetWhy n L f fp K rp cfp t m σ' r
theorem CountedRetZ.forget {n P f σ0 ρ0 fp K rp cfp t m σ v}
    (h : CountedRetZ n L P f σ0 ρ0 fp K rp cfp t m σ v) :
    RetZ L P f σ0 ρ0 fp K rp cfp t m σ v := by
  unfold CountedRetZ at h
  unfold RetZ
  split at h
  · rename_i hp
    rw [if_pos hp]
    exact h.forget
  · rename_i hp
    rw [if_neg hp]
    obtain ⟨m', run, rest⟩ := h
    exact ⟨m', run.forget, rest⟩

theorem CountedRetWhy.forget {n f fp K rp cfp t m σ r}
    (h : CountedRetWhy n L f fp K rp cfp t m σ r) :
    RetWhy L f fp K rp cfp t m σ r := by
  obtain ⟨m', run, rest⟩ := h
  exact ⟨m', run.forget, rest⟩

/-- Erasure preserves precisely the existing simulation outcome index. -/
theorem CountedSim.forget {n P f σ0 ρ0 rp cfp l Γ fp lo K pr t m e eL eN reserved}
    {o : Ausgang (vertragVon D f) l Γ}
    (h : CountedSim n L P f σ0 ρ0 rp cfp fp lo K pr t m e eL eN o reserved) :
    Sim L P f σ0 ρ0 rp cfp fp lo K pr t m e eL eN o reserved := by
  cases o with
  | ok σ ρ => exact CountedReach.forget h
  | leave _ σ ρ => exact CountedReach.forget h
  | next _ σ ρ => exact CountedReach.forget h
  | zurueck σ v => exact CountedRetZ.forget h
  | why σ r => exact CountedRetWhy.forget h
  | logik c => exact CountedStops.forget h
  | hardware c => exact CountedStops.forget h

/-- Prefix composition keeps the counted endpoint and all observations joint. -/
theorem CountedReach.prefix {n k Γ fp lo K pr t0 t m0 m e σ ρ reserved}
    (run : Counted k t0 m0 t m) (agree : AgreeW L fp lo K m0 m)
    (keep : Keeps fp pr m0 m)
    (h : CountedReach n L (Γ := Γ) fp lo K pr t m e σ ρ reserved) :
    CountedReach (k + n) L fp lo K pr t0 m0 e σ ρ reserved := by
  obtain ⟨m', tail, frame, env, world, kept⟩ := h
  exact ⟨m', run.trans tail, agree.trans frame, env, world, keep.trans kept⟩

theorem CountedStops.prefix {n k t0 t m0 m c}
    (run : Counted k t0 m0 t m) (h : CountedStops n t m c) :
    CountedStops (k + n) t0 m0 c := by
  obtain ⟨t', m', q, tail, rest⟩ := h
  exact ⟨t', m', q, run.trans tail, rest⟩

theorem CountedRetZ.prefix {n k : Nat} {L : Lay D} {P : Programm D} {f : D.Fn} {σ0 : World D} {ρ0 : Env D (D.params f)} {fp : Runner.W}
    {K : Nat} {rp cfp : Runner.W} {t0 t : T} {m0 m : Runner.Mem} {σ' : World D} {v : ErgVal D (D.erg f)}
    (h : Counted k t0 m0 t m) (ha : AgreeW L fp 2 K m0 m) (hs : CountedRetZ n L P f σ0 ρ0 fp K rp cfp t m σ' v) :
    CountedRetZ (k + n) L P f σ0 ρ0 fp K rp cfp t0 m0 σ' v := by
  simp only [CountedRetZ] at hs ⊢
  split
  · next hf => rw [if_pos hf] at hs; exact CountedStops.prefix h hs
  · next hf =>
    rw [if_neg hf] at hs
    obtain ⟨m', s, a, hw, hw'⟩ := hs
    exact ⟨m', h.trans s, ha.trans a, hw, hw'⟩

theorem CountedRetWhy.prefix {n k : Nat} {f : D.Fn} {fp : Runner.W} {K : Nat} {rp cfp : Runner.W}
    {t0 t : T} {m0 m : Runner.Mem} {σ : World D} {r : Fin (D.gruende f)}
    (h : Counted k t0 m0 t m) (ha : AgreeW L fp 2 K m0 m) (hs : CountedRetWhy n L f fp K rp cfp t m σ r) :
    CountedRetWhy (k + n) L f fp K rp cfp t0 m0 σ r := by
  obtain ⟨m', s, a, hw, flag, hw'⟩ := hs
  exact ⟨m', h.trans s, ha.trans a, hw, flag, hw'⟩

theorem CountedSim.prefix {n k : Nat} {P : Programm D} {f : D.Fn} {σ0 : World D}
    {ρ0 : Env D (D.params f)} {rp cfp fp : W} {l : Bool} {Γ : Ctx}
    {lo K reserved : Nat} {pr : List Nat} {o : Ausgang (vertragVon D f) l Γ} {t0 t : T} {m0 m : Runner.Mem} {e eL eN : Runner.W}
    (hl : FB ≤ lo) (h : Counted k t0 m0 t m) (ha : AgreeW L fp lo K m0 m) (hk : Keeps fp pr m0 m)
    (hs : CountedSim n L P f σ0 ρ0 rp cfp fp lo K pr t m e eL eN o reserved) : CountedSim (k + n) L P f σ0 ρ0 rp cfp fp lo K pr t0 m0 e eL eN o reserved := by
  cases o with
  | ok σ ρ => exact CountedReach.prefix h ha hk hs
  | leave _ σ ρ => exact CountedReach.prefix h ha hk hs
  | next _ σ ρ => exact CountedReach.prefix h ha hk hs
  | zurueck σ' v =>
    have hFB3 : FB = 4 := rfl
    exact CountedRetZ.prefix h (ha.mono (by omega)) hs
  | logik c => exact CountedStops.prefix h hs
  | hardware c => exact CountedStops.prefix h hs
  | why σ' r => exact CountedRetWhy.prefix h (ha.mono (by have : FB = 4 := rfl; omega)) hs

/-- Both source loop jumps retain one joint state and execute exactly one
    instruction. The signed displacement is justified by accepted lowering. -/
theorem jmp_counted_reach {Γ : Ctx} {m : Mem} {pc fp : W}
    {lo K reserved : Nat} {pr : List Nat} {x : Int}
    {σ : World D} {ρ : Env D Γ}
    (code : CodeAt m pc [ci 18 (16 + x) 0 0])
    (fits : lit32 (16 + x) = true)
    (env : EnvAt L m fp ρ reserved) (world : WeltAt m L σ) :
    CountedReach 1 L fp lo K pr ⟨pc, fp⟩ m
      (pc + 16 + BitVec.ofInt 64 x) σ ρ reserved := by
  have ins := code 0 (by simp)
  simp only [ci, List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero] at ins
  have run := Counted.next (run_step (t := ⟨pc, fp⟩) ins (by decide)
    (run_jmp (t := ⟨pc, fp⟩) ins)) (Counted.refl _ _)
  refine ⟨m, ?_, AgreeW.refl _ _ _ _ _, env, world, Keeps.refl _ _ _⟩
  simpa only [sx_lit fits, BitVec.ofInt_add, BitVec.add_assoc,
    show BitVec.ofInt 64 16 = (16 : W) from rfl] using run

/-- Empty blocks execute no instructions and preserve the entire state. -/
theorem countedBlockNil_case {Γ : Ctx} {fp pc : Runner.W} {lo K : Nat}
    {pr : List Nat} {m : Runner.Mem} {σ : World D} {ρ : Env D Γ}
    (env : EnvAt L m fp ρ reserved) (world : WeltAt m L σ) :
    CountedReach 0 L fp lo K pr ⟨pc, fp⟩ m pc σ ρ reserved :=
  ⟨m, .refl _ _, AgreeW.refl _ _ _ _ _, env, world, Keeps.refl _ _ _⟩

/-- Actual `lowB .cons` composition for normal outcomes. The second child is
    proved at the memory produced by the first, with code and frame restored
    from its agreement proof. Counts include all executed callee instructions;
    neither child count is replaced by its static code length. -/
theorem countedBlockCons_case
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λmid Λ' : List (Res D)}
    {s : Stmt D V l Γ Λ Λmid} {rest : Block D V l Γ Λmid Λ'}
    {passes lo K Ks ns nr top : Nat} {A : D.Fn → Nat}
    {ens : List II × Nat} {pr : List Nat} {ex : Int × Int}
    {code : List II} {m : Runner.Mem} {pc fp : Runner.W}
    {ρ ρ1 ρ2 : Env D Γ} {σ1 σ2 : World D}
    (lower : lowB (reserved := reserved) passes A L lo ens pr ex (.cons s rest) =
      some (code, top))
    (inside : WIn L fp Ks K)
    (pre : PreS L m pc fp K (frei Γ reserved) code ρ reserved)
    (stmtRuns : ∀ cr tr cs ts,
      lowB (reserved := reserved) passes A L lo ens pr ex rest = some (cr, tr) →
      lowS (reserved := reserved) passes A L lo ens pr (exPlus ex cr.length) s = some (cs, ts) →
      PreS L m pc fp K (frei Γ reserved) cs ρ reserved →
      CountedReach ns L fp lo K pr ⟨pc, fp⟩ m
        (pc + BitVec.ofNat 64 (16 * cs.length)) σ1 ρ1 reserved)
    (restRuns : ∀ cr tr,
      lowB (reserved := reserved) passes A L lo ens pr ex rest = some (cr, tr) →
      ∀ m' pc', PreS L m' pc' fp K (frei Γ reserved) cr ρ1 reserved →
      WeltAt m' L σ1 →
      CountedReach nr L fp lo K pr ⟨pc', fp⟩ m'
        (pc' + BitVec.ofNat 64 (16 * cr.length)) σ2 ρ2 reserved) :
    CountedReach (ns + nr) L fp lo K pr ⟨pc, fp⟩ m
      (pc + BitVec.ofNat 64 (16 * code.length)) σ2 ρ2 reserved := by
  simp only [lowB, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at lower
  obtain ⟨⟨cr, tr⟩, hr, ⟨cs, ts⟩, hs, out⟩ := lower
  simp only [Prod.mk.injEq] at out
  obtain ⟨rfl, rfl⟩ := out
  obtain ⟨m1, run1, agree1, env1, world1, keep1⟩ :=
    stmtRuns cr tr cs ts hr hs pre.left
  have far := codeFar_right (n := cs.length) (k := cr.length) (by simpa using pre.far)
  have nextPre : PreS L m1 (pc + BitVec.ofNat 64 (16 * cs.length)) fp K
      (frei Γ reserved) cr ρ1 reserved :=
    ⟨pre.ctx, pre.small, frameOK_agreeW pre.frame agree1,
      codeAt_agreeWIn inside agree1 (codeAt_right pre.code) far,
      far, env1, trivial, wstab_true _ _⟩
  obtain ⟨m2, run2, agree2, env2, world2, keep2⟩ :=
    restRuns cr tr hr m1 _ nextPre world1
  refine ⟨m2, ?_, agree1.trans agree2, env2, world2, keep1.trans keep2⟩
  simpa only [List.length_append, pc_add] using run1.trans run2

/-- A real lexical binding obtains its instruction count from the recursive
    expression certificate, then executes the actual lowered continuation.
    The source value is supplied through `Enc`, as in `bindValue_ok`. -/
theorem countedBlockBind_case
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {τ : Ty}
    {e : Expr D Γ Λ τ} {rest : Block D V l (τ :: Γ) Λ Λ'}
    {passes lo K Ks ne nr top : Nat} {A : D.Fn → Nat}
    {ens : List II × Nat} {pr : List Nat} {ex : Int × Int}
    {code : List II} {m : Runner.Mem} {pc fp : Runner.W}
    {ρ : Env D Γ} {v : Wert D τ} {ρ2 : Env D (τ :: Γ)} {σ σ2 : World D}
    (certificate : ExprCost L reserved e (frei Γ reserved) ne (Enc L τ v))
    (lower : lowB (reserved := reserved) passes A L lo ens pr ex (.bind e rest) =
      some (code, top))
    (fits : top ≤ Ks) (inside : WIn L fp Ks K)
    (low : lo ≤ frei Γ reserved) (hprotected : ∀ j ∈ pr, j < frei Γ reserved)
    (pre : PreS L m pc fp K (frei Γ reserved) code ρ reserved)
    (world : WeltAt m L σ)
    (restRuns : ∀ cr tr,
      lowB (reserved := reserved) passes A L lo ens pr ex rest = some (cr, tr) →
      ∀ m' pc', PreS L m' pc' fp K (frei Γ reserved + 1) cr (Env.cons v ρ) reserved →
      WeltAt m' L σ →
      CountedReach nr L fp lo K pr ⟨pc', fp⟩ m'
        (pc' + BitVec.ofNat 64 (16 * cr.length)) σ2 ρ2 reserved) :
    CountedReach (ne + nr) L fp lo K pr ⟨pc, fp⟩ m
      (pc + BitVec.ofNat 64 (16 * code.length)) σ2 ρ2 reserved := by
  simp only [lowB, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at lower
  obtain ⟨⟨ce, te⟩, he, ⟨cr, tr⟩, hr, out⟩ := lower
  simp only [Prod.mk.injEq] at out
  obtain ⟨rfl, rfl⟩ := out
  have room := lowE_top e _ _ _ he
  have hks := inside.ks
  have hpw := PreS.welt pre.left inside.ks world inside.lay
    (by have := inside.lo; omega)
  obtain ⟨m1, run1, a1s, w, read, encoded⟩ := certificate.sound he
    (Nat.le_trans (Nat.le_max_left _ _) fits) hpw
  have a1 := Agree.widen a1s inside.ks
  have far := codeFar_right (n := ce.length) (k := cr.length) (by simpa using pre.far)
  have nextPre : PreS L m1 (pc + BitVec.ofNat 64 (16 * ce.length)) fp K
      (frei Γ reserved + 1) cr (Env.cons v ρ) reserved :=
    ⟨by simp only [frei, List.length_cons]; omega, pre.small, pre.frame.agree a1,
      (codeAt_right pre.code).agree a1 far, far,
      envAt_cons (envAt_agree pre.env a1 pre.frame (Nat.le_refl _) (by omega))
        read encoded, trivial, wstab_true _ _⟩
  obtain ⟨m2, run2, a2, env2, world2, keep2⟩ := restRuns cr tr hr m1 _ nextPre
    (hpw.wstab m m1 world (a1s.mono (Nat.zero_le _)))
  refine ⟨m2, ?_, (agreeW_of (a1.mono low)).trans a2, env2, world2, ?_⟩
  · simpa only [List.length_append, pc_add] using run1.trans run2
  · exact (keeps_of_agreeW inside a1 hprotected (by omega)).trans keep2

/-- Count a real call opcode, the callee body, and the real return opcode.
    Return addresses and frame restoration are read from the resulting callee
    memory, so a body that corrupts the ABI cannot satisfy this rule. -/
theorem countedCall {t u : T} {m m1 m2 m3 : Runner.Mem}
    {a k c ra rb rc : BitVec 32} {target : Runner.W} {n : Nat}
    (callCode : InsAt m t.pc 20 a k c)
    (targetRead : m.rd64 (slot t.fp (sx a)) = some target)
    (savePC : m.wr64 (slot t.fp (sx k)) (t.pc + 16) = some m1)
    (saveFP : m1.wr64 (slot t.fp (sx k) + 8) t.fp = some m2)
    (callee : Counted n ⟨target, slot t.fp (sx k)⟩ m2 u m3)
    (returnCode : InsAt m3 u.pc 21 ra rb rc)
    (returnPC : m3.rd64 u.fp = some (t.pc + 16))
    (returnFP : m3.rd64 (u.fp + 8) = some t.fp) :
    Counted (n + 2) t m ⟨t.pc + 16, t.fp⟩ m3 := by
  have enter : Counted 1 t m ⟨target, slot t.fp (sx k)⟩ m2 :=
    .next (run_step callCode (by decide)
      (run_call callCode targetRead savePC saveFP)) (.refl _ _)
  have leave : Counted 1 u m3 ⟨t.pc + 16, t.fp⟩ m3 :=
    .next (run_step returnCode (by decide) (run_ret returnPC returnFP)) (.refl _ _)
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using (enter.trans callee).trans leave

/-- A returning expression callee derives its execution count recursively from
    the source certificate. Agreement proves preservation of both ABI cells
    and the return instruction; no post-body ABI or execution premise is used.
    This is an instruction count, not a conversion from declared G costs. -/
theorem ExprCost.returning {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
    {e : Expr D Γ Λ τ} {d n top K : Nat} {P : Runner.W → Prop}
    (certificate : ExprCost L reserved e d n P)
    {code : List II} {m : Runner.Mem} {pc fp resume caller : Runner.W}
    {ρ : Env D Γ} {W : Runner.Mem → Prop}
    (lower : lowE L (reserved := reserved) e d = some (code, top))
    (fits : top ≤ K) (abi : 2 ≤ d) (room : d ≤ K)
    (pre : Pre L m pc fp K d code ρ W reserved)
    (ret : CodeAt m (pc + BitVec.ofNat 64 (16 * code.length)) [ci 21 0 0 0])
    (far : CodeFar (pc + BitVec.ofNat 64 (16 * code.length)) 1 fp K)
    (savedPC : m.rd64 fp = some resume)
    (savedFP : m.rd64 (fp + 8) = some caller) :
    ∃ m', Counted (n + 1) ⟨pc, fp⟩ m ⟨resume, caller⟩ m' ∧
      Agree fp d K m m' ∧
      ∃ w, m'.rd64 (slot fp (BitVec.ofNat 64 d)) = some w ∧ P w := by
  obtain ⟨m', run, agree, value⟩ := certificate.sound lower fits pre
  have ret' := (ret.agree agree far) 0 (by simp)
  simp only [List.getElem_cons_zero, ci, Nat.mul_zero, BitVec.add_zero] at ret'
  have rpc : m'.rd64 fp = some resume := by
    have h := agree_rd_low (i := 0) agree pre.frame.room (by omega) room
    simp only [slot, BitVec.zero_mul, BitVec.add_zero] at h
    exact h.trans savedPC
  have rfp : m'.rd64 (fp + 8) = some caller := by
    have h := agree_rd_low (i := 1) agree pre.frame.room (by omega) room
    have h' : m'.rd64 (fp + 8) = m.rd64 (fp + 8) := by simpa [slot] using h
    exact h'.trans savedFP
  refine ⟨m', ?_, agree, value⟩
  have leave : Counted 1 ⟨pc + BitVec.ofNat 64 (16 * code.length), fp⟩ m'
      ⟨resume, caller⟩ m' :=
    .next (run_step ret' (by decide) (run_ret rpc rfp)) (.refl _ _)
  exact run.trans leave

/-- A checked declaration table in S0IR instruction units for returning
    expression bodies. The exact body cost is derived by `ExprCost`, not
    assumed as an execution premise. The table includes the return opcode;
    the caller's call opcode remains an additional instruction. This is
    independent of `kostenPasst`, whose table counts G own steps. -/
structure CalleeCostCertificate (L : Lay D) (declared : D.Fn → Nat)
    (f : D.Fn) {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
    (reserved : Nat) (e : Expr D Γ Λ τ) (d : Nat)
    (P : Runner.W → Prop) where
  instructions : Nat
  body : ExprCost L reserved e d instructions P
  within : instructions + 1 ≤ declared f

theorem CalleeCostCertificate.returning {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
    {e : Expr D Γ Λ τ} {d top K : Nat} {declared : D.Fn → Nat} {f : D.Fn} {P : Runner.W → Prop}
    (certificate : CalleeCostCertificate L declared f reserved e d P)
    {code : List II} {m : Runner.Mem} {pc fp resume caller : Runner.W}
    {ρ : Env D Γ} {W : Runner.Mem → Prop}
    (lower : lowE L (reserved := reserved) e d = some (code, top))
    (fits : top ≤ K) (abi : 2 ≤ d) (room : d ≤ K)
    (pre : Pre L m pc fp K d code ρ W reserved)
    (ret : CodeAt m (pc + BitVec.ofNat 64 (16 * code.length)) [ci 21 0 0 0])
    (far : CodeFar (pc + BitVec.ofNat 64 (16 * code.length)) 1 fp K)
    (savedPC : m.rd64 fp = some resume)
    (savedFP : m.rd64 (fp + 8) = some caller) :
    ∃ n m', n ≤ declared f ∧ Counted n ⟨pc, fp⟩ m ⟨resume, caller⟩ m' ∧
      Agree fp d K m m' ∧
      ∃ w, m'.rd64 (slot fp (BitVec.ofNat 64 d)) = some w ∧ P w := by
  obtain ⟨m', run, rest⟩ := certificate.body.returning lower fits abi room pre ret far savedPC savedFP
  exact ⟨certificate.instructions + 1, m', certificate.within, run, rest⟩

/-- Declaration-bound execution through the actual call ABI. The entry writes
    are checked before the source-derived callee certificate is applied to the
    resulting memory. The bound includes call and return, in S0IR instructions;
    `Kern` remains the explicit canonical hardware interface. -/
theorem CalleeCostCertificate.call {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
    {e : Expr D Γ Λ τ} {d top K : Nat} {declared : D.Fn → Nat} {f : D.Fn}
    {P : Runner.W → Prop}
    (certificate : CalleeCostCertificate L declared f reserved e d P)
    {code : List II} {m m1 m2 : Runner.Mem} {t : T}
    {a k c : BitVec 32} {target : Runner.W}
    {ρ : Env D Γ} {W : Runner.Mem → Prop}
    (callCode : InsAt m t.pc 20 a k c)
    (targetRead : m.rd64 (slot t.fp (sx a)) = some target)
    (savePC : m.wr64 (slot t.fp (sx k)) (t.pc + 16) = some m1)
    (saveFP : m1.wr64 (slot t.fp (sx k) + 8) t.fp = some m2)
    (lower : lowE L (reserved := reserved) e d = some (code, top))
    (fits : top ≤ K) (abi : 2 ≤ d) (room : d ≤ K)
    (pre : Pre L m2 target (slot t.fp (sx k)) K d code ρ W reserved)
    (ret : CodeAt m2 (target + BitVec.ofNat 64 (16 * code.length)) [ci 21 0 0 0])
    (far : CodeFar (target + BitVec.ofNat 64 (16 * code.length)) 1
      (slot t.fp (sx k)) K)
    (savedPC : m2.rd64 (slot t.fp (sx k)) = some (t.pc + 16))
    (savedFP : m2.rd64 (slot t.fp (sx k) + 8) = some t.fp) :
    ∃ n m', n ≤ declared f + 1 ∧ Counted n t m ⟨t.pc + 16, t.fp⟩ m' ∧
      Agree (slot t.fp (sx k)) d K m2 m' ∧
      ∃ w, m'.rd64 (slot (slot t.fp (sx k)) (BitVec.ofNat 64 d)) = some w ∧ P w := by
  obtain ⟨n, m', bound, run, rest⟩ := certificate.returning lower fits abi room
    pre ret far savedPC savedFP
  have enter : Counted 1 t m ⟨target, slot t.fp (sx k)⟩ m2 :=
    .next (run_step callCode (by decide)
      (run_call callCode targetRead savePC saveFP)) (.refl _ _)
  exact ⟨1 + n, m', by omega, enter.trans run, rest⟩

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
