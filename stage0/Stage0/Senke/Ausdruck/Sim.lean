/-
  File:      stage0/Stage0/Senke/Ausdruck/Sim.lean
  Subject:   `ir_sim` for expressions: the lowered code of `e` computes the word of `eval e` into its slot.

  `Pre`: the code at `pc`, apart from the frame; the frame's slots `0 .. K-1` readable and writable; the
  variables in their slots below `d`. `Ok`: the IR thread runs from `pc` to the end of the code, changes only the
  slots from `d` on, and leaves in slot `d` a word with the property `P`. `lowE_ok`: for every expression the
  lowering accepts, `Ok` with `P` = the word of `eval σ₀ e σ ρ`.
-/
import Stage0.Senke.Hilfe

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable [Kern]

variable {D : Deklaration} {L : Lay D}

variable {reserved : Nat}

/-- `W` survives every run that writes only the frame's slots: a fact about memory outside the frame (the world). -/
def WStab (W : Runner.Mem → Prop) (fp : Runner.W) (K : Nat) : Prop := ∀ m m', W m → Agree fp 0 K m m' → W m'

theorem wstab_true (fp : Runner.W) (K : Nat) : WStab (fun _ => True) fp K := fun _ _ _ _ => trivial

/-- What a piece of code may rely on: the context's slots below `d`, the frame of `K` slots, the code at `pc`, the
    environment in the frame, and a fact `W` about the memory outside the frame. -/
structure Pre (L : Lay D) (m : Runner.Mem) (pc fp : Runner.W) (K d : Nat) (cd : List II) {Γ : Ctx} (ρ : Env D Γ)
    (W : Runner.Mem → Prop) (reserved : Nat := 0) : Prop where
  ctx : frei Γ reserved ≤ d
  small : K < 2 ^ 31
  frame : FrameOK m fp K
  code : CodeAt m pc cd
  far : CodeFar pc cd.length fp K
  env : EnvAt L m fp ρ reserved
  welt : W m
  wstab : WStab W fp K

/-- A statement's precondition: nothing outside the frame is assumed in it (the world comes separately). -/
abbrev PreS (L : Lay D) (m : Runner.Mem) (pc fp : Runner.W) (K d : Nat) (cd : List II) {Γ : Ctx} (ρ : Env D Γ) : Prop :=
  Pre L m pc fp K d cd ρ (fun _ => True)

def Ok (m : Runner.Mem) (pc fp : Runner.W) (K d : Nat) (code : List II) (P : Runner.W → Prop) : Prop :=
  ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * code.length), fp⟩ m' ∧ Agree fp d K m m' ∧
    ∃ w, m'.rd64 (slot fp (BitVec.ofNat 64 d)) = some w ∧ P w

theorem pc_add16 (pc : Runner.W) (n : Nat) :
    pc + BitVec.ofNat 64 (16 * n) + 16#64 = pc + BitVec.ofNat 64 (16 * (n + 1)) := by
  rw [BitVec.add_assoc, Nat.mul_add, BitVec.ofNat_add (16 * n)]

/-- The first part of a code, and the rest from where it ends. -/
theorem Pre.left {m : Runner.Mem} {pc fp : Runner.W} {K d : Nat} {a b : List II} {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} (h : Pre L m pc fp K d (a ++ b) ρ W reserved) : Pre L m pc fp K d a ρ W reserved :=
  ⟨h.ctx, h.small, h.frame, codeAt_left h.code, codeFar_left (by simpa using h.far), h.env, h.welt, h.wstab⟩

theorem Pre.next {m m' : Runner.Mem} {pc fp : Runner.W} {K d d' : Nat} {a b : List II} {Γ : Ctx}
    {ρ : Env D Γ} {W : Runner.Mem → Prop} (h : Pre L m pc fp K d (a ++ b) ρ W reserved) (ha : Agree fp d K m m') (hd : d ≤ d')
    (hK : d ≤ K) : Pre L m' (pc + BitVec.ofNat 64 (16 * a.length)) fp K d' b ρ W reserved :=
  have hf := codeFar_right (n := a.length) (k := b.length) (by simpa using h.far)
  ⟨Nat.le_trans h.ctx hd, h.small, h.frame.agree ha, (codeAt_right h.code).agree ha hf, hf,
   envAt_agree h.env ha h.frame h.ctx hK, h.wstab m m' h.welt (ha.mono (Nat.zero_le _)), h.wstab⟩

/-- A binary operation whose first part has run (`hA` for this memory). -/
theorem bin_ok_keep {m : Runner.Mem} {pc fp : Runner.W} {K d o : Nat} {ca cb : List II} {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop}
    {Pa Pb P : Runner.W → Prop} {g : Runner.W → Runner.W → Option Runner.W}
    (hA : Ok m pc fp K d ca Pa)
    (hB : ∀ m' pc, Agree fp d K m m' → Pre L m' pc fp K (d + 1) cb ρ W → Ok m' pc fp K (d + 1) cb Pb)
    (hg : ∀ wa wb, Pa wa → Pb wb → ∃ r, g wa wb = some r ∧ P r) (hop : op o = bin g) (ho : o < 256)
    (hK : d + 1 < K) (h : Pre L m pc fp K d (ca ++ cb ++ [ci o d d (d + 1)]) ρ W) :
    Ok m pc fp K d (ca ++ cb ++ [ci o d d (d + 1)]) P := by
  have h' : Pre L m pc fp K d (ca ++ (cb ++ [ci o d d (d + 1)])) ρ W := by simpa using h
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
  simp only [ci, List.getElem_cons_zero, Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at hi
  have s3 := star_ins (fp := fp) (m' := write m2 (slot fp (BitVec.ofNat 64 d)) 8 r.toNat) h2.code ho (by
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

/-- A binary operation with a memory-independent proof for its second operand. -/
theorem bin_ok2 {m : Runner.Mem} {pc fp : Runner.W} {K d o : Nat} {ca cb : List II} {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} {Pa Pb P : Runner.W → Prop} {g : Runner.W → Runner.W → Option Runner.W}
    (hA : Ok m pc fp K d ca Pa)
    (hB : ∀ m pc, Pre L m pc fp K (d + 1) cb ρ W → Ok m pc fp K (d + 1) cb Pb)
    (hg : ∀ wa wb, Pa wa → Pb wb → ∃ r, g wa wb = some r ∧ P r) (hop : op o = bin g) (ho : o < 256)
    (hK : d + 1 < K) (h : Pre L m pc fp K d (ca ++ cb ++ [ci o d d (d + 1)]) ρ W) :
    Ok m pc fp K d (ca ++ cb ++ [ci o d d (d + 1)]) P :=
  bin_ok_keep hA (fun m pc _ hp => hB m pc hp) hg hop ho hK h

/-- A binary operation: `a` into `d`, `b` into `d+1`, then the instruction `o` (whose step is `bin g`). -/
theorem bin_ok {m : Runner.Mem} {pc fp : Runner.W} {K d o : Nat} {ca cb : List II} {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop}
    {Pa Pb P : Runner.W → Prop} {g : Runner.W → Runner.W → Option Runner.W}
    (hA : ∀ m pc, Pre L m pc fp K d ca ρ W → Ok m pc fp K d ca Pa)
    (hB : ∀ m pc, Pre L m pc fp K (d + 1) cb ρ W → Ok m pc fp K (d + 1) cb Pb)
    (hg : ∀ wa wb, Pa wa → Pb wb → ∃ r, g wa wb = some r ∧ P r) (hop : op o = bin g) (ho : o < 256)
    (hK : d + 1 < K) (h : Pre L m pc fp K d (ca ++ cb ++ [ci o d d (d + 1)]) ρ W) :
    Ok m pc fp K d (ca ++ cb ++ [ci o d d (d + 1)]) P := by
  have h' : Pre L m pc fp K d (ca ++ (cb ++ [ci o d d (d + 1)])) ρ W := by simpa using h
  exact bin_ok2 (hA m pc h'.left) hB hg hop ho hK h

/-- One instruction that writes slot `d` from a step `ret1 t v`. -/
theorem one_ok {m : Runner.Mem} {pc fp : Runner.W} {K d : Nat} {i : II} {Γ : Ctx} {ρ : Env D Γ} {v : Runner.W}
    {W : Runner.Mem → Prop}
    {P : Runner.W → Prop} (h : Pre L m pc fp K d [i] ρ W) (ho : i.o < 256) (hd : d < K) (hv : P v)
    (hr : ∀ m', m.wr64 (slot fp (BitVec.ofNat 64 d)) v = some m' → Run (op i.o ⟨pc, fp⟩) m ⟨pc + 16, fp⟩ m') :
    Ok m pc fp K d [i] P := by
  obtain ⟨hw, hrd, a3⟩ := wr_slot h.frame hd v
  exact ⟨_, star_ins h.code ho (hr _ hw), a3, v, hrd, hv⟩

theorem const_ok {m : Runner.Mem} {pc fp : Runner.W} {K d : Nat} {k : Int} {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop}
    (h : Pre L m pc fp K d [ci 1 d k 0] ρ W) (hk : lit32 k = true) (hd : d < K) :
    Ok m pc fp K d [ci 1 d k 0] (· = BitVec.ofInt 64 k) := by
  have := h.small
  refine one_ok h (by simp [ci]) hd rfl fun m' hw => ?_
  have hi := h.code 0 (by simp)
  simp only [ci, List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero] at hi
  simp only [ci, op]
  refine f2_run (t := ⟨pc, fp⟩) hi ?_
  simp only [ret1]
  refine f1_run (t := ⟨pc, fp⟩) hi ?_
  rw [sx_lit hk, sx_nat (by omega)]
  exact run_wr64 hw

theorem mov_ok {m : Runner.Mem} {pc fp : Runner.W} {K d s : Nat} {Γ : Ctx} {ρ : Env D Γ} {v : Runner.W}
    {W : Runner.Mem → Prop}
    (h : Pre L m pc fp K d [ci 2 d s 0] ρ W) (hs : s < K) (hd : d < K)
    (hv : m.rd64 (slot fp (BitVec.ofNat 64 s)) = some v) :
    Ok m pc fp K d [ci 2 d s 0] (· = v) := by
  have := h.small
  refine one_ok h (by simp [ci]) hd rfl fun m' hw => ?_
  have hi := h.code 0 (by simp)
  simp only [ci, List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero] at hi
  simp only [ci, op]
  refine f2_run (t := ⟨pc, fp⟩) hi ?_
  rw [sx_nat (by omega)]
  refine run_rd64 hv ?_
  simp only [ret1]
  refine f1_run (t := ⟨pc, fp⟩) hi ?_
  rw [sx_nat (by omega)]
  exact run_wr64 hw

end Gabbro.Stage0.Senke
