/- Frame facts for expression binders. -/
import Stage0.Senke.Ausdruck.Lesen

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable {D : Deklaration}

theorem idx_lt : {Γ : Ctx} → {τ : Ty} → (x : Var Γ τ) → Var.idx x < Γ.length
  | _, _, .here => by simp [Var.idx]
  | _, _, .there x => by have := idx_lt x; simp [Var.idx]; omega

theorem vslot_here {Γ : Ctx} {τ : Ty} : vslot (Var.here : Var (τ :: Γ) τ) = frei Γ := by
  simp [vslot, frei, Var.idx]

theorem vslot_there {Γ : Ctx} {τ σ : Ty} (y : Var Γ τ) : vslot (Var.there y : Var (σ :: Γ) τ) = vslot y := by
  have := idx_lt y
  simp [vslot, Var.idx]; omega

theorem envAt_cons {m : Runner.Mem} {fp : Runner.W} {Γ : Ctx} {ρ : Env D Γ} {τ : Ty} {v : Wert D τ}
    {w : Runner.W} (h : EnvAt m fp ρ) (hw : m.rd64 (slot fp (BitVec.ofNat 64 (frei Γ))) = some w)
    (he : Enc τ v w) : EnvAt m fp (Env.cons v ρ : Env D (τ :: Γ)) := by
  intro τ' y
  cases y with
  | here => exact ⟨w, by rw [vslot_here]; exact hw, he⟩
  | there y =>
    obtain ⟨w', hw', he'⟩ := h τ' y
    exact ⟨w', by rw [vslot_there]; exact hw', he'⟩

theorem envAt_tail {m : Runner.Mem} {fp : Runner.W} {Γ : Ctx} {τ : Ty} {ρ : Env D (τ :: Γ)} (h : EnvAt m fp ρ) :
    EnvAt m fp ρ.tail := by
  intro τ' y
  obtain ⟨w, hw, he⟩ := h τ' (.there y)
  rw [vslot_there] at hw
  cases ρ with
  | cons _ ρ => exact ⟨w, hw, he⟩

/-- Moving one frame word, with the resulting memory explicit. -/
theorem quant_mov [Kern] {m : Runner.Mem} {pc fp : Runner.W} {K dst src : Nat} {v : Runner.W}
    (hf : FrameOK m fp K) (hk : K < 2 ^ 31) (hd : dst < K) (hs : src < K)
    (hc : CodeAt m pc [ci 2 dst src 0]) (hr : m.rd64 (slot fp (BitVec.ofNat 64 src)) = some v) :
    Star ⟨pc, fp⟩ m ⟨pc + 16, fp⟩ (write m (slot fp (BitVec.ofNat 64 dst)) 8 v.toNat) := by
  have hi := hc 0 (by simp)
  simp only [ci, List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero] at hi
  apply Star.one
  apply run_step (t := ⟨pc, fp⟩) hi (by decide)
  simp only [op]
  refine f2_run (t := ⟨pc, fp⟩) hi ?_
  rw [sx_nat (by omega)]
  refine run_rd64 hr ?_
  simp only [ret1]
  refine f1_run (t := ⟨pc, fp⟩) hi ?_
  rw [sx_nat (by omega)]
  exact run_wr64 (wr64_some (hf.wr dst hd))

/-- Reading a word and writing it back preserves each byte of that word. -/
theorem quant_restore_byte {m : Runner.Mem} {a v : Runner.W}
    (hr : m.rd64 a = some v) {j : Nat} (hj : j < 8) :
    BitVec.ofNat 8 (v.toNat / 256 ^ j) = m.b (a + BitVec.ofNat 64 j) := by
  simp only [Runner.Mem.rd64] at hr
  split at hr
  · simp only [Option.some.injEq] at hr
    subst v
    have h0 := (m.b (a + BitVec.ofNat 64 0)).isLt
    have h1 := (m.b (a + BitVec.ofNat 64 1)).isLt
    have h2 := (m.b (a + BitVec.ofNat 64 2)).isLt
    have h3 := (m.b (a + BitVec.ofNat 64 3)).isLt
    have h4 := (m.b (a + BitVec.ofNat 64 4)).isLt
    have h5 := (m.b (a + BitVec.ofNat 64 5)).isLt
    have h6 := (m.b (a + BitVec.ofNat 64 6)).isLt
    have h7 := (m.b (a + BitVec.ofNat 64 7)).isLt
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, le, Nat.reducePow, Nat.zero_add, Nat.mul_one]
    have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by omega
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Nat.reducePow, Nat.div_one] <;> omega
  · cases hr

/-- A borrowed frame word is restored after code that changes only higher scratch slots. -/
theorem quant_restore {m m' : Runner.Mem} {fp v : Runner.W} {s d K : Nat}
    (hf : FrameOK m fp K) (hs : s < d) (hd : d ≤ K)
    (hr : m.rd64 (slot fp (BitVec.ofNat 64 s)) = some v)
    (ha : ∀ x, ¬ inSlots fp d K x → ¬ inSlots fp s (s + 1) x → m'.b x = m.b x)
    (hrd : m'.rd = m.rd) (hwr : m'.wr = m.wr) :
    Agree fp d K m (write m' (slot fp (BitVec.ofNat 64 s)) 8 v.toNat) := by
  refine ⟨hrd, hwr, fun x hx => ?_⟩
  by_cases hb : inSlots fp s (s + 1) x
  · let j := x.toNat - (fp.toNat + 8 * s)
    have hj : j < 8 := by dsimp [j]; unfold inSlots at hb; omega
    have he : x = slot fp (BitVec.ofNat 64 s) + BitVec.ofNat 64 j := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, slot_toNat hf.room (by omega), BitVec.toNat_ofNat]
      have := x.isLt
      unfold inSlots at hb
      dsimp [j]; omega
    rw [he, write_in_b hj (by decide), quant_restore_byte hr hj]
  · have hsmall : fp.toNat + 8 * (s + 1) ≤ 2 ^ 64 := by have := hf.room; omega
    exact ((agree_write (K := s + 1) hsmall (lo := s) (by omega) (by omega) v.toNat).b x hb).trans (ha x hx hb)


end Gabbro.Stage0.Senke
