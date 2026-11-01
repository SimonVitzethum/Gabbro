/- Frame facts for expression binders. -/
module
public import Stage0.Senke.Ausdruck.Lesen
public import Stage0.Senke.Ausdruck.Quant.Literal
@[expose] public section


namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable {D : Deklaration} {L : Lay D} {reserved : Nat}

/-- Different slots of a frame are apart. -/
theorem slot_far {fp : Runner.W} {K i j : Nat} (hr : fp.toNat + 8 * K ≤ 2 ^ 64) (hi : i < K) (hj : j < K)
    (hne : i ≠ j) : Far (slot fp (BitVec.ofNat 64 i)) 8 (slot fp (BitVec.ofNat 64 j)) 8 := by
  rw [Far, slot_toNat hr hi, slot_toNat hr hj]; omega

/-- Header/status writes preserve every limb of a disjoint value, on either side
    of the write. In particular a return cache cannot stand in for its payload. -/
theorem ValueAt.write_slot {m : Runner.Mem} {fp : Runner.W} {K base j : Nat}
    {τ : Ty} {v : Wert D τ} (value : ValueAt L m fp base τ v)
    (room : fp.toNat + 8 * K ≤ 2 ^ 64) (fits : base + valueWords τ ≤ K)
    (index : j < K) (apart : j < base ∨ base + valueWords τ ≤ j) (w : Runner.W) :
    ValueAt L (write m (slot fp (BitVec.ofNat 64 j)) 8 w.toNat) fp base τ v := by
  refine ⟨value.1, ?_⟩
  intro i hi
  have width := encodeWords_length L τ v
  rw [rd64_write_far (slot_far room index (by omega) (by omega))]
  exact value.2 i hi

theorem ResultAt.write_slot {m : Runner.Mem} {fp : Runner.W} {K base j : Nat}
    {e : Option Ty} {v : ErgVal D e} (value : ResultAt L m fp base e v)
    (room : fp.toNat + 8 * K ≤ 2 ^ 64) (fits : base + resultWords e ≤ K)
    (index : j < K) (apart : j < base ∨ base + resultWords e ≤ j) (w : Runner.W) :
    ResultAt L (write m (slot fp (BitVec.ofNat 64 j)) 8 w.toNat) fp base e v := by
  cases e with
  | some τ => exact ValueAt.write_slot value room fits index apart w
  | none =>
    intro i hi
    have zero : i = 0 := by simpa using hi
    subst i
    rw [rd64_write_far (slot_far room index (by change base + 1 ≤ K at fits; omega)
      (by change j < base ∨ base + 1 ≤ j at apart; omega))]
    exact value 0 (by simp)

theorem idx_lt : {Γ : Ctx} → {τ : Ty} → (x : Var Γ τ) → Var.idx x < Γ.length
  | _, _, .here => by simp [Var.idx]
  | _, _, .there x => by have := idx_lt x; simp [Var.idx]; omega

theorem vslot_here {Γ : Ctx} {τ : Ty} : vslot (Var.here : Var (τ :: Γ) τ) reserved = frei Γ reserved := by
  simp [vslot, frei, variableOffset]

theorem vslot_there {Γ : Ctx} {τ σ : Ty} (y : Var Γ τ) : vslot (Var.there y : Var (σ :: Γ) τ) reserved = vslot y reserved := by
  rfl

theorem envAt_cons {m : Runner.Mem} {fp : Runner.W} {Γ : Ctx} {ρ : Env D Γ} {τ : Ty} {v : Wert D τ}
    (h : EnvAt L m fp ρ reserved) (hv : ValueAt L m fp (frei Γ reserved) τ v) :
    EnvAt L m fp (Env.cons v ρ : Env D (τ :: Γ)) reserved := by
  intro τ' y
  cases y with
  | here => rw [vslot_here]; exact hv
  | there y =>
    rw [vslot_there]; exact h τ' y

theorem envAt_tail {m : Runner.Mem} {fp : Runner.W} {Γ : Ctx} {τ : Ty} {ρ : Env D (τ :: Γ)} (h : EnvAt L m fp ρ reserved) :
    EnvAt L m fp ρ.tail reserved := by
  intro τ' y
  have value := h τ' (.there y)
  rw [vslot_there] at value
  cases ρ with
  | cons _ ρ => exact value

/-- One complete parameter sequence is exactly the variable-wise frame relation.
    This supplies the same ABI to a typed start environment and runtime calls. -/
theorem envAt_encoding {m : Runner.Mem} {fp : Runner.W} {Γ : Ctx} (ρ : Env D Γ) :
    EnvAt L m fp ρ reserved ↔
      (∀ τ (x : Var Γ τ), ValueValid L τ (ρ.get x)) ∧
      WordsAt m fp (FB + reserved) (encodeEnv L ρ) := by
  induction ρ with
  | nil =>
    constructor
    · intro env
      constructor
      · intro τ x; nomatch x
      · intro i hi; simp [encodeEnv] at hi
    · intro words τ x; nomatch x
  | @cons τ Γ v ρ ih =>
    constructor
    · intro env
      refine ⟨fun τ x => (env τ x).1, ?_⟩
      rw [encodeEnv, wordsAt_append]
      refine ⟨(ih.mp (envAt_tail env)).2, ?_⟩
      simpa only [encodeEnv_length, vslot_here, Env.get, frei] using (env τ .here).2
    · rintro ⟨valid, words⟩
      rw [encodeEnv, wordsAt_append] at words
      apply envAt_cons
      · exact ih.mpr ⟨fun τ x => valid τ (.there x), words.1⟩
      · exact ⟨valid τ .here, by simpa only [encodeEnv_length, frei] using words.2⟩

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


/-- A read of slot `b` after a write of slot `a ≠ b`. -/
theorem rd_other {m : Runner.Mem} {fp : Runner.W} {K a b : Nat} (hr : fp.toNat + 8 * K ≤ 2 ^ 64) (ha : a < K)
    (hb : b < K) (hne : a ≠ b) (v : Nat) :
    (write m (slot fp (BitVec.ofNat 64 a)) 8 v).rd64 (slot fp (BitVec.ofNat 64 b)) =
      m.rd64 (slot fp (BitVec.ofNat 64 b)) :=
  rd64_write_far (slot_far hr ha hb hne)

theorem rd_same {m : Runner.Mem} {fp : Runner.W} {K a : Nat} (hF : FrameOK m fp K) (ha : a < K) (v : Runner.W) :
    (write m (slot fp (BitVec.ofNat 64 a)) 8 v.toNat).rd64 (slot fp (BitVec.ofNat 64 a)) = some v :=
  rd64_wr64 (wr64_some (hF.wr a ha)) (hF.rd a ha)

end Gabbro.Stage0.Senke
