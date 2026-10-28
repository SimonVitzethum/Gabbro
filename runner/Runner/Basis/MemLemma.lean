import Runner.Basis.Mem

/-! # The byte memory: what a write changes and what it keeps

A write of `n` bytes at `a` changes exactly the bytes `a .. a+n-1` and no permission. Reads of bytes outside that
range see the old bytes; a read of the eight bytes just written sees the word. Address ranges are compared as
natural numbers without wrap-around (`Far`): the lowering of stage 0 places code, frames and data so. -/

namespace Runner.Mem

theorem all_congr {p q : W → Bool} {a : W} : ∀ {n : Nat},
    (∀ j, j < n → p (a + BitVec.ofNat 64 j) = q (a + BitVec.ofNat 64 j)) → all p a n = all q a n
  | 0, _ => rfl
  | n + 1, h => by
    simp only [all]
    rw [all_congr (fun j hj => h j (Nat.lt_succ_of_lt hj)), h n (Nat.lt_succ_self n)]

theorem le_congr {m m' : Mem} {a : W} : ∀ {n : Nat},
    (∀ j, j < n → m.b (a + BitVec.ofNat 64 j) = m'.b (a + BitVec.ofNat 64 j)) → le m a n = le m' a n
  | 0, _ => rfl
  | n + 1, h => by
    simp only [le]
    rw [le_congr (fun j hj => h j (Nat.lt_succ_of_lt hj)), h n (Nat.lt_succ_self n)]

theorem all_spec {p : W → Bool} {a : W} : ∀ {n j : Nat}, all p a n = true → j < n →
    p (a + BitVec.ofNat 64 j) = true
  | 0, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | n + 1, j, h, hj => by
    simp only [all, Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · exact all_spec h.1 hj
    · exact h.2

theorem all_of {p : W → Bool} {a : W} : ∀ {n : Nat}, (∀ j, j < n → p (a + BitVec.ofNat 64 j) = true) →
    all p a n = true
  | 0, _ => rfl
  | n + 1, h => by
    simp only [all, Bool.and_eq_true]
    exact ⟨all_of fun j hj => h j (Nat.lt_succ_of_lt hj), h n (Nat.lt_succ_self n)⟩

@[simp] theorem write_rd (m : Mem) (a : W) (n v : Nat) : (write m a n v).rd = m.rd := rfl
@[simp] theorem write_wr (m : Mem) (a : W) (n v : Nat) : (write m a n v).wr = m.wr := rfl

/-- The byte ranges `[a, a+n)` and `[b, b+k)` are apart, without wrap-around. -/
def Far (a : W) (n : Nat) (b : W) (k : Nat) : Prop :=
  a.toNat + n ≤ 2 ^ 64 ∧ b.toNat + k ≤ 2 ^ 64 ∧ (a.toNat + n ≤ b.toNat ∨ b.toNat + k ≤ a.toNat)

theorem write_far_b {m : Mem} {a b : W} {n k v : Nat} (hf : Far a n b k) {j : Nat} (hj : j < k) :
    (write m a n v).b (b + BitVec.ofNat 64 j) = m.b (b + BitVec.ofNat 64 j) := by
  simp only [write]
  split
  · next h =>
    exfalso
    obtain ⟨h1, h2, h3⟩ := hf
    have ha := a.isLt
    have hb := b.isLt
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat] at h
    omega
  · rfl

theorem rd64_write_far {m : Mem} {a b : W} {n v : Nat} (hf : Far a n b 8) :
    (write m a n v).rd64 b = m.rd64 b := by
  simp only [rd64, write_rd]
  rw [le_congr (fun j hj => write_far_b hf hj)]
  rfl

theorem rd32_write_far {m : Mem} {a b : W} {n v : Nat} (hf : Far a n b 4) :
    (write m a n v).rd32 b = m.rd32 b := by
  simp only [rd32, write_rd]
  rw [le_congr (fun j hj => write_far_b hf hj)]
  rfl

theorem rd8_write_far {m : Mem} {a b : W} {n v : Nat} (hf : Far a n b 1) :
    (write m a n v).rd8 b = m.rd8 b := by
  simp only [rd8, write_rd]
  have := write_far_b (m := m) (v := v) hf (j := 0) (by decide)
  simp only [BitVec.add_zero] at this
  rw [this]
  rfl

theorem write_in_b {m : Mem} {a : W} {n v j : Nat} (hj : j < n) (hn : n ≤ 2 ^ 64) :
    (write m a n v).b (a + BitVec.ofNat 64 j) = BitVec.ofNat 8 (v / 256 ^ j) := by
  have hsub : (a + BitVec.ofNat 64 j - a).toNat = j := by
    have := a.isLt
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  simp only [write, hsub, hj, ↓reduceIte]

theorem le_write_same (m : Mem) (a : W) (v : W) : le (write m a 8 v.toNat) a 8 = v.toNat := by
  have hv := v.isLt
  simp (disch := decide) only [le, write_in_b, BitVec.toNat_ofNat, Nat.zero_add]
  simp only [Nat.reducePow, Nat.div_one]
  omega

theorem rd64_wr64 {m m' : Mem} {a v : W} (hw : m.wr64 a v = some m') (hr : all m.rd a 8 = true) :
    m'.rd64 a = some v := by
  simp only [wr64] at hw
  split at hw
  · cases hw
    simp only [rd64, write_rd, hr, ↓reduceIte, le_write_same, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · cases hw

theorem wr64_spec {m m' : Mem} {a v : W} (hw : m.wr64 a v = some m') : m' = write m a 8 v.toNat := by
  simp only [wr64] at hw
  split at hw
  · cases hw; rfl
  · cases hw

theorem wr64_some {m : Mem} {a v : W} (h : all m.wr a 8 = true) : m.wr64 a v = some (write m a 8 v.toNat) := by
  simp only [wr64, h, ↓reduceIte]

end Runner.Mem
