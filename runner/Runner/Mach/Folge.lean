import Runner.Beweis.Mehr

/-! # The sequentially consistent memory model, with the kernel

One memory (`Runner/Basis/Mem.lean`) answers every request at once; the kernel answers a system call with any
result and any new memory -- the named assumption is only that it keeps the runner's dispatch table (`TabInv`).
A write needs the write permission, and the table is not writable, so no request of a thread changes it either:
`sc_fixed`, the premise of `runner_mt`, holds. -/

namespace Runner.Beweis
open Runner.X86 Runner.Prog Runner.Mach

/-- The bytes `l` at `a` in the memory, readable and not writable. -/
def MBytes (m : Mem) (a : W) (l : List B) : Prop :=
  ∀ j (h : j < l.length), m.b (a + BitVec.ofNat 64 j) = l[j] ∧ m.rd (a + BitVec.ofNat 64 j) = true ∧
    m.wr (a + BitVec.ofNat 64 j) = false

def wbytes (v : W) : List B := (List.range 8).map fun i => byte (v.toNat / 256 ^ i)

def Keeps (m m' : Mem) : Prop :=
  ∀ y, m.wr y = false → m'.b y = m.b y ∧ m'.rd y = m.rd y ∧ m'.wr y = m.wr y

theorem Keeps.refl (m : Mem) : Keeps m m := fun _ _ => ⟨rfl, rfl, rfl⟩

theorem Keeps.trans {m1 m2 m3 : Mem} (h1 : Keeps m1 m2) (h2 : Keeps m2 m3) : Keeps m1 m3 := by
  intro y hy
  obtain ⟨b1, r1, w1⟩ := h1 y hy
  obtain ⟨b2, r2, w2⟩ := h2 y (by rw [w1]; exact hy)
  exact ⟨b2.trans b1, r2.trans r1, w2.trans w1⟩

theorem MBytes.keep {m m' : Mem} {a : W} {l : List B} (hk : Keeps m m') (h : MBytes m a l) :
    MBytes m' a l := by
  intro j hj
  obtain ⟨hb, hr, hw⟩ := h j hj
  obtain ⟨kb, kr, kw⟩ := hk _ hw
  exact ⟨kb.trans hb, kr.trans hr, kw.trans hw⟩

theorem all_spec {p : W → Bool} {a : W} : ∀ {n j : Nat}, Mem.all p a n = true → j < n →
    p (a + BitVec.ofNat 64 j) = true
  | 0, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | n + 1, j, h, hj => by
    simp only [Mem.all, Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · exact all_spec h.1 hj
    · exact h.2

theorem all_of {p : W → Bool} {a : W} : ∀ {n : Nat}, (∀ j, j < n → p (a + BitVec.ofNat 64 j) = true) →
    Mem.all p a n = true
  | 0, _ => rfl
  | n + 1, h => by
    simp only [Mem.all, Bool.and_eq_true]
    exact ⟨all_of fun j hj => h j (Nat.lt_succ_of_lt hj), h n (Nat.lt_succ_self n)⟩

theorem sub_add_ofNat (a y : W) : a + BitVec.ofNat 64 (y - a).toNat = y := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_sub]
  have := a.isLt
  have := y.isLt
  omega

theorem write_keeps {m : Mem} {a : W} {n v : Nat} (h : Mem.all m.wr a n = true) :
    Keeps m (Mem.write m a n v) := by
  intro y hy
  refine ⟨?_, rfl, rfl⟩
  simp only [Mem.write]
  split
  · next hlt =>
    have := all_spec h hlt
    rw [sub_add_ofNat] at this
    rw [hy] at this
    exact absurd this (by decide)
  · rfl

theorem wr64_keeps {m m' : Mem} {a v : W} (h : m.wr64 a v = some m') : Keeps m m' := by
  simp only [Mem.wr64] at h
  split at h
  · next hw => cases h; exact write_keeps hw
  · cases h

theorem cas_keeps {m m' : Mem} {a e n old : W} (h : m.cas a e n = some (old, m')) : Keeps m m' := by
  simp only [Mem.cas] at h
  split at h
  · next hw =>
    simp only [Bool.and_eq_true] at hw
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    split
    · exact write_keeps hw.2
    · exact Keeps.refl m
  · cases h

theorem rd64_bytes {m : Mem} {a v : W} (h : MBytes m a (wbytes v)) : m.rd64 a = some v := by
  have hv := v.isLt
  have hb : ∀ j, j < 8 → m.b (a + BitVec.ofNat 64 j) = byte (v.toNat / 256 ^ j) ∧
      m.rd (a + BitVec.ofNat 64 j) = true := fun j hj => by
    obtain ⟨b1, b2, _⟩ := h j (by simp [wbytes]; exact hj)
    simp only [wbytes, List.getElem_map, List.getElem_range] at b1
    exact ⟨b1, b2⟩
  have ha : Mem.all m.rd a 8 = true := all_of fun j hj => (hb j hj).2
  simp only [Mem.rd64, ha, ↓reduceIte, Option.some.injEq]
  simp only [Mem.le, (hb 0 (by decide)).1, (hb 1 (by decide)).1, (hb 2 (by decide)).1, (hb 3 (by decide)).1,
    (hb 4 (by decide)).1, (hb 5 (by decide)).1, (hb 6 (by decide)).1, (hb 7 (by decide)).1]
  apply BitVec.eq_of_toNat_eq
  simp only [byte, BitVec.toNat_ofNat]
  omega

/-- The runner's table is in the memory, readable and not writable. -/
def TabInv (L : Lay) (m : Mem) : Prop :=
  ∀ op, op < 256 → MBytes m (taddr L (BitVec.ofNat 64 op)) (wbytes (L.H op))

theorem TabInv.keep {L : Lay} {m m' : Mem} (hk : Keeps m m') (h : TabInv L m) : TabInv L m' :=
  fun op hop => (h op hop).keep hk

/-- A read of `n` bytes (1, 4 or 8), the value zero-extended. -/
def rdN (m : Mem) : Nat → W → Option W
  | 1, a => (m.rd8 a).map (·.setWidth 64)
  | 4, a => (m.rd32 a).map (·.setWidth 64)
  | 8, a => m.rd64 a
  | _, _ => none

def SC (L : Lay) : MemSys where
  St := { m : Mem // TabInv L m }
  ans s _ o a s' := match o with
    | .rd n x => s' = s ∧ ∃ w, a = (rdN s.1 n x).map (·, w)
    | .wr x v => (s.1.wr64 x v = none ∧ a = none ∧ s' = s) ∨
        (∃ m, s.1.wr64 x v = some m ∧ a = some (0, 0) ∧ s'.1 = m)
    | .cas x e n => (s.1.cas x e n = none ∧ a = none ∧ s' = s) ∨
        (∃ old m, s.1.cas x e n = some (old, m) ∧ a = some (old, 0) ∧ s'.1 = m)
    | .sys _ => True
  tau _ _ := False

theorem sc_fixed (L : Lay) : Fixed (SC L) L := by
  intro s i op a s' hop h
  obtain ⟨rfl, w, rfl⟩ := h
  refine ⟨rfl, w, ?_⟩
  simp only [rdN, rd64_bytes (s'.2 op hop), Option.map_some]

end Runner.Beweis
