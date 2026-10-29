import Runner.IR.Seq

/-! # Frames and code in the memory of one IR thread

* `FrameOK m fp K`: the slots `0 .. K-1` of the frame at `fp` are readable and writable, without wrap-around.
* `Agree fp lo K m m'`: `m'` has the bytes of `m` everywhere except in the slots `lo .. K-1`, and the same
  permissions. Code and the slots below `lo` survive a run that only writes slots from `lo` on.
* `CodeAt m pc is`: the lowered instructions `is` lie one after the other from `pc` (16 bytes each). -/

namespace Runner.IR
open Runner.Mem

/-- A lowered instruction: opcode and three fields. -/
structure II where
  o : Nat
  a : Int
  b : Int
  c : Int
  deriving DecidableEq, Repr

def II.f (v : Int) : BitVec 32 := BitVec.ofInt 32 v

def CodeAt (m : Mem) (pc : W) (is : List II) : Prop :=
  ∀ k (h : k < is.length), InsAt m (pc + BitVec.ofNat 64 (16 * k)) is[k].o (II.f is[k].a) (II.f is[k].b) (II.f is[k].c)

/-- The byte range of the slots `lo .. K-1`. -/
def inSlots (fp : W) (lo K : Nat) (x : W) : Prop := fp.toNat + 8 * lo ≤ x.toNat ∧ x.toNat < fp.toNat + 8 * K

structure Agree (fp : W) (lo K : Nat) (m m' : Mem) : Prop where
  rd : m'.rd = m.rd
  wr : m'.wr = m.wr
  b : ∀ x, ¬ inSlots fp lo K x → m'.b x = m.b x

theorem Agree.refl (fp : W) (lo K : Nat) (m : Mem) : Agree fp lo K m m := ⟨rfl, rfl, fun _ _ => rfl⟩

theorem Agree.trans {fp : W} {lo K : Nat} {m1 m2 m3 : Mem} (h1 : Agree fp lo K m1 m2) (h2 : Agree fp lo K m2 m3) :
    Agree fp lo K m1 m3 :=
  ⟨h2.rd.trans h1.rd, h2.wr.trans h1.wr, fun x hx => (h2.b x hx).trans (h1.b x hx)⟩

theorem Agree.mono {fp : W} {lo lo' K : Nat} {m m' : Mem} (h : Agree fp lo' K m m') (hl : lo ≤ lo') :
    Agree fp lo K m m' :=
  ⟨h.rd, h.wr, fun x hx => h.b x fun ⟨h1, h2⟩ => hx ⟨by omega, h2⟩⟩

structure FrameOK (m : Mem) (fp : W) (K : Nat) : Prop where
  lt : fp.toNat + 8 * K < 2 ^ 64
  rd : ∀ i, i < K → all m.rd (slot fp (BitVec.ofNat 64 i)) 8 = true
  wr : ∀ i, i < K → all m.wr (slot fp (BitVec.ofNat 64 i)) 8 = true

theorem FrameOK.room {m : Mem} {fp : W} {K : Nat} (h : FrameOK m fp K) : fp.toNat + 8 * K ≤ 2 ^ 64 :=
  Nat.le_of_lt h.lt

theorem FrameOK.agree {m m' : Mem} {fp : W} {K lo : Nat} (h : FrameOK m fp K) (ha : Agree fp lo K m m') :
    FrameOK m' fp K := ⟨h.lt, fun i hi => by rw [ha.rd]; exact h.rd i hi, fun i hi => by rw [ha.wr]; exact h.wr i hi⟩

theorem slot_toNat {fp : W} {K i : Nat} (hr : fp.toNat + 8 * K ≤ 2 ^ 64) (hi : i < K) :
    (slot fp (BitVec.ofNat 64 i)).toNat = fp.toNat + 8 * i := by
  have := fp.isLt
  have h8 : (8 : W).toNat = 8 := rfl
  simp only [slot, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, h8]
  rw [Nat.mod_eq_of_lt (a := i) (by omega)]
  omega

/-- Writing slot `j` (`lo ≤ j < K`) changes only the slots from `lo` on. -/
theorem agree_write {m : Mem} {fp : W} {lo K j : Nat} (hr : fp.toNat + 8 * K ≤ 2 ^ 64) (hj1 : lo ≤ j)
    (hj2 : j < K) (v : Nat) : Agree fp lo K m (write m (slot fp (BitVec.ofNat 64 j)) 8 v) := by
  refine ⟨rfl, rfl, fun x hx => ?_⟩
  show (if _ then _ else _) = _
  split
  · next h =>
    exfalso
    apply hx
    have hs := slot_toNat hr hj2
    have := x.isLt
    simp only [BitVec.toNat_sub, hs] at h
    constructor <;> omega
  · rfl

/-- A read of slot `i < lo` sees the old word. -/
theorem agree_rd_low {m m' : Mem} {fp : W} {lo K i : Nat} (ha : Agree fp lo K m m') (hr : fp.toNat + 8 * K ≤ 2 ^ 64)
    (hi : i < lo) (hK : lo ≤ K) : m'.rd64 (slot fp (BitVec.ofNat 64 i)) = m.rd64 (slot fp (BitVec.ofNat 64 i)) := by
  have hs := slot_toNat (i := i) hr (by omega)
  simp only [Mem.rd64, ha.rd]
  rw [le_congr (fun j hj => ha.b _ fun ⟨h1, h2⟩ => by
    have := fp.isLt
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hs] at h1
    omega)]

/-- Code apart from the frame's slots survives. -/
def CodeFar (pc : W) (n : Nat) (fp : W) (K : Nat) : Prop :=
  pc.toNat + 16 * n < 2 ^ 64 ∧ fp.toNat + 8 * K ≤ 2 ^ 64 ∧ pc.toNat + 16 * n ≤ fp.toNat

theorem far_bytes {m m' : Mem} {fp : W} {lo K : Nat} (ha : Agree fp lo K m m') {a : W} {n : Nat}
    (hfar : a.toNat + n ≤ 2 ^ 64 ∧ (a.toNat + n ≤ fp.toNat ∨ fp.toNat + 8 * K ≤ a.toNat)) :
    ∀ j, j < n → m'.b (a + BitVec.ofNat 64 j) = m.b (a + BitVec.ofNat 64 j) := by
  intro j hj
  apply ha.b
  rintro ⟨h1, h2⟩
  have := a.isLt
  have hx : (a + BitVec.ofNat 64 j).toNat = a.toNat + j := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  rw [hx] at h1 h2
  omega

theorem InsAt.agree {m m' : Mem} {fp : W} {lo K : Nat} (ha : Agree fp lo K m m') {pc : W} {o : Nat}
    {a b c : BitVec 32} (hi : InsAt m pc o a b c)
    (hfar : pc.toNat + 16 ≤ 2 ^ 64 ∧ (pc.toNat + 16 ≤ fp.toNat ∨ fp.toNat + 8 * K ≤ pc.toNat)) :
    InsAt m' pc o a b c := by
  have hb := far_bytes ha hfar
  have off : ∀ q, q + 4 ≤ 16 → ∀ j, j < 4 → m'.b (pc + BitVec.ofNat 64 q + BitVec.ofNat 64 j) =
      m.b (pc + BitVec.ofNat 64 q + BitVec.ofNat 64 j) := fun q hq j hj => by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]; exact hb _ (by omega)
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := hb 0 (by decide)
    simp only [BitVec.add_zero] at this
    simp only [Mem.rd8, ha.rd, this]; exact hi.op
  · have h := hi.f1; simp only [Mem.rd32, ha.rd] at h ⊢
    rw [show (pc + 4 : W) = pc + BitVec.ofNat 64 4 from rfl] at h ⊢
    rw [le_congr (off 4 (by decide))]; exact h
  · have h := hi.f2; simp only [Mem.rd32, ha.rd] at h ⊢
    rw [show (pc + 8 : W) = pc + BitVec.ofNat 64 8 from rfl] at h ⊢
    rw [le_congr (off 8 (by decide))]; exact h
  · have h := hi.f3; simp only [Mem.rd32, ha.rd] at h ⊢
    rw [show (pc + 12 : W) = pc + BitVec.ofNat 64 12 from rfl] at h ⊢
    rw [le_congr (off 12 (by decide))]; exact h

theorem CodeAt.agree {m m' : Mem} {fp : W} {lo K : Nat} (ha : Agree fp lo K m m') {pc : W} {is : List II}
    (hc : CodeAt m pc is) (hf : CodeFar pc is.length fp K) : CodeAt m' pc is := by
  intro k hk
  apply (hc k hk).agree ha
  obtain ⟨h1, _, h3⟩ := hf
  have := pc.isLt
  have hx : (pc + BitVec.ofNat 64 (16 * k)).toNat = pc.toNat + 16 * k := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  rw [hx]
  omega

end Runner.IR
