/-
  File:      stage0/Stage0/Senke/Sperre/Schritt.lean
  Subject:   Single instructions of the lock code (`Sperre/Code.lean`) on a state `LS`: the scratch slots `s .. s+17`
             hold `f`, the lock's three words at `a` hold owner, count and waiters, and apart from both the memory
             is the one the code started in (`AgreeK`). Each lemma runs instruction `i` of the code `code` at `pc`.
-/
module
public import Stage0.Senke.Sperre.Code
public import Stage0.Senke.Umgebung
public import Stage0.Senke.Images.Hilfe
public import Stage0.Senke.Welt.Schreib
@[expose] public section


namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable [Kern]

/-- `f` with `d` set to `r`. -/
def upd (f : Nat → W) (d : Nat) (r : W) : Nat → W := fun j => if j = d then r else f j

@[simp] theorem upd_self (f : Nat → W) (d : Nat) (r : W) : upd f d r d = r := by simp [upd]

theorem upd_ne {f : Nat → W} {d j : Nat} {r : W} (h : j ≠ d) : upd f d r j = f j := by simp [upd, h]

/-- The byte `x` is one of the three words of the lock at `a`. -/
def InLk (a : Nat) (x : W) : Prop := a ≤ x.toNat ∧ x.toNat < a + 24

/-- Apart from the scratch slots `s .. s+17` and the words of the lock at `a`, `m'` is `m`. -/
structure AgreeK (fp : W) (s a : Nat) (m m' : Mem) : Prop where
  rd : m'.rd = m.rd
  wr : m'.wr = m.wr
  b : ∀ x, ¬ inSlots fp s (s + 18) x → ¬ InLk a x → m'.b x = m.b x

theorem AgreeK.refl (fp : W) (s a : Nat) (m : Mem) : AgreeK fp s a m m := ⟨rfl, rfl, fun _ _ _ => rfl⟩

theorem AgreeK.trans {fp : W} {s a : Nat} {m1 m2 m3 : Mem} (h1 : AgreeK fp s a m1 m2)
    (h2 : AgreeK fp s a m2 m3) : AgreeK fp s a m1 m3 :=
  ⟨h2.rd.trans h1.rd, h2.wr.trans h1.wr, fun x hx hl => (h2.b x hx hl).trans (h1.b x hx hl)⟩

theorem agreeK_slot {m : Mem} {fp : W} {s a d : Nat} (hr : fp.toNat + 8 * (s + 18) ≤ 2 ^ 64) (hd : d < 18)
    (v : Nat) : AgreeK fp s a m (write m (slot fp (BitVec.ofNat 64 (s + d))) 8 v) :=
  have h := agree_write (lo := s) (K := s + 18) (j := s + d) (m := m) hr (by omega) (by omega) v
  ⟨h.rd, h.wr, fun x hx _ => h.b x hx⟩

theorem agreeK_lk {m : Mem} {fp : W} {s a y : Nat} (hy : a ≤ y) (hk : y ≤ a + 16) (ha : a + 24 < 2 ^ 31)
    (v : Nat) : AgreeK fp s a m (write m (BitVec.ofNat 64 y) 8 v) := by
  refine ⟨rfl, rfl, fun x _ hx => ?_⟩
  show (if _ then _ else _) = _
  split
  · next h =>
    exfalso; apply hx
    have := x.isLt
    have ha' : (BitVec.ofNat 64 y).toNat = y := by simp only [BitVec.toNat_ofNat]; omega
    simp only [BitVec.toNat_sub, ha'] at h
    unfold InLk; omega
  · rfl

/-- What the lock code relies on: its scratch slots, the lock above them, its code below the frame. -/
structure LE (m0 : Mem) (pc fp : W) (s a : Nat) (code : List II) : Prop where
  frame : FrameOK m0 fp (s + 18)
  small : s + 18 < 2 ^ 31
  far : fp.toNat + 8 * (s + 18) ≤ a
  top : a + 24 < 2 ^ 31
  wr0 : all m0.wr (BitVec.ofNat 64 a) 8 = true
  wr1 : all m0.wr (BitVec.ofNat 64 (a + 8)) 8 = true
  wr2 : all m0.wr (BitVec.ofNat 64 (a + 16)) 8 = true
  hcode : CodeAt m0 pc code
  cfar : CodeFar pc code.length fp (s + 18)

theorem AgreeK.big {fp : W} {s a : Nat} {m m' : Mem} (h : AgreeK fp s a m m') (hf : fp.toNat + 8 * (s + 18) ≤ a)
    (ha : a + 24 < 2 ^ 31) : Agree fp s ((2 ^ 64 - fp.toNat) / 8) m m' := by
  refine ⟨h.rd, h.wr, fun x hx => h.b x (fun ⟨h1, h2⟩ => hx ⟨h1, ?_⟩) (fun ⟨h1, h2⟩ => hx ⟨?_, ?_⟩)⟩
  · have := x.isLt; have := fp.isLt; omega
  · omega
  · have := x.isLt; have := fp.isLt; omega

/-- The instruction `i` of the code, in a memory the lock code reached. -/
theorem LE.ins {m0 m : Mem} {pc fp : W} {s a : Nat} {code : List II} (E : LE m0 pc fp s a code)
    (h : AgreeK fp s a m0 m) {i : Nat} {x : II} (hi : code[i]? = some x) :
    InsAt m (pc + BitVec.ofNat 64 (16 * i)) x.o (II.f x.a) (II.f x.b) (II.f x.c) := by
  obtain ⟨hl, hx⟩ := List.getElem?_eq_some_iff.mp hi
  have hc := E.hcode.agree (h.big E.far E.top)
    (by obtain ⟨h1, h2, h3⟩ := E.cfar; have := fp.isLt; exact ⟨h1, by omega, h3⟩)
  have := hc i hl
  rw [hx] at this
  exact this

theorem LE.frameK {m0 m : Mem} {pc fp : W} {s a : Nat} {code : List II} (E : LE m0 pc fp s a code)
    (h : AgreeK fp s a m0 m) : FrameOK m fp (s + 18) :=
  ⟨E.frame.lt, fun i hi => by rw [h.rd]; exact E.frame.rd i hi, fun i hi => by rw [h.wr]; exact E.frame.wr i hi⟩

/-- The state of the lock code. -/
structure LS (m0 m : Mem) (fp : W) (s a : Nat) (f : Nat → W) (o c w : W) : Prop where
  sl : ∀ j, j < 18 → m.rd64 (slot fp (BitVec.ofNat 64 (s + j))) = some (f j)
  o : m.rd64 (BitVec.ofNat 64 a) = some o
  c : m.rd64 (BitVec.ofNat 64 (a + 8)) = some c
  w : m.rd64 (BitVec.ofNat 64 (a + 16)) = some w
  ag : AgreeK fp s a m0 m

theorem LS.congr {m0 m : Mem} {fp : W} {s a : Nat} {f : Nat → W} {o c w o' c' w' : W}
    (h : LS m0 m fp s a f o c w) (ho : o = o') (hc : c = c') (hw : w = w') : LS m0 m fp s a f o' c' w' := by
  subst ho hc hw; exact h

theorem far_slot_lk {fp : W} {s a d y : Nat} (hr : fp.toNat + 8 * (s + 18) ≤ a) (ha : a + 24 < 2 ^ 31)
    (hd : d < 18) (hy : a ≤ y) (hk : y ≤ a + 16) : Far (slot fp (BitVec.ofNat 64 (s + d))) 8 (BitVec.ofNat 64 y) 8 := by
  have hs := slot_toNat (fp := fp) (K := s + 18) (i := s + d) (by omega) (by omega)
  have : (BitVec.ofNat 64 y).toNat = y := by simp only [BitVec.toNat_ofNat]; omega
  rw [Far, hs, this]; omega

theorem far_lk_slot {fp : W} {s a d y : Nat} (hr : fp.toNat + 8 * (s + 18) ≤ a) (ha : a + 24 < 2 ^ 31)
    (hd : d < 18) (hy : a ≤ y) (hk : y ≤ a + 16) : Far (BitVec.ofNat 64 y) 8 (slot fp (BitVec.ofNat 64 (s + d))) 8 := by
  obtain ⟨h1, h2, h3⟩ := far_slot_lk (fp := fp) (s := s) (d := d) hr ha hd hy hk; exact ⟨h2, h1, h3.symm⟩

theorem far_lk_lk {y z : Nat} (hy : y + 8 < 2 ^ 31) (hz : z + 8 < 2 ^ 31) (hne : y + 8 ≤ z ∨ z + 8 ≤ y) :
    Far (BitVec.ofNat 64 y) 8 (BitVec.ofNat 64 z) 8 := by
  have h1 : (BitVec.ofNat 64 y).toNat = y := by simp only [BitVec.toNat_ofNat]; omega
  have h2 : (BitVec.ofNat 64 z).toNat = z := by simp only [BitVec.toNat_ofNat]; omega
  rw [Far, h1, h2]; omega

/-- A scratch slot written. -/
theorem LS.slot {m0 m : Mem} {pc fp : W} {s a : Nat} {code : List II} {f : Nat → W} {o c w : W}
    (E : LE m0 pc fp s a code) (h : LS m0 m fp s a f o c w) {d : Nat} (hd : d < 18) (r : W) :
    LS m0 (write m (slot fp (BitVec.ofNat 64 (s + d))) 8 r.toNat) fp s a (upd f d r) o c w := by
  have hF := E.frameK h.ag
  have hr := hF.room
  have hfar := E.far
  have htop := E.top
  refine ⟨fun j hj => ?_, ?_, ?_, ?_, h.ag.trans (agreeK_slot hr hd _)⟩
  · by_cases hjd : j = d
    · subst hjd
      rw [upd_self]
      exact rd64_wr64 (wr64_some (hF.wr _ (by omega))) (hF.rd _ (by omega))
    · rw [upd_ne hjd, rd64_write_far (slot_far hr (by omega) (by omega) (by omega))]
      exact h.sl j hj
  · rw [rd64_write_far (far_slot_lk (y := a) hfar htop hd (by omega) (by omega))]; exact h.o
  · rw [rd64_write_far (far_slot_lk (y := a + 8) hfar htop hd (by omega) (by omega))]; exact h.c
  · rw [rd64_write_far (far_slot_lk (y := a + 16) hfar htop hd (by omega) (by omega))]; exact h.w

/-- The owner word written. -/
theorem LS.owner {m0 m : Mem} {pc fp : W} {s a : Nat} {code : List II} {f : Nat → W} {o c w : W}
    (E : LE m0 pc fp s a code) (h : LS m0 m fp s a f o c w) (o' : W) :
    LS m0 (write m (BitVec.ofNat 64 a) 8 o'.toNat) fp s a f o' c w := by
  have hfar := E.far
  have htop := E.top
  refine ⟨fun j hj => ?_, ?_, ?_, ?_, h.ag.trans (agreeK_lk (Nat.le_refl _) (by omega) htop _)⟩
  · rw [rd64_write_far (far_lk_slot (y := a) hfar htop hj (by omega) (by omega))]; exact h.sl j hj
  · exact rd64_wr64 (wr64_some (by rw [h.ag.wr]; exact E.wr0)) (rd64_some_all h.o)
  · rw [rd64_write_far (far_lk_lk (y := a) (z := a + 8) (by omega) (by omega) (by omega))]; exact h.c
  · rw [rd64_write_far (far_lk_lk (y := a) (z := a + 16) (by omega) (by omega) (by omega))]; exact h.w

/-- The count word written. -/
theorem LS.count {m0 m : Mem} {pc fp : W} {s a : Nat} {code : List II} {f : Nat → W} {o c w : W}
    (E : LE m0 pc fp s a code) (h : LS m0 m fp s a f o c w) (c' : W) :
    LS m0 (write m (BitVec.ofNat 64 (a + 8)) 8 c'.toNat) fp s a f o c' w := by
  have hfar := E.far
  have htop := E.top
  refine ⟨fun j hj => ?_, ?_, ?_, ?_, h.ag.trans (agreeK_lk (by omega) (by omega) htop _)⟩
  · rw [rd64_write_far (far_lk_slot (y := a + 8) hfar htop hj (by omega) (by omega))]; exact h.sl j hj
  · rw [rd64_write_far (far_lk_lk (y := a + 8) (z := a) (by omega) (by omega) (by omega))]; exact h.o
  · exact rd64_wr64 (wr64_some (by rw [h.ag.wr]; exact E.wr1)) (rd64_some_all h.c)
  · rw [rd64_write_far (far_lk_lk (y := a + 8) (z := a + 16) (by omega) (by omega) (by omega))]; exact h.w

/-! ## Instructions -/

theorem pc_next (pc : W) (i : Nat) : pc + BitVec.ofNat 64 (16 * i) + 16 = pc + BitVec.ofNat 64 (16 * (i + 1)) := by
  rw [BitVec.add_assoc, show (16 : W) = BitVec.ofNat 64 16 from rfl]; congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

theorem pc_jump (pc : W) (i k : Nat) :
    pc + BitVec.ofNat 64 (16 * i) + BitVec.ofNat 64 (16 * k) = pc + BitVec.ofNat 64 (16 * (i + k)) := by
  rw [BitVec.add_assoc]; congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

theorem ls_star {m m' : Mem} {pc fp : W} {i j o : Nat} {x y z : BitVec 32}
    (hi : InsAt m (pc + BitVec.ofNat 64 (16 * i)) o x y z) (ho : o < 256)
    (hr : Run (op o ⟨pc + BitVec.ofNat 64 (16 * i), fp⟩) m ⟨pc + BitVec.ofNat 64 (16 * j), fp⟩ m') :
    Star ⟨pc + BitVec.ofNat 64 (16 * i), fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * j), fp⟩ m' :=
  Star.one (run_step (t := ⟨_, fp⟩) hi ho hr)

/-- The run of instruction `i` to `i + 1` with the scratch slot `d` set to `r`. -/
abbrev Next1 (m0 m : Mem) (pc fp : W) (s a i d : Nat) (f : Nat → W) (o c w r : W) : Prop :=
  ∃ m', Star ⟨pc + BitVec.ofNat 64 (16 * i), fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * (i + 1)), fp⟩ m' ∧
    LS m0 m' fp s a (upd f d r) o c w


end Gabbro.Stage0.Senke
