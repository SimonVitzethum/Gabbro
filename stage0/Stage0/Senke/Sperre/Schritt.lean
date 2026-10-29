/-
  File:      stage0/Stage0/Senke/Sperre/Schritt.lean
  Subject:   Single instructions of the lock code (`Sperre/Code.lean`) on a state `LS`: the scratch slots `s .. s+17`
             hold `f`, the lock's three words at `a` hold owner, count and waiters, and apart from both the memory
             is the one the code started in (`AgreeK`). Each lemma runs instruction `i` of the code `code` at `pc`.
-/
import Stage0.Senke.Sperre.Code
import Stage0.Senke.Umgebung
import Stage0.Senke.Hilfe
import Stage0.Senke.Welt.Schreib

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

section
variable {m0 m : Mem} {pc fp : W} {s a : Nat} {code : List II} {f : Nat → W} {o c w : W}

theorem ls_const (E : LE m0 pc fp s a code) (h : LS m0 m fp s a f o c w) {i d : Nat} {D k : Int}
    (hi : code[i]? = some (ci 1 D k 0)) (hD : D = ((s + d : Nat) : Int)) (hd : d < 18) (hk : lit32 k = true) :
    Next1 m0 m pc fp s a i d f o c w (BitVec.ofInt 64 k) := by
  subst hD
  have hI := E.ins h.ag hi
  simp only [ci] at hI
  have hs := E.small
  have hF := E.frameK h.ag
  refine ⟨_, ls_star hI (by decide) ?_, h.slot E hd _⟩
  rw [← pc_next]
  simp only [op]
  refine f2_run hI ?_
  simp only [ret1]
  refine f1_run hI ?_
  rw [sx_lit hk, sx_nat (by omega)]
  exact run_wr64 (wr64_some (hF.wr _ (by omega)))

theorem ls_mov (E : LE m0 pc fp s a code) (h : LS m0 m fp s a f o c w) {i d e : Nat} {D A : Int}
    (hi : code[i]? = some (ci 2 D A 0)) (hD : D = ((s + d : Nat) : Int)) (hA : A = ((s + e : Nat) : Int))
    (hd : d < 18) (he : e < 18) : Next1 m0 m pc fp s a i d f o c w (f e) := by
  subst hD hA
  have hI := E.ins h.ag hi
  simp only [ci] at hI
  have hs := E.small
  have hF := E.frameK h.ag
  refine ⟨_, ls_star hI (by decide) ?_, h.slot E hd _⟩
  rw [← pc_next]
  simp only [op]
  refine f2_run hI ?_
  rw [sx_nat (by omega)]
  simp only [ld]
  refine run_rd64 (h.sl e he) ?_
  simp only [ret1]
  refine f1_run hI ?_
  rw [sx_nat (by omega)]
  exact run_wr64 (wr64_some (hF.wr _ (by omega)))

theorem ls_bin (E : LE m0 pc fp s a code) (h : LS m0 m fp s a f o c w) {i d e g' : Nat} {D A B : Int} {op' : Nat}
    {g : W → W → Option W} {r : W} (hi : code[i]? = some (ci op' D A B)) (hop : op op' = bin g) (ho : op' < 256)
    (hD : D = ((s + d : Nat) : Int)) (hA : A = ((s + e : Nat) : Int)) (hB : B = ((s + g' : Nat) : Int))
    (hd : d < 18) (he : e < 18) (hg' : g' < 18) (hr : g (f e) (f g') = some r) :
    Next1 m0 m pc fp s a i d f o c w r := by
  subst hD hA hB
  have hI := E.ins h.ag hi
  simp only [ci] at hI
  have hs := E.small
  have hF := E.frameK h.ag
  refine ⟨_, ls_star hI ho ?_, h.slot E hd _⟩
  rw [← pc_next, hop]
  have hra := h.sl e he
  have hrb := h.sl g' hg'
  rw [← sx_nat (d := s + e) (by omega)] at hra
  rw [← sx_nat (d := s + g') (by omega)] at hrb
  have hw := wr64_some (v := r) (hF.wr (s + d) (by omega))
  rw [← sx_nat (d := s + d) (by omega)] at hw
  have := run_bin (t := ⟨pc + BitVec.ofNat 64 (16 * i), fp⟩) hI hra hrb hr hw
  rwa [sx_nat (d := s + d) (by omega)] at this

/-- `lea d 0`: the frame's address. -/
theorem ls_lea (E : LE m0 pc fp s a code) (h : LS m0 m fp s a f o c w) {i d : Nat} {D : Int}
    (hi : code[i]? = some (ci 17 D 0 0)) (hD : D = ((s + d : Nat) : Int)) (hd : d < 18) :
    Next1 m0 m pc fp s a i d f o c w fp := by
  subst hD
  have hI := E.ins h.ag hi
  simp only [ci] at hI
  have hs := E.small
  have hF := E.frameK h.ag
  have e0 : slot fp (BitVec.ofNat 64 0) = fp := by simp [slot]
  refine ⟨_, ls_star hI (by decide) ?_, h.slot E hd _⟩
  rw [← pc_next]
  simp only [op]
  refine f2_run hI ?_
  simp only [ret1]
  refine f1_run hI ?_
  rw [sx_nat (d := s + d) (by omega), show ((0 : Int)) = ((0 : Nat) : Int) from rfl, sx_nat (d := 0) (by omega)]
  show Run (wr64 _ (slot fp (BitVec.ofNat 64 0)) _) _ _ _
  rw [e0]
  exact run_wr64 (wr64_some (hF.wr _ (by omega)))

/-- `ld d e`: a word read from the address in slot `e`. -/
theorem ls_ld (E : LE m0 pc fp s a code) (h : LS m0 m fp s a f o c w) {i d e : Nat} {D A : Int} {v : W}
    (hi : code[i]? = some (ci 15 D A 0)) (hD : D = ((s + d : Nat) : Int)) (hA : A = ((s + e : Nat) : Int))
    (hd : d < 18) (he : e < 18) (hv : m.rd64 (f e) = some v) : Next1 m0 m pc fp s a i d f o c w v := by
  subst hD hA
  have hI := E.ins h.ag hi
  simp only [ci] at hI
  have hs := E.small
  have hF := E.frameK h.ag
  refine ⟨_, ls_star hI (by decide) ?_, h.slot E hd _⟩
  rw [← pc_next]
  have hra := h.sl e he
  rw [← sx_nat (d := s + e) (by omega)] at hra
  have hw := wr64_some (v := v) (hF.wr (s + d) (by omega))
  rw [← sx_nat (d := s + d) (by omega)] at hw
  have := run_ld (t := ⟨pc + BitVec.ofNat 64 (16 * i), fp⟩) hI hra hv hw
  rwa [sx_nat (d := s + d) (by omega)] at this

/-- `st e g` to the count word. -/
theorem ls_st_count (E : LE m0 pc fp s a code) (h : LS m0 m fp s a f o c w) {i e g' : Nat} {A B : Int}
    (hi : code[i]? = some (ci 16 A B 0)) (hA : A = ((s + e : Nat) : Int)) (hB : B = ((s + g' : Nat) : Int))
    (he : e < 18) (hg' : g' < 18) (hae : f e = BitVec.ofNat 64 (a + 8)) :
    ∃ m', Star ⟨pc + BitVec.ofNat 64 (16 * i), fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * (i + 1)), fp⟩ m' ∧
      LS m0 m' fp s a f o (f g') w := by
  subst hA hB
  have hI := E.ins h.ag hi
  simp only [ci] at hI
  have hs := E.small
  refine ⟨_, ls_star hI (by decide) ?_, h.count E (f g')⟩
  rw [← pc_next]
  have hra := h.sl e he
  rw [← sx_nat (d := s + e) (by omega), hae] at hra
  have hrb := h.sl g' hg'
  rw [← sx_nat (d := s + g') (by omega)] at hrb
  exact run_st (t := ⟨pc + BitVec.ofNat 64 (16 * i), fp⟩) hI hra hrb
    (wr64_some (by rw [h.ag.wr]; exact E.wr1))

/-- `brz e L` with slot `e` zero: on at instruction `i + k`. -/
theorem ls_brz_zero (E : LE m0 pc fp s a code) (h : LS m0 m fp s a f o c w) {i e k : Nat} {A Lb : Int}
    (hi : code[i]? = some (ci 19 A Lb 0)) (hA : A = ((s + e : Nat) : Int)) (hL : Lb = ((16 * k : Nat) : Int))
    (he : e < 18) (hk : 16 * k < 2 ^ 31) (hz : f e = 0) :
    Star ⟨pc + BitVec.ofNat 64 (16 * i), fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * (i + k)), fp⟩ m := by
  subst hA hL
  have hI := E.ins h.ag hi
  simp only [ci] at hI
  have hs := E.small
  refine ls_star hI (by decide) ?_
  have hra := h.sl e he
  rw [← sx_nat (d := s + e) (by omega), hz] at hra
  have := run_brz_zero (t := ⟨pc + BitVec.ofNat 64 (16 * i), fp⟩) hI hra
  rwa [sx_nat hk, pc_jump] at this

/-- `brz e L` with slot `e` not zero: on at instruction `i + 1`. -/
theorem ls_brz_ne (E : LE m0 pc fp s a code) (h : LS m0 m fp s a f o c w) {i e : Nat} {A Lb : Int}
    (hi : code[i]? = some (ci 19 A Lb 0)) (hA : A = ((s + e : Nat) : Int)) (he : e < 18) (hz : f e ≠ 0) :
    Star ⟨pc + BitVec.ofNat 64 (16 * i), fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * (i + 1)), fp⟩ m := by
  subst hA
  have hI := E.ins h.ag hi
  simp only [ci] at hI
  have hs := E.small
  refine ls_star hI (by decide) ?_
  have hra := h.sl e he
  rw [← sx_nat (d := s + e) (by omega)] at hra
  rw [← pc_next]
  exact run_brz_ne (t := ⟨pc + BitVec.ofNat 64 (16 * i), fp⟩) hI hra hz

/-- `jmp L` forward: on at instruction `i + k`. -/
theorem ls_jmp (E : LE m0 pc fp s a code) (h : AgreeK fp s a m0 m) {i k : Nat} {Lb : Int}
    (hi : code[i]? = some (ci 18 Lb 0 0)) (hL : Lb = ((16 * k : Nat) : Int)) (hk : 16 * k < 2 ^ 31) :
    Star ⟨pc + BitVec.ofNat 64 (16 * i), fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * (i + k)), fp⟩ m := by
  subst hL
  have hI := E.ins h hi
  simp only [ci] at hI
  refine ls_star hI (by decide) ?_
  simp only [op]
  refine f1_run hI ?_
  rw [sx_nat hk, pc_jump]
  exact .next

end

theorem sdiv_nat {x y : Nat} (hx : x < 2 ^ 63) (hy0 : 0 < y) (hy : y < 2 ^ 63) :
    sdiv (BitVec.ofNat 64 x) (BitVec.ofNat 64 y) = some (BitVec.ofNat 64 (x / y)) := by
  have tx : (BitVec.ofNat 64 x).toInt = x := by
    rw [BitVec.toInt_eq_toNat_cond]; simp only [BitVec.toNat_ofNat]; split <;> omega
  have ty : (BitVec.ofNat 64 y).toInt = y := by
    rw [BitVec.toInt_eq_toNat_cond]; simp only [BitVec.toNat_ofNat]; split <;> omega
  have hq : (x : Int).tdiv (y : Int) = ((x / y : Nat) : Int) := (Int.ofNat_tdiv x y).symm
  have hle : x / y ≤ x := Nat.div_le_self x y
  unfold sdiv
  rw [tx, ty, hq]
  have h1 : ¬ ((y : Int) = 0) := by omega
  have h2 : ¬ (((x / y : Nat) : Int) < -2 ^ 63 ∨ 2 ^ 63 ≤ ((x / y : Nat) : Int)) := by
    have h3 : ((x / y : Nat) : Int) ≤ (x : Int) := by exact_mod_cast hle
    have h4 : (0 : Int) ≤ ((x / y : Nat) : Int) := Int.natCast_nonneg _
    generalize ((x / y : Nat) : Int) = q at *
    omega
  simp only [h1, h2, ite_false, BitVec.ofInt_natCast]

theorem cas_spec {m : Mem} {a e n o : W} (h : m.rd64 a = some o) (hw : all m.wr a 8 = true) :
    m.cas a e n = some (o, if o = e then write m a 8 n.toNat else m) := by
  unfold Mem.rd64 at h
  unfold Mem.cas
  split at h
  · next hr =>
    simp only [Option.some.injEq] at h
    simp only [hr, hw, Bool.and_self, ite_true, h]
  · simp at h

theorem slot_plus8 (fp : W) (j : Nat) : slot fp (BitVec.ofNat 64 j) + 8 = slot fp (BitVec.ofNat 64 (j + 1)) := by
  simp only [slot]
  rw [BitVec.add_assoc]; congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
  rw [show (8 : W).toNat = 8 from rfl]
  omega

section
variable {m0 m : Mem} {pc fp : W} {s a : Nat} {code : List II} {f : Nat → W} {o c w : W}

/-- `cas d e x` on the owner word: its address in slot `e`, the expected owner in slot `x`, the new one in slot
    `x + 1`; the old owner into slot `d`. -/
theorem ls_cas (E : LE m0 pc fp s a code) (h : LS m0 m fp s a f o c w) {i d e x : Nat} {D A X : Int}
    (hi : code[i]? = some (ci 22 D A X)) (hD : D = ((s + d : Nat) : Int)) (hA : A = ((s + e : Nat) : Int))
    (hX : X = ((s + x : Nat) : Int)) (hd : d < 18) (he : e < 18) (hx : x + 1 < 18)
    (hae : f e = BitVec.ofNat 64 a) :
    ∃ m', Star ⟨pc + BitVec.ofNat 64 (16 * i), fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * (i + 1)), fp⟩ m' ∧
      LS m0 m' fp s a (upd f d o) (if o = f x then f (x + 1) else o) c w := by
  subst hD hA hX
  have hI := E.ins h.ag hi
  simp only [ci] at hI
  have hs := E.small
  have hcas := cas_spec (e := f x) (n := f (x + 1)) h.o (by rw [h.ag.wr]; exact E.wr0)
  have hL1 : LS m0 (if o = f x then write m (BitVec.ofNat 64 a) 8 (f (x + 1)).toNat else m) fp s a f
      (if o = f x then f (x + 1) else o) c w := by
    by_cases heq : o = f x
    · simp only [heq, ite_true]; exact h.owner E _
    · simp only [heq, ite_false]; exact h
  generalize hm1 : (if o = f x then write m (BitVec.ofNat 64 a) 8 (f (x + 1)).toNat else m) = m1 at hcas hL1
  have hF := E.frameK hL1.ag
  refine ⟨_, ls_star hI (by decide) ?_, hL1.slot E hd o⟩
  rw [← pc_next]
  simp only [op]
  refine f2_run hI ?_
  rw [sx_nat (d := s + e) (by omega)]
  simp only [ld]
  refine run_rd64 (h.sl e he) ?_
  refine f3_run hI ?_
  rw [sx_nat (d := s + x) (by omega)]
  refine run_rd64 (h.sl x (by omega)) ?_
  rw [slot_plus8]
  refine run_rd64 (h.sl (x + 1) hx) ?_
  rw [hae]
  refine .ask (a := some (o, 0)) (m' := m1) (by simp only [memAns, hcas]) ?_
  simp only [opt_some, ret1]
  have hI1 := E.ins hL1.ag hi
  simp only [ci] at hI1
  refine f1_run hI1 ?_
  rw [sx_nat (d := s + d) (by omega)]
  exact run_wr64 (wr64_some (hF.wr _ (by omega)))

end

end Gabbro.Stage0.Senke
