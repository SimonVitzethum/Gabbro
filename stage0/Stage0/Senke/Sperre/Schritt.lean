/-
  File:      stage0/Stage0/Senke/Sperre/Schritt.lean
  Subject:   Single instructions of the lock code (`Sperre/Code.lean`) on a state `LS`: the scratch slots `s .. s+17`
             hold `f`, the lock's three words at `a` hold owner, count and waiters, and apart from both the memory
             is the one the code started in (`AgreeK`). Each lemma runs instruction `i` of the code `code` at `pc`.
-/
module
public import Stage0.Senke.Sperre.Schritta
public import Stage0.Senke.Sperre.Code
public import Stage0.Senke.Umgebung
public import Stage0.Senke.Hilfe
public import Stage0.Senke.Welt.Schreib
@[expose] public section


namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable [Kern]

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
