/-
  File:      stage0/Stage0/Senke/Sperre/Lauf.lean
  Subject:   What survives the lock code (`AgreeK`: only the scratch slots and the lock's own words change): the
             frame's lower slots, the code, the world, the other locks; the start state `LS` of the lock code; a
             word read back as before has its bytes back (`bytes_of_rd64`), so a lock taken and given again leaves the
             memory as a statement may (`AgreeW`).
-/
import Stage0.Senke.Sperre.Sync
import Stage0.Senke.Rueckkehr

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable [Kern]

variable {D : Deklaration} {L : Lay D}

/-! ## Bytes from a word -/

theorem le_lt (m : Mem) (a : W) : ∀ n, Mem.le m a n < 256 ^ n
  | 0 => by simp [Mem.le]
  | n + 1 => by
    have ih := le_lt m a n
    have hb := (m.b (a + BitVec.ofNat 64 n)).isLt
    have hm := Nat.mul_le_mul_right (256 ^ n) (show (m.b (a + BitVec.ofNat 64 n)).toNat ≤ 255 by omega)
    simp only [Mem.le, Nat.pow_succ]
    omega

theorem le_inj {m m' : Mem} {a : W} : ∀ {n : Nat}, Mem.le m a n = Mem.le m' a n →
    ∀ j, j < n → m.b (a + BitVec.ofNat 64 j) = m'.b (a + BitVec.ofNat 64 j)
  | 0, _, j, hj => absurd hj (Nat.not_lt_zero j)
  | n + 1, h, j, hj => by
    simp only [Mem.le] at h
    have hp : 0 < 256 ^ n := Nat.lt_of_lt_of_le (by decide) (Nat.one_le_pow n 256 (by decide))
    have l1 := le_lt m a n
    have l2 := le_lt m' a n
    have hd := congrArg (· / 256 ^ n) h
    have hr := congrArg (· % 256 ^ n) h
    simp only [Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt l1, Nat.div_eq_of_lt l2, Nat.zero_add,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt l1, Nat.mod_eq_of_lt l2] at hd hr
    by_cases hjn : j = n
    · subst hjn; exact BitVec.eq_of_toNat_eq hd
    · exact le_inj hr j (by omega)

/-- Two memories reading the same word at `y` agree on its bytes. -/
theorem bytes_of_rd64 {m m' : Mem} {y : W} {v : W} (h : m.rd64 y = some v) (h' : m'.rd64 y = some v) :
    ∀ j, j < 8 → m'.b (y + BitVec.ofNat 64 j) = m.b (y + BitVec.ofNat 64 j) := by
  unfold Mem.rd64 at h h'
  split at h
  · split at h'
    · simp only [Option.some.injEq] at h h'
      have e := h'.trans h.symm
      have l1 := le_lt m y 8
      have l2 := le_lt m' y 8
      have e2 : Mem.le m' y 8 = Mem.le m y 8 := by
        have := congrArg BitVec.toNat e
        simp only [BitVec.toNat_ofNat] at this
        rw [Nat.mod_eq_of_lt (by simpa using l2), Nat.mod_eq_of_lt (by simpa using l1)] at this
        exact this
      exact le_inj e2
    · cases h'
  · cases h

/-! ## What the lock code keeps -/

theorem AgreeK.rd_low {fp : W} {s a i : Nat} {m m' : Mem} (h : AgreeK fp s a m m') (hi : i < s)
    (hf : fp.toNat + 8 * (s + 18) ≤ a) (ha : a + 24 < 2 ^ 31) :
    m'.rd64 (slot fp (BitVec.ofNat 64 i)) = m.rd64 (slot fp (BitVec.ofNat 64 i)) := by
  have hs := slot_toNat (fp := fp) (K := s + 18) (i := i) (by omega) (by omega)
  refine rd64_keep h.rd fun j hj => h.b _ (fun ⟨h1, _⟩ => ?_) (fun ⟨h1, _⟩ => ?_)
  · have := fp.isLt
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hs] at h1; omega
  · have := fp.isLt
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hs] at h1; omega

theorem AgreeK.envAt {fp : W} {s a : Nat} {m m' : Mem} {Γ : Ctx} {ρ : Env D Γ} (h : AgreeK fp s a m m')
    (he : EnvAt L m fp ρ) (hs : frei Γ ≤ s) (hf : fp.toNat + 8 * (s + 18) ≤ a) (ha : a + 24 < 2 ^ 31) :
    EnvAt L m' fp ρ := fun τ x => by
  obtain ⟨w, hw, hen⟩ := he τ x
  have := vslot_lt x
  exact ⟨w, by rw [h.rd_low (by omega) hf ha]; exact hw, hen⟩

theorem AgreeK.codeAt {fp : W} {s a : Nat} {m m' : Mem} (h : AgreeK fp s a m m') (hf : fp.toNat + 8 * (s + 18) ≤ a)
    (ha : a + 24 < 2 ^ 31) {pc : W} {is : List II} (hc : CodeAt m pc is) {K : Nat} (hcf : CodeFar pc is.length fp K) :
    CodeAt m' pc is :=
  hc.agree (h.big hf ha) (by obtain ⟨h1, h2, h3⟩ := hcf; have := fp.isLt; exact ⟨h1, by omega, h3⟩)

theorem AgreeK.preS {m m1 : Mem} {pc fp : W} {K d s a : Nat} {xs ys : List II} {Γ : Ctx} {ρ : Env D Γ}
    (h : PreS L m pc fp K d (xs ++ ys) ρ) (ha : AgreeK fp s a m m1) (hs : frei Γ ≤ s) (hf : fp.toNat + 8 * (s + 18) ≤ a)
    (ha31 : a + 24 < 2 ^ 31) : PreS L m1 (pc + BitVec.ofNat 64 (16 * xs.length)) fp K d ys ρ :=
  have hcf := codeFar_right (n := xs.length) (k := ys.length) (by simpa using h.far)
  ⟨h.ctx, h.small, ⟨h.frame.lt, fun i hi => by rw [ha.rd]; exact h.frame.rd i hi,
    fun i hi => by rw [ha.wr]; exact h.frame.wr i hi⟩, ha.codeAt hf ha31 (codeAt_right h.code) hcf, hcf,
   ha.envAt h.env hs hf ha31, trivial, wstab_true _ _⟩

theorem AgreeK.kopf {P : Programm D} {σ0 : World D} {m m1 : Mem} {fp : W} {K s a : Nat} {f : D.Fn} {rp cfp : W} {ρ0 : Env D (D.params f)}
    (h : Kopf L f m fp K rp cfp ρ0 P σ0) (ha : AgreeK fp s a m m1) (hs : FB + (D.params f).length ≤ s)
    (hf : fp.toNat + 8 * (s + 18) ≤ a) (ha31 : a + 24 < 2 ^ 31) : Kopf L f m1 fp K rp cfp ρ0 P σ0 := by
  have hFB3 : FB = 4 := rfl
  refine ⟨by rw [ha.rd_low (by omega) hf ha31]; exact h.r0, by rw [ha.rd_low (by omega) hf ha31]; exact h.r1,
    ha.envAt h.env (by simp only [frei]; omega) hf ha31, h.big, ?_⟩
  intro c hc
  obtain ⟨w, hw, he⟩ := h.entry c hc
  exact ⟨w, by rw [ha.rd_low (by omega) hf ha31]; exact hw, he⟩

theorem weltAt_keep {m m' : Mem} {L : Lay D} {σ : World D} (h : WeltAt m L σ) (hl : LayIn L) (hrd : m'.rd = m.rd)
    (hwr : m'.wr = m.wr) (hb : ∀ x : W, L.lo ≤ x.toNat → x.toNat < L.hi → m'.b x = m.b x) : WeltAt m' L σ := by
  obtain ⟨hs, hg, hw⟩ := h
  obtain ⟨hl1, hl2, hl3⟩ := hl
  refine ⟨fun t f k hk => ?_, fun g => ?_, hw.keep hwr⟩
  · obtain ⟨w, hrw, he⟩ := hs t f k hk
    have := hl1 t f k hk
    refine ⟨w, ?_, he⟩
    rw [rd64_keep hrd fun j hj => hb _ (by rw [lk_byte (by omega) hj]; omega) (by rw [lk_byte (by omega) hj]; omega)]
    exact hrw
  · obtain ⟨w, hrw, he⟩ := hg g
    have := hl2 g
    refine ⟨w, ?_, he⟩
    rw [rd64_keep hrd fun j hj => hb _ (by rw [lk_byte (by omega) hj]; omega) (by rw [lk_byte (by omega) hj]; omega)]
    exact hrw

theorem AgreeK.weltAt {m m1 : Mem} {fp : W} {s a : Nat} {L : Lay D} {σ : World D} (h : AgreeK fp s a m m1)
    (hw : WeltAt m L σ) (hl : LayIn L) (hlo : fp.toNat + 8 * (s + 18) ≤ L.lo) (hhi : L.hi ≤ a) : WeltAt m1 L σ :=
  weltAt_keep hw hl h.rd h.wr fun x h1 h2 => h.b x (fun ⟨_, h3⟩ => by omega) (fun ⟨h3, _⟩ => by omega)

theorem AgreeK.pcode {m m1 : Mem} {fp : W} {s a K : Nat} {A : D.Fn → Nat} {C : D.Fn → List II}
    (h : AgreeK fp s a m m1) (hp : PCode m A C fp K) (hf : fp.toNat + 8 * (s + 18) ≤ a) (ha : a + 24 < 2 ^ 31) :
    PCode m1 A C fp K := fun g => ⟨h.codeAt hf ha (hp g).1 (hp g).2, (hp g).2⟩

/-- The lock words of another lock survive. -/
theorem AgreeK.lockOK {m m1 : Mem} {fp : W} {s Ks Ks' : Nat} {L : Lay D} {Lk Lk' : D.Lock}
    (h : AgreeK fp s (L.lk Lk) m m1) (hy : SyncOK m L fp Ks) (hne : Lk' ≠ Lk) (hs : Ks' ≤ Ks)
    (hf : fp.toNat + 8 * (s + 18) ≤ L.hi) :
    LockOK m1 L fp Ks' Lk' := by
  obtain ⟨o, c, ho, hc, hw, hz⟩ := hy.zust Lk'
  have hd := hy.dis Lk' Lk hne
  have hl := hy.lay Lk'
  have hsy := hy.sye
  have keep : ∀ y, L.lk Lk' ≤ y → y ≤ L.lk Lk' + 16 → m1.rd64 (BitVec.ofNat 64 y) = m.rd64 (BitVec.ofNat 64 y) :=
    fun y h1 h2 => rd64_keep h.rd fun j hj => h.b _ (fun ⟨_, h3⟩ => by
        rw [lk_byte (by omega) hj] at h3
        omega) (fun ⟨h3, h4⟩ => by rw [lk_byte (by omega) hj] at h3 h4; omega)
  refine ⟨o, c, by rw [keep _ (Nat.le_refl _) (by omega)]; exact ho, by rw [keep _ (by omega) (by omega)]; exact hc,
    by rw [keep _ (by omega) (Nat.le_refl _)]; exact hw, ?_⟩
  rcases hz with h0 | ⟨h1, h2, h3⟩
  · exact Or.inl h0
  · exact Or.inr ⟨h1, h2, by omega⟩

end Gabbro.Stage0.Senke
