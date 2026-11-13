/-
  File:      stage0/Stage0/Senke/Sperre/Lauf.lean
  Subject:   What survives the lock code (`AgreeK`: only the scratch slots and the lock's own words change): the
             frame's lower slots, the code, the world, the environment, the frame header.
-/
module
public import Stage0.Senke.Sperre.Nimm
public import Stage0.Senke.Sperre.Ticket.Sync
public import Stage0.Senke.Rueckkehr
@[expose] public section


namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable [Kern]

variable {D : Deklaration} {L : Lay D}

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

/-- Lock bookkeeping preserves complete values below its scratch frame. -/
theorem AgreeK.valueAt {fp : W} {base s a : Nat} {m m' : Mem} {τ : Ty} {v : Wert D τ}
    (h : AgreeK fp s a m m') (value : ValueAt L m fp base τ v)
    (below : base + valueWords τ ≤ s) (hf : fp.toNat + 8 * (s + 18) ≤ a)
    (ha : a + 24 < 2 ^ 31) : ValueAt L m' fp base τ v := by
  refine ⟨value.1, ?_⟩
  intro i hi
  have width := encodeWords_length L τ v
  rw [h.rd_low (by omega) hf ha]
  exact value.2 i hi

theorem AgreeK.envAt {reserved : Nat} {fp : W} {s a : Nat} {m m' : Mem} {Γ : Ctx} {ρ : Env D Γ} (h : AgreeK fp s a m m')
    (he : EnvAt L m fp ρ reserved) (hs : frei Γ reserved ≤ s) (hf : fp.toNat + 8 * (s + 18) ≤ a) (ha : a + 24 < 2 ^ 31) :
    EnvAt L m' fp ρ reserved := fun τ x => by
  have bound := variableOffset_bound x
  exact h.valueAt (he τ x) (by unfold vslot frei at *; omega) hf ha

theorem AgreeK.codeAt {fp : W} {s a : Nat} {m m' : Mem} (h : AgreeK fp s a m m') (hf : fp.toNat + 8 * (s + 18) ≤ a)
    (ha : a + 24 < 2 ^ 31) {pc : W} {is : List II} (hc : CodeAt m pc is) {K : Nat} (hcf : CodeFar pc is.length fp K) :
    CodeAt m' pc is :=
  hc.agree (h.big hf ha) (by obtain ⟨h1, h2, h3⟩ := hcf; have := fp.isLt; exact ⟨h1, by omega, h3⟩)

theorem AgreeK.preS {reserved : Nat} {m m1 : Mem} {pc fp : W} {K d s a : Nat} {xs ys : List II} {Γ : Ctx} {ρ : Env D Γ}
    (h : PreS L m pc fp K d (xs ++ ys) ρ reserved) (ha : AgreeK fp s a m m1) (hs : frei Γ reserved ≤ s) (hf : fp.toNat + 8 * (s + 18) ≤ a)
    (ha31 : a + 24 < 2 ^ 31) : PreS L m1 (pc + BitVec.ofNat 64 (16 * xs.length)) fp K d ys ρ reserved :=
  have hcf := codeFar_right (n := xs.length) (k := ys.length) (by simpa using h.far)
  ⟨h.ctx, h.small, ⟨h.frame.lt, fun i hi => by rw [ha.rd]; exact h.frame.rd i hi,
    fun i hi => by rw [ha.wr]; exact h.frame.wr i hi⟩, ha.codeAt hf ha31 (codeAt_right h.code) hcf, hcf,
   ha.envAt h.env hs hf ha31, trivial, wstab_true _ _⟩

theorem AgreeK.kopf {P : Programm D} {σ0 : World D} {m m1 : Mem} {fp : W} {K s a : Nat} {f : D.Fn} {rp cfp : W} {ρ0 : Env D (D.params f)}
    (h : Kopf L f m fp K rp cfp ρ0 P σ0) (ha : AgreeK fp s a m m1) (hs : (functionFrame P f).internalResult ≤ s)
    (hf : fp.toNat + 8 * (s + 18) ≤ a) (ha31 : a + 24 < 2 ^ 31) : Kopf L f m1 fp K rp cfp ρ0 P σ0 := by
  have hFB3 : FB = 4 := rfl
  have original := functionFrame_prefix P f
  have parameterEnd : frei (D.params f) (functionFrame P f).ensReserved =
      (functionFrame P f).internalResult := rfl
  have snapshotEnd : FB + EntrySnapshots.words (oldCells (P.ensures f)) ≤
      (functionFrame P f).internalResult := (functionFrame P f).protected_prefix.1
  refine ⟨by rw [ha.rd_low (by omega) hf ha31]; exact h.r0,
    by rw [ha.rd_low (by omega) hf ha31]; exact h.r1,
    ha.envAt h.env (by rw [parameterEnd]; exact hs) hf ha31, h.big, ?_⟩
  have saved := (EntrySnapshots.values_at σ0 (oldCells (P.ensures f)) (reserved := 0)).mpr h.entry
  have kept := ha.envAt saved (by
    simp only [frei, Nat.add_zero, EntrySnapshots.types_words]
    omega) hf ha31
  exact (EntrySnapshots.values_at σ0 (oldCells (P.ensures f)) (reserved := 0)).mp kept

/-- A complete cell whose bytes keep their values keeps every word and its recursive validity. -/
theorem valueAt_keep {m m' : Mem} {address : Nat} {τ : Ty} {v : Wert D τ}
    (input : ValueAt L m (BitVec.ofNat 64 address) 0 τ v) (hrd : m'.rd = m.rd)
    (bound : address + 8 * valueWords τ < 2 ^ 31)
    (hb : ∀ x : W, address ≤ x.toNat → x.toNat < address + 8 * valueWords τ → m'.b x = m.b x) :
    ValueAt L m' (BitVec.ofNat 64 address) 0 τ v := by
  refine ⟨input.1, fun i hi => ?_⟩
  have index : i < valueWords τ := by simpa only [encodeWords_length] using hi
  have addr : slot (BitVec.ofNat 64 address) (BitVec.ofNat 64 (0 + i)) =
      BitVec.ofNat 64 (address + 8 * i) := by
    simp only [Nat.zero_add, slot]
    change BitVec.ofNat 64 address + BitVec.ofNat 64 i * BitVec.ofNat 64 8 = _
    rw [← BitVec.ofNat_mul, ← BitVec.ofNat_add]
    congr 1; omega
  have h := input.2 i hi
  rw [addr] at h ⊢
  rw [rd64_keep hrd fun j hj => hb _ (by rw [lk_byte (by omega) hj]; omega) (by rw [lk_byte (by omega) hj]; omega)]
  exact h

theorem weltAt_keep {m m' : Mem} {L : Lay D} {σ : World D} (h : WeltAt m L σ) (hl : LayIn L) (hrd : m'.rd = m.rd)
    (hwr : m'.wr = m.wr) (hb : ∀ x : W, L.lo ≤ x.toNat → x.toNat < L.hi → m'.b x = m.b x) : WeltAt m' L σ := by
  obtain ⟨hs, hg, hw⟩ := h
  obtain ⟨hl1, hl2, hl3⟩ := hl
  refine ⟨fun t f k hk => ?_, fun g => ?_, hw.keep hwr⟩
  · have := hl1 t f k hk
    exact valueAt_keep (hs t f k hk) hrd (by omega) fun x h1 h2 => hb x (by omega) (by omega)
  · have := hl2 g
    exact valueAt_keep (hg g) hrd (by omega) fun x h1 h2 => hb x (by omega) (by omega)

theorem AgreeK.weltAt {m m1 : Mem} {fp : W} {s a : Nat} {L : Lay D} {σ : World D} (h : AgreeK fp s a m m1)
    (hw : WeltAt m L σ) (hl : LayIn L) (hlo : fp.toNat + 8 * (s + 18) ≤ L.lo) (hhi : L.hi ≤ a) : WeltAt m1 L σ :=
  weltAt_keep hw hl h.rd h.wr fun x h1 h2 => h.b x (fun ⟨_, h3⟩ => by omega) (fun ⟨h3, _⟩ => by omega)

theorem AgreeK.pcode {m m1 : Mem} {fp : W} {s a K : Nat} {A : D.Fn → Nat} {C : D.Fn → List II}
    (h : AgreeK fp s a m m1) (hp : PCode m A C fp K) (hf : fp.toNat + 8 * (s + 18) ≤ a) (ha : a + 24 < 2 ^ 31) :
    PCode m1 A C fp K := fun g => ⟨h.codeAt hf ha (hp g).1 (hp g).2, (hp g).2⟩

end Gabbro.Stage0.Senke
