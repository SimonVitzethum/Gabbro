/-
  File:      stage0/Stage0/Senke/Welt/Schreib.lean
  Subject:   Writing a cell of the world: the word at its address is writable and lies in the frame's slots from `lo`
             on (`frame_wr_at`, `agree_write_at`); after the write the memory holds the world with that one cell
             changed (`weltAt_glob`, `weltAt_slot`), because no two cells share a word (`LayDis`).
-/
import Stage0.Senke.Welt.WeltAt

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

variable {D : Deklaration}

/-- A byte inside the frame's slots is writable. -/
theorem frame_wr_byte {m : Runner.Mem} {fp : Runner.W} {K : Nat} (hF : FrameOK m fp K) {x : Nat}
    (h1 : fp.toNat ≤ x) (h2 : x < fp.toNat + 8 * K) : m.wr (BitVec.ofNat 64 x) = true := by
  have hr := hF.room
  have hw := all_spec (hF.wr ((x - fp.toNat) / 8) (by omega)) (j := (x - fp.toNat) % 8) (by omega)
  have e : slot fp (BitVec.ofNat 64 ((x - fp.toNat) / 8)) + BitVec.ofNat 64 ((x - fp.toNat) % 8) =
      BitVec.ofNat 64 x := by
    apply BitVec.eq_of_toNat_eq
    have := fp.isLt
    have h8 : (8 : Runner.W).toNat = 8 := rfl
    simp only [slot, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, h8]
    omega
  rwa [e] at hw

/-- A word inside the frame's slots is writable. -/
theorem frame_wr_at {m : Runner.Mem} {fp : Runner.W} {K : Nat} (hF : FrameOK m fp K) {a : Nat}
    (h1 : fp.toNat ≤ a) (h2 : a + 8 ≤ fp.toNat + 8 * K) : all m.wr (BitVec.ofNat 64 a) 8 = true := by
  have hr := hF.room
  refine all_of fun j hj => ?_
  have e : BitVec.ofNat 64 a + BitVec.ofNat 64 j = BitVec.ofNat 64 (a + j) := by
    rw [BitVec.ofNat_add]
  rw [e]
  exact frame_wr_byte hF (by omega) (by omega)

/-- Writing a word inside the slots from `lo` changes only the slots from `lo` on. -/
theorem agree_write_at {m : Runner.Mem} {fp : Runner.W} {lo K a : Nat} (hr : fp.toNat + 8 * K ≤ 2 ^ 64)
    (h1 : fp.toNat + 8 * lo ≤ a) (h2 : a + 8 ≤ fp.toNat + 8 * K) (v : Nat) :
    Agree fp lo K m (write m (BitVec.ofNat 64 a) 8 v) := by
  refine ⟨rfl, rfl, fun x hx => ?_⟩
  show (if _ then _ else _) = _
  split
  · next h =>
    exfalso
    apply hx
    have := x.isLt
    have ha : (BitVec.ofNat 64 a).toNat = a := by simp only [BitVec.toNat_ofNat]; omega
    simp only [BitVec.toNat_sub, ha] at h
    constructor <;> omega
  · rfl

/-- The words of two different cells are apart. -/
theorem cell_far {L : Lay D} (hl : LayIn L) (hd : LayDis L) {c c' : Zelle D} (hc : c.da) (hc' : c'.da)
    (hin : c.adr L + 8 ≤ L.hi) (hin' : c'.adr L + 8 ≤ L.hi) (hne : c ≠ c') :
    Far (BitVec.ofNat 64 (c.adr L)) 8 (BitVec.ofNat 64 (c'.adr L)) 8 := by
  have := hl.2.2
  have h1 : (BitVec.ofNat 64 (c.adr L)).toNat = c.adr L := by simp only [BitVec.toNat_ofNat]; omega
  have h2 : (BitVec.ofNat 64 (c'.adr L)).toNat = c'.adr L := by simp only [BitVec.toNat_ofNat]; omega
  have := hd.far hc hc' hne
  unfold Far
  rw [h1, h2]
  omega

theorem rd64_some_all {m : Runner.Mem} {a w : Runner.W} (h : m.rd64 a = some w) : all m.rd a 8 = true := by
  simp only [rd64] at h
  split at h
  · assumption
  · cases h

theorem rd64_write_same {m : Runner.Mem} {a w : Runner.W} (hr : all m.rd a 8 = true) :
    (write m a 8 w.toNat).rd64 a = some w := by
  simp only [rd64, write_rd, hr, ↓reduceIte, le_write_same, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- Writing the word of `v` at the global `g`. -/
theorem weltAt_glob {m : Runner.Mem} {L : Lay D} {σ : World D} {g : D.Glob} {v : Wert D (D.gtyp g)} {w : Runner.W}
    (hW : WeltAt m L σ) (hl : LayIn L) (hd : LayDis L) (he : Enc (D.gtyp g) v w) :
    WeltAt (write m (BitVec.ofNat 64 (L.ga g)) 8 w.toNat) L (σ.storeGlob g v) := by
  obtain ⟨hs, hg⟩ := hW
  have hgin := hl.2.1 g
  refine ⟨fun t f k hk => ?_, fun g' => ?_⟩
  · obtain ⟨w', hw', he'⟩ := hs t f k hk
    have := hl.1 t f k hk
    refine ⟨w', ?_, he'⟩
    have hf := cell_far (c := .glob g) (c' := .elem t f k) hl hd trivial hk (by simpa [Zelle.adr] using hgin.2)
      (by simpa [Zelle.adr] using this.2) (by simp)
    simp only [Zelle.adr] at hf
    rw [rd64_write_far hf]
    exact hw'
  · by_cases hgg : g' = g
    · subst hgg
      obtain ⟨w0, hw0, _⟩ := hg g'
      refine ⟨w, ?_, by simpa [World.storeGlob] using he⟩
      exact rd64_write_same (rd64_some_all hw0)
    · obtain ⟨w', hw', he'⟩ := hg g'
      have := hl.2.1 g'
      refine ⟨w', ?_, by simpa [World.storeGlob, hgg] using he'⟩
      have hf := cell_far (c := .glob g) (c' := .glob g') hl hd trivial trivial
        (by simpa [Zelle.adr] using hgin.2) (by simpa [Zelle.adr] using this.2) (by simp [Ne.symm hgg])
      simp only [Zelle.adr] at hf
      rw [rd64_write_far hf]
      exact hw'

/-- The other elements keep their values under `storeSlot`. -/
theorem storeSlot_other {σ : World D} {t t' : D.Tab} {f : D.Feld t} {f' : D.Feld t'} {kn k' : Nat}
    {v : Wert D (D.typ t f)} (hc : (Zelle.elem t' f' k' : Zelle D) ≠ .elem t f kn) :
    (σ.storeSlot t kn f v).slots t' k' f' = σ.slots t' k' f' := by
  simp only [World.storeSlot]
  split
  · next ht =>
    subst ht
    simp only
    split
    · next hkk =>
      split
      · next hff =>
        subst hff
        exact absurd (by rw [show k' = kn by omega]) hc
      · rfl
    · rfl
  · rfl

/-- Writing the word of `v` at element `kn` of column `f` of table `t`. -/
theorem weltAt_slot {m : Runner.Mem} {L : Lay D} {σ : World D} {t : D.Tab} {f : D.Feld t} {kn : Nat}
    {v : Wert D (D.typ t f)} {w : Runner.W} (hW : WeltAt m L σ) (hl : LayIn L) (hd : LayDis L)
    (hk : (kn : Int) < D.count t) (he : Enc (D.typ t f) v w) :
    WeltAt (write m (BitVec.ofNat 64 (L.elem t f kn)) 8 w.toNat) L (σ.storeSlot t kn f v) := by
  obtain ⟨hs, hg⟩ := hW
  have hin := hl.1 t f kn hk
  refine ⟨fun t' f' k' hk' => ?_, fun g => ?_⟩
  · by_cases hc : (Zelle.elem t' f' k' : Zelle D) = .elem t f kn
    · cases hc
      obtain ⟨w0, hw0, _⟩ := hs t f kn hk
      exact ⟨w, rd64_write_same (rd64_some_all hw0), by simpa [World.storeSlot] using he⟩
    · obtain ⟨w', hw', he'⟩ := hs t' f' k' hk'
      have := hl.1 t' f' k' hk'
      refine ⟨w', ?_, by rw [storeSlot_other hc]; exact he'⟩
      have hf := cell_far (c := .elem t f kn) (c' := .elem t' f' k') hl hd hk hk'
        (by simpa [Zelle.adr] using hin.2) (by simpa [Zelle.adr] using this.2) (Ne.symm hc)
      simp only [Zelle.adr] at hf
      rw [rd64_write_far hf]
      exact hw'
  · obtain ⟨w', hw', he'⟩ := hg g
    have := hl.2.1 g
    refine ⟨w', ?_, he'⟩
    have hf := cell_far (c := .elem t f kn) (c' := .glob g) hl hd hk trivial
      (by simpa [Zelle.adr] using hin.2) (by simpa [Zelle.adr] using this.2) (by simp)
    simp only [Zelle.adr] at hf
    rw [rd64_write_far hf]
    exact hw'

end Gabbro.Stage0.Senke
