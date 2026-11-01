/- Full-span source world updates and disjoint-cell preservation. The actual
   store loop is connected to these updates through StoreWorld. -/
import Stage0.Senke.Welt.Spans.SpanWrite

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

variable {D : Deklaration} {L : Lay D}

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

/-- A byte inside the frame's slots is readable. -/
theorem frame_rd_byte {m : Runner.Mem} {fp : Runner.W} {K : Nat} (hF : FrameOK m fp K) {x : Nat}
    (h1 : fp.toNat ≤ x) (h2 : x < fp.toNat + 8 * K) : m.rd (BitVec.ofNat 64 x) = true := by
  have hr := hF.room
  have hw := all_spec (hF.rd ((x - fp.toNat) / 8) (by omega)) (j := (x - fp.toNat) % 8) (by omega)
  have e : slot fp (BitVec.ofNat 64 ((x - fp.toNat) / 8)) + BitVec.ofNat 64 ((x - fp.toNat) % 8) =
      BitVec.ofNat 64 x := by
    apply BitVec.eq_of_toNat_eq
    have := fp.isLt
    have h8 : (8 : Runner.W).toNat = 8 := rfl
    simp only [slot, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, h8]
    omega
  rwa [e] at hw

/-- A word inside the frame's slots is readable. -/
theorem frame_rd_at {m : Runner.Mem} {fp : Runner.W} {K : Nat} (hF : FrameOK m fp K) {a : Nat}
    (h1 : fp.toNat ≤ a) (h2 : a + 8 ≤ fp.toNat + 8 * K) : all m.rd (BitVec.ofNat 64 a) 8 = true := by
  have hr := hF.room
  refine all_of fun j hj => ?_
  have e : BitVec.ofNat 64 a + BitVec.ofNat 64 j = BitVec.ofNat 64 (a + j) := by
    rw [BitVec.ofNat_add]
  rw [e]
  exact frame_rd_byte hF (by omega) (by omega)

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
theorem cell_far {L : Lay D} (hl : LayIn L) (hd : LayDis L) {c c' : Zelle D} (hc : c.da L) (hc' : c'.da L)
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

/-- A complete disjoint value keeps all words and recursive validity. -/
theorem valueAt_writeSpan_far {m : Runner.Mem} {address a : Nat} {τ : Ty} {v : Wert D τ}
    (ws : List Runner.W) (bound : address + 8 * ws.length ≤ 2 ^ 64)
    (readBound : a + 8 * valueWords τ ≤ 2 ^ 64)
    (sep : a + 8 * valueWords τ ≤ address ∨ address + 8 * ws.length ≤ a)
    (input : ValueAt L m (BitVec.ofNat 64 a) 0 τ v) :
    ValueAt L (writeSpan m address ws) (BitVec.ofNat 64 a) 0 τ v := by
  refine ⟨input.1, fun i hi => ?_⟩
  have index : i < valueWords τ := by simpa only [encodeWords_length] using hi
  simp only [Nat.zero_add, absolute_slot]
  rw [writeSpan_far ws bound (by omega) (by omega)]
  simpa only [Nat.zero_add, absolute_slot] using input.2 i hi

/-- Writing every encoded word of a global, preserving all other complete cells. -/
theorem weltAt_glob {m : Runner.Mem} {L : Lay D} {σ : World D} {g : D.Glob}
    {v : Wert D (D.gtyp g)} (hW : WeltAt m L σ) (hl : LayIn L) (hd : LayDis L)
    (valid : ValueValid L (D.gtyp g) v) :
    WeltAt (writeSpan m (L.ga g) (encodeWords L (D.gtyp g) v)) L (σ.storeGlob g v) := by
  obtain ⟨hs, hg, hwr⟩ := hW
  have gin := hl.2.1 g
  have top := hl.2.2
  have spanBound : L.ga g + 8 * (encodeWords L (D.gtyp g) v).length ≤ 2 ^ 64 := by
    rw [encodeWords_length]; omega
  refine ⟨fun t f k hk => ?_, fun g' => ?_, hwr.keep (writeSpan_wr _ _ _)⟩
  · have hin := hl.1 t f k hk
    have sep := hd.spans (.glob g) (.elem t f k) trivial hk (by simp)
    exact valueAt_writeSpan_far _ spanBound (by omega)
      (by simpa [Zelle.adr, Zelle.bytes, encodeWords_length, or_comm] using sep) (hs t f k hk)
  · by_cases eq : g' = g
    · subst g'
      have old := hg g
      have stored := writeValue_same (L := L) (m := m) (address := L.ga g)
        (by omega) (fun i hi => rd64_some_all (by
          simpa only [Nat.zero_add, absolute_slot] using old.2 i (by simpa only [encodeWords_length] using hi))) valid
      simpa [World.storeGlob, StorageAt] using stored
    · have hin := hl.2.1 g'
      have sep := hd.spans (.glob g) (.glob g') trivial trivial (by simp [Ne.symm eq])
      have kept := valueAt_writeSpan_far _ spanBound (by omega)
        (by simpa [Zelle.adr, Zelle.bytes, encodeWords_length, or_comm] using sep) (hg g')
      simpa [World.storeGlob, eq] using kept

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

/-- Writing the complete value at a typed table cell. -/
theorem weltAt_slot {m : Runner.Mem} {L : Lay D} {σ : World D} {t : D.Tab} {f : D.Feld t} {kn : Nat}
    {v : Wert D (D.typ t f)} (hW : WeltAt m L σ) (hl : LayIn L) (hd : LayDis L)
    (hk : (kn : Int) < L.count t) (valid : ValueValid L (D.typ t f) v) :
    WeltAt (writeSpan m (L.elem t f kn) (encodeWords L (D.typ t f) v)) L (σ.storeSlot t kn f v) := by
  obtain ⟨hs, hg, hwr⟩ := hW
  have hin := hl.1 t f kn hk
  have top := hl.2.2
  have spanBound : L.elem t f kn + 8 * (encodeWords L (D.typ t f) v).length ≤ 2 ^ 64 := by
    rw [encodeWords_length]; omega
  refine ⟨fun t' f' k' hk' => ?_, fun g => ?_, hwr.keep (writeSpan_wr _ _ _)⟩
  · by_cases eq : (Zelle.elem t' f' k' : Zelle D) = .elem t f kn
    · cases eq
      have old := hs t f kn hk
      have stored := writeValue_same (L := L) (m := m) (address := L.elem t f kn)
        (by omega) (fun i hi => rd64_some_all (by
          simpa only [Nat.zero_add, absolute_slot] using old.2 i (by simpa only [encodeWords_length] using hi))) valid
      simpa [World.storeSlot, StorageAt] using stored
    · have hin' := hl.1 t' f' k' hk'
      have sep := hd.spans (.elem t f kn) (.elem t' f' k') hk hk' (Ne.symm eq)
      have kept := valueAt_writeSpan_far _ spanBound (by omega)
        (by simpa [Zelle.adr, Zelle.bytes, encodeWords_length, or_comm] using sep) (hs t' f' k' hk')
      rw [storeSlot_other eq]
      exact kept
  · have gin := hl.2.1 g
    have sep := hd.spans (.elem t f kn) (.glob g) hk trivial (by simp)
    exact valueAt_writeSpan_far _ spanBound (by omega)
      (by simpa [Zelle.adr, Zelle.bytes, encodeWords_length, or_comm] using sep) (hg g)

/-- A word whose bytes are kept reads the same. -/
theorem rd64_keep {m m' : Runner.Mem} {a : Runner.W} (hrd : m'.rd = m.rd)
    (hb : ∀ j, j < 8 → m'.b (a + BitVec.ofNat 64 j) = m.b (a + BitVec.ofNat 64 j)) : m'.rd64 a = m.rd64 a := by
  simp only [Runner.Mem.rd64, hrd]
  rw [le_congr (m := m') (m' := m) hb]

end Gabbro.Stage0.Senke
