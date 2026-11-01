/- Complete storage writes and exact byte footprints for canonical value spans. -/
module
public import Stage0.Senke.Welt.Spans.Span
@[expose] public section


namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable {D : Deklaration} {L : Lay D}

/-- All words are stored, with the same little-endian word ordering as encodeWords. -/
def writeSpan (m : Runner.Mem) (address : Nat) : List Runner.W → Runner.Mem
  | [] => m
  | w :: ws => writeSpan (write m (BitVec.ofNat 64 address) 8 w.toNat) (address + 8) ws

@[simp] theorem writeSpan_rd (m : Runner.Mem) (address : Nat) (ws : List Runner.W) :
    (writeSpan m address ws).rd = m.rd := by
  induction ws generalizing m address with
  | nil => rfl
  | cons w ws ih => exact ih _ _

@[simp] theorem writeSpan_wr (m : Runner.Mem) (address : Nat) (ws : List Runner.W) :
    (writeSpan m address ws).wr = m.wr := by
  induction ws generalizing m address with
  | nil => rfl
  | cons w ws ih => exact ih _ _

/-- Exactly the addressed byte span may change, with no permission changes. -/
theorem writeSpan_out (m : Runner.Mem) (address : Nat) (ws : List Runner.W)
    (bound : address + 8 * ws.length ≤ 2 ^ 64) (x : Runner.W)
    (outside : x.toNat < address ∨ address + 8 * ws.length ≤ x.toNat) :
    (writeSpan m address ws).b x = m.b x := by
  induction ws generalizing m address with
  | nil => rfl
  | cons w ws ih =>
    rw [writeSpan, ih _ _ (by simp at bound; omega) (by simp at outside; omega)]
    change (if _ then _ else _) = _
    split
    · next hit =>
      have := x.isLt
      have ha : (BitVec.ofNat 64 address).toNat = address := by
        simp only [BitVec.toNat_ofNat]; simp at bound; omega
      simp only [BitVec.toNat_sub, ha] at hit
      simp only [List.length_cons] at outside bound
      omega
    · rfl

/-- A disjoint readable word survives the whole write. -/
theorem writeSpan_far {m : Runner.Mem} {address a : Nat} (ws : List Runner.W)
    (bound : address + 8 * ws.length ≤ 2 ^ 64) (readBound : a + 8 ≤ 2 ^ 64)
    (sep : a + 8 ≤ address ∨ address + 8 * ws.length ≤ a) :
    (writeSpan m address ws).rd64 (BitVec.ofNat 64 a) = m.rd64 (BitVec.ofNat 64 a) := by
  simp only [rd64, writeSpan_rd]
  rw [le_congr (m := writeSpan m address ws) (m' := m) (fun j hj => ?_)]
  have e : BitVec.ofNat 64 a + BitVec.ofNat 64 j = BitVec.ofNat 64 (a + j) := by rw [BitVec.ofNat_add]
  rw [e]
  apply writeSpan_out _ _ _ bound
  have h : (BitVec.ofNat 64 (a + j)).toNat = a + j := by simp only [BitVec.toNat_ofNat]; omega
  rw [h]
  omega

/-- Readability of each source cell is enough to preserve a complete stored value. -/
theorem writeSpan_same {m : Runner.Mem} {address : Nat} (ws : List Runner.W)
    (bound : address + 8 * ws.length ≤ 2 ^ 64)
    (readable : ∀ i, i < ws.length → all m.rd (BitVec.ofNat 64 (address + 8 * i)) 8 = true) :
    WordsAt (writeSpan m address ws) (BitVec.ofNat 64 address) 0 ws := by
  induction ws generalizing m address with
  | nil => intro i hi; simp at hi
  | cons w ws ih =>
    let m1 := write m (BitVec.ofNat 64 address) 8 w.toNat
    have tail := ih (m := m1) (address := address + 8) (by simp at bound; omega)
      (fun i hi => by
        have h := readable (i + 1) (by simp; omega)
        simpa [m1, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h)
    intro i hi
    simp only [Nat.zero_add, absolute_slot]
    cases i with
    | zero =>
      simp only [Nat.mul_zero, Nat.add_zero, List.getElem_cons_zero]
      rw [writeSpan, writeSpan_far ws (by simp at bound; omega) (by simp at bound; omega) (Or.inl (by omega))]
      have hread : all m.rd (BitVec.ofNat 64 address) 8 = true := by simpa using readable 0 (by simp)
      simp only [rd64, write_rd, hread, ↓reduceIte, le_write_same, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    | succ i =>
      have h := tail i (by simp at hi; omega)
      simpa [writeSpan, WordsAt, m1, absolute_slot, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

/-- Full typed update with the same recursive validity as frames and returns. -/
theorem writeValue_same {m : Runner.Mem} {address : Nat} {τ : Ty} {v : Wert D τ}
    (bound : address + 8 * valueWords τ ≤ 2 ^ 64)
    (readable : ∀ i, i < valueWords τ → all m.rd (BitVec.ofNat 64 (address + 8 * i)) 8 = true)
    (valid : ValueValid L τ v) :
    StorageAt L (writeSpan m address (encodeWords L τ v)) address τ v := by
  exact ⟨valid, writeSpan_same _ (by simpa only [encodeWords_length] using bound)
    (fun i hi => readable i (by simpa only [encodeWords_length] using hi))⟩

/-- A genuine store instruction; permissions are checked on its actual destination. -/
theorem span_store_step [Kern] {m m' : Runner.Mem} {pc fp va vb : Runner.W} {K tmp src : Nat}
    (small : K < 2 ^ 31) (ht : tmp < K) (hs : src < K)
    (code : CodeAt m pc [ci 16 tmp src 0])
    (address : m.rd64 (slot fp (BitVec.ofNat 64 tmp)) = some va)
    (input : m.rd64 (slot fp (BitVec.ofNat 64 src)) = some vb)
    (writable : m.wr64 va vb = some m') :
    Star ⟨pc, fp⟩ m ⟨pc + 16, fp⟩ m' := by
  have hi := code 0 (by simp)
  simp only [ci, List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero] at hi
  apply Star.one
  apply run_step (t := ⟨pc, fp⟩) hi (by decide)
  apply run_st hi
  · rw [sx_nat (by omega)]; exact address
  · rw [sx_nat (by omega)]; exact input
  · exact writable

end Gabbro.Stage0.Senke
