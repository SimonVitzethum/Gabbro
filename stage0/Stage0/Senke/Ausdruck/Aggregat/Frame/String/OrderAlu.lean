/- The descending string scan executes through the existing generic ALU kernel. -/
module
public import Stage0.Senke.Ausdruck.Aggregat.Frame.String.OrderModel
public import Stage0.Senke.Ausdruck.Arithmetik.Wide.Run
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR

/-- Moving a write bound downward retains the same instructions and operands. -/
theorem AluIns.lower {K lo hi : Nat} {i : II} (h : AluIns K hi i) (below : lo ≤ hi) :
    AluIns K lo i := by
  cases h <;> constructor <;> first | assumption | omega

theorem stringKey_admitted {K n a k out tmp : Nat}
    (hn : n < 2 ^ 31) (ha : a + n + 1 ≤ out) (ht : out < tmp) (hK : tmp + 1 < K) :
    ∀ i ∈ stringKeyC n a k out tmp, AluIns K out i := by
  intro i hi
  unfold stringKeyC at hi
  split at hi
  · next hk =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl
    · exact AluIns.const _ _ (by omega) (by omega)
        (by simp only [lit32, Bool.and_eq_true, decide_eq_true_eq]; omega)
    · exact AluIns.bin 27 _ _ _ _ rfl (by omega) (by omega) (by omega) (by omega)
    · exact AluIns.const _ _ (by omega) (by omega) (by decide)
    · exact AluIns.bin 3 tmp tmp (a + 1 + k) _ rfl
        (by omega) (by omega) (by omega) (by omega)
    · exact AluIns.bin 5 _ _ _ _ rfl (by omega) (by omega) (by omega) (by omega)
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
    subst i
    exact AluIns.const _ _ (by omega) (by omega) (by decide)

theorem stringCompare_admitted {K acc : Nat} (hK : acc + 5 ≤ K) :
    ∀ i ∈ stringCompareC (acc + 1) (acc + 2) acc (acc + 3), AluIns K acc i := by
  intro i hi
  simp only [stringCompareC, List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · exact AluIns.bin 27 _ _ _ _ rfl (by omega) (by omega) (by omega) (by omega)
  · exact AluIns.bin 14 (acc + 3 + 1) (acc + 1) (acc + 2) _ rfl
      (by omega) (by omega) (by omega) (by omega)
  · exact AluIns.bin 8 acc (acc + 3 + 1) acc _ rfl
      (by omega) (by omega) (by omega) (by omega)
  · exact AluIns.bin 9 _ _ _ _ rfl (by omega) (by omega) (by omega) (by omega)

theorem stringScan_admitted {K n q a b acc : Nat}
    (hn : n < 2 ^ 31) (hq : q < 2 ^ 31)
    (ha : a + n + 1 ≤ acc) (hb : b + q + 1 ≤ acc) (hK : acc + 5 ≤ K) :
    ∀ k i, i ∈ stringScanC k n q a b acc → AluIns K acc i := by
  intro k
  induction k with
  | zero => intro i hi; simp [stringScanC] at hi
  | succ k ih =>
    intro i hi
    simp only [stringScanC, List.mem_append] at hi
    rcases hi with ((hx | hy) | hc) | ht
    · exact (stringKey_admitted (K := K) (k := k) hn (by omega : a + n + 1 ≤ acc + 1)
        (by omega : acc + 1 < acc + 3) (by omega) i hx).lower (by omega)
    · exact (stringKey_admitted (K := K) (k := k) hq (by omega : b + q + 1 ≤ acc + 2)
        (by omega : acc + 2 < acc + 3) (by omega) i hy).lower (by omega)
    · exact stringCompare_admitted hK i hc
    · exact ih i ht

theorem stringKey_value {n a k out tmp : Nat} (s : Nat → Runner.W)
    (bs : List (Zahl 0 255)) (hlen : bs.length ≤ n) (hn : n < 2 ^ 31)
    (ha : a + n + 1 ≤ out) (ht : out < tmp)
    (len : s a = BitVec.ofNat 64 bs.length)
    (bytes : ∀ j, j < n → s (a + 1 + j) =
      BitVec.ofInt 64 ((bs[j]?).getD ⟨0, by omega, by omega⟩).n) :
    aluRun (stringKeyC n a k out tmp) s out = BitVec.ofNat 64 (keyAt (bs.map (·.n)) k) := by
  unfold stringKeyC
  split
  · next hk =>
    simp (disch := omega) only [aluRun_cons, aluRun_nil, aluStep, aluVal, ci, aluFn,
      Int.toNat_natCast, slotUpd_same, slotUpd_other, ite_true, ite_false,
      OfNat.ofNat_ne_one, Nat.reduceEqDiff, ne_eq, not_false_eq_true]
    have slotIndex : ((a : Int) + 1 + (k : Int)).toNat = a + 1 + k :=
      Int.toNat_natCast (a + 1 + k)
    rw [slotIndex, len, bytes k hk, keyAt_byte]
    have byte0 := ((bs[k]?).getD ⟨0, by omega, by omega⟩).lo_le
    have byteWord : BitVec.ofInt 64 ((bs[k]?).getD ⟨0, by omega, by omega⟩).n =
        BitVec.ofNat 64 ((bs[k]?).getD ⟨0, by omega, by omega⟩).n.toNat := by
      rw [← Int.toNat_of_nonneg byte0, BitVec.ofInt_natCast]
    rw [byteWord]
    by_cases present : k < bs.length
    · have flag : (BitVec.ofInt 64 (k : Int)).ult (BitVec.ofNat 64 bs.length) = true := by
        simp only [BitVec.ofInt_natCast, BitVec.ult, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
      simp only [flag, Runner.IR.bool, ite_true, ite_eq_left present]
      change (1#64) * ((1#64) + BitVec.ofNat 64
        ((bs[k]?).getD ⟨0, by omega, by omega⟩).n.toNat) = _
      rw [BitVec.one_mul, BitVec.ofNat_add]
      exact BitVec.add_comm _ _
    · have flag : (BitVec.ofInt 64 (k : Int)).ult (BitVec.ofNat 64 bs.length) = false := by
        simp only [BitVec.ofInt_natCast, BitVec.ult, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
      simp only [flag, Runner.IR.bool, ite_false, ite_eq_right present]
      change (0#64) * _ = 0#64
      exact BitVec.zero_mul
  · next hk =>
    have absent : ¬ k < bs.length := by omega
    simp [aluRun, aluStep, aluVal, ci, slotUpd, keyAt_byte, absent]

theorem stringCompare_value (acc : Nat) (s : Nat → Runner.W) (x y : Nat) (r : Bool)
    (hx : x < 2 ^ 64) (hy : y < 2 ^ 64)
    (rx : s (acc + 1) = BitVec.ofNat 64 x) (ry : s (acc + 2) = BitVec.ofNat 64 y)
    (rr : s acc = Runner.IR.bool r) :
    aluRun (stringCompareC (acc + 1) (acc + 2) acc (acc + 3)) s acc =
      Runner.IR.bool (scanStep x y r) := by
  simp (disch := omega) only [stringCompareC, aluRun_cons, aluRun_nil, aluStep, aluVal,
    ci, aluFn, Int.toNat_natCast, slotUpd_same, slotUpd_other, ite_true, ite_false,
    OfNat.ofNat_ne_one, Nat.reduceEqDiff, ne_eq, not_false_eq_true]
  rw [rx, ry, rr]
  have lt : (BitVec.ofNat 64 x).ult (BitVec.ofNat 64 y) = decide (x < y) := by
    simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]
  have eq : (BitVec.ofNat 64 x == BitVec.ofNat 64 y) = (x == y) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq]
    constructor
    · intro h
      have values := congrArg BitVec.toNat h
      simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] using values
    · exact congrArg (BitVec.ofNat 64)
  rw [lt, eq]
  by_cases less : x < y <;> by_cases equal : x = y <;>
    cases r <;> simp_all [Runner.IR.bool, scanStep]

end Gabbro.Stage0.Senke
