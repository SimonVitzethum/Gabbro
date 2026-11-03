/- The descending string scan executes through the existing generic ALU kernel. -/
module
public import Stage0.Senke.Ausdruck.Aggregat.Frame.String.OrderModel
public import Stage0.Senke.Ausdruck.Arithmetik.Wide.Run
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR

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
    · exact AluIns.bin 3 _ _ _ _ rfl (by omega) (by omega) (by omega) (by omega)
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
  · exact AluIns.bin 14 _ _ _ _ rfl (by omega) (by omega) (by omega) (by omega)
  · exact AluIns.bin 8 _ _ _ _ rfl (by omega) (by omega) (by omega) (by omega)
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
    · cases stringKey_admitted (K := K) (k := k) hn (by omega : a + n + 1 ≤ acc + 1)
        (by omega : acc + 1 < acc + 3) (by omega) i hx <;>
        constructor <;> first | assumption | omega
    · cases stringKey_admitted (K := K) (k := k) hq (by omega : b + q + 1 ≤ acc + 2)
        (by omega : acc + 2 < acc + 3) (by omega) i hy <;>
        constructor <;> first | assumption | omega
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
    rw [len, bytes k hk, keyAt_byte]
    have byte0 := ((bs[k]?).getD ⟨0, by omega, by omega⟩).lo_le
    rw [← Int.toNat_of_nonneg byte0, BitVec.ofInt_natCast]
    by_cases present : k < bs.length
    · have flag : (BitVec.ofInt 64 (k : Int)).ult (BitVec.ofNat 64 bs.length) = true := by
        simp only [BitVec.ofInt_natCast, BitVec.ult, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
      simp only [flag, Runner.IR.bool, ite_true, if_pos present, BitVec.one_mul]
      rw [BitVec.ofNat_add, BitVec.add_comm]
      rfl
    · have flag : (BitVec.ofInt 64 (k : Int)).ult (BitVec.ofNat 64 bs.length) = false := by
        simp only [BitVec.ofInt_natCast, BitVec.ult, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
      simp [flag, Runner.IR.bool, present]
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
    simp only [Bool.beq_eq_decide_eq]
    congr 1
    constructor
    · intro h; have := congrArg BitVec.toNat h; simpa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] using this
    · exact congrArg (BitVec.ofNat 64)
  rw [lt, eq]
  cases r <;> cases (decide (x < y)) <;> cases (x == y) <;> simp_all [Runner.IR.bool, scanStep]

end Gabbro.Stage0.Senke
