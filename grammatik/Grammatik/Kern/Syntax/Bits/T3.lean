/- Part 3 of 3 of `Bits` (split by instrumente/teile/lean-teilen.py; the umbrella `Bits.lean` imports all parts). -/
import Grammatik.Kern.Syntax.Bits.T2

namespace Gabbro.Grammatik

/-- `bswap_bswap`: double reversal is identity, at all three widths. -/
theorem bswap_bswap16 (x : Zahl 0 ((2 : Int) ^ 16 - 1)) :
    (Zahl.bswap16 (Zahl.bswap16 x)).n = x.n := by
  have hnn : 0 ≤ x.n := by have := x.lo_le; omega
  have h2n : (x.n.toNat : Int) = x.n := Int.toNat_of_nonneg hnn
  have hx : x.n.toNat < 256 ^ 2 := by
    have hhi := x.le_hi
    have hcast : ((2 ^ 16 : Nat) : Int) = (2 : Int) ^ 16 := by simp only [Nat.reducePow, Int.cast_ofNat_Int, Int.reducePow]
    have e : (256 : Nat) ^ 2 = 2 ^ 16 := by decide
    rw [e]
    have hlt : x.n < ((2 ^ 16 : Nat) : Int) := by omega
    exact (Int.toNat_lt hnn).mpr hlt
  have hmid : (Zahl.bswap16 x).n.toNat = bswap16n x.n.toNat := by
    show ((bswap16n x.n.toNat : Nat) : Int).toNat = _
    exact Int.toNat_natCast _
  have h := bswap16n_invol x.n.toNat hx
  show ((bswap16n (Zahl.bswap16 x).n.toNat : Nat) : Int) = x.n
  rw [hmid, h, h2n]

theorem bswap_bswap32 (x : Zahl 0 ((2 : Int) ^ 32 - 1)) :
    (Zahl.bswap32 (Zahl.bswap32 x)).n = x.n := by
  have hnn : 0 ≤ x.n := by have := x.lo_le; omega
  have h2n : (x.n.toNat : Int) = x.n := Int.toNat_of_nonneg hnn
  have hx : x.n.toNat < 256 ^ 4 := by
    have hhi := x.le_hi
    have e : (256 : Nat) ^ 4 = 2 ^ 32 := by decide
    rw [e]
    have hlt : x.n < ((2 ^ 32 : Nat) : Int) := by
      have hcast : ((2 ^ 32 : Nat) : Int) = (2 : Int) ^ 32 := by simp only [Nat.reducePow, Int.cast_ofNat_Int, Int.reducePow]
      omega
    exact (Int.toNat_lt hnn).mpr hlt
  have hmid : (Zahl.bswap32 x).n.toNat = bswap32n x.n.toNat := by
    show ((bswap32n x.n.toNat : Nat) : Int).toNat = _
    exact Int.toNat_natCast _
  have h := bswap32n_invol x.n.toNat hx
  show ((bswap32n (Zahl.bswap32 x).n.toNat : Nat) : Int) = x.n
  rw [hmid, h, h2n]

theorem bswap_bswap64 (x : Zahl 0 ((2 : Int) ^ 64 - 1)) :
    (Zahl.bswap64 (Zahl.bswap64 x)).n = x.n := by
  have hnn : 0 ≤ x.n := by have := x.lo_le; omega
  have h2n : (x.n.toNat : Int) = x.n := Int.toNat_of_nonneg hnn
  have hx : x.n.toNat < 256 ^ 8 := by
    have hhi := x.le_hi
    have e : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
    rw [e]
    have hlt : x.n < ((2 ^ 64 : Nat) : Int) := by
      have hcast : ((2 ^ 64 : Nat) : Int) = (2 : Int) ^ 64 := by simp only [Nat.reducePow, Int.cast_ofNat_Int, Int.reducePow]
      omega
    exact (Int.toNat_lt hnn).mpr hlt
  have hmid : (Zahl.bswap64 x).n.toNat = bswap64n x.n.toNat := by
    show ((bswap64n x.n.toNat : Nat) : Int).toNat = _
    exact Int.toNat_natCast _
  have h := bswap64n_invol x.n.toNat hx
  show ((bswap64n (Zahl.bswap64 x).n.toNat : Nat) : Int) = x.n
  rw [hmid, h, h2n]

/-! ## Witness for `clz_log2` (rule 13): width 32, `x = 1` and `x = 2 ^ 31`.

    `clz_log2` has no universal premise over program syntax, but the lane
    names it as TARGET (`ZEUGE: clz_log2`), so it needs a joint witness
    anyway. Both cases evaluate by `decide` to the required numerals. -/

/-- Width-32 field element `1`: `clz = 31`, `log2 = 0`. -/
def zeuge1 : Zahl 1 ((2 : Int) ^ (31 + 1) - 1) := ⟨1, by decide, by decide⟩

/-- Width-32 field element `2 ^ 31`: `clz = 0`, `log2 = 31`. -/
def zeuge2 : Zahl 1 ((2 : Int) ^ (31 + 1) - 1) := ⟨2 ^ 31, by decide, by decide⟩

theorem clz_log2_zeuge :
    (Zahl.clz 31 zeuge1).n = 31 ∧ (Zahl.log2_floor 31 zeuge1).n = 0
      ∧ (Zahl.clz 31 zeuge2).n = 0 ∧ (Zahl.log2_floor 31 zeuge2).n = 31 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/- CUTS: what is not proved.
   - Syntax integration: no `Expr.clz` / `Stmt` constructor takes these
     operations yet; the file is the model half (PLAN-BITS.md section 3).
     Wiring the intrinsics into `Syntax.lean` / the checker ranges is open.
   - `rotl_rotr` is proved in one direction only (`rotr ∘ rotl = id`);
     `rotl ∘ rotr = id` is not stated (same proof shape, mirrored halves).
   - `bswap` range/round-trip at `Nat` level is proved; the `Zahl` wrappers
     for 16/32/64 restate involution per width instead of one parametric
     theorem (the task allows three functions or one with a premise; the
     three-function form was chosen because the widths are concrete types).
   - C lowering note: `Zahl.clz` / `Zahl.ctz` / `Zahl.log2_floor` map to
     `__builtin_clz` / `__builtin_ctz` / `31 - __builtin_clz` (on `unsigned`);
     `Zahl.popcount` to `__builtin_popcount`; `Zahl.rotl` / `Zahl.rotr` to
     the `(x << s) | (x >> (W - s))` idiom (GCC/Clang lower it to `rol`);
     `Zahl.bswap16/32/64` to `__builtin_bswap16/32/64`. The zero case is
     unreachable because the argument type `Zahl 1 (2^(w+1) - 1)` excludes
     `0`: there is no value to pass to `__builtin_clz(0)` (undefined per
     the GCC manual), so no convention like `clz 0 = w` is needed and no
     `31 - clz(x)` index derivation can go negative from it.
-/

#print axioms Gabbro.Grammatik.log2_floor_spez
#print axioms Gabbro.Grammatik.clz_log2
#print axioms Gabbro.Grammatik.ctz_spez
#print axioms Gabbro.Grammatik.popcount_rotl
#print axioms Gabbro.Grammatik.rotl_rotr
#print axioms Gabbro.Grammatik.bswap_bswap16
#print axioms Gabbro.Grammatik.bswap_bswap32
#print axioms Gabbro.Grammatik.bswap_bswap64
#print axioms Gabbro.Grammatik.clz_log2_zeuge


end Gabbro.Grammatik
