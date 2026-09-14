/-
  File:      Grammatik/BitVecProben.lean
  Subject:   MEASURE bv_decide ON BIT-VECTOR OBLIGATIONS (lane 181).

  Standalone measurement file: NOT imported by `Grammatik.lean`, so the project's
  axiom discipline is untouched. Build it separately with
  `lean grammatik/Grammatik/BitVecProben.lean` (toolchain `Std` only -- no mathlib,
  no project imports). Uses `bv_decide`, never `native_decide` (forbidden).

  SOURCES
    (a) The QF_BV-shaped obligations of `dokumente/GABBROV.md` /
        `programmlogik/gabbrov/V1.lean` (the 55 sayable of the 66 L rows) and
        `dokumente/PFLICHTEN.md` (range / wraparound / layout rows). "QF_BV-shaped"
        means: the statement is a quantifier-free formula over fixed-width
        values once table domains are instantiated -- propositional combinations
        of equalities, order tests, shifts and masks. Rows that need `countD`,
        `firstD`, `reachesIn`, or a state BETWEEN pre and post are NOT in this
        shape and are listed in CUTS, not tried here.
    (b) Four kernel idioms the task names: lowest-set-bit clear, power-of-two
        alignment, page-table index, a CRC-8 step -- plus a modular-inverse
        Newton step as the nonlinear probe.

  Every theorem below is a VALID BitVec fact (each was checked against an
  independent Python model before it was written down here); `bv_decide` is
  measured as the CLOSER, not as the oracle. `#print axioms` after each proof
  records exactly what it rests on.
-/
import Std.Tactic.BVDecide

namespace Gabbro.Grammatik.BitVecProben

/-! ## A. Doc-sourced QF obligations, stated over `BitVec`.

    Each entry names its source row. What is stated is the load-bearing
    bit-vector fact BEHIND the row (a `requires` clause itself is an assumption
    about a state, not a tautology, so there is nothing to close). -/

/-- A1 -- OR of disjoint status bits is their sum (behind V1 L36-L39,
    PFLICHTEN F4:773-779: "the OR of a subset is its sum"). -/
theorem a1_virtio_or_sum (s : BitVec 8) :
    s &&& (3 : BitVec 8) = 0 → s + 3 = s ||| 3 := by
  bv_decide

/-- A2 -- clearing then setting a status bit sets it (behind V1 L40,
    PFLICHTEN F4:780-782: "a reset applies from EVERY state"). -/
theorem a2_reset_sets (v : BitVec 8) :
    ((v &&& ~~~(1 : BitVec 8)) ||| 1) &&& 1 = 1 := by
  bv_decide

/-- A3 -- frame reconstruction: low 12 bits plus shifted high part
    (PFLICHTEN F9:1514-1516: "the frame is bits 51..12 x 4096"). -/
theorem a3_frame_split (va : BitVec 64) :
    ((va >>> 12) <<< 12) ||| (va &&& (0xFFF : BitVec 64)) = va := by
  bv_decide

/-- A4 -- W^X per instance (V1 L64, PFLICHTEN F9: W^X over the page table). -/
theorem a4_wx_bit (w x : BitVec 1) :
    ¬(w = 1 ∧ x = 1) ↔ (w &&& x) = 0 := by
  bv_decide

/-- A5 -- the refcount fell by exactly one (V1 L08, PFLICHTEN F1 delete_leaf). -/
theorem a5_refcount_down (n : BitVec 16) :
    n ≠ 0 → n - (n - 1) = 1 := by
  bv_decide

/-- A6 -- token consumption decreases (V1 L66, PFLICHTEN F10:1656). -/
theorem a6_token_down (n : BitVec 8) :
    n ≠ 0 → n - 1 < n := by
  bv_decide

/-- A7 -- a wrapping addition had a nonzero length (the overflow half behind
    V1 L49, PFLICHTEN F5:992-993: "the request lies inside the range"). -/
theorem a7_wrap_nonzero (s l : BitVec 8) :
    (s + l < s) → l ≠ 0 := by
  bv_decide

/-- A8 -- a masked index is in range (the M103 shape behind PFLICHTEN
    F1:142-149 "every index into CapObjects lies below 4096"). -/
theorem a8_mask_bound (i : BitVec 64) :
    (i &&& (0xFFF : BitVec 64)) < (4096 : BitVec 64) := by
  bv_decide

/-- A9 -- a single-bit device write preserves every other bit (behind
    PFLICHTEN F2:400 `mirrors` and F2:450-453: "carrying every bit but the
    one the transition names"). -/
theorem a9_single_bit_update (g : BitVec 32) :
    (((g &&& ~~~(1 : BitVec 32)) ||| 1) &&& ~~~(1 : BitVec 32))
      = g &&& ~~~(1 : BitVec 32) := by
  bv_decide

/-! ## B. Kernel idioms (task §4: "3-5 obligations from real kernel idioms"). -/

/-- K1 -- lowest-set-bit clear/isolate partition, at full 64-bit width. -/
theorem k1_lsb_partition (x : BitVec 64) :
    (x &&& (x - 1)) ||| (x &&& -x) = x := by
  bv_decide

/-- K2a -- align-up to 4096 yields a multiple of 4096. -/
theorem k2a_align_mult (x : BitVec 64) :
    (((x + 4095) &&& ~~~(4095 : BitVec 64)) &&& (4095 : BitVec 64)) = 0 := by
  bv_decide

/-- K2b -- align-up is the identity on aligned addresses. -/
theorem k2b_align_idem (x : BitVec 64) :
    x &&& (4095 : BitVec 64) = 0 →
      (x + 4095) &&& ~~~(4095 : BitVec 64) = x := by
  bv_decide

/-- K3 -- page-table index extraction is in range (PFLICHTEN F2:505-510,
    the second-level PTE layout; also F9). -/
theorem k3_pt_index (va : BitVec 64) :
    ((va >>> 12) &&& (0x1FF : BitVec 64)) < (512 : BitVec 64) := by
  bv_decide

/-- K4 -- one CRC-8 byte step, MSB-first, polynomial 0x07, init folded in
    (`s0 = d`, i.e. init 0). Eight explicit steps: `bv_decide` treats a
    plain `def` as opaque, so call sites `unfold` it first. -/
def crc8Byte (d : BitVec 8) : BitVec 8 :=
  let s0 := d
  let s1 := if s0.msb then (s0 <<< 1) ^^^ (0x07 : BitVec 8) else s0 <<< 1
  let s2 := if s1.msb then (s1 <<< 1) ^^^ (0x07 : BitVec 8) else s1 <<< 1
  let s3 := if s2.msb then (s2 <<< 1) ^^^ (0x07 : BitVec 8) else s2 <<< 1
  let s4 := if s3.msb then (s3 <<< 1) ^^^ (0x07 : BitVec 8) else s3 <<< 1
  let s5 := if s4.msb then (s4 <<< 1) ^^^ (0x07 : BitVec 8) else s4 <<< 1
  let s6 := if s5.msb then (s5 <<< 1) ^^^ (0x07 : BitVec 8) else s5 <<< 1
  let s7 := if s6.msb then (s6 <<< 1) ^^^ (0x07 : BitVec 8) else s6 <<< 1
  let s8 := if s7.msb then (s7 <<< 1) ^^^ (0x07 : BitVec 8) else s7 <<< 1
  s8

/-- K4a -- closed known answers (checked against an independent Python model:
    CRC-8/ITU check value of "123456789" is 0xF4 with the same parameters). -/
theorem k4a_crc_zero : crc8Byte 0x00 = 0x00 := by
  unfold crc8Byte
  bv_decide

theorem k4a_crc_ff : crc8Byte 0xFF = 0xF3 := by
  unfold crc8Byte
  bv_decide

/-- K4b -- CRC-8 with init 0 is GF(2)-linear (all 65536 pairs checked in
    Python before stating). -/
theorem k4b_crc_linear (a b : BitVec 8) :
    crc8Byte (a ^^^ b) = crc8Byte a ^^^ crc8Byte b := by
  unfold crc8Byte
  bv_decide

/-- K5 -- one Newton step for the odd modular inverse: if `x` is odd then
    `x * (2 - x) = 1 mod 4` (the nonlinear probe: 32-bit multiplication). -/
theorem k5_newton_mod4 (x : BitVec 32) :
    (x &&& (1 : BitVec 32)) = 1 → ((x * (2 - x)) &&& (3 : BitVec 32)) = 1 := by
  bv_decide

/-! ## C. The kernel-only route: `decide` on small widths.

    No SAT call, no native evaluation, no per-computation axiom -- kernel
    reduction only. Width 4 keeps the exhaustive check instant. -/

/-- C1 -- the K1 shape at width 4, closed by kernel `decide`. -/
theorem c1_kernel_lsb4 (x : BitVec 4) :
    (x &&& (x - 1)) ||| (x &&& -x) = x := by
  decide +revert

#print axioms a1_virtio_or_sum
#print axioms a2_reset_sets
#print axioms a3_frame_split
#print axioms a4_wx_bit
#print axioms a5_refcount_down
#print axioms a6_token_down
#print axioms a7_wrap_nonzero
#print axioms a8_mask_bound
#print axioms a9_single_bit_update
#print axioms k1_lsb_partition
#print axioms k2a_align_mult
#print axioms k2b_align_idem
#print axioms k3_pt_index
#print axioms k4a_crc_zero
#print axioms k4a_crc_ff
#print axioms k4b_crc_linear
#print axioms k5_newton_mod4
#print axioms c1_kernel_lsb4

end Gabbro.Grammatik.BitVecProben
