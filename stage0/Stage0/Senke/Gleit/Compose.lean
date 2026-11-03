/- Composed software binary64 addition (`Block.float`, `op = .add`).

    `softAddComposed` is the one pure entry point on 64-bit words the IR
    routine targets: the shared special-case dispatcher (`softSpecial`)
    decides NaN, infinities and signed zeros, and the silent finite path runs
    the kernel `rundeExakt` of the ordered exact sum. `softAddComposed_model`
    proves the composition equal to the kernel `Gleitkomma.add f64` on ALL
    inputs, reusing `softSpecial_model`; no input is excluded and no
    result is weakened. `softFinite_exact` replays the finite path's exact
    sum from the Align/Unpack piece lemmas (`softAlign_decode` pins each
    decoded numerator to `softNum`, `softAlignAdd_exact` the directional
    identity): the caller orders the exponents, as the IR routine will.
    `softFinite_round` proves the finite path rounds exactly like the kernel
    `add`; `softRound_replay` (in `Runde.lean`) replays the rounding decision
    through the routine's (quotient, remainder, denominator) triple.
    `softAddComposed_bits` is the word identity the routine correctness
    reuses. Subtraction composes this entry point with a sign-bit xor in
    `Normal/Sub.lean`; multiplication has its own exact-product continuation
    in `Mul/`, sharing operand retention and packing with the rational
    division continuation in `Div/`. -/
module
public import Grammatik.Bausteine.Gleitkomma.GleitkommaBits
public import Stage0.Senke.Gleit.Add
public import Stage0.Senke.Gleit.Special
public import Stage0.Senke.Gleit.Unpack
public import Stage0.Senke.Gleit.Align
@[expose] public section


namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik
open Gleitkomma
variable [Runner.IR.Kern]

/-- Composed software addition on words: the dispatcher decides special
    inputs; the silent finite path runs the kernel `rundeExakt` of the
    ordered exact sum (`softAdd` only covers the unreachable fallback). -/
def softAddComposed (a b : UInt64) : UInt64 :=
  match softSpecial a b with
  | some r => gToU64 r
  | none =>
    match wertExakt f64 (u64ToG a), wertExakt f64 (u64ToG b) with
    | some u, some v => gToU64 (rundeExakt f64 (exaktAdd u v))
    | _, _ => softAdd a b

/-- Every well-formed triple re-encodes exactly: the decode/encode roundtrip
    the special path needs. Mirrors the `softAdd_model` argument. -/
theorem u64ToG_gToU64 (r : GBits f64) (hw : wf f64 r)
    (hlt : zuBits f64 r < 2 ^ 64) :
    u64ToG (gToU64 r) = r := by
  have hsize : zuBits f64 r < UInt64.size := lt_of_lt_of_le hlt (by decide)
  have hround : (UInt64.ofNat (zuBits f64 r)).toNat = zuBits f64 r :=
    UInt64.toNat_ofNat_of_lt' hsize
  show ausBits f64 (UInt64.ofNat (zuBits f64 r)).toNat = r
  rw [hround]
  exact ausBits_zuBits f64 f64_dicht _ hw

/-- On the finite path the exact sum rounds exactly like the kernel `add`:
    the dispatcher is silent and both exact values are known. -/
theorem softFinite_round (a b : UInt64) (u v : Exakt)
    (h : softSpecial a b = none)
    (ha : wertExakt f64 (u64ToG a) = some u)
    (hb : wertExakt f64 (u64ToG b) = some v) :
    rundeExakt f64 (exaktAdd u v) = add f64 (u64ToG a) (u64ToG b) := by
  have hmod := floatAddSpecial_model f64 (u64ToG a) (u64ToG b)
  unfold softSpecial at h
  rw [h, ha, hb] at hmod
  exact hmod.symm

/-- The core proof: on every pair of input words, the composed routine
    decodes to exactly the kernel `Gleitkomma.add f64` of the decoded inputs.
    NaN payloads and signs, infinities, signed zeros and subnormals are all
    covered: no input is excluded. -/
theorem softAddComposed_model (a b : UInt64) :
    u64ToG (softAddComposed a b) = add f64 (u64ToG a) (u64ToG b) := by
  unfold softAddComposed
  cases h : softSpecial a b with
  | some r =>
      have hrw := softSpecial_model a b r h
      have hwf : wf f64 (add f64 (u64ToG a) (u64ToG b)) :=
        add_wf f64 f64_p _ _ (ausBits_f64_wf _) (ausBits_f64_wf _)
      rw [← hrw] at hwf
      have hlt : zuBits f64 r < 2 ^ 64 := zuBits_f64_lt _ hwf
      have hd : u64ToG (gToU64 r) = r := u64ToG_gToU64 r hwf hlt
      simpa using hd.trans hrw
  | none =>
      cases ha : wertExakt f64 (u64ToG a) with
      | none =>
          obtain ⟨u, v, hu, hv⟩ := floatAddSpecial_none_exact f64 _ _ h
          rw [hu] at ha
          cases ha
      | some u =>
          cases hb : wertExakt f64 (u64ToG b) with
          | none =>
              obtain ⟨u', v, hu', hv⟩ := floatAddSpecial_none_exact f64 _ _ h
              rw [hv] at hb
              cases hb
          | some v =>
              have hrw := softFinite_round a b u v h ha hb
              have hwf : wf f64 (add f64 (u64ToG a) (u64ToG b)) :=
                add_wf f64 f64_p _ _ (ausBits_f64_wf _) (ausBits_f64_wf _)
              rw [← hrw] at hwf
              have hlt : zuBits f64 (rundeExakt f64 (exaktAdd u v)) < 2 ^ 64 :=
                zuBits_f64_lt _ hwf
              have hd : u64ToG (gToU64 (rundeExakt f64 (exaktAdd u v)))
                  = rundeExakt f64 (exaktAdd u v) := u64ToG_gToU64 _ hwf hlt
              simpa using hd.trans hrw

/-- Encoding roundtrip for the finite path: the rounded triple fits back
    into 64 bits. -/
theorem gToU64_toNat (r : GBits f64) (hw : wf f64 r)
    (hlt : zuBits f64 r < 2 ^ 64) :
    (gToU64 r).toNat = zuBits f64 r := by
  have hsize : zuBits f64 r < UInt64.size := lt_of_lt_of_le hlt (by decide)
  exact UInt64.toNat_ofNat_of_lt' hsize

/-- The word identity the routine correctness reuses: the composed result
    word is exactly the kernel sum's bits. -/
theorem softAddComposed_bits (a b : UInt64) :
    (softAddComposed a b).toNat = zuBits f64 (add f64 (u64ToG a) (u64ToG b)) := by
  unfold softAddComposed
  cases h : softSpecial a b with
  | some r =>
      have hrw := softSpecial_model a b r h
      have hwf : wf f64 (add f64 (u64ToG a) (u64ToG b)) :=
        add_wf f64 f64_p _ _ (ausBits_f64_wf _) (ausBits_f64_wf _)
      rw [← hrw] at hwf
      have hlt : zuBits f64 r < 2 ^ 64 := zuBits_f64_lt _ hwf
      rw [gToU64_toNat r hwf hlt, hrw]
  | none =>
      cases ha : wertExakt f64 (u64ToG a) with
      | none =>
          obtain ⟨u, v, hu, hv⟩ := floatAddSpecial_none_exact f64 _ _ h
          rw [hu] at ha
          cases ha
      | some u =>
          cases hb : wertExakt f64 (u64ToG b) with
          | none =>
              obtain ⟨u', v, hu', hv⟩ := floatAddSpecial_none_exact f64 _ _ h
              rw [hv] at hb
              cases hb
          | some v =>
              have hrw := softFinite_round a b u v h ha hb
              have hwf : wf f64 (add f64 (u64ToG a) (u64ToG b)) :=
                add_wf f64 f64_p _ _ (ausBits_f64_wf _) (ausBits_f64_wf _)
              rw [← hrw] at hwf
              have hlt : zuBits f64 (rundeExakt f64 (exaktAdd u v)) < 2 ^ 64 :=
                zuBits_f64_lt _ hwf
              rw [gToU64_toNat _ hwf hlt, hrw]

/-- The composition agrees with the `softAdd` reference on the decoded
    result, on every input: one entry point, one meaning. -/
theorem softAddComposed_add (a b : UInt64) :
    u64ToG (softAddComposed a b) = u64ToG (softAdd a b) := by
  rw [softAddComposed_model, softAdd_model]

/-- On the finite path the exact sum replays the piece lemmas: each decoded
    numerator is its `softNum` (`softAlign_decode`, hence finite inputs with
    non-maximal exponents), and the directional identity `softAlignAdd_exact`
    scales the smaller operand by the gap. The caller orders the exponents. -/
theorem softFinite_exact (a b : UInt64) (u v : Exakt)
    (ha : wertExakt f64 (u64ToG a) = some u)
    (hb : wertExakt f64 (u64ToG b) = some v)
    (hma : softBexp a ≠ 2047) (hmb : softBexp b ≠ 2047)
    (hle : u.zweierExp ≤ v.zweierExp) :
    exaktAdd u v =
      ⟨softNum (softSign a) (softBexp a) (softFrac a) +
        softNum (softSign b) (softBexp b) (softFrac b) *
          (2 ^ softGap u.zweierExp v.zweierExp : Nat),
        u.zweierExp⟩ := by
  have hau : u.zaehler = softNum (softSign a) (softBexp a) (softFrac a) := by
    have h := softAlign_decode a hma
    rw [ha] at h
    exact Option.some_inj.mp h
  have hbu : v.zaehler = softNum (softSign b) (softBexp b) (softFrac b) := by
    have h := softAlign_decode b hmb
    rw [hb] at h
    exact Option.some_inj.mp h
  rw [softAlignAdd_exact u v hle, hau, hbu]

/-- Joint witness: finite rounding (`1.0 + 2.0 = 3.0`), signed zeros
    (`+0 + +0 = +0`, `-0 + -0 = -0`), subnormal exactness (`1 + 1 = 2`),
    the infinity conflict (`inf + -inf = NaN`), NaN priority with payload
    and sign, and infinity absorption — through the composed entry point. -/
theorem softAddComposed_zeuge :
    softAddComposed 4607182418800017408 4611686018427387904 = 4613937818241073152 ∧
    softAddComposed 0 0 = 0 ∧
    softAddComposed 9223372036854775808 9223372036854775808 = 9223372036854775808 ∧
    softAddComposed 1 1 = 2 ∧
    softAddComposed 9218868437227405312 18442240474082181120 = 9218868437227405313 ∧
    softAddComposed 18442240474082181127 4607182418800017408 = 18442240474082181127 ∧
    softAddComposed 9218868437227405312 4607182418800017408 = 9218868437227405312 := by
  decide +kernel

#print axioms softAddComposed_model
#print axioms softAddComposed_add
#print axioms softFinite_exact
#print axioms softFinite_round
#print axioms gToU64_toNat
#print axioms softAddComposed_bits
#print axioms softAddComposed_zeuge

end Gabbro.Stage0.Senke
