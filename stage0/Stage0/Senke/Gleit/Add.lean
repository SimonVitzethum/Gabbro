/- Pure-Lean software reference for binary64 addition (`Block.float`, `op = .add`).

    `softAdd` decodes two 64-bit words with `ausBits`, runs the kernel
    `Gleitkomma.add f64`, and encodes the result with `zuBits`.
    `softAdd_model` proves it equals the kernel operation on ALL inputs,
    including NaN payloads, infinities, signed zeros and subnormals; no
    input is excluded and no result is weakened. `softAdd_special`
    connects the reference to the shared special-case dispatcher
    (`floatAddSpecial_model`), so the later IR routine replays the same
    decomposition (unpack, special cases, align, add, round, normalize,
    pack) lemma by lemma. `sub`/`mul`/`div` have no reference here and
    stay refused. -/
module
public import Grammatik.Bausteine.Gleitkomma.GleitkommaBits
public import Stage0.Senke.Ausdruck.Arithmetik.AddSub
@[expose] public section


namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik
open Gleitkomma

/-- Decode a 64-bit word as a binary64 triple (sign, biased exponent, fraction). -/
def u64ToG (a : UInt64) : GBits f64 := ausBits f64 a.toNat

/-- Encode a binary64 triple as a 64-bit word. -/
def gToU64 (g : GBits f64) : UInt64 := UInt64.ofNat (zuBits f64 g)

/-- Software reference for `Block.float` with `op = .add`: the exact kernel
    addition, transported to 64-bit words. -/
def softAdd (a b : UInt64) : UInt64 := gToU64 (add f64 (u64ToG a) (u64ToG b))

/-- Every 64-bit word decodes to a well-formed binary64 triple: the exponent
    field holds values below `2^11`, the fraction below `2^52`. -/
theorem ausBits_f64_wf (n : Nat) : wf f64 (ausBits f64 n) := by
  have e11 : Format.ebits f64 = 11 := by decide
  have f52 : Format.fracBits f64 = 52 := by decide
  have bmax : Format.bexpMax f64 = 2047 := by decide
  unfold wf ausBits
  rw [e11, f52, bmax]
  constructor
  · show (n / 2 ^ 52) % 2 ^ 11 ≤ 2047
    have h : (n / 2 ^ 52) % 2 ^ 11 < 2 ^ 11 := Nat.mod_lt _ (by decide)
    omega
  · show n % 2 ^ 52 < 2 ^ 52
    exact Nat.mod_lt _ (by decide)

/-- Every kernel addition result fits back into 64 bits. -/
theorem zuBits_f64_lt (g : GBits f64) (hw : wf f64 g) : zuBits f64 g < 2 ^ 64 := by
  have h := zuBits_lt f64 f64_dicht g hw
  have e11 : Format.ebits f64 = 11 := by decide
  have f52 : Format.fracBits f64 = 52 := by decide
  rw [e11, f52] at h
  exact h

/-- The core proof: on every pair of input words, the software reference
    decodes to exactly the kernel `Gleitkomma.add f64` of the decoded inputs.
    NaN payloads and signs, infinities, signed zeros and subnormals are all
    covered: no input is excluded. -/
theorem softAdd_model (a b : UInt64) :
    u64ToG (softAdd a b) = add f64 (u64ToG a) (u64ToG b) := by
  have hw : wf f64 (add f64 (u64ToG a) (u64ToG b)) :=
    add_wf f64 f64_p _ _ (ausBits_f64_wf _) (ausBits_f64_wf _)
  have hlt : zuBits f64 (add f64 (u64ToG a) (u64ToG b)) < 2 ^ 64 :=
    zuBits_f64_lt _ hw
  have hsize : zuBits f64 (add f64 (u64ToG a) (u64ToG b)) < UInt64.size :=
    lt_of_lt_of_le hlt (by decide)
  have hround : (UInt64.ofNat (zuBits f64 (add f64 (u64ToG a) (u64ToG b)))).toNat
      = zuBits f64 (add f64 (u64ToG a) (u64ToG b)) :=
    UInt64.toNat_ofNat_of_lt' hsize
  show ausBits f64 (UInt64.ofNat (zuBits f64 (add f64 (u64ToG a) (u64ToG b)))).toNat
      = add f64 (u64ToG a) (u64ToG b)
  rw [hround]
  exact ausBits_zuBits f64 f64_dicht _ hw

/-- The reference follows the shared decomposition: the special-case
    dispatcher decides, and the finite path rounds the exact sum. This is
    the per-step kernel lemma the IR routine replays. -/
theorem softAdd_special (a b : UInt64) :
    u64ToG (softAdd a b) =
      match floatAddSpecial f64 (u64ToG a) (u64ToG b) with
      | some r => r
      | none =>
        match wertExakt f64 (u64ToG a), wertExakt f64 (u64ToG b) with
        | some u, some v => rundeExakt f64 (exaktAdd u v)
        | _, _ => nanQ f64 := by
  rw [softAdd_model, floatAddSpecial_model]

/-- Joint witness: finite rounding (`1.0 + 2.0 = 3.0`), signed zeros
    (`+0 + +0 = +0`, `-0 + -0 = -0`), subnormal exactness (`1 + 1 = 2`),
    the infinity conflict (`inf + -inf = NaN`), NaN priority with payload
    and sign, and infinity absorption. -/
theorem softAdd_zeuge :
    softAdd 4607182418800017408 4611686018427387904 = 4613937818241073152 ∧
    softAdd 0 0 = 0 ∧
    softAdd 9223372036854775808 9223372036854775808 = 9223372036854775808 ∧
    softAdd 1 1 = 2 ∧
    softAdd 9218868437227405312 18442240474082181120 = 9218868437227405313 ∧
    softAdd 18442240474082181127 4607182418800017408 = 18442240474082181127 ∧
    softAdd 9218868437227405312 4607182418800017408 = 9218868437227405312 := by
  decide +kernel

#print axioms softAdd_model
#print axioms softAdd_special
#print axioms softAdd_zeuge

end Gabbro.Stage0.Senke
