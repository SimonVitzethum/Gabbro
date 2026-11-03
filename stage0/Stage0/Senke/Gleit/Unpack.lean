/- Bit-field unpacking for software binary64 addition (`Block.float`, `op = .add`).

    `softSign`/`softBexp`/`softFrac` read the three IEEE-754 binary64 fields of a
    64-bit word as pure Lean functions; `softUnpack_model` proves they are exactly
    the kernel decode `u64ToG` (hence `ausBits f64`), so the later IR routine
    replays the kernel decomposition on the same fields. `unpackSignWord`,
    `unpackBexpWord` and `unpackFracWord` are the same fields as runner words, and
    `unpackSignL`, `unpackBexpL`, `unpackFracL` compute them as Stage-0 IR from
    existing integer opcodes only (`shr` 12 and `and` 8 via `wordL`/`wordK`, the
    52-bit mask via `konstWL`): no float instruction, no runner change. Each
    fragment carries its `WordCode` correctness lemma, proved by `WordCode`
    composition exactly as `floatMagnitudeL_ok`/`floatExponentAuxL_ok`. -/
module
public import Grammatik.Bausteine.Gleitkomma.GleitkommaBits
public import Stage0.Senke.Ausdruck.Aggregat.Hilfena
public import Stage0.Senke.Ausdruck.Gleit.Komposition
public import Stage0.Senke.Gleit.Add
@[expose] public section


namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik
open Gleitkomma
open Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D}

/-- Sign bit of a 64-bit word (bit 63). -/
def softSign (a : UInt64) : Bool := (a.toNat / 2 ^ 63) % 2 == 1

/-- Biased exponent field: 11 bits above the 52 fraction bits. -/
def softBexp (a : UInt64) : Nat := (a.toNat / 2 ^ 52) % 2 ^ 11

/-- Stored fraction field: the low 52 bits. -/
def softFrac (a : UInt64) : Nat := a.toNat % 2 ^ 52

/-- The three pure field readers are exactly the kernel decode: no input is
    excluded and no field is weakened. -/
theorem softUnpack_model (a : UInt64) :
    u64ToG a = ⟨softSign a, softBexp a, softFrac a⟩ := by
  have e11 : Format.ebits f64 = 11 := by decide
  have f52 : Format.fracBits f64 = 52 := by decide
  unfold u64ToG ausBits softSign softBexp softFrac
  rw [e11, f52]

/-- Sign bit into the low bit: logical shift right by 63. The shift amount is
    written as the runner sees it (`toNat % 64` of the immediate word). -/
def unpackSignWord (w : Runner.W) : Runner.W :=
  w >>> ((BitVec.ofInt 64 63).toNat % 64)

/-- Biased exponent field: shift right by 52, then mask 11 bits. -/
def unpackBexpWord (w : Runner.W) : Runner.W :=
  (w >>> ((BitVec.ofInt 64 52).toNat % 64)) &&& (BitVec.ofInt 64 2047)

/-- Fraction field: mask the low 52 bits (`2^52 - 1`, built from immediates). -/
def unpackFracWord (w : Runner.W) : Runner.W :=
  w &&& (BitVec.ofNat 64 4503599627370495)

/-- `sign = word >> 63` as IR (opcode 12). -/
def unpackSignL (d : Nat) (a : Nat → Option (List II × Nat)) :
    Option (List II × Nat) :=
  wordK 12 d (a d) 63

/-- `bexp = (word >> 52) & 2047` as IR (opcodes 12 then 8). -/
def unpackBexpL (d : Nat) (a : Nat → Option (List II × Nat)) :
    Option (List II × Nat) :=
  wordK 8 d (wordK 12 d (a d) 52) 2047

/-- `frac = word & (2^52 - 1)` as IR (opcode 8 against a `konstWL` mask, since
    the mask does not fit a signed 32-bit immediate). -/
def unpackFracL (d : Nat) (a : Nat → Option (List II × Nat)) :
    Option (List II × Nat) :=
  wordL 8 d (a d) (fun j => some (konstWL 4 4503599627370495 j))

/-- Compositional IR simulation for the sign fragment. -/
theorem unpackSignL_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {a : Nat → Option (List II × Nat)} {av : Runner.W}
    (ha : WordCode (L := L) ρ W a av) :
    WordCode (L := L) ρ W (fun d => unpackSignL d a) (unpackSignWord av) := by
  have hc : lit32 (63 : Int) = true := by decide
  have result : WordCode (L := L) ρ W _ _ := WordCode.bin ha (WordCode.const 63 hc)
    (g := fun x y => some (x >>> (y.toNat % 64))) rfl rfl (by decide : 12 < 256)
  intro fp K d c top h hK m pc hp
  simpa only [unpackSignWord, BitVec.ofInt_ofNat, BitVec.ofNat_eq_ofNat] using
    result (fp := fp) (K := K) (d := d) (c := c) (top := top) h hK m pc hp

/-- Compositional IR simulation for the biased-exponent fragment. -/
theorem unpackBexpL_ok {reserved : Nat} {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {a : Nat → Option (List II × Nat)} {av : Runner.W}
    (ha : WordCode (L := L) (reserved := reserved) ρ W a av) :
    WordCode (L := L) (reserved := reserved) ρ W (fun d => unpackBexpL d a) (unpackBexpWord av) := by
  have hc52 : lit32 (52 : Int) = true := by decide
  have hc2047 : lit32 (2047 : Int) = true := by decide
  have inner : WordCode (L := L) (reserved := reserved) ρ W _ _ := WordCode.bin ha (WordCode.const 52 hc52)
    (g := fun x y => some (x >>> (y.toNat % 64))) rfl rfl (by decide : 12 < 256)
  have result : WordCode (L := L) (reserved := reserved) ρ W _ _ := WordCode.bin inner (WordCode.const 2047 hc2047)
    (g := fun x y => some (x &&& y)) rfl rfl (by decide : 8 < 256)
  intro fp K d c top h hK m pc hp
  simpa only [unpackBexpWord, BitVec.ofInt_ofNat, BitVec.ofNat_eq_ofNat] using
    result (fp := fp) (K := K) (d := d) (c := c) (top := top) h hK m pc hp

/-- Compositional IR simulation for the fraction fragment. -/
theorem unpackFracL_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {a : Nat → Option (List II × Nat)} {av : Runner.W}
    (ha : WordCode (L := L) ρ W a av) :
    WordCode (L := L) ρ W (fun d => unpackFracL d a) (unpackFracWord av) := by
  have hmask : 4503599627370495 < 2 ^ 64 := by decide
  have result : WordCode (L := L) ρ W _ _ :=
    WordCode.bin ha (WordCode.konst 4503599627370495 hmask)
      (g := fun x y => some (x &&& y)) rfl rfl (by decide : 8 < 256)
  intro fp K d c top h hK m pc hp
  simpa only [unpackFracWord, BitVec.ofInt_ofNat, BitVec.ofNat_eq_ofNat] using
    result (fp := fp) (K := K) (d := d) (c := c) (top := top) h hK m pc hp

/-- Joint fixtures: `1.0` unpacks to sign false, bexp 1023, frac 0; `-0.0` has
    its sign bit set; the all-ones fraction mask survives the `and`. -/
theorem unpack_zeuge :
    softSign 4607182418800017408 = false ∧
    softBexp 4607182418800017408 = 1023 ∧
    softFrac 4607182418800017408 = 0 ∧
    softSign 9223372036854775808 = true ∧
    softBexp 0 = 0 ∧
    softFrac 1 = 1 ∧
    unpackSignWord (BitVec.ofNat 64 9223372036854775808) = 1 ∧
    unpackBexpWord (BitVec.ofNat 64 4607182418800017408) = BitVec.ofNat 64 1023 ∧
    unpackFracWord (BitVec.ofNat 64 4503599627370495) =
      BitVec.ofNat 64 4503599627370495 := by
  decide +kernel

#print axioms softUnpack_model
#print axioms unpackSignL_ok
#print axioms unpackBexpL_ok
#print axioms unpackFracL_ok
#print axioms unpack_zeuge

end Gabbro.Stage0.Senke
