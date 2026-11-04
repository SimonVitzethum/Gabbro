/- Special-case dispatch for software binary64 addition (`Block.float`, `op = .add`).

    `softSpecial` replays the shared kernel dispatcher `floatAddSpecial` on words:
    NaN priority with payload and sign, the infinity conflict to `nanQ`,
    infinity absorption and the signed-zero rule; `none` is the finite path.
    `softSpecial_model` proves the dispatched triple IS the kernel `add` on those
    inputs by reusing `floatAddSpecial_model`, and `softSpecial_add` connects the
    dispatch to the `softAdd` reference without any well-formedness detour.
    `softIsNan`/`softIsInf`/`softIsZero` read the three dispatched classes off the
    unpacked fields, with `softClass_model` proving they decide the kernel
    `klasse`. `isNanL`/`isInfL`/`isZeroL` compute the same tests as Stage-0 IR
    from existing integer opcodes only (`eq` 14, `and` 8, `sub` 4 via
    `wordL`/`wordK`), each with its `WordCode` correctness lemma proved by
    `WordCode` composition as `floatMagnitudeL_ok`. The nested-`wennL`
    tag dispatch over these tests lands once `pack` provides result words. -/
module
public import Grammatik.Bausteine.Gleitkomma.GleitkommaBits
public import Stage0.Senke.Ausdruck.Aggregat.Hilfena
public import Stage0.Senke.Ausdruck.Gleit.Komposition
public import Stage0.Senke.Ausdruck.Arithmetik.AddSub
public import Stage0.Senke.Gleit.Add
public import Stage0.Senke.Gleit.Unpack
@[expose] public section


namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik
open Gleitkomma
open Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D}

/-- Special-case dispatch on words, replaying the shared kernel dispatcher.
    `none` hands the finite path to align/add/round. -/
def softSpecial (a b : UInt64) : Option (GBits f64) :=
  floatAddSpecial f64 (u64ToG a) (u64ToG b)

omit [Kern] in
/-- On special inputs the dispatched triple IS the kernel sum. Reuses
    `floatAddSpecial_model`; the finite path is not decided here. -/
theorem softSpecial_model (a b : UInt64) (r : GBits f64)
    (h : softSpecial a b = some r) :
    r = add f64 (u64ToG a) (u64ToG b) := by
  unfold softSpecial at h
  rw [floatAddSpecial_model f64 (u64ToG a) (u64ToG b), h]

/-- The dispatch agrees with the `softAdd` reference on the decoded result,
    with no well-formedness detour: both replay the same kernel `add`. -/
theorem softSpecial_add (a b : UInt64) (r : GBits f64)
    (h : softSpecial a b = some r) :
    u64ToG (softAdd a b) = r := by
  rw [softAdd_model, (softSpecial_model a b r h).symm]

/-- NaN word test: maximal exponent, nonzero fraction. -/
def softIsNan (a : UInt64) : Bool :=
  if softBexp a = 2047 then (if softFrac a = 0 then false else true) else false

/-- Infinity word test: maximal exponent, zero fraction. -/
def softIsInf (a : UInt64) : Bool :=
  if softBexp a = 2047 then (if softFrac a = 0 then true else false) else false

/-- Zero word test (either sign): zero exponent, zero fraction. -/
def softIsZero (a : UInt64) : Bool :=
  if softBexp a = 0 then (if softFrac a = 0 then true else false) else false

/-- The unpacked fields decide the kernel class: maximal exponent splits NaN
    from infinity, zero fields mean zero, and everything else falls through to
    subnormal or normal. -/
theorem softClass_model (a : UInt64) :
    klasse f64 (u64ToG a) =
      if softBexp a = 2047 then
        if softFrac a = 0 then Klasse.unendlich else Klasse.nan
      else if softBexp a = 0 then
        if softFrac a = 0 then Klasse.null else Klasse.subnormal
      else Klasse.normal := by
  have hbmax : f64.bexpMax = 2047 := rfl
  rw [softUnpack_model a]
  show (if softBexp a = f64.bexpMax then
      (if softFrac a = 0 then Klasse.unendlich else Klasse.nan)
    else if softBexp a = 0 then
      (if softFrac a = 0 then Klasse.null else Klasse.subnormal)
    else Klasse.normal) = _
  rw [hbmax]

/-- The NaN word test decides the kernel NaN class. -/
theorem softIsNan_model (a : UInt64) :
    softIsNan a = true ↔ klasse f64 (u64ToG a) = .nan := by
  rw [softClass_model a]
  unfold softIsNan
  by_cases hb : softBexp a = 2047 <;> by_cases hz : softBexp a = 0 <;>
    by_cases hf : softFrac a = 0 <;> simp_all

/-- The infinity word test decides the kernel infinity class. -/
theorem softIsInf_model (a : UInt64) :
    softIsInf a = true ↔ klasse f64 (u64ToG a) = .unendlich := by
  rw [softClass_model a]
  unfold softIsInf
  by_cases hb : softBexp a = 2047 <;> by_cases hz : softBexp a = 0 <;>
    by_cases hf : softFrac a = 0 <;> simp_all

/-- The zero word test decides the kernel zero class. -/
theorem softIsZero_model (a : UInt64) :
    softIsZero a = true ↔ klasse f64 (u64ToG a) = .null := by
  rw [softClass_model a]
  unfold softIsZero
  by_cases hb : softBexp a = 0 <;> by_cases hm : softBexp a = 2047 <;>
    by_cases hf : softFrac a = 0 <;> simp_all

/-- The word `1` at any base, for `1 - test` negations. -/
def constOneL : Nat → Option (List II × Nat) := fun j => some ([ci 1 j 1 0], j + 1)

theorem constOneL_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop} :
    WordCode (L := L) ρ W constOneL (BitVec.ofInt 64 1) :=
  WordCode.const 1 (by decide)

/-- `bexp == 2047` as IR (opcode 14 against an immediate). -/
def isExpMaxL (d : Nat) (e : Nat → Option (List II × Nat)) :
    Option (List II × Nat) :=
  wordK 14 d (e d) 2047

/-- `bexp == 0` as IR (opcode 14 against an immediate). -/
def isExpZeroL (d : Nat) (e : Nat → Option (List II × Nat)) :
    Option (List II × Nat) :=
  wordK 14 d (e d) 0

/-- `frac == 0` as IR (opcode 14 against an immediate). -/
def isFracZeroL (d : Nat) (f : Nat → Option (List II × Nat)) :
    Option (List II × Nat) :=
  wordK 14 d (f d) 0

/-- `frac != 0` as a word: `1 - (frac == 0)` (opcodes 4 and 14). The constant
    `1` is emitted first at the result slot, the equality test runs above it,
    so no scratch is clobbered. -/
def isFracNonzeroWord (f : Runner.W) : Runner.W :=
  BitVec.ofInt 64 1 - Runner.IR.bool (f == BitVec.ofInt 64 0)

def isFracNonzeroL (d : Nat) (f : Nat → Option (List II × Nat)) :
    Option (List II × Nat) :=
  wordL 4 d (constOneL d) (wordK 14 (d + 1) (f (d + 1)) 0)

/-- NaN test word: `(bexp == 2047) & (frac != 0)`. -/
def isNanWord (e f : Runner.W) : Runner.W :=
  Runner.IR.bool (e == BitVec.ofInt 64 2047) &&& isFracNonzeroWord f

def isNanL (d : Nat) (e f : Nat → Option (List II × Nat)) :
    Option (List II × Nat) :=
  wordL 8 d (isExpMaxL d e) (isFracNonzeroL (d + 1) f)

/-- Infinity test word: `(bexp == 2047) & (frac == 0)`. -/
def isInfWord (e f : Runner.W) : Runner.W :=
  Runner.IR.bool (e == BitVec.ofInt 64 2047) &&& Runner.IR.bool (f == BitVec.ofInt 64 0)

def isInfL (d : Nat) (e f : Nat → Option (List II × Nat)) :
    Option (List II × Nat) :=
  wordL 8 d (isExpMaxL d e) (isFracZeroL (d + 1) f)

/-- Zero test word: `(bexp == 0) & (frac == 0)`. -/
def isZeroWord (e f : Runner.W) : Runner.W :=
  Runner.IR.bool (e == BitVec.ofInt 64 0) &&& Runner.IR.bool (f == BitVec.ofInt 64 0)

def isZeroL (d : Nat) (e f : Nat → Option (List II × Nat)) :
    Option (List II × Nat) :=
  wordL 8 d (isExpZeroL d e) (isFracZeroL (d + 1) f)

/-- Compositional IR simulation for `bexp == 2047`. -/
theorem isExpMaxL_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {e : Nat → Option (List II × Nat)} {ev : Runner.W}
    (he : WordCode (L := L) ρ W e ev) :
    WordCode (L := L) ρ W (fun j => isExpMaxL j e)
      (Runner.IR.bool (ev == BitVec.ofInt 64 2047)) := by
  have hc : lit32 (2047 : Int) = true := by decide
  have result : WordCode (L := L) ρ W _ _ := WordCode.bin he (WordCode.const 2047 hc)
    (g := fun x y => some (Runner.IR.bool (x == y))) rfl rfl (by decide : 14 < 256)
  intro fp K d c top h hK m pc hp
  simpa only [BitVec.ofInt_ofNat, BitVec.ofNat_eq_ofNat] using
    result (fp := fp) (K := K) (d := d) (c := c) (top := top) h hK m pc hp

/-- Compositional IR simulation for `bexp == 0`. -/
theorem isExpZeroL_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {e : Nat → Option (List II × Nat)} {ev : Runner.W}
    (he : WordCode (L := L) ρ W e ev) :
    WordCode (L := L) ρ W (fun j => isExpZeroL j e)
      (Runner.IR.bool (ev == BitVec.ofInt 64 0)) := by
  have hc : lit32 (0 : Int) = true := by decide
  have result : WordCode (L := L) ρ W _ _ := WordCode.bin he (WordCode.const 0 hc)
    (g := fun x y => some (Runner.IR.bool (x == y))) rfl rfl (by decide : 14 < 256)
  intro fp K d c top h hK m pc hp
  simpa only [BitVec.ofInt_ofNat, BitVec.ofNat_eq_ofNat] using
    result (fp := fp) (K := K) (d := d) (c := c) (top := top) h hK m pc hp

/-- Compositional IR simulation for `frac == 0`. -/
theorem isFracZeroL_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {f : Nat → Option (List II × Nat)} {fv : Runner.W}
    (hf : WordCode (L := L) ρ W f fv) :
    WordCode (L := L) ρ W (fun j => isFracZeroL j f)
      (Runner.IR.bool (fv == BitVec.ofInt 64 0)) := by
  have hc : lit32 (0 : Int) = true := by decide
  have result : WordCode (L := L) ρ W _ _ := WordCode.bin hf (WordCode.const 0 hc)
    (g := fun x y => some (Runner.IR.bool (x == y))) rfl rfl (by decide : 14 < 256)
  intro fp K d c top h hK m pc hp
  simpa only [BitVec.ofInt_ofNat, BitVec.ofNat_eq_ofNat] using
    result (fp := fp) (K := K) (d := d) (c := c) (top := top) h hK m pc hp

/-- Compositional IR simulation for `frac != 0`. -/
theorem isFracNonzeroL_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {f : Nat → Option (List II × Nat)} {fv : Runner.W}
    (hf : WordCode (L := L) ρ W f fv) :
    WordCode (L := L) ρ W (fun j => isFracNonzeroL j f) (isFracNonzeroWord fv) := by
  have hc : lit32 (0 : Int) = true := by decide
  have eqz : WordCode (L := L) ρ W _ _ := WordCode.bin hf (WordCode.const 0 hc)
    (g := fun x y => some (Runner.IR.bool (x == y))) rfl rfl (by decide : 14 < 256)
  have result : WordCode (L := L) ρ W _ _ := WordCode.bin constOneL_ok eqz
    (g := fun x y => some (x - y)) rfl rfl (by decide : 4 < 256)
  intro fp K d c top h hK m pc hp
  simpa only [isFracNonzeroWord, BitVec.ofInt_ofNat, BitVec.ofNat_eq_ofNat] using
    result (fp := fp) (K := K) (d := d) (c := c) (top := top) h hK m pc hp

/-- Compositional IR simulation for the NaN test. -/
theorem isNanL_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {e f : Nat → Option (List II × Nat)} {ev fv : Runner.W}
    (he : WordCode (L := L) ρ W e ev) (hf : WordCode (L := L) ρ W f fv) :
    WordCode (L := L) ρ W (fun d => isNanL d e f) (isNanWord ev fv) := by
  have result : WordCode (L := L) ρ W _ _ :=
    WordCode.bin (isExpMaxL_ok he) (isFracNonzeroL_ok hf)
      (g := fun x y => some (x &&& y)) rfl rfl (by decide : 8 < 256)
  intro fp K d c top h hK m pc hp
  simpa only [isNanL, isExpMaxL, isFracNonzeroL, isNanWord, isFracNonzeroWord,
    BitVec.ofInt_ofNat, BitVec.ofNat_eq_ofNat] using
    result (fp := fp) (K := K) (d := d) (c := c) (top := top) h hK m pc hp

/-- Compositional IR simulation for the infinity test. -/
theorem isInfL_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {e f : Nat → Option (List II × Nat)} {ev fv : Runner.W}
    (he : WordCode (L := L) ρ W e ev) (hf : WordCode (L := L) ρ W f fv) :
    WordCode (L := L) ρ W (fun d => isInfL d e f) (isInfWord ev fv) := by
  have result : WordCode (L := L) ρ W _ _ :=
    WordCode.bin (isExpMaxL_ok he) (isFracZeroL_ok hf)
      (g := fun x y => some (x &&& y)) rfl rfl (by decide : 8 < 256)
  intro fp K d c top h hK m pc hp
  simpa only [isInfL, isExpMaxL, isFracZeroL, isInfWord,
    BitVec.ofInt_ofNat, BitVec.ofNat_eq_ofNat] using
    result (fp := fp) (K := K) (d := d) (c := c) (top := top) h hK m pc hp

/-- Compositional IR simulation for the zero test. -/
theorem isZeroL_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {e f : Nat → Option (List II × Nat)} {ev fv : Runner.W}
    (he : WordCode (L := L) ρ W e ev) (hf : WordCode (L := L) ρ W f fv) :
    WordCode (L := L) ρ W (fun d => isZeroL d e f) (isZeroWord ev fv) := by
  have result : WordCode (L := L) ρ W _ _ :=
    WordCode.bin (isExpZeroL_ok he) (isFracZeroL_ok hf)
      (g := fun x y => some (x &&& y)) rfl rfl (by decide : 8 < 256)
  intro fp K d c top h hK m pc hp
  simpa only [isZeroL, isExpZeroL, isFracZeroL, isZeroWord,
    BitVec.ofInt_ofNat, BitVec.ofNat_eq_ofNat] using
    result (fp := fp) (K := K) (d := d) (c := c) (top := top) h hK m pc hp

/-- Joint fixtures: infinity absorption and the infinity conflict dispatch to
    the kept payload and `nanQ`; `-0 + -0` dispatches to `-0`; finite inputs
    fall through; the word tests decide their classes on closed words. -/
theorem special_zeuge :
    softSpecial 9218868437227405312 4607182418800017408 = some ⟨false, 2047, 0⟩ ∧
    softSpecial 9218868437227405312 18442240474082181120 = some ⟨false, 2047, 1⟩ ∧
    softSpecial 9223372036854775808 9223372036854775808 = some ⟨true, 0, 0⟩ ∧
    softSpecial 4607182418800017408 4611686018427387904 = none ∧
    softIsNan 18442240474082181127 = true ∧
    softIsInf 9218868437227405312 = true ∧
    softIsZero 9223372036854775808 = true ∧
    softIsNan 4607182418800017408 = false ∧
    isNanWord (BitVec.ofNat 64 2047) (BitVec.ofNat 64 9) = 1 ∧
    isInfWord (BitVec.ofNat 64 2047) (BitVec.ofNat 64 0) = 1 ∧
    isZeroWord (BitVec.ofNat 64 0) (BitVec.ofNat 64 0) = 1 ∧
    isNanWord (BitVec.ofNat 64 1023) (BitVec.ofNat 64 9) = 0 := by
  decide +kernel

#print axioms softSpecial_model
#print axioms softSpecial_add
#print axioms softClass_model
#print axioms softIsNan_model
#print axioms softIsInf_model
#print axioms softIsZero_model
#print axioms isNanL_ok
#print axioms isInfL_ok
#print axioms isZeroL_ok
#print axioms special_zeuge

end Gabbro.Stage0.Senke
