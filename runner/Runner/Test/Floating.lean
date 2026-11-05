module
public import Runner.Prog.IRAsm
@[expose] public section

namespace Runner.Test.Floating
open Runner Runner.Prog

/-! Whole-IR CPU regressions, off the proof path. Only nativeFPBits supplies
    expected results. Each generated image executes the installed FP opcode,
    checks its result with integer IR and calls exit_group with zero or one.
    There is no executable IR evaluator in this generator. -/

def operations : List NativeFPOp :=
  [.add .f32, .add .f64, .sub .f32, .sub .f64,
   .mul .f32, .mul .f64, .div .f32, .div .f64,
   .neg .f32, .neg .f64, .eq .f32, .eq .f64,
   .lt .f32, .lt .f64, .le .f32, .le .f64,
   .isFinite .f32, .isFinite .f64, .fromInt64 .f32, .fromInt64 .f64,
   .fromUInt64 .f32, .fromUInt64 .f64, .toInt64 .f32, .toInt64 .f64,
   .toUInt64 .f32, .toUInt64 .f64, .widen32, .narrow32,
   .compare .f32, .compare .f64, .truncateInt64 .f32, .truncateInt64 .f64]

/-- Zeroes, both subnormal extremes, ordinary values, infinities and distinct
    quiet/signaling NaNs. All entries are raw input words, not source literals. -/
def basicWords (format : FPFormat) : List W :=
  (match format with
    | .f32 => [0, 0x80000000, 1, 0x80000001, 0x007FFFFF, 0x807FFFFF,
        0x00800000, 0x3F800000, 0x3FC00000, 0xBF800000, 0x7F7FFFFF,
        0xFF7FFFFF, 0x7F800000, 0xFF800000, 0x7FC01234, 0xFFC00123, 0x7F800001]
    | .f64 => [0, 0x8000000000000000, 1, 0x8000000000000001,
        0x000FFFFFFFFFFFFF, 0x800FFFFFFFFFFFFF, 0x0010000000000000,
        0x3FF0000000000000, 0x3FF8000000000000, 0xBFF0000000000000,
        0x7FEFFFFFFFFFFFFF, 0xFFEFFFFFFFFFFFFF, 0x7FF0000000000000,
        0xFFF0000000000000, 0x7FF8000000001234, 0xFFF8000000000123,
        0x7FF0000000000001] : List Nat).map (BitVec.ofNat 64)

/-- Nonzero upper halves exercise binary32's actual low-lane normalization. -/
def upperWords : List W :=
  [0xA5A5A5A500000000, 0x123456783F800000, 0xFFFFFFFF7FC01234, 0xFFFF000080000000]

def castWords (format : FPFormat) : List W :=
  let limits : List Nat := match format with
    | .f32 => [0x5F000000, 0xDF000000, 0x5F800000]
    | .f64 => [0x43E0000000000000, 0xC3E0000000000000, 0x43F0000000000000]
  let fractions : List Nat := match format with
    | .f32 => [0x3F000000, 0xBF000000, 0xBFC00000]
    | .f64 => [0x3FE0000000000000, 0xBFE0000000000000, 0xBFF8000000000000]
  ((limits.flatMap fun word => [word - 1, word, word + 1]) ++ fractions).map (BitVec.ofNat 64)

def floatingWords (format : FPFormat) : List W :=
  basicWords format ++ castWords format ++ (match format with | .f32 => upperWords | .f64 => [])

/-- Signed/unsigned endpoints and rounding ties at the binary32/binary64
    integer precision boundaries, including odd high-half sticky inputs. -/
def integerWords : List W :=
  ([0, 1, 2, 3, 2 ^ 24 - 1, 2 ^ 24, 2 ^ 24 + 1, 2 ^ 24 + 3,
    2 ^ 53 - 1, 2 ^ 53, 2 ^ 53 + 1, 2 ^ 53 + 3,
    2 ^ 63 - 1, 2 ^ 63, 2 ^ 63 + 1, 2 ^ 64 - 1, 2 ^ 64 - 2,
    2 ^ 64 - (2 ^ 24 + 1), 2 ^ 64 - (2 ^ 53 + 1), 0x8000000000000801] : List Nat).map
      (BitVec.ofNat 64)

/-- Neighbors of binary32 rounding, underflow and overflow boundaries,
    expressed as binary64 input words for the real narrowing opcode. -/
def narrowWords : List W :=
  (([0x3690000000000000, 0x36A0000000000000, 0x3810000000000000,
    0x47EFFFFFE0000000, 0x47F0000000000000, 0x3FF0000010000000] : List Nat).flatMap
      (fun word => [word - 1, word, word + 1])).map (BitVec.ofNat 64)

def binaryInputs (format : FPFormat) : List (W × W) :=
  let one : W := match format with | .f32 => 0x3F800000 | .f64 => 0x3FF0000000000000
  let negativeOne : W := match format with | .f32 => 0xBF800000 | .f64 => 0xBFF0000000000000
  let halfMore : W := match format with | .f32 => 0x3FC00000 | .f64 => 0x3FF8000000000000
  let sign : W := match format with | .f32 => 0x80000000 | .f64 => 0x8000000000000000
  let infinity : W := match format with | .f32 => 0x7F800000 | .f64 => 0x7FF0000000000000
  let largest := infinity - 1
  let first := basicWords format ++ (match format with | .f32 => upperWords | .f64 => [])
  first.map (fun word => (word, one)) ++
    [(0, 0), (sign, sign), (0, sign), (one, 0), (one, sign),
     (infinity, infinity), (infinity, infinity ||| sign), (0, infinity),
     (largest, largest), (1, halfMore), (one, halfMore), (negativeOne, halfMore)]

def inputs : NativeFPOp → List (W × W)
  | .add format | .sub format | .mul format | .div format
  | .eq format | .lt format | .le format | .compare format => binaryInputs format
  | .fromInt64 _ | .fromUInt64 _ => integerWords.map fun word => (word, 0xDEADBEEFCAFEBABE)
  | .neg format | .isFinite format | .toInt64 format | .toUInt64 format
  | .truncateInt64 format => (floatingWords format).map fun word => (word, 0xDEADBEEFCAFEBABE)
  | .widen32 => (floatingWords .f32).map fun word => (word, 0xDEADBEEFCAFEBABE)
  | .narrow32 => (floatingWords .f64 ++ narrowWords).map fun word => (word, 0xDEADBEEFCAFEBABE)

structure Case where
  kind : NativeFPOp
  a : W
  b : W

def fixtures : List Case := operations.flatMap fun kind =>
  (inputs kind).map fun (a, b) => { kind := kind, a := a, b := b }

def Case.expected (test : Case) : W := nativeFPBits test.kind test.a test.b

/-- Only decoded floating outputs may vary in NaN payload. NEG and every
    integer/Boolean/flags result always use the complete exact word. -/
def decodedFormat : NativeFPOp → Option FPFormat
  | .add format | .sub format | .mul format | .div format
  | .fromInt64 format | .fromUInt64 format => some format
  | .widen32 => some .f64
  | .narrow32 => some .f32
  | _ => none

def Case.nanFormat (test : Case) : Option FPFormat :=
  match decodedFormat test.kind with
  | some .f32 => if (readFloat32 test.expected).hwIsNaN then some .f32 else none
  | some .f64 => if (readFloat test.expected).hwIsNaN then some .f64 else none
  | none => none

def Case.comparison (test : Case) : String :=
  match test.nanFormat with | none => "word" | some .f32 => "nan32" | some .f64 => "nan64"

def Case.fileName (test : Case) (index : Nat) : String := s!"fp-{test.kind.code}-{index}.img"

def wordHex (word : W) : String := "0x" ++ String.ofList (Nat.toDigits 16 word.toNat)

/-- Header: file, opcode, case, exit, input_a, input_b, expected, comparison.
    Paths are relative to the generator directory; every expected exit is zero. -/
def manifestHeader : String := "file\topcode\tcase\texit\tinput_a\tinput_b\texpected\tcomparison\n"

def Case.manifestRow (test : Case) (index : Nat) : String :=
  s!"{test.fileName index}\t{test.kind.code}\t{index}\t0\t{wordHex test.a}\t{wordHex test.b}\t{wordHex test.expected}\t{test.comparison}\n"

def smallConst (slot value : Int) : IItem := .op 1 slot value 0

/-- The operands, expected word and masks are loaded from eight-byte data
    entries. CONST is used only for small offsets and syscall arguments. -/
def loadWord (slot : Int) (index : Nat) : List IItem :=
  [.adr 20 1, smallConst 21 (Int.ofNat (8 * index)), .op 3 20 20 21, .op 15 slot 20 0]

def Case.image (test : Case) : List B :=
  let nan := test.nanFormat
  let exponent : W := match nan with | some .f32 => 0x7F800000 | _ => 0x7FF0000000000000
  let fraction : W := match nan with | some .f32 => 0x007FFFFF | _ => 0x000FFFFFFFFFFFFF
  let upper : W := match nan with | some .f32 => 0xFFFFFFFF00000000 | _ => 0
  let words := [test.a, test.b, test.expected, exponent, fraction, upper]
  let comparison : List IItem := match nan with
    | none => [.op 14 6 2 3, .brzL 6 3]
    | some _ =>
      [ .op 8 7 2 4, .op 14 6 7 4, .brzL 6 3,
        .op 8 7 2 5, .brzL 7 3,
        .op 8 7 2 8, smallConst 9 0, .op 14 6 7 9, .brzL 6 3 ]
  let items := loadWord 0 0 ++ loadWord 1 1 ++ loadWord 3 2 ++
    loadWord 4 3 ++ loadWord 5 4 ++ loadWord 8 5 ++
    [.op test.kind.code 2 0 1] ++ comparison ++
    [ smallConst 10 231, smallConst 11 0, .op 23 17 10 0,
      .lab 3, smallConst 10 231, smallConst 11 1, .op 23 17 10 0, .op 0 0 0 0,
      .lab 1, .zeros (8 * words.length), .lab 2, .zeros 256 ]
  let original := irImage items 2
  let offset := find (ilabels items 16) 1
  original.take offset ++ words.flatMap (fun word => leN 8 word.toNat) ++
    original.drop (offset + 8 * words.length)

end Runner.Test.Floating
