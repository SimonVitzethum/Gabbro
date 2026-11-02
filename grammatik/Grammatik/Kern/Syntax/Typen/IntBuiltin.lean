/- C13: the closed family of typed integer builtins (lane C13, `IR-COMPILATION-LANES.md`).

   Every operation names its storage width `W = w + 1` in its constructor, never inferred from an
   interval. The index lists are the operand types, the index type is the result type; the
   semantics is `Zahl.addW/subW/mulW/shlW/addS` (`Kern/Semantik/Ueberlauf`) and
   `Zahl.clz/ctz/log2_floor/popcount/rotl/rotr/bswap16/32/64` (`Kern/Syntax/Bits/T2`), applied in
   `Kern/Semantik/Semantik/T1`. There is no arbitrary function-valued primitive. -/

module

public import Grammatik.Kern.Syntax.Typen.Teil2

@[expose] public section

namespace Gabbro.Grammatik

/-- A closed typed integer builtin from operand types `ts` to the result type `τ`. -/
inductive IntBuiltin : List Ty → Ty → Type where
  /-- `a +% b` on the exact range `0 .. 2^W - 1`. -/
  | addW (w : Nat) : IntBuiltin [.int 0 ((2 : Int) ^ (w + 1) - 1), .int 0 ((2 : Int) ^ (w + 1) - 1)]
      (.int 0 ((2 : Int) ^ (w + 1) - 1))
  /-- `a -% b` on the exact range. -/
  | subW (w : Nat) : IntBuiltin [.int 0 ((2 : Int) ^ (w + 1) - 1), .int 0 ((2 : Int) ^ (w + 1) - 1)]
      (.int 0 ((2 : Int) ^ (w + 1) - 1))
  /-- `a *% b` on the exact range. -/
  | mulW (w : Nat) : IntBuiltin [.int 0 ((2 : Int) ^ (w + 1) - 1), .int 0 ((2 : Int) ^ (w + 1) - 1)]
      (.int 0 ((2 : Int) ^ (w + 1) - 1))
  /-- `a <<% s`: the amount `s` is typed `0 .. w`. -/
  | shlW (w : Nat) : IntBuiltin [.int 0 ((2 : Int) ^ (w + 1) - 1), .int 0 (w : Int)]
      (.int 0 ((2 : Int) ^ (w + 1) - 1))
  /-- `a +| b`: saturating, on every range `lo .. hi`. -/
  | addS (lo hi : Int) : IntBuiltin [.int lo hi, .int lo hi] (.int lo hi)
  /-- Leading zeros: the operand excludes zero. -/
  | clz (w : Nat) : IntBuiltin [.int 1 ((2 : Int) ^ (w + 1) - 1)] (.int 0 (w : Int))
  /-- Trailing zeros: the operand excludes zero. -/
  | ctz (w : Nat) : IntBuiltin [.int 1 ((2 : Int) ^ (w + 1) - 1)] (.int 0 (w : Int))
  /-- Floor of the binary logarithm: the operand excludes zero. -/
  | log2Floor (w : Nat) : IntBuiltin [.int 1 ((2 : Int) ^ (w + 1) - 1)] (.int 0 (w : Int))
  /-- Population count over the full unsigned range; the result reaches `W`. -/
  | popcount (w : Nat) : IntBuiltin [.int 0 ((2 : Int) ^ (w + 1) - 1)] (.int 0 ((w : Int) + 1))
  /-- Rotate left by an amount `0 .. w`. -/
  | rotl (w : Nat) : IntBuiltin [.int 0 ((2 : Int) ^ (w + 1) - 1), .int 0 (w : Int)]
      (.int 0 ((2 : Int) ^ (w + 1) - 1))
  /-- Rotate right by an amount `0 .. w`. -/
  | rotr (w : Nat) : IntBuiltin [.int 0 ((2 : Int) ^ (w + 1) - 1), .int 0 (w : Int)]
      (.int 0 ((2 : Int) ^ (w + 1) - 1))
  /-- Byte reversal of a `u16`. -/
  | bswap16 : IntBuiltin [.int 0 ((2 : Int) ^ 16 - 1)] (.int 0 ((2 : Int) ^ 16 - 1))
  /-- Byte reversal of a `u32`. -/
  | bswap32 : IntBuiltin [.int 0 ((2 : Int) ^ 32 - 1)] (.int 0 ((2 : Int) ^ 32 - 1))
  /-- Byte reversal of a `u64`. -/
  | bswap64 : IntBuiltin [.int 0 ((2 : Int) ^ 64 - 1)] (.int 0 ((2 : Int) ^ 64 - 1))

/-- The bounded work of a builtin, in Gabbro primitives (`kostenExpr`): a wrapping operation, a rotate or
    a byte swap is one primitive, a saturating addition three (sum, bound test, clamp), and a bit scan or
    a population count at most one primitive per bit of its width `W = w + 1`. It is an over-approximation
    bound, not a claim of physical instruction timing. -/
def IntBuiltin.arbeit {ts : List Ty} {τ : Ty} : IntBuiltin ts τ → Nat
  | .addW _ => 1
  | .subW _ => 1
  | .mulW _ => 1
  | .shlW _ => 1
  | .addS _ _ => 3
  | .clz w => w + 1
  | .ctz w => w + 1
  | .log2Floor w => w + 1
  | .popcount w => w + 1
  | .rotl _ => 1
  | .rotr _ => 1
  | .bswap16 => 1
  | .bswap32 => 1
  | .bswap64 => 1

end Gabbro.Grammatik
