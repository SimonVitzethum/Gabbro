module

public import Grammatik.Parser.Elab.Uebersetze.Teil3

@[expose] public section

namespace Gabbro.Grammatik.Parser.Uebersetze
set_option maxRecDepth 100000

/-- C13: the builtin of a binary operator spelling (`+%`, `-%`, `*%`, `<<%`, `+|`). -/
def uBinEin : String → Option UBi
  | "+%" => some .addW
  | "-%" => some .subW
  | "*%" => some .mulW
  | "<<%" => some .shlW
  | "+|" => some .addS
  | _ => none

/-- C13: the one-operand bit intrinsic of a call name. -/
def uBitEin : String → Option UBi
  | "clz" => some .clz
  | "ctz" => some .ctz
  | "log2_floor" => some .log2Floor
  | "popcount" => some .popcount
  | "bswap" => some .bswap
  | _ => none

/-- C13: the two-operand bit intrinsic of a call name. -/
def uRotEin : String → Option UBi
  | "rotl" => some .rotl
  | "rotr" => some .rotr
  | _ => none

/-- C13: the declared STORAGE width in bits of an operand, where the declaration names it: a parameter or a `let`
    local at a bare unsigned word (`UCtx.bits`), a conversion `T(e)` to an unsigned range `0 .. 2^W - 1`, or a
    wrapping builtin of such operands. Every other operand (a field, a static, an alias) has no width here, and the
    builtin over it is refused: the width is never read off the interval the checker computed. -/
def uBreite (ctx : UCtx) : SExpr → Option Nat
  | .variable p =>
    match uParamNr ctx p with
    | .ok j =>
      match ctx.bits[j]? with
      | some w => if 0 < w then some w else none
      | none => none
    | .error _ => none
  | .call f [_] =>
    match uTypName ctx.alias f with
    | .ok (lo, hi) =>
      if lo == 0 && decide (1 ≤ hi) && decide ((2 : Int) ^ Nat.log2 (hi + 1).toNat = hi + 1) then
        some (Nat.log2 (hi + 1).toNat)
      else none
    | .error _ => none
  | .bin op a b =>
    match uBinEin op with
    | some .shlW => uBreite ctx a
    | some .addW | some .subW | some .mulW => (uBreite ctx a).orElse fun _ => uBreite ctx b
    | _ => none
  | _ => none

end Gabbro.Grammatik.Parser.Uebersetze
