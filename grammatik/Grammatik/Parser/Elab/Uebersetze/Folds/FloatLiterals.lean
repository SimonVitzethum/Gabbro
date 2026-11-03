module

public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil2

@[expose] public section
namespace Gabbro.Grammatik.Parser.Uebersetze

/-- Generated names are outside the source identifier alphabet. -/
def foldName (n : Nat) (suffix : String) : String := "#fold:" ++ toString n ++ ":" ++ suffix

/-- Largest finite binary64 value. `Ty.fl` deliberately retains the canonical
    model's existing binary64 interpretation of both f32 and f64 source types. -/
def uFloatLimit : Int := (2^53 - 1) * 2^971

def uFloatTy : Ty := .fl (-uFloatLimit, 1) (uFloatLimit, 1)

/-- Read decimal digits structurally so literal witnesses reduce in the kernel. -/
def uFloatDigits (digits : List Char) : Option Nat :=
  if digits.isEmpty || !digits.all istZiffer then none
  else some (digits.foldl (fun n c => 10 * n + (c.toNat - 48)) 0)

/-- Exact decimal rational, including scientific notation and the parser's
    `rounded` suffix. Rounding remains the canonical `Block.floatLit` operation. -/
def uFloatRational (text : String) : Except String (Int × Int) := do
  let chars := text.toList.takeWhile (· != ' ')
  let negative := chars.head? == some '-'
  let chars := if negative then chars.drop 1 else chars
  let mantissa := chars.takeWhile (fun c => c != 'e' && c != 'E')
  let exponent := chars.drop mantissa.length
  let exponent ← match exponent with
    | [] => pure (0 : Int)
    | _ :: rest => do
      let (negative, digits) := match rest with
        | '-' :: ds => (true, ds)
        | '+' :: ds => (false, ds)
        | ds => (false, ds)
      let some value := uFloatDigits digits | throw "float: malformed exponent"
      if value > 4096 then throw "float: exponent exceeds literal export limit"
      pure (if negative then -(value : Int) else (value : Int))
  let whole := mantissa.takeWhile (· != '.')
  let fraction := (mantissa.drop whole.length).drop 1
  let some numerator := uFloatDigits (whole ++ fraction) | throw "float: malformed decimal literal"
  if negative && numerator == 0 then throw "float: signed zero requires unary negation"
  let scale := exponent - (fraction.length : Int)
  let numerator : Int := if negative then -(numerator : Int) else (numerator : Int)
  pure (if scale < 0 then (numerator, (10 : Int)^(-scale).toNat)
    else (numerator * (10 : Int)^scale.toNat, 1))

/-- Float type bounds retain exact rationals; integer constants share the ordinary
    bound reader. No machine rounding is performed on a declared range. -/
def uFloatBound (alias : List (String × (Int × Int))) : SExpr → Except String (Int × Int)
  | .float text => uFloatRational text
  | .un "-" value | .un "-()" value => do
    let (numerator, denominator) ← uFloatBound alias value
    pure (-numerator, denominator)
  | value =>
    match uSchranke alias value with
    | some number => .ok (number, 1)
    | none => .error "float range: bound is not a known rational"

end Gabbro.Grammatik.Parser.Uebersetze
