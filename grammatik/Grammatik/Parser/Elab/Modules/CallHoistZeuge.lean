/-
  Witnesses of the call rewrite: a call in an operand, a call as an argument of a call, a call in a
  condition and in an assigned value are bound in front; a call behind a read of a static, in the
  right operand of `&&`, and a call that already stands alone are left where they are.
-/
module
public import Grammatik.Parser.Elab.Modules.CallHoist
import Grammatik.Kern.Taktik.KernelRfl
import all Init.Data.Repr
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.Modify
import all Init.Data.String.OrderInstances
import all Init.Data.String.Pattern
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.Char
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Pattern.String
import all Init.Data.String.PosRaw
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Stream
import all Init.Data.String.Subslice
import all Init.Data.String.Substring
import all Init.Data.String.TakeDrop
import all Init.Data.String.Termination
import all Init.Data.String.ToSlice
@[expose] public section

namespace Gabbro.Grammatik.Parser.CallHoist

def zeugeK : Kontext := { fns := ["f", "g"], statics := ["s"] }

/-- `return f(3) + 1;` binds the call first. -/
theorem operand_zeuge :
    hebeKoerper zeugeK (.block [] (some (.ret (some (.bin "+" (.call "f" [.lit 3]) (.lit 1)))))) =
      .block [.bind false "#r0" none (.call "f" [.lit 3])]
        (some (.ret (some (.bin "+" (.variable "#r0") (.lit 1))))) := by kernel_rfl

/-- `let a = f(g(3));` binds the inner call; the outer one already stands alone. -/
theorem argument_zeuge :
    hebeKoerper zeugeK (.block [.bind false "a" none (.call "f" [.call "g" [.lit 3]])] none) =
      .block [.bind false "#r0" none (.call "g" [.lit 3]),
        .bind false "a" none (.call "f" [.variable "#r0"])] none := by kernel_rfl

/-- `if g(7) { }` binds the condition's call in front of the `if`; `x = f(1) + f(2);` binds both in order. -/
theorem bedingung_zeuge :
    hebeKoerper zeugeK (.block [.cond (.call "g" [.lit 7]) (.block [] none) [] none,
        .set (.variable "x") "=" (.bin "+" (.call "f" [.lit 1]) (.call "f" [.lit 2]))] none) =
      .block [.bind false "#r0" none (.call "g" [.lit 7]),
        .cond (.variable "#r0") (.block [] none) [] none,
        .bind false "#r1" none (.call "f" [.lit 1]),
        .bind false "#r2" none (.call "f" [.lit 2]),
        .set (.variable "x") "=" (.bin "+" (.variable "#r1") (.variable "#r2"))] none := by kernel_rfl

/-- A call behind a read of the static `s`, and a call in the right operand of `&&`, stay. -/
theorem bleibt_zeuge :
    hebeKoerper zeugeK (.block [.bind false "a" none (.bin "+" (.variable "s") (.call "f" [.lit 1])),
        .bind false "b" none (.bin "&&" (.variable "c") (.call "g" [.lit 1]))] none) =
      .block [.bind false "a" none (.bin "+" (.variable "s") (.call "f" [.lit 1])),
        .bind false "b" none (.bin "&&" (.variable "c") (.call "g" [.lit 1]))] none := by kernel_rfl

/-- A call through a local pointer is bound as well: `let p = &f; return p() + 1;`. -/
theorem zeiger_zeuge :
    hebeKoerper zeugeK (.block [.bind false "p" none (.fnref "f")]
        (some (.ret (some (.bin "+" (.call "p" []) (.lit 1)))))) =
      .block [.bind false "p" none (.fnref "f"), .bind false "#r0" none (.call "p" [])]
        (some (.ret (some (.bin "+" (.variable "#r0") (.lit 1))))) := by kernel_rfl

/-- A constructed value as an argument and as a stored value is bound first; assigned to a variable
    or returned it stays: `f(Num(7));  t.slots[i].k = Num(9);  x = Num(5);`. -/
theorem fall_zeuge :
    hebeKoerper { zeugeK with faelle := ["Num"] } (.block [.call "f" [.call "Num" [.lit 7]],
        .set (.field (.index (.field (.variable "t") "slots") (.variable "i")) "k") "=" (.call "Num" [.lit 9]),
        .set (.variable "x") "=" (.call "Num" [.lit 5])] none) =
      .block [.bind false "#r0" none (.call "Num" [.lit 7]), .call "f" [.variable "#r0"],
        .bind false "#r1" none (.call "Num" [.lit 9]),
        .set (.field (.index (.field (.variable "t") "slots") (.variable "i")) "k") "=" (.variable "#r1"),
        .set (.variable "x") "=" (.call "Num" [.lit 5])] none := by kernel_rfl

/-- A case without a payload as an argument is bound as well: `return f(End);`. -/
theorem fall_ohne_nutzlast_zeuge :
    hebeKoerper { zeugeK with faelle := ["End"] }
        (.block [] (some (.ret (some (.call "f" [.variable "End"]))))) =
      .block [.bind false "#r0" none (.variable "End")]
        (some (.ret (some (.call "f" [.variable "#r0"])))) := by kernel_rfl

/-- An untyped `let` of an aggregate table field gets the field's declared type. -/
theorem feld_zeuge :
    hebeKoerper { zeugeK with felder := [("T", "s", .str (.lit 16))] }
        (.block [.bind false "a" none (.field (.index (.field (.variable "T") "slots") (.lit 1)) "s")] none) =
      .block [.bind false "a" (some (.str (.lit 16)))
        (.field (.index (.field (.variable "T") "slots") (.lit 1)) "s")] none := by kernel_rfl

end Gabbro.Grammatik.Parser.CallHoist
