module
public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil10
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

namespace Gabbro.Grammatik.Parser.Uebersetze

def equalitySchema : USum :=
  { name := "Token", cases := [("End", none), ("Number", some (.int 0 9))] }

def equalityContext : UCtx :=
  { names := ["a", "b"], kinds := [.sum 0, .sum 0],
    types := [.sum equalitySchema.spec, .sum equalitySchema.spec],
    tabs := [], locks := [], held := [], res := some (0, 255), fname := "sample", alias := [], lits := [],
    sums := [equalitySchema], narrow := true }

def equalityYes : SAnw := .block [] (some (.ret (some (.lit 42))))
def equalityNo : SAnw := .block [] (some (.ret (some (.lit 7))))

/-- Every pair of constructors is explicit, including a mismatch with a present payload. -/
theorem uTaggedEqualityArms_zeuge :
    uTaggedEqualityArms equalitySchema "b" equalityYes equalityNo =
      [.arm "End" none (.block [.cases (.variable "b")
          [.arm "End" none equalityYes, .arm "Number" (some "#eq-right") equalityNo]] none),
        .arm "Number" (some "#eq-left") (.block [.cases (.variable "b")
          [.arm "End" none equalityNo, .arm "Number" (some "#eq-right")
            (.block [.cond (.bin "==" (.variable "#eq-left") (.variable "#eq-right"))
              equalityYes [] (some equalityNo)] none)]] none)] := by kernel_rfl

/-- Both equality operators select the same exhaustive match, exchanging only the outcomes. -/
theorem uTaggedEquality_zeuge :
    uTaggedEquality equalityContext (.bin "==" (.variable "a") (.variable "b")) equalityYes equalityNo =
      .ok (some (.cases (.variable "a") (uTaggedEqualityArms equalitySchema "b" equalityYes equalityNo))) ∧
    uTaggedEquality equalityContext (.bin "!=" (.variable "a") (.variable "b")) equalityYes equalityNo =
      .ok (some (.cases (.variable "a") (uTaggedEqualityArms equalitySchema "b" equalityNo equalityYes))) := by
  constructor <;> kernel_rfl

/-- The production dispatcher and match elaborator accept the expansion with actual returns. -/
theorem uCond_tagged_zeuge :
    (uAnwReihe [] [] 32 equalityContext
      [.cond (.bin "==" (.variable "a") (.variable "b")) equalityYes [] (some equalityNo)]).toBool = true := by
  kernel_rfl

/-- Boolean payloads use the existing logical connectives rather than numeric equality. -/
theorem tagged_bool_payload_zeuge :
    (uAnwReihe [] [] 32 { equalityContext with
      types := [.sum [none, some .bool], .sum [none, some .bool]],
      sums := [{ name := "Truth", cases := [("End", none), ("Flag", some .bool)] }] }
      [.cond (.bin "==" (.variable "a") (.variable "b")) equalityYes [] (some equalityNo)]).toBool = true := by
  kernel_rfl

/-- A foreign declaration cannot borrow the first type's cases by matching its scalar layout. -/
theorem tagged_identity_refused_zeuge :
    uTaggedEquality { equalityContext with kinds := [.sum 0, .sum 1] }
      (.bin "==" (.variable "a") (.variable "b")) equalityYes equalityNo =
      .error "source export: equality of different tagged types" := by kernel_rfl

/-- Ordinary numeric comparisons never enter the tagged rewrite. -/
theorem numeric_equality_unchanged_zeuge :
    uTaggedEquality { equalityContext with kinds := [.int, .int] }
      (.bin "==" (.variable "a") (.variable "b")) equalityYes equalityNo = .ok none := by kernel_rfl

end Gabbro.Grammatik.Parser.Uebersetze
