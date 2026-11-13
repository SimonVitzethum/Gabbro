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
set_option maxRecDepth 100000

/-- The option's extent is four, but its table position is one. -/
def payloadKindContext (ty : Ty) : UCtx :=
  { names := ["message"], kinds := [.sum 0], types := [.sum [some ty]],
    tabs := [{ name := "Other", count := 9, cols := [] },
             { name := "T", count := 4, cols := [] }],
    locks := [], held := [], res := some (0, 255), fname := "value", alias := [], lits := [],
    sums := [{ name := "Message", cases := [("Item", some ty)] },
             { name := "Inner", cases := [("End", none), ("Flag", some .bool)] }],
    narrow := true }

def optionPayloadMatch : SAnw :=
  .cases (.variable "message")
    [.arm "Item" (some "payload") (.block
      [.cases (.variable "payload")
        [.arm "Some" (some "i") (.block [] (some (.ret (some (.bin "+" (.variable "i") (.lit 10)))))),
         .arm "None" none (.block [] (some (.ret (some (.lit 7)))))]]
      none)]

/-- The production dispatcher can immediately match the arm's option payload again. -/
theorem option_payload_match_zeuge :
    (uAnwReihe (payloadKindContext (.opt 4)).tabs [] 32 (payloadKindContext (.opt 4))
      [optionPayloadMatch]).toBool = true := by kernel_rfl

/-- Canonical export retains the previous refusal, leaving read-back statements unchanged. -/
theorem option_payload_canonical_zeuge :
    (uAnwReihe (payloadKindContext (.opt 4)).tabs [] 32
      { payloadKindContext (.opt 4) with narrow := false } [optionPayloadMatch]).toBool = false := by
  kernel_rfl

/-- Inspect the actual context supplied to the arm reader, with a separate continuation call. -/
def payloadKindAccepted (ty : Ty) (expected : UParamArt) : Bool :=
  let ctx := payloadKindContext ty
  let run : UCtx → List SAnw → Except String (List UStmt × UCtx) := fun scope _ =>
    if scope.names.head? == some "payload" && scope.kinds.head? != some expected then
      Except.error "wrong payload kind"
    else Except.ok ([], scope)
  (uCases run ctx (.variable "message")
    [.arm "Item" (some "payload") (.block [] none)] []).toBool

theorem option_payload_table_position_zeuge : payloadKindAccepted (.opt 4) (.opt 1) = true := by
  kernel_rfl

/-- An absent table cannot supply an invented option identity. -/
theorem option_payload_missing_table_zeuge :
    payloadKindAccepted (.opt 7) .wert = true := by kernel_rfl

/-- Equal extents have lost their source table identity in `Ty.opt`; do not guess one. -/
theorem option_payload_ambiguous_table_zeuge :
    (uAnwReihe [] [] 32
      { payloadKindContext (.opt 4) with
        tabs := [{ name := "T", count := 4, cols := [] },
                 { name := "U", count := 4, cols := [] }] }
      [optionPayloadMatch]).toBool = false := by kernel_rfl

theorem bool_payload_kind_zeuge : payloadKindAccepted .bool .bool = true := by kernel_rfl
theorem string_payload_kind_zeuge : payloadKindAccepted (.str 8) .wert = true := by kernel_rfl
theorem array_payload_kind_zeuge : payloadKindAccepted (.arr (.int 0 9) 2) .wert = true := by kernel_rfl
theorem nested_tagged_payload_kind_zeuge :
    payloadKindAccepted (.sum [none, some .bool]) (.sum 1) = true := by kernel_rfl

end Gabbro.Grammatik.Parser.Uebersetze
