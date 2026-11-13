module
public import Grammatik.Parser.Elab.Uebersetze.Records.ConstantLaws
public import Grammatik.Parser.Elab.UebersetzeAllg
public import Grammatik.Parser.Elab.Uebersetze.Kontext.LocalBindings
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
open Gabbro.Grammatik.Parser.UebersetzeAllg

def stringConstantItems : List SItemTief :=
  [.constT "Q" (.str (.lit 8)) (.one (.ext .text ["hi!"] []))]

def stringConstantCtx : UCtx :=
  { names := [], kinds := [], types := [], tabs := [], locks := [], held := [], res := none,
    resBool := false, fname := "sample", alias := [], lits := [],
    arrKonst := uKonstArrays [] [] [] stringConstantItems [] (uRecordConstant [] [] [] []) true }

def stringConstantUnit : UProg := { tabs := [], locks := [], fns := [] }

/-- Nonempty strings enter the same production collector as constant arrays and products. -/
theorem string_constant_collect_zeuge :
    uKonstArrays [] [] [] stringConstantItems [] (uRecordConstant [] [] [] []) true =
      [("Q", .typed (.str 8) (.text [104, 105, 33]))] := by kernel_rfl

/-- The canonical constant reader emits UTF-8 bytes, including multibyte characters. -/
theorem string_constant_utf8_zeuge :
    uKonstZeile [] [] [] (.str 2) (.one (.ext .text ["é"] [])) =
      some (.text [195, 169]) := by kernel_rfl

/-- The actual body reader resolves the name to its typed literal before indexing. -/
theorem string_constant_read_zeuge :
    uWertBody stringConstantCtx (.index (.variable "Q") (.lit 0)) =
      .ok (.idx (.typed (.str 8) (.text [104, 105, 33])) (.lit 0)) := by kernel_rfl

/-- Both parameter scope and a newly bound local hide a constant of the same name. -/
theorem string_constant_parameter_shadow_zeuge :
    uWertBody { stringConstantCtx with names := ["Q"], kinds := [.wert], types := [.str 1] }
        (.index (.variable "Q") (.lit 0)) =
      .ok (.idx (.param "Q") (.lit 0)) := by kernel_rfl

theorem string_constant_local_shadow_zeuge :
    uWertBody (uMitLokal stringConstantCtx "Q" .wert (.str 1) [])
        (.index (.variable "Q") (.lit 0)) =
      .ok (.idx (.param "Q") (.lit 0)) := by kernel_rfl

/-- The unchanged typed literal gate accepts the declared bound and refuses a shorter one. -/
theorem string_constant_bound_zeuge :
    (lowLit (u := stringConstantUnit) (Γ := []) (Λ := []) (.str 8)
      (.text [104, 105, 33])).toOption.isSome = true := by kernel_rfl

theorem string_constant_bound_refused_zeuge :
    (lowLit (u := stringConstantUnit) (Γ := []) (Λ := []) (.str 2)
      (.text [104, 105, 33])).toOption.isSome = false := by kernel_rfl

end Gabbro.Grammatik.Parser.Uebersetze
