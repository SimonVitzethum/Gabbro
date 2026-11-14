module
public import Grammatik.Parser.Elab.Konst.Scopes.AliasMeaning
public import Stage0.Frontend.Functions
import Lean.Elab.Tactic.Cbv
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


namespace Gabbro.Stage0.Frontend
open Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze

attribute [local cbv_eval] strEq_apply_eq_decide

theorem checkAliasMeaning_sound_zeuge :
    AliasMeaning [("Byte", (0, 255)), ("Count", (0, 255))]
      (.typeT [] "Count" [] [] (some (.atom "Byte"))) :=
  checkAliasMeaning_sound _ _ (by cbv)

/-- A successful name lookup alone cannot certify a wrong alias range. -/
theorem checkAliasMeaning_refused_zeuge :
    checkAliasMeaning [("Byte", (0, 255)), ("Count", (0, 100))]
      (.typeT [] "Count" [] [] (some (.atom "Byte"))) = false := by cbv

end Gabbro.Stage0.Frontend
