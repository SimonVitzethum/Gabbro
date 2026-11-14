module
public import Grammatik.Parser.Elab.Konst.Scopes.Aliases
public import Grammatik.Parser.Elab.UebersetzePipeline
public import Grammatik.Parser.Elab.Uebersetze.Records.ConstantLaws
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

theorem aliasBody_correct_zeuge :
    aliasBody [("Small", (-4, 9))] "Small" =
      .ok (.range (.atom "Small") (bound (-4)) (bound 9) false) ∧
    uTyp [("Small", (-4, 9))] [] [] []
      (.range (.atom "Small") (bound (-4)) (bound 9) false) = .ok (.int (-4) 9) :=
  aliasBody_correct _ _ _ _ _ (by cbv)

theorem constant_correct_zeuge :
    constant [("Small", (0, 100))] [] []
      (.constT "N" (.atom "Small") (.one (.bin "+" (.lit 40) (.lit 2)))) =
      .constT "N" (.atom "Small") (.one (.lit 42)) ∧
    uConstsRech [] [.constT "N" (.atom "Small") (.one (.lit 42))] [] = [("N", 42)] :=
  constant_correct _ _ _ _ _ _ 0 100 42 (by cbv) (by cbv) (by omega)

/-- Alias spelling and the signed minimum are represented without widening the canonical type. -/
theorem negative_sound_zeuge :
    negative [("Signed", (-128, 127))] [] [] "MIN" (.atom "Signed")
      (.bin "-" (.bin "-" (.lit 0) (.lit 127)) (.lit 1)) (-128) 127 (-128) =
      .constT "MIN" (.atom "i8") (.one (.bin "+" (.field (.variable "i8") "min") (.lit 0))) := by
  exact negative_materializes _ _ _ _ _ _ "i8" (-128) 127 (-128)
    (by cbv) (by cbv) (by cbv) (by omega) (by omega)

end Gabbro.Stage0.Frontend
