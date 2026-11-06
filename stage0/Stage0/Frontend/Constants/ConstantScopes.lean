module
public import Grammatik.Parser.Elab.Konst.Scopes.ConstantScopes
public import Stage0.Frontend.DependentScopes
public import Stage0.Frontend.Constants.ConstantOrder
public import Stage0.Frontend.Constants.ConstantMeaning
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

/-- A forward scalar supplies another scalar's exclusive range and an alias bound. -/
theorem elaborateConstantScopes_forward_zeuge :
    let items := [SItemTief.constT "ANSWER"
        (.range (.atom "u8") (.lit 0) (.bin "+" (.variable "LIMIT") (.lit 1)) true)
        (.one (.variable "LIMIT")),
      .typeT [] "Result" [] [] (some (.atom "Bound")),
      .typeT [] "Bound" [] [] (some (.range (.atom "u8") (.lit 0) (.variable "LIMIT") false)),
      .constT "LIMIT" (.atom "u8") (.one (.bin "+" (.variable "BASE") (.lit 2))),
      .constT "BASE" (.atom "u8") (.one (.lit 40))]
    ∃ result, elaborateConstantScopes items = .ok result ∧
      result.scope.values = [("BASE", 40), ("LIMIT", 42), ("ANSWER", 42)] ∧
      result.scope.scalarOrder.Perm items ∧ ConstantAcyclic items := by
  dsimp only
  refine ⟨(elaborateConstantScopes _).toOption.get (by decide +kernel), ?_, ?_, ?_, ?_⟩
  · exact Gabbro.Grammatik.except_ok_get _
  · decide +kernel
  · exact ((elaborateConstantScopes _).toOption.get (by decide +kernel)).scope.scalarPermutation
  · exact (elaborateConstantScopes_dependencies _
      ((elaborateConstantScopes _).toOption.get (by decide +kernel))
      (Gabbro.Grammatik.except_ok_get _)).1

end Gabbro.Stage0.Frontend
