module
public import Grammatik.Parser.Elab.Konst.Scopes.Functions
public import Stage0.Frontend.Aliases
import Lean.Elab.Tactic.Cbv
import all Init.Data.String.Basic
import all Init.Data.String.Defs
@[expose] public section


namespace Gabbro.Stage0.Frontend
open Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze

attribute [local cbv_eval] strEq_apply_eq_decide

end Gabbro.Stage0.Frontend
