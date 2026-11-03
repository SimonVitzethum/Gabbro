module
public import Stage0.Frontend.Source
public import Stage0.Senke.Ausdruck.Old.Source
public import Stage0.Frontend.Tables
public import Grammatik.Parser.Elab.Konst.ErsetzungTor
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

/-- Expand through the canonical exporter before using the shared runtime elaborator.
    The supplied scopes retain their original-source certificates and table adapter. -/
def elabWithScopes (items : List SItemTief) (consts : List (String × Int))
    (typeEnv : List (String × (Int × Int)))
    (functions : List UKonstFn := uKonstFns (uOhneSenken (uMembers items)))
    (tableLowering : List String → SItemTief → Except String UTab := uTabelle consts typeEnv) : Except String UProg := do
  let (expanded, requirements) ← expandU items
  elabExpandedWithScopes (expanded.map OldSource.normalizeItem) consts typeEnv functions tableLowering requirements

/-- Equality on the expanded program, including every expansion and const-admission error.
    Both endpoints share the entire phase body, so later elaborator changes cannot drift. -/
theorem elabU_scopes (items : List SItemTief) :
    elabU items = ((expandU items).bind fun (expanded, requirements) => do
      checkCanonicalConstants expanded
      let consts := uConstsRech (uKonstFns expanded) expanded []
      let types := uAliase consts expanded ++ uAliasBreiten expanded ++
        consts.map (fun c => (c.1, (c.2, c.2)))
      elabExpandedWithScopes expanded consts types
        (uKonstFns (uOhneSenken expanded)) (uTabelle consts types) requirements) := by
  rfl

/-- The actual canonical consumer sees identical complete scopes on every input admitted by
    the former collector comparison, including all error branches of runtime elaboration. -/
theorem elabWithScopes_collector_redundant (original runtime : List SItemTief)
    (h : EnvironmentCompatible original (normalizeAliases original))
    (result : DerivedScopes original) (hr : deriveScopes original = .ok result) :
    elabWithScopes runtime result.scope.values result.scope.types result.scope.functions
      (tableWithEmpty result.scope.values result.scope.types) =
      elabWithScopes runtime
        (scopes original (normalizeAliases original) (normalize_environments original h)).values
        (scopes original (normalizeAliases original) (normalize_environments original h)).types
        (scopes original (normalizeAliases original) (normalize_environments original h)).functions
        (tableWithEmpty
          (scopes original (normalizeAliases original) (normalize_environments original h)).values
          (scopes original (normalizeAliases original) (normalize_environments original h)).types) := by
  obtain ⟨old, he, hs⟩ := deriveScopes_of_compatible original h
  have same : result = old := Except.ok.inj (hr.symm.trans he)
  subst result
  rw [hs]

/-- The canonical array evaluator accepts the source-derived alias signature; the old builtin-only
    extractor cannot evaluate this same leaf. No array semantics is duplicated by the adapter. -/
theorem canonical_array_functions_zeuge :
    let items := [SItemTief.fnT
        ⟨"const", "identity", [("x", .atom "Small")], some (.atom "Small"), none, []⟩
        (.block [] (some (.ret (some (.variable "x"))))),
      .constT "VALUES" (.array (.atom "Small") (.lit 1)) (.rows [.one (.call "identity" [.lit 42])])]
    uKonstArrays [("Small", (0, 100))] (constantFunctions [("Small", (0, 100))] items) [] items []
      (uRecordConstant [] [("Small", (0, 100))] (constantFunctions [("Small", (0, 100))] items) []) true =
      [("VALUES", .typed (.arr (.int 0 100) 1) (.arrCons (.lit 42) .arrNil))] ∧
    uKonstArrays [("Small", (0, 100))] (uKonstFns items) [] items []
      (uRecordConstant [] [("Small", (0, 100))] (uKonstFns items) []) true = [] := by
  decide +kernel

end Gabbro.Stage0.Frontend
