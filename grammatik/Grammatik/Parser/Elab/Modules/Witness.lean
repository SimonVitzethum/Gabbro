module
public import Grammatik.Parser.Elab.Modules.Witness.Data
public import Grammatik.Parser.Elab.Modules.Frontend
public import Grammatik.Parser.Print.Item

import all Grammatik.Parser.Elab.Modules.Witness.Phases
import all Grammatik.Parser.Elab.Modules.Shape
import all Grammatik.Parser.Item.ElementTief.Kopf.Teil1a
import all Grammatik.Parser.Item.ElementTief.Kopf.Teil2
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
namespace Gabbro.Grammatik.Parser.Modules

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The actual parameter and argument parsers are shared with generic functions. -/
theorem module_parameters_parser_zeuge :
    (parsedSource stackTemplateSource).map (fun items => match items with
      | [.moduleTemplateT "stack" params _] => beqSGenericParams params
          [.type "T" [], .constant "N" (.range (.atom "u32") (.lit 1) (.lit 65536) false)]
      | _ => false) = .ok true := by
  rw [WitnessPhases.templateParsed.property]
  cbv

theorem use_alias_parser_zeuge :
    (parsedSource "pub use Jobs = stack::[index into Tasks, 64];").map (fun items =>
      beqSItemTiefList items [.pubT (.moduleUseT "Jobs" ["stack"] ["index into Tasks", "64"])]) =
      .ok true := by
  rw [WitnessPhases.useParsed.property]
  cbv

theorem module_use_roundtrip_zeuge :
    rundlaufItem (.moduleUseT "Jobs" ["containers", "stack"] ["index into Tasks", "64"]) = true := by
  exact WitnessPhases.roundtrip_use

/-- The table count is 64 and its actual field type is the supplied nominal index type. -/
theorem stack_table_zeuge :
    (expandedSource stackSource).map (fun items => items.any (beqSItemTief (itemsTable "Jobs"))) =
      .ok true := by
  rw [WitnessPhases.stackExpanded]
  cbv

theorem stack_static_zeuge :
    (expandedSource stackSource).map (fun items => items.any (beqSItemTief (topStatic "Jobs"))) =
      .ok true := by
  rw [WitnessPhases.stackExpanded]
  cbv

/-- Both signatures, their reason channels, costs and memory effects survive substitution. -/
theorem stack_functions_zeuge :
    (expandedSource stackSource).map (fun items =>
      hasSignature (pushSignature "Jobs") items && hasSignature (popSignature "Jobs") items) =
      .ok true := by
  rw [WitnessPhases.stackExpanded]
  cbv


/-- Equal module arguments are deliberately not memoized: each use owns all its storage. -/
theorem two_uses_disjoint_tables_zeuge :
    (expandedSource twoUsesSource).map (fun items => items.filterMap fun
      | .tableT name _ _ _ _ _ _ _ => some name
      | _ => none) =
      .ok ["Tasks", memberName ["Jobs", "Items"], memberName ["Other", "Items"]] := by
  rw [WitnessPhases.twoExpanded]
  cbv

theorem two_uses_disjoint_statics_zeuge :
    (expandedSource twoUsesSource).map (fun items => items.filterMap fun
      | .globT _ name _ _ _ _ _ => some name
      | _ => none) = .ok [memberName ["Jobs", "top"], memberName ["Other", "top"]] := by
  rw [WitnessPhases.twoExpanded]
  cbv

theorem two_uses_disjoint_functions_zeuge :
    (expandedSource twoUsesSource).map (fun items => items.filterMap fun
      | .fnT sig _ => some sig.name
      | _ => none) = .ok [memberName ["Jobs", "push"], memberName ["Jobs", "pop"],
        memberName ["Other", "push"], memberName ["Other", "pop"]] := by
  rw [WitnessPhases.twoExpanded]
  cbv

theorem instance_names_disjoint_zeuge :
    (memberName ["Jobs", "Items"] == memberName ["Other", "Items"]) = false := by cbv

/-- A recursive application would allocate fresh storage forever, even with unchanged arguments. -/
theorem recursive_module_refused_zeuge :
    expandedSource ("module loop[T] { use Again = loop::[T]; } " ++
      "use Start = loop::[u8];") = .error "parametric-module-recursion: loop" := by
  exact WitnessPhases.recursiveRefused

theorem alias_collision_refused_zeuge :
    expandedSource ("module empty[T] { } use A = empty::[u8]; use A = empty::[u8];") =
      .error "parametric-module-alias-collision: A" := by
  exact WitnessPhases.aliasRefused

/-- The collision gate also protects against a declaration supplied directly as surface AST. -/
theorem generated_name_collision_refused_zeuge :
    expand [.constT (memberName ["A", "v"]) (.atom "u8") (.one (.lit 0)),
      .moduleTemplateT "m" [.type "T" []]
        [.globT false "v" (.atom "T") (.one (.lit 0)) none none false],
      .moduleUseT "A" ["m"] ["u8"]] =
        .error "parametric-module-name-collision: generated name is already declared" := by
  exact WitnessPhases.nameRefused

theorem constant_range_refused_zeuge :
    expandedSource (stackPreamble ++ stackTemplateSource ++
      "use Bad = stack::[index into Tasks, 0];") =
        .error "generic constant argument: C17 evaluation failed or exceeded its bound" := by
  exact WitnessPhases.badRefused

end Gabbro.Grammatik.Parser.Modules
