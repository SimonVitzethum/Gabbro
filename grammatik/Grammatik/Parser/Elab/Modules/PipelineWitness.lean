module
public import Grammatik.Parser.Elab.Modules.PipelineWitness.Data
public import Grammatik.Parser.Elab.UebersetzeAllg3

import all Grammatik.Parser.Stmt.Anweisung.Kopf
import Grammatik.Kern.Taktik.KernelRfl
import all Init.Data.Int.Repr
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
open Uebersetze UebersetzeAllg2

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem module_before_generic_function_zeuge :
    (preparedSource genericModuleSource).map (fun items => items.filterMap fun
      | .fnT sig _ => some sig.name
      | _ => none) =
      .ok [memberName ["Bytes", "value"], Generic.instanceName innerInstance] := by
  kernel_rfl

theorem generic_module_call_zeuge :
    (preparedSource genericModuleSource).map (fun items => items.any fun
      | .fnT sig (.block [.bind false "copy" none (.call name [.variable "x"])] _) =>
        strEq sig.name (memberName ["Bytes", "value"]) && strEq name (Generic.instanceName innerInstance)
      | _ => false) = .ok true := by
  kernel_rfl

theorem qualified_call_zeuge :
    (preparedSource callerSource).map (fun items => items.any fun
      | .fnT sig (.block [.call name [.variable "t"]] _) =>
        strEq sig.name "send" && strEq name (memberName ["Jobs", "push"])
      | _ => false) = .ok true := by
  kernel_rfl

/-- A real exporter result contains ordinary integer signatures for both concrete functions. -/
theorem exporter_generic_module_zeuge :
    (exportedSource genericModuleSource).map (fun unit =>
      unit.fns.map (fun fn => (fn.name, fn.params.map Prod.snd))) =
      .ok [(memberName ["Bytes", "value"], [.int 0 255]),
        (Generic.instanceName innerInstance, [.int 0 255])] := by
  kernel_rfl

/-- Non-degenerate inhabited instance of the generic existing-forms guarantee. -/
theorem prepare_existingForms_zeuge :
    (preparedSource stackSource).map existingForms = .ok true := by
  kernel_rfl

/-- **FINDING (open): the plan's stack fixture expands but is not exported.** Its functions declare
    `writes Items` on a plain table; the effect reader has a form for `writes T.slots`, an arena and a
    static only, so the exporter refuses the unit by name. -/
theorem exporter_stack_refused_zeuge :
    (exportedSource stackSource).map (fun unit => unit.tabs.map (fun tab => (tab.name, tab.count))) =
      .error "writes clause without G form" := by
  kernel_rfl

theorem definition_scope_zeuge :
    (preparedSource lexicalSource).map (fun items => items.any fun
      | .fnT sig (.block [] (some (.ret (some (.variable name))))) =>
        strEq sig.name (memberName ["client", "A", "read"]) && strEq name "definition::K"
      | _ => false) = .ok true := by
  kernel_rfl

/-- The actual exporter also retains the definition-site constant; flattening modules before
    instantiation would lose the template's lexical scope and cannot satisfy this statement. -/
theorem definition_scope_exporter_zeuge :
    (exportedSource lexicalSource).map (fun unit => unit.fns.map (fun fn => (fn.name, fn.ret))) =
      .ok [(memberName ["client", "A", "read"], .val (.lit 3))] := by
  kernel_rfl

theorem module_static_requirements_zeuge :
    ((parsedSource callbackSource).bind prepare).map (fun result => result.2.length) = .ok 2 := by
  kernel_rfl

theorem module_literal_last_zeuge :
    (preparedSource callbackSource).map (fun items => (items.length,
      items.filterMap fun
        | .fnT sig (.block [.bind false "value" none (.call name [.variable "x"])] _) =>
          some (sig.name, name)
        | _ => none)) = .ok (4, [
          (memberName ["Named", "run"], "twice"),
          (memberName ["Literal", "run"], Generic.literalName
            "fn ( x : u8 ) -> u8 effects { } costs <= 3 ops { return x ; }")]) := by
  kernel_rfl

theorem module_callback_forwarding_zeuge :
    ((parsedSource callbackForwardSource).bind prepare).map (fun result =>
      (existingForms result.1, result.2.length)) = .ok (true, 2) := by
  kernel_rfl

theorem complete_expansion_order_zeuge :
    (preparedSource completeOrderSource).map (fun items => items.filterMap fun
      | .fnT sig _ => some sig.name
      | _ => none) = .ok [memberName ["A", "run"],
        Generic.instanceName ⟨"copy_value", ["u8"]⟩,
        Generic.literalName "fn ( x : u8 ) -> u8 effects { } costs <= 3 ops { return x ; }", "$spec$0$copy"] := by
  kernel_rfl

theorem complete_order_spec_call_zeuge :
    (preparedSource completeOrderSource).map (fun items => items.any fun
      | .fnT sig body => strEq sig.name (Generic.instanceName ⟨"copy_value", ["u8"]⟩) &&
          beqSAnw body (.block [.bind false "value" none (.call "$spec$0$copy" [.variable "x"])]
            (some (.ret (some (.variable "value")))))
      | _ => false) = .ok true := by
  kernel_rfl

theorem generic_spec_before_reason_zeuge :
    (exportedSource reasonOrderSource).map (fun unit =>
      (unit.fns.map (·.name), (unit.fns.flatMap (·.body)).countP
        (fun | .bindElse .. => true | _ => false))) =
      .ok (["entry", Generic.instanceName ⟨"forward", ["u8"]⟩, "$spec$0$copy"], 2) := by
  kernel_rfl

end Gabbro.Grammatik.Parser.Modules
