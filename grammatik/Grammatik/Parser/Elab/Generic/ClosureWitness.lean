module
public import Grammatik.Parser.Elab.Generic.Closure
import Lean.Elab.Tactic.Cbv
import all Grammatik.Parser.Elab.Generic.Closure
import all Grammatik.Parser.Elab.Generic.Substitution
import all Grammatik.Parser.Elab.Instantiation.Names
import all Init.Data.String.Basic
import all Init.Data.String.Defs
@[expose] public section
namespace Gabbro.Grammatik.Parser.Generic

attribute [local cbv_eval] strEq_apply_eq_decide

 theorem two_instances_zeuge :
    instanceClosure (fun _ => .ok []) 2
      [⟨"identity", ["u32"]⟩, ⟨"identity", ["bool"]⟩] [] =
      .ok [⟨"identity", ["u32"]⟩, ⟨"identity", ["bool"]⟩] := by cbv

 theorem growing_recursion_refused_zeuge :
    instanceClosure (fun i => .ok [⟨i.function, "array" :: i.arguments⟩]) 2
      [⟨"grow", ["u32"]⟩] [] =
      .error "generic-instance-limit: growing or polymorphically recursive instantiation" := by cbv

 theorem substituted_bodies_zeuge :
    surfaceType [("T", .atom "u32")] [] (.atom "T") = .atom "u32" ∧
    surfaceType [("T", .atom "bool")] [] (.atom "T") = .atom "bool" := by cbv

 theorem collision_refused_zeuge :
    checkInstanceNames [instanceName ⟨"identity", ["u32"]⟩]
      [⟨"identity", ["u32"]⟩] =
      .error "generic-instance-name-collision: generated instance name is already declared" := by cbv

end Gabbro.Grammatik.Parser.Generic
