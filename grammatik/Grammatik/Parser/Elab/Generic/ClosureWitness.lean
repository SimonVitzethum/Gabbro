module
public import Grammatik.Parser.Elab.Generic.Closure
@[expose] public section
namespace Gabbro.Grammatik.Parser.Generic

 theorem two_instances_zeuge :
    instanceClosure (fun _ => .ok []) 2
      [⟨"identity", ["u32"]⟩, ⟨"identity", ["bool"]⟩] [] =
      .ok [⟨"identity", ["u32"]⟩, ⟨"identity", ["bool"]⟩] := rfl

 theorem growing_recursion_refused_zeuge :
    instanceClosure (fun i => .ok [⟨i.function, "array" :: i.arguments⟩]) 2
      [⟨"grow", ["u32"]⟩] [] =
      .error "generic-instance-limit: growing or polymorphically recursive instantiation" := rfl

 theorem substituted_bodies_zeuge :
    surfaceType [("T", .atom "u32")] [] (.atom "T") = .atom "u32" ∧
    surfaceType [("T", .atom "bool")] [] (.atom "T") = .atom "bool" := ⟨rfl, rfl⟩

 theorem collision_refused_zeuge :
    checkInstanceNames [instanceName ⟨"identity", ["u32"]⟩]
      [⟨"identity", ["u32"]⟩] =
      .error "generic-instance-name-collision: generated instance name is already declared" := rfl

end Gabbro.Grammatik.Parser.Generic
