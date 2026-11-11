module
public import Grammatik.Parser.Elab.Generic.Substitution
public import Grammatik.Parser.Elab.Instantiation.Names
@[expose] public section
namespace Gabbro.Grammatik.Parser.Generic

/-- A canonical instance key. The frontend must normalize arguments before closure. -/
structure Instance where
  function : String
  arguments : List String
  deriving BEq, DecidableEq, Repr

/-- Length encoding makes component boundaries unambiguous. -/
def encodeComponent (s : String) : String :=
  toString s.length ++ ":" ++ s

/-- The caller checks this reserved name against all source declarations. -/
def instanceName (i : Instance) : String :=
  "$generic$" ++ encodeComponent i.function ++
    String.join (i.arguments.map encodeComponent)

/-- The pending instances from the first one not visited yet. -/
def firstUnseen (seen : List Instance) : List Instance → List Instance
  | [] => []
  | next :: pending => if seen.contains next then firstUnseen seen pending else next :: pending

/-- Reachable instance closure. Fuel is an explicit compilation resource limit,
not a silently truncated result. Already visited recursive instances need no fuel.
The expansion correctness theorem attaches to successful closure plus the body
substitution and call-rewriting pass; closure alone is not that theorem.
The recursion is structural in the fuel, so the closure reduces on closed terms. -/
def instanceClosure (dependencies : Instance → Except String (List Instance)) :
    Nat → List Instance → List Instance → Except String (List Instance)
  | fuel, pending, seen =>
    match firstUnseen seen pending with
    | [] => .ok seen
    | next :: rest =>
      match fuel with
      | 0 => .error "generic-instance-limit: growing or polymorphically recursive instantiation"
      | n + 1 => do
        let children ← dependencies next
        instanceClosure dependencies n (rest ++ children) (seen ++ [next])
termination_by structural fuel => fuel

/-- Structural compilation budget: declarations times distinct source instantiation
sites plus one. Exhaustion refuses compilation; it never returns partial closure.
Sites are canonical keys, counted once even when repeated in source. -/
def structuralFuel (genericDeclarations : Nat) (sites : List Instance) : Nat :=
  genericDeclarations * sites.eraseDups.length + 1

/-- Frontend entry point with a fixed structural budget rather than caller fuel. -/
def boundedInstanceClosure (genericDeclarations : Nat)
    (dependencies : Instance → Except String (List Instance))
    (sites : List Instance) : Except String (List Instance) :=
  instanceClosure dependencies (structuralFuel genericDeclarations sites) sites []

/-- Reject collisions before adding any generated declarations. -/
def checkInstanceNames (sourceNames : List String) (instances : List Instance) :
    Except String Unit :=
  Instantiation.checkFreshNames sourceNames (instances.map instanceName)
    "generic-instance-name-collision: generated instance name is already declared"

theorem checkInstanceNames_hygiene (sourceNames : List String) (instances : List Instance)
    (h : checkInstanceNames sourceNames instances = .ok ()) :
    (instances.map instanceName).Nodup ∧
      ∀ name ∈ instances.map instanceName, name ∉ sourceNames :=
  Instantiation.checkFreshNames_sound _ _ _ h

end Gabbro.Grammatik.Parser.Generic
