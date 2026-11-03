module
public import Grammatik.Parser.Elab.Modules.Witness
public import Grammatik.Parser.Elab.UebersetzeAllg3
@[expose] public section
namespace Gabbro.Grammatik.Parser.Modules
open Uebersetze UebersetzeAllg2

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def preparedSource (text : String) : Except String (List SItemTief) := do
  pure (← prepare (pre108 (← parsedSource text))).1

def exportedSource (text : String) : Except String UProg := do
  elabU (pre108 (← parsedSource text))

/-- A module contains a generic function, so reversing the two frontend phases cannot pass. -/
def genericModuleSource : String :=
  "module box[T] { fn identity[U](x: U) -> U { return x; } " ++
  "fn value(x: T) -> T { let copy = identity::[T](x); return copy; } } " ++
  "use Bytes = box::[u8];"

def innerInstance : Generic.Instance := ⟨memberName ["Bytes", "identity"], ["u8"]⟩

theorem module_before_generic_function_zeuge :
    (preparedSource genericModuleSource).map (fun items => items.filterMap fun
      | .fnT sig _ => some sig.name
      | _ => none) =
      .ok [memberName ["Bytes", "value"], Generic.instanceName innerInstance] := by decide +kernel

theorem generic_module_call_zeuge :
    (preparedSource genericModuleSource).map (fun items => items.any fun
      | .fnT sig (.block [.bind false "copy" none (.call name [.variable "x"])] _) =>
        strEq sig.name (memberName ["Bytes", "value"]) && strEq name (Generic.instanceName innerInstance)
      | _ => false) = .ok true := by decide +kernel

/-- Alias qualification is resolved by the same instance keys used inside the copied functions. -/
def callerSource : String := stackSource ++
  " fn send(t: index into Tasks) or Full effects { writes Jobs::Items, writes Jobs::top } " ++
  "costs <= 20 ops { Jobs::push(t); return; }"

theorem qualified_call_zeuge :
    (preparedSource callerSource).map (fun items => items.any fun
      | .fnT sig (.block [.call name [.variable "t"]] _) =>
        strEq sig.name "send" && strEq name (memberName ["Jobs", "push"])
      | _ => false) = .ok true := by decide +kernel

/-- A real exporter result contains ordinary integer signatures for both concrete functions. -/
theorem exporter_generic_module_zeuge :
    (exportedSource genericModuleSource).map (fun unit =>
      unit.fns.map (fun fn => (fn.name, fn.params.map Prod.snd))) =
      .ok [(memberName ["Bytes", "value"], [.int 0 255]),
        (Generic.instanceName innerInstance, [.int 0 255])] := by decide +kernel

/-- Non-degenerate inhabited instance of the generic existing-forms guarantee. -/
theorem prepare_existingForms_zeuge :
    (preparedSource stackSource).map existingForms = .ok true := by decide +kernel

theorem exporter_stack_zeuge :
    (exportedSource stackSource).map (fun unit => unit.tabs.map (fun tab => (tab.name, tab.count))) =
      .ok [("Tasks", 128), (memberName ["Jobs", "Items"], 64)] := by decide +kernel

/-- Definition-site globals remain fixed when a use appears in another ordinary module. -/
def lexicalSource : String :=
  "module definition { const K: u8 = 3; module sample[T] { fn read() -> u8 { return K; } } } " ++
  "module client { const K: u8 = 7; use A = definition::sample::[u8]; }"

theorem definition_scope_zeuge :
    (preparedSource lexicalSource).map (fun items => items.any fun
      | .fnT sig (.block [] (some (.ret (some (.variable name))))) =>
        strEq sig.name (memberName ["client", "A", "read"]) && strEq name "definition::K"
      | _ => false) = .ok true := by decide +kernel

/-- The actual exporter also retains the definition-site constant; flattening modules before
    instantiation would lose the template's lexical scope and cannot satisfy this statement. -/
theorem definition_scope_exporter_zeuge :
    (exportedSource lexicalSource).map (fun unit => unit.fns.map (fun fn => (fn.name, fn.ret))) =
      .ok [(memberName ["client", "A", "read"], .val (.lit 3))] := by decide +kernel

/-- Static callbacks become direct calls; their requirements are retained for SigPasst. -/
def callbackSource : String :=
  "fn twice(x: u8) -> u8 effects {} costs <= 3 ops { return x; } " ++
  "module callback[g: fn(u8) -> u8 effects {} costs <= 8 ops] { " ++
  "fn run(x: u8) -> u8 { let value = g(x); return value; } } " ++
  "use Named = callback::[twice]; " ++
  "use Literal = callback::[fn(x: u8) -> u8 effects {} costs <= 3 ops { return x; }];"

theorem module_static_requirements_zeuge :
    ((parsedSource callbackSource).bind prepare).map (fun result => result.2.length) = .ok 2 := by decide +kernel

theorem module_literal_last_zeuge :
    (preparedSource callbackSource).map (fun items => (items.length,
      items.filterMap fun
        | .fnT sig (.block [.bind false "value" none (.call name [.variable "x"])] _) =>
          some (sig.name, name)
        | _ => none)) = .ok (4, [
          (memberName ["Named", "run"], "twice"),
          (memberName ["Literal", "run"], Generic.literalName
            "fn ( x : u8 ) -> u8 effects { } costs <= 3 ops { return x ; }")]) := by decide +kernel

/-- A module callback can itself be forwarded into a generic function. Its canonical literal
    syntax, rather than its generated internal name, crosses that phase boundary. -/
def callbackForwardSource : String :=
  "fn apply[f: fn(u8) -> u8 effects {} costs <= 8 ops](x: u8) -> u8 " ++
  "{ let value = f(x); return value; } " ++
  "module forward[g: fn(u8) -> u8 effects {} costs <= 8 ops] { " ++
  "fn run(x: u8) -> u8 { let value = apply::[g](x); return value; } } " ++
  "use A = forward::[fn(x: u8) -> u8 effects {} costs <= 3 ops { return x; }];"

theorem module_callback_forwarding_zeuge :
    ((parsedSource callbackForwardSource).bind prepare).map (fun result =>
      (existingForms result.1, result.2.length)) = .ok (true, 2) := by decide +kernel

/-- One source exercises all four phases: a generative module calls a bounded generic function,
    that instance resolves a spec call, and the pending callback literal is appended last. -/
def completeOrderSource : String :=
  "spec Copy[T] { fn copy(x: T) -> T effects {} costs <= 8 ops; } " ++
  "impl Copy[u8] { fn copy(x: u8) -> u8 effects {} costs <= 3 ops { return x; } } " ++
  "fn copy_value[T: Copy](x: T) -> T { let value = Copy::copy(x); return value; } " ++
  "module callback[g: fn(u8) -> u8 effects {} costs <= 8 ops] { " ++
  "fn run(x: u8) -> u8 { let value = copy_value::[u8](x); let answer = g(value); return answer; } } " ++
  "use A = callback::[fn(x: u8) -> u8 effects {} costs <= 3 ops { return x; }];"

theorem complete_expansion_order_zeuge :
    (preparedSource completeOrderSource).map (fun items => items.filterMap fun
      | .fnT sig _ => some sig.name
      | _ => none) = .ok ["$spec$0$copy", memberName ["A", "run"],
        Generic.instanceName ⟨"copy_value", ["u8"]⟩,
        Generic.literalName "fn ( x : u8 ) -> u8 effects { } costs <= 3 ops { return x ; }"] :=
      by decide +kernel

theorem complete_order_spec_call_zeuge :
    (preparedSource completeOrderSource).map (fun items => items.any fun
      | .fnT sig body => strEq sig.name (Generic.instanceName ⟨"copy_value", ["u8"]⟩) &&
          beqSAnw body (.block [.bind false "value" none (.call "$spec$0$copy" [.variable "x"])]
            (some (.ret (some (.variable "value")))))
      | _ => false) = .ok true := by decide +kernel

end Gabbro.Grammatik.Parser.Modules
