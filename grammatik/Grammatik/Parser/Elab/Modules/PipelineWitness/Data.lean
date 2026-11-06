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

/-- Alias qualification is resolved by the same instance keys used inside the copied functions. -/
def callerSource : String := stackSource ++
  " fn send(t: index into Tasks) or Full effects { writes Jobs::Items, writes Jobs::top } " ++
  "costs <= 20 ops { Jobs::push(t); return; }"

/-- Definition-site globals remain fixed when a use appears in another ordinary module. -/
def lexicalSource : String :=
  "module definition { const K: u8 = 3; module sample[T] { fn read() -> u8 { return K; } } } " ++
  "module client { const K: u8 = 7; use A = definition::sample::[u8]; }"

/-- Static callbacks become direct calls; their requirements are retained for SigPasst. -/
def callbackSource : String :=
  "fn twice(x: u8) -> u8 effects {} costs <= 3 ops { return x; } " ++
  "module callback[g: fn(u8) -> u8 effects {} costs <= 8 ops] { " ++
  "fn run(x: u8) -> u8 { let value = g(x); return value; } } " ++
  "use Named = callback::[twice]; " ++
  "use Literal = callback::[fn(x: u8) -> u8 effects {} costs <= 3 ops { return x; }];"

/-- A module callback can itself be forwarded into a generic function. Its canonical literal
    syntax, rather than its generated internal name, crosses that phase boundary. -/
def callbackForwardSource : String :=
  "fn apply[f: fn(u8) -> u8 effects {} costs <= 8 ops](x: u8) -> u8 " ++
  "{ let value = f(x); return value; } " ++
  "module forward[g: fn(u8) -> u8 effects {} costs <= 8 ops] { " ++
  "fn run(x: u8) -> u8 { let value = apply::[g](x); return value; } } " ++
  "use A = forward::[fn(x: u8) -> u8 effects {} costs <= 3 ops { return x; }];"

/-- One source exercises all four phases: a generative module calls a bounded generic function,
    that instance resolves a spec call, then the pending callback literal is materialized.
    Final declaration desugaring appends the ordinary spec implementation body. -/
def completeOrderSource : String :=
  "spec Copy[T] { fn copy(x: T) -> T effects {} costs <= 8 ops; } " ++
  "impl Copy[u8] { fn copy(x: u8) -> u8 effects {} costs <= 3 ops { return x; } } " ++
  "fn copy_value[T: Copy](x: T) -> T { let value = Copy::copy(x); return value; } " ++
  "module callback[g: fn(u8) -> u8 effects {} costs <= 8 ops] { " ++
  "fn run(x: u8) -> u8 { let value = copy_value::[u8](x); let answer = g(value); return answer; } } " ++
  "use A = callback::[fn(x: u8) -> u8 effects {} costs <= 3 ops { return x; }];"

/-- Generic applications and concrete spec calls must resolve before reason desugaring.
    Both success values still pass through the generated fallible direct calls. -/
def reasonOrderSource : String :=
  "reason R { Empty = 1 \"empty\" exhaustive } " ++
  "spec Copy[T] { fn copy(x: T) -> T or R effects {} costs <= 8 ops; } " ++
  "impl Copy[u8] { fn copy(x: u8) -> u8 or R effects {} costs <= 3 ops { return x; } } " ++
  "fn forward[T: Copy](x: T) -> T or R { let value = Copy::copy(x) ?; return value; } " ++
  "fn entry(x: u8) -> u8 or R { let value = forward::[u8](x) ?; return value; }"

end Gabbro.Grammatik.Parser.Modules
