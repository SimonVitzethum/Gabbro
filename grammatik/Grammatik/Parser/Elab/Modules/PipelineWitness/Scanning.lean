module
public import Grammatik.Parser.Elab.Modules.PipelineWitness.Data
import all Grammatik.Parser.Elab.Modules.Witness.Scanning

namespace Gabbro.Grammatik.Parser.Modules.PipelinePhases
open scoped Gabbro.Grammatik.Parser.UebersetzeProben11.Phases

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

-- The original lexer infers every token and step count. Source concatenations
-- retain the original spelling and character-count fuel, using existing chunks.

rights_cut generic0 as "module box[T] { fn identity[U](x: U) -> U { return x; } "
bound_fragment generic0 as "module box[T] { fn identity[U](x: U) -> U { return x; } "
rights_cut generic1 as "fn value(x: T) -> T { let copy = identity::[T](x); return copy; } } "
bound_fragment generic1 as "fn value(x: T) -> T { let copy = identity::[T](x); return copy; } } "
rights_cut generic2 as "use Bytes = box::[u8];"
bound_fragment generic2 as "use Bytes = box::[u8];"

rights_input genericInput : genericModuleSource
  with_cuts [generic0, generic1, generic2]
  with_text ["module box[T] { fn identity[U](x: U) -> U { return x; } ", "fn value(x: T) -> T { let copy = identity::[T](x); return copy; } } ", "use Bytes = box::[u8];"]

rights_cut caller0 as " fn send(t: index into Tasks) or Full effects { "
bound_fragment caller0 as " fn send(t: index into Tasks) or Full effects { "
rights_cut caller1 as "writes Jobs::Items, writes Jobs::top } "
bound_fragment caller1 as "writes Jobs::Items, writes Jobs::top } "
rights_cut caller2 as "costs <= 20 ops { Jobs::push(t); return; }"
bound_fragment caller2 as "costs <= 20 ops { Jobs::push(t); return; }"

rights_input callerInput : callerSource
  with_cuts [WitnessPhases.preamble0, WitnessPhases.preamble1, WitnessPhases.preamble2, WitnessPhases.template0, WitnessPhases.template1, WitnessPhases.template2, WitnessPhases.template3, WitnessPhases.template4, WitnessPhases.template5, WitnessPhases.template6, WitnessPhases.template7, WitnessPhases.template8, WitnessPhases.jobs, caller0, caller1, caller2]
  with_text ["table Tasks count 128 { slot { v: u8, } } ", "reason Full { full = 1 \"full\" exhaustive } ", "reason Empty { empty = 1 \"empty\" exhaustive } ", "module stack[T, N: const u32 in 1 .. 65536] { ", "table Items count N { slot { v: T, } } ", "static mut top: u32 in 0 .. N = 0; ", "pub fn push(x: T) or Full effects { ", "writes Items, writes top } costs <= 12 ops ", "{ Items[0].v = x; top = 1; return; } ", "pub fn pop() -> T or Empty effects { ", "reads Items, writes top } costs <= 10 ops ", "{ top = 0; return Items[0].v; } } ", "use Jobs = stack::[index into Tasks, 64];", " fn send(t: index into Tasks) or Full effects { ", "writes Jobs::Items, writes Jobs::top } ", "costs <= 20 ops { Jobs::push(t); return; }"]

rights_cut lexical0 as "module definition { const K: u8 = 3; "
bound_fragment lexical0 as "module definition { const K: u8 = 3; "
rights_cut lexical1 as "module sample[T] { fn read() -> u8 { return K; } } } "
bound_fragment lexical1 as "module sample[T] { fn read() -> u8 { return K; } } } "
rights_cut lexical2 as "module client { const K: u8 = 7; "
bound_fragment lexical2 as "module client { const K: u8 = 7; "
rights_cut lexical3 as "use A = definition::sample::[u8]; }"
bound_fragment lexical3 as "use A = definition::sample::[u8]; }"

rights_input lexicalInput : lexicalSource
  with_cuts [lexical0, lexical1, lexical2, lexical3]
  with_text ["module definition { const K: u8 = 3; ", "module sample[T] { fn read() -> u8 { return K; } } } ", "module client { const K: u8 = 7; ", "use A = definition::sample::[u8]; }"]

rights_cut callback0 as "fn twice(x: u8) -> u8 effects {} costs <= 3 ops { return x; } "
bound_fragment callback0 as "fn twice(x: u8) -> u8 effects {} costs <= 3 ops { return x; } "
rights_cut callback1 as "module callback[g: fn(u8) -> u8 effects {} costs <= 8 ops] { "
bound_fragment callback1 as "module callback[g: fn(u8) -> u8 effects {} costs <= 8 ops] { "
rights_cut callback2 as "fn run(x: u8) -> u8 { let value = g(x); return value; } } "
bound_fragment callback2 as "fn run(x: u8) -> u8 { let value = g(x); return value; } } "
rights_cut callback3 as "use Named = callback::[twice]; "
bound_fragment callback3 as "use Named = callback::[twice]; "
rights_cut callback4 as "use Literal = callback::[fn(x: u8) -> u8 effects {} "
bound_fragment callback4 as "use Literal = callback::[fn(x: u8) -> u8 effects {} "
rights_cut callback5 as "costs <= 3 ops { return x; }];"
bound_fragment callback5 as "costs <= 3 ops { return x; }];"

rights_input callbackInput : callbackSource
  with_cuts [callback0, callback1, callback2, callback3, callback4, callback5]
  with_text ["fn twice(x: u8) -> u8 effects {} costs <= 3 ops { return x; } ", "module callback[g: fn(u8) -> u8 effects {} costs <= 8 ops] { ", "fn run(x: u8) -> u8 { let value = g(x); return value; } } ", "use Named = callback::[twice]; ", "use Literal = callback::[fn(x: u8) -> u8 effects {} ", "costs <= 3 ops { return x; }];"]

rights_cut forward0 as "fn apply[f: fn(u8) -> u8 effects {} costs <= 8 ops](x: u8) -> u8 "
bound_fragment forward0 as "fn apply[f: fn(u8) -> u8 effects {} costs <= 8 ops](x: u8) -> u8 "
rights_cut forward1 as "{ let value = f(x); return value; } "
bound_fragment forward1 as "{ let value = f(x); return value; } "
rights_cut forward2 as "module forward[g: fn(u8) -> u8 effects {} costs <= 8 ops] { "
bound_fragment forward2 as "module forward[g: fn(u8) -> u8 effects {} costs <= 8 ops] { "
rights_cut forward3 as "fn run(x: u8) -> u8 { let value = apply::[g](x); return value; } } "
bound_fragment forward3 as "fn run(x: u8) -> u8 { let value = apply::[g](x); return value; } } "
rights_cut forward4 as "use A = forward::[fn(x: u8) -> u8 effects {} costs <= 3 ops { return x; }];"
bound_fragment forward4 as "use A = forward::[fn(x: u8) -> u8 effects {} costs <= 3 ops { return x; }];"

rights_input forwardInput : callbackForwardSource
  with_cuts [forward0, forward1, forward2, forward3, forward4]
  with_text ["fn apply[f: fn(u8) -> u8 effects {} costs <= 8 ops](x: u8) -> u8 ", "{ let value = f(x); return value; } ", "module forward[g: fn(u8) -> u8 effects {} costs <= 8 ops] { ", "fn run(x: u8) -> u8 { let value = apply::[g](x); return value; } } ", "use A = forward::[fn(x: u8) -> u8 effects {} costs <= 3 ops { return x; }];"]

rights_cut complete0 as "spec Copy[T] { fn copy(x: T) -> T effects {} costs <= 8 ops; } "
bound_fragment complete0 as "spec Copy[T] { fn copy(x: T) -> T effects {} costs <= 8 ops; } "
rights_cut complete1 as "impl Copy[u8] { fn copy(x: u8) -> u8 effects {} "
bound_fragment complete1 as "impl Copy[u8] { fn copy(x: u8) -> u8 effects {} "
rights_cut complete2 as "costs <= 3 ops { return x; } } "
bound_fragment complete2 as "costs <= 3 ops { return x; } } "
rights_cut complete3 as "fn copy_value[T: Copy](x: T) -> T { let value = Copy::copy(x); return value; } "
bound_fragment complete3 as "fn copy_value[T: Copy](x: T) -> T { let value = Copy::copy(x); return value; } "
rights_cut complete4 as "module callback[g: fn(u8) -> u8 effects {} costs <= 8 ops] { "
bound_fragment complete4 as "module callback[g: fn(u8) -> u8 effects {} costs <= 8 ops] { "
rights_cut complete5 as "fn run(x: u8) -> u8 { let value = copy_value::[u8](x); "
bound_fragment complete5 as "fn run(x: u8) -> u8 { let value = copy_value::[u8](x); "
rights_cut complete6 as "let answer = g(value); return answer; } } "
bound_fragment complete6 as "let answer = g(value); return answer; } } "
rights_cut complete7 as "use A = callback::[fn(x: u8) -> u8 effects {} costs <= 3 ops { return x; }];"
bound_fragment complete7 as "use A = callback::[fn(x: u8) -> u8 effects {} costs <= 3 ops { return x; }];"

rights_input completeInput : completeOrderSource
  with_cuts [complete0, complete1, complete2, complete3, complete4, complete5, complete6, complete7]
  with_text ["spec Copy[T] { fn copy(x: T) -> T effects {} costs <= 8 ops; } ", "impl Copy[u8] { fn copy(x: u8) -> u8 effects {} ", "costs <= 3 ops { return x; } } ", "fn copy_value[T: Copy](x: T) -> T { let value = Copy::copy(x); return value; } ", "module callback[g: fn(u8) -> u8 effects {} costs <= 8 ops] { ", "fn run(x: u8) -> u8 { let value = copy_value::[u8](x); ", "let answer = g(value); return answer; } } ", "use A = callback::[fn(x: u8) -> u8 effects {} costs <= 3 ops { return x; }];"]

rights_cut reason0 as "reason R { Empty = 1 \"empty\" exhaustive } "
bound_fragment reason0 as "reason R { Empty = 1 \"empty\" exhaustive } "
rights_cut reason1 as "spec Copy[T] { fn copy(x: T) -> T or R effects {} costs <= 8 ops; } "
bound_fragment reason1 as "spec Copy[T] { fn copy(x: T) -> T or R effects {} costs <= 8 ops; } "
rights_cut reason2 as "impl Copy[u8] { fn copy(x: u8) -> u8 or R effects {} "
bound_fragment reason2 as "impl Copy[u8] { fn copy(x: u8) -> u8 or R effects {} "
rights_cut reason3 as "costs <= 3 ops { return x; } } "
bound_fragment reason3 as "costs <= 3 ops { return x; } } "
rights_cut reason4 as "fn forward[T: Copy](x: T) -> T or R { "
bound_fragment reason4 as "fn forward[T: Copy](x: T) -> T or R { "
rights_cut reason5 as "let value = Copy::copy(x) ?; return value; } "
bound_fragment reason5 as "let value = Copy::copy(x) ?; return value; } "
rights_cut reason6 as "fn entry(x: u8) -> u8 or R { let value = forward::[u8](x) ?; return value; }"
bound_fragment reason6 as "fn entry(x: u8) -> u8 or R { let value = forward::[u8](x) ?; return value; }"

rights_input reasonInput : reasonOrderSource
  with_cuts [reason0, reason1, reason2, reason3, reason4, reason5, reason6]
  with_text ["reason R { Empty = 1 \"empty\" exhaustive } ", "spec Copy[T] { fn copy(x: T) -> T or R effects {} costs <= 8 ops; } ", "impl Copy[u8] { fn copy(x: u8) -> u8 or R effects {} ", "costs <= 3 ops { return x; } } ", "fn forward[T: Copy](x: T) -> T or R { ", "let value = Copy::copy(x) ?; return value; } ", "fn entry(x: u8) -> u8 or R { let value = forward::[u8](x) ?; return value; }"]

end Gabbro.Grammatik.Parser.Modules.PipelinePhases
