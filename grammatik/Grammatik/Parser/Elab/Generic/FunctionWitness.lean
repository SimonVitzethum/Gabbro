module
public import Grammatik.Parser.Elab.Generic.PipelineWitness

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
namespace Gabbro.Grammatik.Parser.Generic
open Uebersetze UebersetzeAllg UebersetzeAllg2

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The callback type and literal from the plan's apply_all example. The small wrapper isolates
    static specialization from the independent traversal and table rules. -/
def callbackType : String :=
  "fn(u32 in 0 .. 1000) -> u32 effects {} costs <= 8 ops"

def doublingLiteral : String :=
  "fn(x: u32 in 0 .. 1000) -> u32 effects {} costs <= 3 ops { return x * 2; }"

def canonicalDoublingLiteral : String :=
  "fn ( x : u32 in 0 .. 1000 ) -> u32 effects { } costs <= 3 ops { return x * 2 ; }"

def callbackTemplate : String :=
  "fn apply_all[g: " ++ callbackType ++ "]() { let doubled = g(7); } "

def literalSource : String :=
  "module callbacks { " ++ callbackTemplate ++
  "fn entry() { apply_all::[" ++ doublingLiteral ++ "](); } }"

def literalInstance : Instance := ⟨"apply_all", [canonicalDoublingLiteral]⟩

def surfaceCalls : SAnw → List String
  | .call name _ | .bind _ _ _ (.call name _) => [name]
  | .block statements _ => statements.flatMap surfaceCalls
  | _ => []

/-- Parser/AST: the last argument constructor is a complete function literal, with its own binder. -/
theorem literal_parser_zeuge :
    (functionArgument doublingLiteral).map (fun (_, arg) => match arg with
      | .literal sig body => sig.params.map Prod.fst == ["x"] &&
          beqSAnw body (.block [] (some (.ret (some
            (.bin "*" (.variable "x") (.lit 2))))))
      | _ => false) = .ok true := by kernel_rfl

theorem static_parameter_parser_zeuge :
    (parsedSource ("fn apply_all[g: " ++ callbackType ++ "]() {}" )).map (fun items =>
      match items with
      | [.fnT sig _] => match sig.generics with
        | [.function "g" (.raw _)] => true
        | _ => false
      | _ => false) = .ok true := by kernel_rfl

/-- The complete expansion has an ordinary caller, its instance with a DIRECT callback call,
    and the lifted function last. Neither a runtime parameter nor an indirect call is added. -/
theorem literal_direct_call_zeuge :
    (expandedSource literalSource).map (fun items => items.filterMap fun
      | .fnT sig body => some (sig.name, sig.params.length, surfaceCalls body)
      | _ => none) = .ok
      [("entry", 0, [instanceName literalInstance]),
       (instanceName literalInstance, 0, [literalName canonicalDoublingLiteral]),
       (literalName canonicalDoublingLiteral, 1, [])] := by kernel_rfl

/-- Actual exporter: conformance succeeds and the same direct edges survive export. -/
theorem literal_export_zeuge :
    (exportedSource literalSource).map (fun unit =>
      (unit.ptrs.length, unit.fns.map (fun fn => (fn.name, callNames fn)))) = .ok
      (0, [("entry", [instanceName literalInstance]),
        (instanceName literalInstance, [literalName canonicalDoublingLiteral]),
        (literalName canonicalDoublingLiteral, [])]) := by kernel_rfl

theorem literal_lowering_zeuge :
    (match exportedSource literalSource with
    | .ok unit => (lowerAllg unit).toOption.isSome
    | .error _ => false) = true := by kernel_rfl

/-- Named global arguments follow the same conformance and direct-call path as literals. -/
def namedCallbackSource : String :=
  "module callbacks { fn twice(x: u32 in 0 .. 1000) -> u32 { return x * 2; } " ++
  callbackTemplate ++ "fn entry() { apply_all::[twice](); } }"

theorem named_callback_zeuge :
    (exportedSource namedCallbackSource).map (fun unit => unit.fns.map callNames) =
      .ok [[], [instanceName ⟨"apply_all", ["twice"]⟩], ["twice"]] := by kernel_rfl

/-- An enclosing runtime local is unavailable to the literal, even when it is in scope at the call. -/
theorem capture_refused_zeuge :
    expandedSource ("module callbacks { " ++ callbackTemplate ++
      "fn entry(captured: u32) { apply_all::[fn(x: u32 in 0 .. 1000) -> u32 " ++
      "effects {} costs <= 3 ops { return captured; }](); } }") =
      .error "function-literal-capture: captured" := by kernel_rfl

/-- A declaration after a read does not retroactively bind that read. -/
theorem late_binding_capture_refused_zeuge :
    expandedSource ("module callbacks { " ++ callbackTemplate ++
      "fn entry() { apply_all::[fn(x: u32 in 0 .. 1000) -> u32 effects {} costs <= 3 ops " ++
      "{ let copy = captured; let captured = x; return copy; }](); } }") =
      .error "function-literal-capture: captured" := by kernel_rfl

/-- Argument and return signatures are checked against the parameter type, even if the callback
    is never called by the template body. This is the actual exporter refusal. -/
theorem nonconforming_callback_refused_zeuge :
    exportedSource ("module callbacks { fn wrong(x: u8) -> u8 { return x; } " ++
      "fn apply_all[g: " ++ callbackType ++ "]() {} " ++
      "fn entry() { apply_all::[wrong](); } }") =
      .error "static-function-signature-mismatch: wrong" := by kernel_rfl

/-- C06 retains nontrivial static interfaces; conformance is checked on concrete arguments. -/
theorem nontrivial_parameter_contract_preserved_zeuge :
    staticParameterType {} (.raw "fn(u32) -> u32 requires false effects {} costs <= 8 ops") =
      .ok (.raw "fn ( u32 ) -> u32 requires false effects { } costs <= 8 ops") := by kernel_rfl

/-- The same parsed callback and interface contract reach the actual exporter. -/
def contractedCallbackSource (post : String) : String :=
  "module callbacks { fn actual(x: u8) -> u8 requires x >= 1 " ++
  "ensures result >= 1 effects {} costs <= 3 ops { return x; } " ++
  "fn apply[g: fn(x: u8) -> u8 requires x >= 1 ensures " ++ post ++
  " effects {} costs <= 8 ops]() {} fn entry() { apply::[actual](); } }"

theorem matching_parameter_contract_zeuge :
    (exportedSource (contractedCallbackSource "result >= 1")).map (fun unit =>
      (unit.ptrs.length, unit.fns.map (·.name))) =
      .ok (0, ["actual", "entry", instanceName ⟨"apply", ["actual"]⟩]) := by kernel_rfl

/-- Structural equality cannot silently admit a stronger interface postcondition. -/
theorem nonconforming_parameter_contract_refused_zeuge :
    exportedSource (contractedCallbackSource "result >= 2") =
      .error "static-function-signature-mismatch: actual" := by kernel_rfl

/-- A literal's parameters shadow global items with the same spelling during name resolution. -/
theorem own_binder_is_not_capture_zeuge :
    (expandedSource ("module callbacks { const x: u32 = 9; " ++ callbackTemplate ++
      "fn entry() { apply_all::[" ++ doublingLiteral ++ "](); } }" )).toOption.isSome = true :=
      by decide +kernel

/-- Comparison signs in a literal body are not generic type delimiters. -/
theorem literal_comparison_parser_zeuge :
    (expandedSource ("module callbacks { fn choose[g: fn(u32) -> bool effects {} costs <= 8 ops]() {} " ++
      "fn entry() { choose::[fn(x: u32) -> bool effects {} costs <= 3 ops " ++
      "{ return x < 2; }](); } }" )).toOption.isSome = true := by kernel_rfl

/-- Source names cannot impersonate generated literal names, including literal names in another
    namespace. This synthetic AST probes the collision guard rather than lexical restrictions. -/
theorem literal_name_collision_refused_zeuge :
    appendLiterals [literalName canonicalDoublingLiteral] []
      [({ art := "", name := literalName canonicalDoublingLiteral, params := [],
          res := none, fehler := none, klauseln := [] }, .block [] none)] =
      .error "function-literal-name-collision: generated literal name is already declared" := by kernel_rfl

/-- Spec contracts expand after instantiation and before the named literal is appended. -/
theorem literal_spec_contract_zeuge :
    (expandedSource ("module callbacks { spec fn nonnegative(x: u32) -> bool = x >= 0; " ++
      callbackTemplate ++ "fn entry() { apply_all::[fn(x: u32 in 0 .. 1000) -> u32 " ++
      "requires nonnegative(x) effects {} costs <= 3 ops { return x * 2; }](); } }" )).map
      (fun items => items.any fun
        | .fnT sig _ => sig.klauseln.any (fun clause =>
          beqSKlausel clause (.needs (.bin ">=" (.variable "x") (.lit 0))))
        | _ => false) = .ok true := by kernel_rfl

/-- Forwarding a static callback to another generic function keeps its canonical argument. -/
theorem forwarded_callback_zeuge :
    (exportedSource ("module callbacks { fn twice(x: u32 in 0 .. 1000) -> u32 { return x * 2; } " ++
      callbackTemplate ++ "fn forward[h: " ++ callbackType ++ "]() { apply_all::[h](); } " ++
      "fn entry() { forward::[twice](); } }" )).map (fun unit => unit.fns.map callNames) =
      .ok [[], [instanceName ⟨"forward", ["twice"]⟩],
        [instanceName ⟨"apply_all", ["twice"]⟩], ["twice"]] := by kernel_rfl

end Gabbro.Grammatik.Parser.Generic
