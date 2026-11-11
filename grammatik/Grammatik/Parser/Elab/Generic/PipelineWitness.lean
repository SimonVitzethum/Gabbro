module
public import Grammatik.Parser.Elab.Generic.ClosureWitness
public import Grammatik.Parser.Elab.Generic.Expansion
public import Grammatik.Parser.Elab.UebersetzeAllg3
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
set_option maxHeartbeats 2000000

/-- A complete body, including a local type annotation, is shared by two distinct instantiations. -/
def pipelineSource : String :=
  "module generic_probe { fn identity[T](x: T) -> T { let copy: T = x; return copy; } " ++
  "fn byte_use(x: u8) -> u8 { let value = identity::[u8](x); return value; } " ++
  "fn word_use(x: u16) -> u16 { let value = identity::[u16](x); return value; } }"

def parsedSource (text : String) : Except String (List SItemTief) := do
  let ts ← tokens text
  parseTopTief ts

def expandedSource (text : String) : Except String (List SItemTief) := do
  let source ← parsedSource text
  expand (uMembers (pre108 source))

/-- This is the actual canonical exporter entry, not a fixture-only instantiation helper. -/
def exportedSource (text : String) : Except String UProg := do
  let source ← parsedSource text
  elabU (pre108 source)

def byteInstance : Instance := ⟨"identity", ["u8"]⟩
def wordInstance : Instance := ⟨"identity", ["u16"]⟩

def instanceBody (ty : STyp) : SAnw :=
  .block [.bind false "copy" (some ty) (.variable "x")]
    (some (.ret (some (.variable "copy"))))

def instanceItem (key : Instance) (ty : STyp) : SItemTief :=
  .fnT { art := "", name := instanceName key, params := [("x", ty)],
          res := some ty, fehler := none, klauseln := [] } (instanceBody ty)

def callerItem (name : String) (ty : STyp) (key : Instance) : SItemTief :=
  .fnT { art := "", name, params := [("x", ty)], res := some ty,
          fehler := none, klauseln := [] }
    (.block [.bind false "value" none (.call (instanceName key) [.variable "x"])]
      (some (.ret (some (.variable "value")))))

/-- Exact complete output: both rewritten callers, both concrete bodies, no template declaration. -/
theorem full_body_two_types_zeuge :
    (expandedSource pipelineSource).map (fun actual => beqSItemTiefList actual
      [callerItem "byte_use" (.atom "u8") byteInstance,
       callerItem "word_use" (.atom "u16") wordInstance,
       instanceItem byteInstance (.atom "u8"), instanceItem wordInstance (.atom "u16")]) =
      .ok true := by decide +kernel

/-- The syntactic theorem is inhabited by the same complete source program. -/
theorem expand_ordinary_zeuge :
    (expandedSource pipelineSource).map (fun target => target.any genericHeader) = .ok false := by
  decide +kernel

/-- The canonical exporter sees four concrete functions and direct calls to the two instances. -/
theorem exporter_two_types_zeuge :
    (exportedSource pipelineSource).map (fun unit =>
      (unit.fns.map (fun fn => (fn.name, fn.params.map Prod.snd)),
       unit.fns.map (fun fn => fn.body.filterMap fun
         | .bindCall _ target _ => some target
         | _ => none))) =
      .ok ([("byte_use", [.int 0 255]), ("word_use", [.int 0 65535]),
        (instanceName byteInstance, [.int 0 255]), (instanceName wordInstance, [.int 0 65535])],
        [[instanceName byteInstance], [instanceName wordInstance], [], []]) := by decide +kernel

/-- Ordinary generic lowering consumes the same exported function bodies. -/
theorem lowering_two_types_zeuge :
    (match exportedSource pipelineSource with
    | .ok unit => (lowerAllg unit).toOption.isSome
    | .error _ => false) = true := by decide +kernel

/-- A constant expression is evaluated before it becomes part of the deterministic instance key. -/
def constantSource : String :=
  "module generic_constant { fn limit[N: u64]() -> u64 { return N; } " ++
  "fn use_limit() -> u64 { let value = limit::[3 + 5](); return value; } }"

theorem constant_body_zeuge :
    (expandedSource constantSource).map (fun items => items.filterMap fun
      | .fnT sig (.block [] (some (.ret (some (.lit n))))) => some (sig.name, n)
      | _ => none) = .ok [(instanceName ⟨"limit", ["8"]⟩, 8)] := by kernel_rfl

/-- Generic calls are available as statements too, without adding a runtime instruction form. -/
def statementSource : String :=
  "module generic_statement { fn consume[T](x: T) { let copy: T = x; } " ++
  "fn use_value(x: u8) { consume::[u8](x); } }"

theorem statement_call_zeuge :
    (expandedSource statementSource).map (fun items => items.filterMap fun
      | .fnT _ (.block [.call name [.variable "x"]] none) => some name
      | _ => none) = .ok [instanceName ⟨"consume", ["u8"]⟩] := by kernel_rfl

theorem explicit_arguments_required_zeuge :
    expandedSource ("module m { fn identity[T](x: T) -> T { return x; } " ++
      "fn use_value(x: u8) -> u8 { let value = identity(x); return value; } }") =
      .error "generic call requires explicit ::[arguments]: identity" := by kernel_rfl

theorem argument_count_refused_zeuge :
    expandedSource ("module m { fn identity[T](x: T) -> T { return x; } " ++
      "fn use_value(x: u8) -> u8 { let value = identity::[u8, u16](x); return value; } }") =
      .error "generic argument count does not match declaration" := by kernel_rfl

/-- A finite change of instance arguments along a recursive edge is still polymorphic recursion. -/
theorem polymorphic_recursion_refused_zeuge :
    expandedSource ("module m { fn recur[T]() { recur::[u16](); } " ++
      "fn use_value() { recur::[u8](); } }") =
      .error "polymorphic generic recursion is refused" := by kernel_rfl

/-- The declaration spelling requested by the owner retains both parameter kinds in the AST. -/
theorem mixed_parameter_parser_zeuge :
    (parsedSource "fn sample[T, N: u64](xs: [T; N]) { }").map (fun items =>
      match items with
      | [.fnT sig _] => beqSGenericParams sig.generics
          [.type "T" [], .constant "N" (.atom "u64")]
      | _ => false) = .ok true := by decide +kernel

end Gabbro.Grammatik.Parser.Generic
