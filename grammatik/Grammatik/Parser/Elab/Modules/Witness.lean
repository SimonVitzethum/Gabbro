module
public import Grammatik.Parser.Elab.Modules.Frontend
public import Grammatik.Parser.Print.Item

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

def parsedSource (text : String) : Except String (List SItemTief) := do
  parseTopTief (← Generic.tokens text)

def expandedSource (text : String) : Except String (List SItemTief) := do
  expand (← parsedSource text)

/-- The plan's stack fixture, with explicit ordinary static initialization and complete bodies.
    Inclusive ranges retain the existing `..` spelling. This fixture tests instantiation, not a
    claim that these minimal bodies implement a complete container specification. -/
def stackTemplateSource : String :=
  "module stack[T, N: const u32 in 1 .. 65536] { " ++
  "table Items count N { slot { v: T, } } " ++
  "static mut top: u32 in 0 .. N = 0; " ++
  "pub fn push(x: T) or Full effects { writes Items, writes top } costs <= 12 ops " ++
  "{ Items[0].v = x; top = 1; return; } " ++
  "pub fn pop() -> T or Empty effects { reads Items, writes top } costs <= 10 ops " ++
  "{ top = 0; return Items[0].v; } } "

def stackPreamble : String :=
  "table Tasks count 128 { slot { v: u8, } } " ++
  "reason Full { full = 1 \"full\" exhaustive } " ++
  "reason Empty { empty = 1 \"empty\" exhaustive } "

def stackSource : String := stackPreamble ++ stackTemplateSource ++
  "use Jobs = stack::[index into Tasks, 64];"

def indexField : SFeld :=
  { fname := "v", ftyp := .index false "Tasks", pos := none, bezug := none,
    wo := none, reserviert := false, byOps := false }

def itemsTable (alias : String) : SItemTief :=
  .tableT (memberName [alias, "Items"]) none (some (.lit 64)) none none false [.tSlot [indexField]]

def topStatic (alias : String) : SItemTief :=
  .globT true (memberName [alias, "top"]) (.range (.atom "u32") (.lit 0) (.lit 64) false)
    (.one (.lit 0)) none none false

def pushSignature (alias : String) : FnSig :=
  { art := "", name := memberName [alias, "push"], params := [("x", .index false "Tasks")],
    res := none, fehler := some "Full", klauseln := [
      .effs [.writes (.variable (memberName [alias, "Items"])),
             .writes (.variable (memberName [alias, "top"]))], .cost (.lit 12)] }

def popSignature (alias : String) : FnSig :=
  { art := "", name := memberName [alias, "pop"], params := [], res := some (.index false "Tasks"),
    fehler := some "Empty", klauseln := [
      .effs [.reads (.variable (memberName [alias, "Items"])),
             .writes (.variable (memberName [alias, "top"]))], .cost (.lit 10)] }

def hasSignature (expected : FnSig) (items : List SItemTief) : Bool :=
  items.any fun
    | .fnT actual _ => beqFnSig actual expected
    | _ => false

/-- The actual parameter and argument parsers are shared with generic functions. -/
theorem module_parameters_parser_zeuge :
    (parsedSource stackTemplateSource).map (fun items => match items with
      | [.moduleTemplateT "stack" params _] => beqSGenericParams params
          [.type "T" [], .constant "N" (.range (.atom "u32") (.lit 1) (.lit 65536) false)]
      | _ => false) = .ok true := by decide +kernel

theorem use_alias_parser_zeuge :
    (parsedSource "pub use Jobs = stack::[index into Tasks, 64];").map (fun items =>
      beqSItemTiefList items [.pubT (.moduleUseT "Jobs" ["stack"] ["index into Tasks", "64"])]) =
      .ok true := by decide +kernel

theorem module_use_roundtrip_zeuge :
    rundlaufItem (.moduleUseT "Jobs" ["containers", "stack"] ["index into Tasks", "64"]) = true := by
  decide +kernel

/-- The table count is 64 and its actual field type is the supplied nominal index type. -/
theorem stack_table_zeuge :
    (expandedSource stackSource).map (fun items => items.any (beqSItemTief (itemsTable "Jobs"))) =
      .ok true := by decide +kernel

theorem stack_static_zeuge :
    (expandedSource stackSource).map (fun items => items.any (beqSItemTief (topStatic "Jobs"))) =
      .ok true := by decide +kernel

/-- Both signatures, their reason channels, costs and memory effects survive substitution. -/
theorem stack_functions_zeuge :
    (expandedSource stackSource).map (fun items =>
      hasSignature (pushSignature "Jobs") items && hasSignature (popSignature "Jobs") items) =
      .ok true := by decide +kernel

def twoUsesSource : String := stackSource ++ " use Other = stack::[index into Tasks, 64];"

/-- Equal module arguments are deliberately not memoized: each use owns all its storage. -/
theorem two_uses_disjoint_tables_zeuge :
    (expandedSource twoUsesSource).map (fun items => items.filterMap fun
      | .tableT name _ _ _ _ _ _ _ => some name
      | _ => none) =
      .ok ["Tasks", memberName ["Jobs", "Items"], memberName ["Other", "Items"]] := by decide +kernel

theorem two_uses_disjoint_statics_zeuge :
    (expandedSource twoUsesSource).map (fun items => items.filterMap fun
      | .globT _ name _ _ _ _ _ => some name
      | _ => none) = .ok [memberName ["Jobs", "top"], memberName ["Other", "top"]] := by decide +kernel

theorem two_uses_disjoint_functions_zeuge :
    (expandedSource twoUsesSource).map (fun items => items.filterMap fun
      | .fnT sig _ => some sig.name
      | _ => none) = .ok [memberName ["Jobs", "push"], memberName ["Jobs", "pop"],
        memberName ["Other", "push"], memberName ["Other", "pop"]] := by decide +kernel

theorem instance_names_disjoint_zeuge :
    (memberName ["Jobs", "Items"] == memberName ["Other", "Items"]) = false := by decide +kernel

/-- A recursive application would allocate fresh storage forever, even with unchanged arguments. -/
theorem recursive_module_refused_zeuge :
    expandedSource ("module loop[T] { use Again = loop::[T]; } " ++
      "use Start = loop::[u8];") = .error "parametric-module-recursion: loop" := by rfl

theorem alias_collision_refused_zeuge :
    expandedSource ("module empty[T] { } use A = empty::[u8]; use A = empty::[u8];") =
      .error "parametric-module-alias-collision: A" := by rfl

/-- The collision gate also protects against a declaration supplied directly as surface AST. -/
theorem generated_name_collision_refused_zeuge :
    expand [.constT (memberName ["A", "v"]) (.atom "u8") (.one (.lit 0)),
      .moduleTemplateT "m" [.type "T" []]
        [.globT false "v" (.atom "T") (.one (.lit 0)) none none false],
      .moduleUseT "A" ["m"] ["u8"]] =
        .error "parametric-module-name-collision: generated name is already declared" := by rfl

theorem constant_range_refused_zeuge :
    expandedSource (stackPreamble ++ stackTemplateSource ++
      "use Bad = stack::[index into Tasks, 0];") =
        .error "generic constant argument: C17 evaluation failed or exceeded its bound" := by rfl

end Gabbro.Grammatik.Parser.Modules
