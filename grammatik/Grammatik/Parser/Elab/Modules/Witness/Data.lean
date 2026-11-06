module
public import Grammatik.Parser.Elab.Modules.Frontend
public import Grammatik.Parser.Print.Item

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

def twoUsesSource : String := stackSource ++ " use Other = stack::[index into Tasks, 64];"

end Gabbro.Grammatik.Parser.Modules
