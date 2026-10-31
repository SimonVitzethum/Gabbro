/- Explicit configuration for the existing Stage0 runner image. This is a checked adapter,
   not semantics for boot, entrust or hardware profiles. -/
import Grammatik.Parser.Item.ElementTief

namespace Gabbro.Stage0.Profil
open Gabbro.Grammatik.Parser

/-- These values select bindings for the execution image, independently of the compiler host. -/
structure Options where
  arch : String := "x86_64"
  target : Option String := none
  deriving Repr

/-- Parse explicit image-binding options after the source and image paths. Repeated flags
    have the usual last-value-wins meaning. Unknown flags fail instead of being ignored. -/
def parseOptions : List String → Options → Except String Options
  | [], options => .ok options
  | "--arch" :: arch :: rest, options => parseOptions rest { options with arch := arch }
  | "--target" :: target :: rest, options => parseOptions rest { options with target := some target }
  | "--arch" :: [], _ => .error "--arch requires an architecture"
  | "--target" :: [], _ => .error "--target requires a target name"
  | flag :: _, _ => .error ("unknown image option: " ++ flag)

/-- The current image startup emits the x86_64 runner's syscall and thread ABI. -/
def runnerCompatible (options : Options) : Prop := options.arch = "x86_64"
instance (options : Options) : Decidable (runnerCompatible options) :=
  inferInstanceAs (Decidable (options.arch = "x86_64"))

/-- Hardware entry obligations have no implementation in the IR thread startup. An empty
    dispatch-only model entry remains available; an actual hardware obligation is never erased. -/
def checkEntry (e : SEingang) : Except String Unit := do
  if e.vektor.isSome || e.via.isSome then
    throw s!"ir: entry {e.name}: vector/interrupt routing has no Stage0 image lowering"
  if !e.regIn.isEmpty || !e.regOut.isEmpty || !e.erhaelt.isEmpty || !e.kills.isEmpty then
    throw s!"ir: entry {e.name}: register ABI has no Stage0 image lowering"
  if !e.stapel.isEmpty || e.perCpu || e.ist.isSome || e.nest.isSome then
    throw s!"ir: entry {e.name}: declared stack/nesting has no Stage0 image lowering"
  if e.arch != "x86_64" then
    throw s!"ir: entry {e.name}: architecture differs from the Stage0 runner image"

/-- Check recursively before flattening can hide an unsupported declaration. No declarations
    are removed; frozen canonical model prerequisites remain explicit refusals. -/
def checkItems : Nat → List SItemTief → Except String Unit
  | 0, _ => .error "ir: profile validation nesting limit"
  | _ + 1, [] => .ok ()
  | fuel + 1, it :: rest => do
    match it with
    | .modT _ body => checkItems fuel body
    | .pubT body => checkItems fuel [body]
    | .entryT e => checkEntry e
    | .bootT .. => throw "ir: boot is outside userspace compilation"
    | .trustT .. => throw "ir: entrust: canonical source-to-G guest entry semantics missing"
    | .profT .. => throw "ir: profile: canonical source-to-goal profile binding missing"
    | .gateT .. => throw "ir: when TESTBUILD: canonical conditional selection proof missing"
    | _ => pure ()
    checkItems fuel rest

/-- An accepted input carries both exact syntax preservation and the runner ABI check. -/
structure Prepared (options : Options) (items : List SItemTief) where
  selected : List SItemTief
  unchanged : selected = items
  compatible : runnerCompatible options

def prepareItems (options : Options) (items : List SItemTief) :
    Except String (Prepared options items) := do
  if h : runnerCompatible options then
    checkItems 100000 items
    pure ⟨items, rfl, h⟩
  else throw s!"ir: architecture {options.arch}: no compatible Stage0 runner image ABI"

/-- Any canonical elaborator, root extractor, linker or image compiler sees the original input. -/
theorem prepareItems_preserves {options : Options} {items : List SItemTief}
    (result : Prepared options items) {α : Sort _} (consumer : List SItemTief → α) :
    consumer result.selected = consumer items := by rw [result.unchanged]

/-- Selecting gate bindings from an accepted configuration cannot silently change the image ISA. -/
theorem prepareItems_arch {options : Options} {items : List SItemTief}
    (result : Prepared options items) : options.arch = "x86_64" := result.compatible

/-- Joint witness: a real target declaration survives validation, and its binding
    architecture is exactly the existing image architecture. -/
theorem prepareItems_preserves_zeuge :
    ∃ result : Prepared {} [.goalT "userspace" none],
      prepareItems {} [.goalT "userspace" none] = .ok result ∧
      result.selected = [.goalT "userspace" none] ∧ runnerCompatible ({} : Options) :=
  ⟨⟨[.goalT "userspace" none], rfl, rfl⟩, rfl, rfl, rfl⟩

end Gabbro.Stage0.Profil
