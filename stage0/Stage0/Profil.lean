/- Explicit configuration for the existing Stage0 runner image. This is a checked adapter,
   not semantics for boot, entrust or hardware profiles. -/
module
public import Grammatik.Parser.Profil.Auswahl
public import Grammatik.Parser.Profil.Pipeline
public import Grammatik.Parser.Profil.Register
public import Grammatik.Parser.Profil.Eintritt
public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Lauf.Consumer
@[expose] public section


namespace Gabbro.Stage0.Profil
open Gabbro.Grammatik.Parser

/-- These values select bindings for the execution image, independently of the compiler host. -/
structure Options where
  arch : String := "x86_64"
  target : Option String := none
  mode : Auswahl.BauModus := .auslieferung
  checkConsumer : Option Uebersetze.CheckConsumerSelection := none
  deriving Repr

/-- Parse explicit image-binding options after the source and image paths. Repeated flags
    have the usual last-value-wins meaning. Unknown flags fail instead of being ignored. -/
def parseOptions : List String → Options → Except String Options
  | [], options => .ok options
  | "--testbuild" :: rest, options => parseOptions rest { options with mode := .pruefbau }
  | "--check" :: check :: gate :: rest, options =>
    parseOptions rest { options with checkConsumer := some ⟨check, gate⟩ }
  | "--check" :: _, _ => .error "--check requires a check and one declared gate"
  | "--arch" :: arch :: rest, options => parseOptions rest { options with arch := arch }
  | "--target" :: target :: rest, options => parseOptions rest { options with target := some target }
  | "--arch" :: [], _ => .error "--arch requires an architecture"
  | "--target" :: [], _ => .error "--target requires a target name"
  | flag :: _, _ => .error ("unknown image option: " ++ flag)

/-- An explicit test-driver image enters one selected producer/consumer
    cycle. Source-only declarations still do not execute a check. -/
def entryName (options : Options) : String :=
  match options.checkConsumer with
  | none => "main"
  | some selection => Uebersetze.driverFnName selection.check selection.gate

/-- Selection runs after canonical profile/build selection and elaboration,
    before declaration lowering. Removed test-only checks cannot be selected. -/
def selectUnit (options : Options) (unit : Uebersetze.UProg) : Except String Uebersetze.UProg :=
  match options.checkConsumer with
  | none => .ok unit
  | some selection =>
    Uebersetze.uSelectCheckConsumers
      { unit with checks := unit.checks.map fun c =>
          { c with testbau := decide (options.mode = .pruefbau) } } [selection]

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
    are removed; frozen canonical model prerequisites remain explicit refusals. Admitted profile
    blocks never reach this check: `prepareItems` strips them after admission (their content lives
    in the checked binding), so the `profT` arm below only fires for direct callers. -/
def checkItems : Nat → List SItemTief → Except String Unit
  | 0, _ => .error "ir: profile validation nesting limit"
  | _ + 1, [] => .ok ()
  | fuel + 1, it :: rest => do
    match it with
    | .modT _ body => checkItems fuel body
    | .pubT body => checkItems fuel [body]
    | .entryT e => checkEntry e
    | .bootT .. => throw "ir: boot is outside userspace compilation"
    | .trustT _ _ arch regs stack assumption service =>
      ProfilBindung.gastQuellePruefung arch regs stack assumption service
    | .profT .. => throw "ir: profile: canonical source-to-goal profile binding missing"
    | .gateT .. => throw "ir: when TESTBUILD: canonical conditional selection proof missing"
    | _ => pure ()
    checkItems fuel rest

mutual
/-- A named section has no Stage-0 image relocation policy: the runner image is flat,
    so every static with a `section` is refused by name. Alignment without a section
    is laid out on the common grid (`Senke.globStarts`) and needs no policy. -/
def abschnittFehlerI (modul : List String) : SItemTief → Option String
  | .modT n b => abschnittFehlerL (modul ++ [n]) b
  | .pubT it => abschnittFehlerI modul it
  | .gateT it => abschnittFehlerI modul it
  | .globT _ n _ _ _ sec _ =>
    match sec with
    | none => none
    | some s => some s!"ir: section \"{s}\" of global {String.intercalate "." (modul ++ [n])} has no Stage0 image relocation policy"
  | _ => none
def abschnittFehlerL (modul : List String) : List SItemTief → Option String
  | [] => none
  | it :: rest =>
    match abschnittFehlerI modul it with
    | some e => some e
    | none => abschnittFehlerL modul rest
end

/-- The first named section of the tree, if any. -/
def abschnittFehler : List SItemTief → Option String := abschnittFehlerL []

/-- An accepted input carries exact canonical build selection, the checked profile
    binding of the selected tree (`ProfileBinding`, admitted by `bindungB`) with no
    named sections, and the runner ABI check. The elaborator sees `elaborierbar`:
    the selected tree without its admitted profile blocks. -/
structure Prepared (options : Options) (items : List SItemTief) where
  selected : List SItemTief
  selection : selected = Auswahl.waehleL options.mode items
  admitted : Auswahl.reserviertL items = false
  compatible : runnerCompatible options
  bindung : ProfilBindung.ProfileBinding
  bindungOk : ProfilBindung.bindungB bindung = true
  abschnittFrei : abschnittFehler selected = none

/-- The tree the elaborator sees: the selected tree without its admitted profile blocks.
    Their content lives in the checked binding (`bindung`), not in the elaborated unit
    (`ProfilBindung.ohneProfilL`: profiles are metadata, as in `uebersetzeWahlItems`). -/
def Prepared.elaborierbar {options : Options} {items : List SItemTief}
    (result : Prepared options items) : List SItemTief :=
  ProfilBindung.ohneProfilL result.selected

/-- The elaborated tree is the stripped canonical selection. -/
theorem Prepared.elaborierbar_eq {options : Options} {items : List SItemTief}
    (result : Prepared options items) :
    result.elaborierbar = ProfilBindung.ohneProfilL (Auswahl.waehleL options.mode items) := by
  unfold Prepared.elaborierbar
  rw [result.selection]

def prepareItems (options : Options) (items : List SItemTief) :
    Except String (Prepared options items) := do
  if h : runnerCompatible options then
    if reserved : Auswahl.reserviertL items = false then
      let selected := Auswahl.waehleL options.mode items
      if hb : ProfilBindung.bindungB (ProfilBindung.ProfileBinding.aus selected) then
        match he : abschnittFehler selected with
        | some e => throw e
        | none =>
          checkItems 100000 (ProfilBindung.ohneProfilL selected)
          pure ⟨selected, rfl, reserved, h, ProfilBindung.ProfileBinding.aus selected, hb, he⟩
      else throw "ir: profile binding refused: modes, assumptions or library requirements are not consistent"
    else throw "build selection: TESTBUILD is reserved (G003)"
  else throw s!"ir: architecture {options.arch}: no compatible Stage0 runner image ABI"

/-- Any canonical elaborator, root extractor, linker or image compiler sees the canonically selected input. -/
theorem prepareItems_preserves {options : Options} {items : List SItemTief}
    (result : Prepared options items) {α : Sort _} (consumer : List SItemTief → α) :
    consumer result.selected = consumer (Auswahl.waehleL options.mode items) := by
  rw [result.selection]

/-- Selecting gate bindings from an accepted configuration cannot silently change the image ISA. -/
theorem prepareItems_arch {options : Options} {items : List SItemTief}
    (result : Prepared options items) : options.arch = "x86_64" := result.compatible

/-- Joint witness: a real target declaration survives validation, and its binding
    architecture is exactly the existing image architecture. -/
theorem prepareItems_preserves_zeuge :
    ∃ result : Prepared {} [.goalT "userspace" none],
      prepareItems {} [.goalT "userspace" none] = .ok result ∧
      result.selected = [.goalT "userspace" none] ∧ runnerCompatible ({} : Options) :=
  ⟨⟨[.goalT "userspace" none], rfl, rfl, rfl,
    ProfilBindung.ProfileBinding.aus [.goalT "userspace" none], by decide, by decide⟩,
    rfl, rfl, rfl⟩

end Gabbro.Stage0.Profil
