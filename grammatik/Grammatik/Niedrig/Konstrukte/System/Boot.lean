module

public import Grammatik.Niedrig.Konstrukte.System.Interrupt
public import Grammatik.Niedrig.Boot.Preservation

@[expose] public section

namespace Gabbro.Grammatik.LowLevel.Construct

open Niedrig

variable {D : Deklaration}

/-- Source entry descriptors use exactly the existing checker, including its
    register, stack and clobber checks. Target-specific code-generation duties
    are software obligations and cannot be inferred from this Bool. -/
def BootEntryOk (c : SystemContext D) (declaration : Parser.SEingang) : Prop :=
  Eingang.alleOk declaration ∧ (Eingang.rahmenAus declaration).privVor = c.privilege.priv ∧
  c.views = []

instance (c : SystemContext D) (declaration : Parser.SEingang) :
    Decidable (BootEntryOk c declaration) := by
  unfold BootEntryOk
  infer_instance

def bootEntryB (c : SystemContext D) (declaration : Parser.SEingang) : Bool :=
  decide (BootEntryOk c declaration)

theorem bootEntryB_iff (c : SystemContext D) (declaration : Parser.SEingang) :
    bootEntryB c declaration = true ↔ BootEntryOk c declaration := by
  simp only [bootEntryB, decide_eq_true_eq]

/-- The FirmwareEntry identity is a unit-declared assumption. Only the
    existing FirmwareEntry proposition establishes the initial grant; a
    literal address or an entry descriptor cannot establish it. -/
structure NamedFirmwareEntry (names : SystemAssumptions D) (item : D.Ax)
    (contract : BootContract D Arch.ArchState Maske.PrioMaske)
    (a : Authority D) (c : SystemContext D) : Prop where
  origin : CtxOriginOk item
  named : D.axBeleg item = some names.FirmwareEntry
  firmware : FirmwareEntry contract a c

/-- Entry is the chosen firmware boundary, not execution of unverified boot
    code. The World and authority originate in the explicit firmware contract. -/
def firmwareEntryStep (names : SystemAssumptions D) (item : D.Ax)
    (contract : BootContract D Arch.ArchState Maske.PrioMaske)
    (a : Authority D) (c : SystemContext D) (declaration : Parser.SEingang)
    (_entry : NamedFirmwareEntry names item contract a c)
    (_checked : BootEntryOk c declaration) (world : World D) : SystemContext D × World D := (c, world)

theorem firmwareEntryStep_sim (names : SystemAssumptions D) (item : D.Ax)
    (contract : BootContract D Arch.ArchState Maske.PrioMaske)
    (a : Authority D) (c : SystemContext D) (declaration : Parser.SEingang)
    (entry : NamedFirmwareEntry names item contract a c)
    (checked : BootEntryOk c declaration) (layout : AdressLayout D) (world : World D) :
    ClassSimRel a layout (firmwareEntryStep names item contract a c declaration entry checked world).1 world := by
  apply classSimRel_of_simRel (simRel_initial entry.firmware.valid entry.firmware.noViews world)
  intro view member
  rw [entry.firmware.noViews] at member
  cases member

theorem firmwareEntryStep_descriptor {c : SystemContext D} {declaration : Parser.SEingang}
    (checked : BootEntryOk c declaration) :
    Eingang.frameOf declaration = .ok (Eingang.rahmenAus declaration) := by
  simp only [Eingang.frameOf, checked.1, ↓reduceIte]

theorem entryChecks_of_frameOf {declaration : Parser.SEingang} {frame : Eingang.EntryFrame}
    (accepted : Eingang.frameOf declaration = .ok frame) : Eingang.alleOk declaration := by
  unfold Eingang.frameOf at accepted
  split at accepted
  · assumption
  · cases accepted

/-- Boot handoff is actual fresh-grant transfer, never an assumed software
    effect. Both authority and receiving context are the canonical receipt. -/
def bootHandoffStep {a : Authority D} {c : SystemContext D} (r : HandoffResult a c) (world : World D) :
    Authority D × SystemContext D × World D := (r.authority, r.next, world)

theorem bootHandoffStep_sim {a : Authority D} {c : SystemContext D} {world : World D}
    (simulation : SimRel a c world) (r : HandoffResult a c) (layout : AdressLayout D) :
    ClassSimRel r.authority layout r.next world := by
  apply classSimRel_of_simRel (simRel_initial (handoff_preserves simulation.valid r) rfl world)
  intro view member
  cases member

theorem bootHandoffStep_root {names : SystemAssumptions D} {item : D.Ax}
    {contract : BootContract D Arch.ArchState Maske.PrioMaske}
    {a : Authority D} {c : SystemContext D} (entry : NamedFirmwareEntry names item contract a c)
    (logic : BootObligation contract) (r : HandoffResult a c)
    (transition : contract.transition a c r.authority r.next) :
    contract.root r.authority r.next ∧
    ∀ frame, ¬ r.next.owners.access a.names frame a.token :=
  ⟨boot_root_from_logic logic entry.firmware r transition,
    handoff_old_context_spent entry.firmware.valid r⟩

/-- Generated entry/exit code must preserve every register not declared as an
    output or clobber, and every explicitly preserved register. Memory effects
    require the ordinary World frame theorem independently of these registers. -/
def EntryCodeDuty (frame : Eingang.EntryFrame) (before after : String → Int) : Prop :=
  (∀ register, register ∉ frame.kills → register ∉ frame.regOut → after register = before register) ∧
  (∀ register ∈ frame.erhaelt, after register = before register)

def bootEntryFootprint : Footprint D := Footprint.empty

/-- The binding supplies the checked generated-code cost. There is no
    hardware assumption saying that user boot logic has unit cost. -/
def bootEntryCost (generated : Nat) : Nat := generated

end Gabbro.Grammatik.LowLevel.Construct
