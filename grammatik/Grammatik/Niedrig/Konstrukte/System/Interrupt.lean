module

public import Grammatik.Niedrig.Konstrukte.System.Basis
public import Grammatik.Niedrig.Eingang.Rahmen

@[expose] public section

namespace Gabbro.Grammatik.LowLevel.Construct

open Niedrig

variable {D : Deklaration}

/-- The kernel installs this vector-to-(handler, priority) table by proved software writes. IrqDelivery
    observes it; it is not a hardware promise that software installed it well. -/
abbrev HandlerTable := Nat → Nat → Option (Nat × Nat)

/-- Explicit named delivery boundary: instruction boundary, installed handler,
    unmasked acting core and strictly higher declared priority. -/
def IrqDelivery (handlers : HandlerTable) (state : Maske.PrioMaske)
    (delivered : Nat → Nat → Nat → Nat → Bool → Prop) : Prop :=
  ∀ core vector handler priority boundary, delivered core vector handler priority boundary →
    boundary = true ∧ handlers core vector = some (handler, priority) ∧
    (state.maske.zustand core).maskiert = false ∧
    1 ≤ priority ∧ (state.prio core).aktuell < priority

/-- Checked descriptor fields are the existing Eingang frame fields. The
    caller also retains frameOf's successful declaration as software evidence;
    a descriptor alone does not prove the generated entry code correct. -/
def IrqEnterOk (c : SystemContext D) (frame : Eingang.EntryFrame) (handlers : HandlerTable)
    (vector handler priority : Nat) : Prop :=
  frame.art = .irqEntry ∧ frame.privVor = c.privilege.priv ∧ frame.privNach = .kern ∧
  frame.maskiertBeimEintritt = true ∧
  handlers c.privilege.kern vector = some (handler, priority) ∧
  (c.interrupt.maske.zustand c.privilege.kern).maskiert = false ∧
  1 ≤ priority ∧ (c.interrupt.prio c.privilege.kern).aktuell < priority ∧
  c.views = []

instance (c : SystemContext D) (frame : Eingang.EntryFrame) (handlers : HandlerTable)
    (vector handler priority : Nat) : Decidable (IrqEnterOk c frame handlers vector handler priority) := by
  unfold IrqEnterOk
  infer_instance

def irqEnterB (c : SystemContext D) (frame : Eingang.EntryFrame) (handlers : HandlerTable)
    (vector handler priority : Nat) : Bool := decide (IrqEnterOk c frame handlers vector handler priority)

theorem irqEnterB_iff (c : SystemContext D) (frame : Eingang.EntryFrame) (handlers : HandlerTable)
    (vector handler priority : Nat) :
    irqEnterB c frame handlers vector handler priority = true ↔
      IrqEnterOk c frame handlers vector handler priority := by
  simp only [irqEnterB, decide_eq_true_eq]

/-- The source descriptor's input mode is specialized to the actually
    interrupted context. IRQs may enter from kernel or user mode; outputs,
    register/stack declarations and entry mask are preserved verbatim. The
    generated frame code must prove the saved incoming mode for return. -/
def irqFrameAt (frame : Eingang.EntryFrame) (incoming : Arch.Priv) : Eingang.EntryFrame :=
  { frame with privVor := incoming }

theorem frameOf_replaceVector (source : Parser.SEingang) (old new : Parser.SExpr)
    (present : source.vektor = some old) :
    Eingang.frameOf { source with vektor := some new } = Eingang.frameOf source := by
  cases via : source.via <;>
    simp only [Eingang.frameOf, Eingang.alleOk, Eingang.hatBeide, Eingang.artAus,
      Eingang.rahmenAus, Eingang.ersteFehler, present, via, Bool.true_eq_false, false_and,
      ↓reduceIte, Option.isSome_some]

/-- Save both mask/depth and priority. PrioStep's intermediate mask update is
    combined with MaskStep's saved-bit stack; neither state replaces the other. -/
def irqEntered (state : Maske.PrioMaske) (core priority : Nat) : Maske.PrioMaske :=
  { maske := Maske.betreteNach state.maske core
    prio := (Maske.erhoeheNach state core priority true).prio }

def irqEnterStep (c : SystemContext D) (frame : Eingang.EntryFrame) (handlers : HandlerTable)
    (vector handler priority : Nat) (_checked : IrqEnterOk c frame handlers vector handler priority)
    (world : World D) : SystemContext D × World D :=
  systemMetadataStep c { c.privilege with priv := frame.privNach, maske := true }
    (irqEntered c.interrupt c.privilege.kern priority) world

theorem irqEnterStep_mask {c : SystemContext D} {frame : Eingang.EntryFrame} {handlers : HandlerTable}
    {vector handler priority : Nat} (checked : IrqEnterOk c frame handlers vector handler priority) :
    Maske.MaskStep (.betreteHandler c.privilege.kern vector) c.interrupt.maske
      (irqEntered c.interrupt c.privilege.kern priority).maske :=
  .betrete _ _ _ checked.2.2.2.2.2.1

theorem irqEnterStep_priority {c : SystemContext D} {frame : Eingang.EntryFrame} {handlers : HandlerTable}
    {vector handler priority : Nat} (checked : IrqEnterOk c frame handlers vector handler priority) :
    Maske.PrioStep (.erhoehe c.privilege.kern priority true) c.interrupt
      (Maske.erhoeheNach c.interrupt c.privilege.kern priority true) :=
  .erhoehe _ _ _ _ checked.2.2.2.2.2.1 checked.2.2.2.2.2.2.1 checked.2.2.2.2.2.2.2.1

/-- Return restores the actual saved mask and priority. Returning with an
    empty/mismatched frame is refused. The interrupted privilege is retained
    by the entry continuation, rather than inferred from a numeric address. -/
def IrqExitOk (c : SystemContext D) (frame : Eingang.EntryFrame)
    (mask : Bool) (masks : List Bool) (priority : Nat) (priorities : List Nat) : Prop :=
  frame.art = .irqReturn ∧ c.privilege.priv = .kern ∧ c.views = [] ∧
  (c.interrupt.maske.zustand c.privilege.kern).stapel = mask :: masks ∧
  (c.interrupt.prio c.privilege.kern).unterbrochen = priority :: priorities ∧
  (c.interrupt.maske.zustand c.privilege.kern).tiefe = masks.length + 1

instance (c : SystemContext D) (frame : Eingang.EntryFrame) (mask : Bool) (masks : List Bool)
    (priority : Nat) (priorities : List Nat) :
    Decidable (IrqExitOk c frame mask masks priority priorities) := by
  unfold IrqExitOk
  infer_instance

def irqExitB (c : SystemContext D) (frame : Eingang.EntryFrame) (mask : Bool) (masks : List Bool)
    (priority : Nat) (priorities : List Nat) : Bool :=
  decide (IrqExitOk c frame mask masks priority priorities)

theorem irqExitB_iff (c : SystemContext D) (frame : Eingang.EntryFrame) (mask : Bool) (masks : List Bool)
    (priority : Nat) (priorities : List Nat) :
    irqExitB c frame mask masks priority priorities = true ↔
      IrqExitOk c frame mask masks priority priorities := by
  simp only [irqExitB, decide_eq_true_eq]

def irqExited (state : Maske.PrioMaske) (core : Nat) (mask : Bool) (masks : List Bool)
    (priority : Nat) (priorities : List Nat) : Maske.PrioMaske :=
  { maske := Maske.verlasseNach state.maske core mask masks
    prio := (Maske.senkeNach state core priority priorities).prio }

def irqExitStep (c : SystemContext D) (frame : Eingang.EntryFrame) (mask : Bool) (masks : List Bool)
    (priority : Nat) (priorities : List Nat) (_checked : IrqExitOk c frame mask masks priority priorities)
    (world : World D) : SystemContext D × World D :=
  systemMetadataStep c { c.privilege with priv := frame.privNach, maske := mask }
    (irqExited c.interrupt c.privilege.kern mask masks priority priorities) world

theorem irqExitStep_mask {c : SystemContext D} {frame : Eingang.EntryFrame}
    {mask : Bool} {masks : List Bool} {priority : Nat} {priorities : List Nat}
    (checked : IrqExitOk c frame mask masks priority priorities) :
    Maske.MaskStep (.verlasseHandler c.privilege.kern) c.interrupt.maske
      (irqExited c.interrupt c.privilege.kern mask masks priority priorities).maske :=
  .verlasse _ _ _ _ checked.2.2.2.1

theorem irqExitStep_priority {c : SystemContext D} {frame : Eingang.EntryFrame}
    {mask : Bool} {masks : List Bool} {priority : Nat} {priorities : List Nat}
    (checked : IrqExitOk c frame mask masks priority priorities) :
    Maske.PrioStep (.senke c.privilege.kern) c.interrupt
      (Maske.senkeNach c.interrupt c.privilege.kern priority priorities) :=
  .senke _ _ _ _ checked.2.2.2.2.1

theorem irqEnterStep_sim {a : Authority D} {layout : AdressLayout D} {c : SystemContext D}
    {world : World D} (simulation : ClassSimRel a layout c world) (frame : Eingang.EntryFrame)
    (handlers : HandlerTable) (vector handler priority : Nat)
    (checked : IrqEnterOk c frame handlers vector handler priority) :
    ClassSimRel a layout (irqEnterStep c frame handlers vector handler priority checked world).1 world :=
  classMetadata_sim simulation _ _

theorem irqExitStep_sim {a : Authority D} {layout : AdressLayout D} {c : SystemContext D}
    {world : World D} (simulation : ClassSimRel a layout c world) (frame : Eingang.EntryFrame)
    (mask : Bool) (masks : List Bool) (priority : Nat) (priorities : List Nat)
    (checked : IrqExitOk c frame mask masks priority priorities) :
    ClassSimRel a layout (irqExitStep c frame mask masks priority priorities checked world).1 world :=
  classMetadata_sim simulation _ _

end Gabbro.Grammatik.LowLevel.Construct
