module

public import Grammatik.Niedrig.Konstrukte.System.Mmu
public import Grammatik.Niedrig.Konstrukte.System.Maske
public import Grammatik.Niedrig.Konstrukte.System.Boot

@[expose] public section

namespace Gabbro.Grammatik.LowLevel.Construct

open Niedrig

variable {D : Deklaration}

/-- The continuation retains the interrupted mode and both saved stacks.
    Generated return code proves this relation; IrqDelivery never proves it. -/
structure IrqReturnDuty (interrupted current : SystemContext D) (frame : Eingang.EntryFrame)
    (mask : Bool) (masks : List Bool) (priority : Nat) (priorities : List Nat) : Prop where
  checked : IrqExitOk current frame mask masks priority priorities
  sameCore : current.privilege.kern = interrupted.privilege.kern
  savedMask : mask = (interrupted.interrupt.maske.zustand interrupted.privilege.kern).maskiert
  savedPriority : priority = (interrupted.interrupt.prio interrupted.privilege.kern).aktuell
  savedMasks : masks = (interrupted.interrupt.maske.zustand interrupted.privilege.kern).stapel
  savedPriorities : priorities = (interrupted.interrupt.prio interrupted.privilege.kern).unterbrochen
  resume : frame.privNach = interrupted.privilege.priv

/-- Install/switch is a bindCtx call with precisely the Mmu evidence name.
    The state function alone is not a privileged source operation. -/
def mmuBindingStep {Γ : Ctx} {resources : List (Res D)}
    (oracle : Orakel D) (a : Authority D) (c : SystemContext D) (names : SystemAssumptions D)
    (item : D.Ax) (args : Args D Γ resources (D.aparams item)) (env : Env D Γ)
    (before after : OwnerBindings D.Marke) (source into : Nat)
    (call : SystemCallOk a c item names.Mmu before after source into)
    {regime : Uebersetzung.Regime} {tables : Uebersetzung.Tables}
    {observed : Nat → Nat → Option (Nat × Uebersetzung.Perm)}
    (_hardware : NamedMmu names item regime tables observed)
    (roots : List Nat) (root : Nat) (ready sync : Bool)
    {rootValid synchronization : Prop} (_software : MmuInstallDuty ready sync rootValid synchronization)
    (checked : MmuInstallOk c roots root ready sync) (world : World D) :=
  systemBindingStep oracle a c item names.Mmu args env before after source into call
    (mmuInstallStep c roots root ready sync checked world).1.privilege c.interrupt world

/-- Masks reuse bindCtx and IrqDelivery's exact named boundary. No new G
    instruction constructor is needed for masking or address-space selection. -/
def maskBindingStep {Γ : Ctx} {resources : List (Res D)}
    (oracle : Orakel D) (a : Authority D) (c : SystemContext D) (names : SystemAssumptions D)
    (item : D.Ax) (args : Args D Γ resources (D.aparams item)) (env : Env D Γ)
    (before after : OwnerBindings D.Marke) (source into : Nat)
    (call : SystemCallOk a c item names.IrqDelivery before after source into)
    (mask : Bool) (checked : MaskSetOk c) (world : World D) :=
  systemBindingStep oracle a c item names.IrqDelivery args env before after source into call
    (maskSetStep c mask checked world).1.privilege
    (maskSetStep c mask checked world).1.interrupt world

def irqExitBindingStep {Γ : Ctx} {resources : List (Res D)}
    (oracle : Orakel D) (a : Authority D) (c : SystemContext D) (names : SystemAssumptions D)
    (item : D.Ax) (args : Args D Γ resources (D.aparams item)) (env : Env D Γ)
    (before after : OwnerBindings D.Marke) (source into : Nat)
    (call : SystemCallOk a c item names.IrqDelivery before after source into)
    (frame : Eingang.EntryFrame) (mask : Bool) (masks : List Bool) (priority : Nat) (priorities : List Nat)
    (interrupted : SystemContext D)
    (duty : IrqReturnDuty interrupted c frame mask masks priority priorities) (world : World D) :=
  systemBindingStep oracle a c item names.IrqDelivery args env before after source into call
    (irqExitStep c frame mask masks priority priorities duty.checked world).1.privilege
    (irqExitStep c frame mask masks priority priorities duty.checked world).1.interrupt world

/-- IRQ entry is environmental delivery, followed by the kernel's generated
    entry code. The kernel proves its installed handler table and frame code;
    only boundary delivery, masking and priority come from IrqDelivery. -/
structure IrqEntryDuty (names : SystemAssumptions D) (item : D.Ax)
    (c : SystemContext D) (frame : Eingang.EntryFrame) (handlers : HandlerTable)
    (vector handler priority : Nat)
    (delivered : Nat → Nat → Nat → Nat → Bool → Prop) : Prop where
  origin : CtxOriginOk item
  named : D.axBeleg item = some names.IrqDelivery
  declaration : ∃ source declared, Eingang.frameOf source = .ok declared ∧
    frame = irqFrameAt declared c.privilege.priv ∧ source.vektor = some (.lit vector)
  checked : IrqEnterOk c frame handlers vector handler priority
  hardware : IrqDelivery handlers c.interrupt delivered
  arrival : delivered c.privilege.kern vector handler priority true

/-- Page-table store preservation is the same typed-view theorem, with the
    class guard kept at this interface. Encoding is a separate software duty. -/
theorem pageTablePutStep_sim {P I : Type} {a : Authority D} {layout : AdressLayout D}
    {c : Context D P I} {world : World D} (simulation : ClassSimRel a layout c world)
    (view : View D) (live : view ∈ c.views) (active : c.frame = view.borrower)
    (ram : view.span.memoryClass = .ordinaryRam) (field : D.Feld view.span.table)
    (index : Int) (value : Wert D (D.typ view.span.table field))
    (resources : List (Res D)) (writes : D.Tab → Bool)
    (checked : ViewPutOk view layout field index resources writes) (held : HeldIn resources world.haelt) :
    ClassSimRel a layout c (pageTablePutStep view layout field index value resources writes checked ram world) :=
  classViewPutStep_sim simulation view live active ram field index value resources writes checked held

end Gabbro.Grammatik.LowLevel.Construct
