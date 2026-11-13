module

public import Grammatik.Niedrig.Konstrukte.System.Interrupt

@[expose] public section

namespace Gabbro.Grammatik.LowLevel.Construct

open Niedrig

variable {D : Deklaration}

def MaskSetOk (c : SystemContext D) : Prop := c.privilege.priv = .kern

instance (c : SystemContext D) : Decidable (MaskSetOk c) := by
  unfold MaskSetOk
  infer_instance

def maskSetB (c : SystemContext D) : Bool := decide (MaskSetOk c)

theorem maskSetB_iff (c : SystemContext D) : maskSetB c = true ↔ MaskSetOk c := by
  simp only [maskSetB, decide_eq_true_eq]

/-- Masking is per core. It does not acquire a multicore lock, alter owner
    escrow or suppress delivery on another core. -/
def maskSetStep (c : SystemContext D) (mask : Bool) (_checked : MaskSetOk c)
    (world : World D) : SystemContext D × World D :=
  systemMetadataStep c { c.privilege with maske := mask }
    (Maske.maskeSetze c.interrupt c.privilege.kern mask) world

theorem maskSetStep_arch (c : SystemContext D) (mask : Bool) (checked : MaskSetOk c) (world : World D) :
    Arch.ArchStep (.setMask mask) c.privilege (maskSetStep c mask checked world).1.privilege :=
  .maske _ _ checked

theorem maskSetStep_mask (c : SystemContext D) (mask : Bool) (checked : MaskSetOk c) (world : World D) :
    ((maskSetStep c mask checked world).1.interrupt.maske.zustand c.privilege.kern).maskiert = mask := by
  exact congrArg Maske.KernZustand.maskiert (Maske.aufKernEq c.interrupt.maske c.privilege.kern _)

theorem maskSetStep_other (c : SystemContext D) (mask : Bool) (checked : MaskSetOk c) (world : World D)
    (other : Nat) (different : other ≠ c.privilege.kern) :
    (maskSetStep c mask checked world).1.interrupt.maske.zustand other = c.interrupt.maske.zustand other :=
  Maske.aufKernAnderer c.interrupt.maske c.privilege.kern other _ different

theorem maskSetStep_sim {a : Authority D} {layout : AdressLayout D} {c : SystemContext D}
    {world : World D} (simulation : ClassSimRel a layout c world) (mask : Bool) (checked : MaskSetOk c) :
    ClassSimRel a layout (maskSetStep c mask checked world).1 world := classMetadata_sim simulation _ _

/-- Delivery at the acting core is excluded while masked by the named
    delivery premise itself. No claim about locks or other cores follows. -/
theorem masked_no_delivery {handlers : HandlerTable} {state : Maske.PrioMaske}
    {delivered : Nat → Nat → Nat → Nat → Bool → Prop} (hardware : IrqDelivery handlers state delivered)
    {core vector handler priority : Nat} {boundary : Bool}
    (masked : (state.maske.zustand core).maskiert = true) :
    ¬ delivered core vector handler priority boundary := by
  intro delivery
  have unmasked := (hardware core vector handler priority boundary delivery).2.2.1
  rw [unmasked] at masked
  cases masked

end Gabbro.Grammatik.LowLevel.Construct
