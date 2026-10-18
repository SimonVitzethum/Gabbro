import Grammatik.Code.Conc.Mask

/-
  File:      Grammatik/Code/Conc/MaskNeed.lean
  Subject:   TRACK L, PHASE L3 -- THE NAMED HARDWARE ASSUMPTION of the interrupt mask, in the style of `Model/Need.lean`
             (a statement of obligations on a CPU model, not an instance and not an ISA model; ISA-neutral).

  `Code`'s `imsk` is an ordinary word exchange for every semantic statement (`stepI`), so `Need.plain` already asks the
  CPU side to simulate it. What the CPU must ADDITIONALLY provide is `MaskHw`, three facts about a CPU state type `Mach`
  with, for every core `c`, a predicate `Masked c x` ("core `c` takes no interrupt and is not rescheduled in state `x`")
  and the two transitions `Irq c x y` (core `c` enters an interrupt handler) and `Switch c x y` (core `c` switches to
  another thread):

    * H1 `masked_of_cell` -- THE CELL IS THE REGISTER: when `Rel` holds the core's mask word `mb c` of the `Code` memory,
      a nonzero word means the core is masked;
    * H2 `irq_unmasked`   -- an interrupt handler is entered only on an unmasked core;
    * H3 `switch_unmasked` -- a core does not switch threads while masked (a thread inside a masking section is not
      descheduled; this is what makes the saved word of `Conc/Mask.lean` restore LIFO, and it is what keeps machine G's
      per-core mask list faithful: no other thread of the core moves in between).

  H1 and H2 give the refinement of the entry guard of machine G (`Conc/MaskRel.lean`, `irq_guard`): the hardware enters a
  handler only where G's guard `Z.mask (kern f) = []` holds. Nothing here names an instruction of any ISA.
-/

namespace Gabbro.Code.Lower

variable [Conf]

/-- **The obligations on the CPU side for the interrupt mask.** `mb c` is the block of core `c`'s mask word. -/
structure MaskHw (Mach : Type) (Rel : Mem → Regs → Mach → Prop) (mb : Nat → Nat)
    (Masked : Nat → Mach → Prop) (Irq Switch : Nat → Mach → Mach → Prop) : Prop where
  /-- H1: a nonzero mask word is a masked core. -/
  masked_of_cell : ∀ c m rs x v, Rel m rs x → m.load (mb c) 0 lw = some v → v ≠ tk 0 → Masked c x
  /-- H2: an interrupt is taken only on an unmasked core. -/
  irq_unmasked : ∀ c x y, Irq c x y → ¬ Masked c x
  /-- H3: a masked core does not switch threads. -/
  switch_unmasked : ∀ c x y, Switch c x y → ¬ Masked c x

end Gabbro.Code.Lower
