module

public import Stage0.Senke.Sperre.Bindung.ImageCAS
public import Stage0.Senke.Sperre.Schritta
public import Stage0.Senke.Sperre.Faeden.Maschine
import Stage0.Senke.Bild.Mehr.ImageTransition
import Stage0.Senke.Bild.Mehr.StartupOperands
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace Gabbro.Stage0.Senke.Faeden

open Gabbro.Grammatik Gabbro.Stage0.Senke Gabbro.Stage0.Senke.BildMehr
  Runner Runner.IR Runner.Mem Runner.Mach Runner.Beweis

variable [Kern] {D : Deklaration} {layout : Senke.Lay D}
  {machine : Cfg imageTSO (Res T)} {baseline : Mem} {thread : Nat}
  {pc fp : W} {scratch base : Nat} {code : List II}
  {registers : Nat → W} {old serving waiting : W}

private theorem savedCAS (environment : LE baseline pc fp scratch base code)
    (slots : LS baseline (machine.ms.1.view thread) fp scratch base registers old serving waiting)
    {index dest address expected : Nat}
    (addressFits : address < 18) (nextFits : expected + 1 < 18)
    (cell : code[index]? = some
      (ci 22 ((scratch + dest : Nat) : Int) ((scratch + address : Nat) : Int) ((scratch + expected : Nat) : Int)))
    (running : machine.ths[thread]? =
      some (some (.next ⟨pc + BitVec.ofNat 64 (16 * index), fp⟩))) :
    let pointer : T := ⟨pc + BitVec.ofNat 64 (16 * index), fp⟩
    ProcessPrefix imageTSO actI machine [] 7
      ⟨machine.ms, machine.ths.set thread (some
        (.ask (.cas (registers address) (registers expected) (registers (expected + 1)))
          (fun reply => opt reply fun pair => ret1 pointer pair.1)))⟩ := by
  intro pointer
  have opcode := environment.ins slots.ag cell
  have small := environment.small
  have addressSlot := sx_nat (d := scratch + address) (by omega)
  have savedSlot := sx_nat (d := scratch + expected) (by omega)
  have addressRead : (machine.ms.1.view thread).rd64 (slot fp (sx (II.f (scratch + address : Nat)))) =
      some (registers address) := by rw [addressSlot]; exact slots.sl address addressFits
  have expectedRead : (machine.ms.1.view thread).rd64 (slot fp (sx (II.f (scratch + expected : Nat)))) =
      some (registers expected) := by rw [savedSlot]; exact slots.sl expected (by omega)
  have updateRead : (machine.ms.1.view thread).rd64 (slot fp (sx (II.f (scratch + expected : Nat))) + 8) =
      some (registers (expected + 1)) := by
    rw [savedSlot, slot_plus8, Nat.add_assoc]
    exact slots.sl (expected + 1) nextFits
  exact tso_silent_prefix_image
    (tso_cas_prefix (before := imageToTSO machine) (t := pointer)
      running opcode addressRead expectedRead updateRead) rfl

private theorem savedLoad (environment : LE baseline pc fp scratch base code)
    (slots : LS baseline (machine.ms.1.view thread) fp scratch base registers old serving waiting)
    {index dest address : Nat} (addressFits : address < 18)
    (cell : code[index]? = some
      (ci 15 ((scratch + dest : Nat) : Int) ((scratch + address : Nat) : Int) 0))
    (running : machine.ths[thread]? =
      some (some (.next ⟨pc + BitVec.ofNat 64 (16 * index), fp⟩))) :
    let pointer : T := ⟨pc + BitVec.ofNat 64 (16 * index), fp⟩
    ProcessPrefix imageTSO actI machine [] 4
      ⟨machine.ms, machine.ths.set thread (some
        (.ask (.rd 8 (registers address)) (fun reply => opt reply fun pair => ret1 pointer pair.1)))⟩ := by
  intro pointer
  have opcode := environment.ins slots.ag cell
  have small := environment.small
  have addressSlot := sx_nat (d := scratch + address) (by omega)
  have addressRead : (machine.ms.1.view thread).rd64 (slot fp (sx (II.f (scratch + address : Nat)))) =
      some (registers address) := by rw [addressSlot]; exact slots.sl address addressFits
  exact tso_silent_prefix_image
    (tso_load_prefix (before := imageToTSO machine) (t := pointer) running opcode addressRead) rfl

/-- The relocated draw instruction reads the saved expected ticket and
    issues CAS on the emitted next word, including modulo 64 wraparound. -/
theorem image_ticket_draw_prefix {position expected : Nat}
    (environment : LE baseline pc fp scratch base code)
    (slots : LS baseline (machine.ms.1.view thread) fp scratch base registers old serving waiting)
    (atCode : At code position (nimmT layout base scratch))
    (address : registers 1 = BitVec.ofNat 64 base)
    (sample : registers 2 = BitVec.ofNat 64 expected)
    (successor : registers 3 = BitVec.ofNat 64 (expected + 1))
    (running : machine.ths[thread]? =
      some (some (.next ⟨pc + BitVec.ofNat 64 (16 * (position + 4)), fp⟩))) :
    let pointer : T := ⟨pc + BitVec.ofNat 64 (16 * (position + 4)), fp⟩
    ProcessPrefix imageTSO actI machine [] 7
      ⟨machine.ms, machine.ths.set thread (some (.ask
        (.cas (BitVec.ofNat 64 base) (BitVec.ofNat 64 expected) (BitVec.ofNat 64 (expected + 1)))
        (fun reply => opt reply fun pair => ret1 pointer pair.1)))⟩ := by
  simpa only [address, sample, successor] using
    savedCAS environment slots (address := 1) (expected := 2) (dest := 5) (by decide) (by decide)
      (atCode.get (nimmT_casN layout base scratch)) running

/-- The emitted read of the serving word drives the abstract admission
    step and supplies the actual waiting comparison. -/
theorem image_ticket_serving_prefix {position : Nat}
    (environment : LE baseline pc fp scratch base code)
    (slots : LS baseline (machine.ms.1.view thread) fp scratch base registers old serving waiting)
    (atCode : At code position (nimmT layout base scratch))
    (address : registers 1 = BitVec.ofNat 64 (base + 8))
    (running : machine.ths[thread]? =
      some (some (.next ⟨pc + BitVec.ofNat 64 (16 * (position + 8)), fp⟩))) :
    let pointer : T := ⟨pc + BitVec.ofNat 64 (16 * (position + 8)), fp⟩
    ProcessPrefix imageTSO actI machine [] 4
      ⟨machine.ms, machine.ths.set thread (some
        (.ask (.rd 8 (BitVec.ofNat 64 (base + 8))) (fun reply => opt reply fun pair => ret1 pointer pair.1)))⟩ := by
  simpa only [address] using
    savedLoad environment slots (address := 1) (dest := 5) (by decide)
      (atCode.get (nimmT_ladeS layout base scratch).2) running

/-- The relocated release CAS addresses serving and publishes the exact
    saved successor. The same release prefix serves every unwind case. -/
theorem image_ticket_release_prefix {position sampled : Nat}
    (environment : LE baseline pc fp scratch base code)
    (slots : LS baseline (machine.ms.1.view thread) fp scratch base registers old serving waiting)
    (atCode : At code position (gibT layout base scratch)) (futex : layout.lockWait = .futex)
    (address : registers 1 = BitVec.ofNat 64 (base + 8))
    (sample : registers 2 = BitVec.ofNat 64 sampled)
    (successor : registers 3 = BitVec.ofNat 64 (sampled + 1))
    (running : machine.ths[thread]? =
      some (some (.next ⟨pc + BitVec.ofNat 64 (16 * (position + 4)), fp⟩))) :
    let pointer : T := ⟨pc + BitVec.ofNat 64 (16 * (position + 4)), fp⟩
    ProcessPrefix imageTSO actI machine [] 7
      ⟨machine.ms, machine.ths.set thread (some (.ask
        (.cas (BitVec.ofNat 64 (base + 8)) (BitVec.ofNat 64 sampled) (BitVec.ofNat 64 (sampled + 1)))
        (fun reply => opt reply fun pair => ret1 pointer pair.1)))⟩ := by
  simpa only [address, sample, successor] using
    savedCAS environment slots (address := 1) (expected := 2) (dest := 5) (by decide) (by decide)
      (atCode.get (gibT_schritte layout base scratch futex).2.2.1) running

end Gabbro.Stage0.Senke.Faeden
