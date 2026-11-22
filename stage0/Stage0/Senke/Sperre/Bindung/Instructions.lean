module

public import Stage0.Senke.Sperre.Bindung.ImageCAS
public import Stage0.Senke.Sperre.Bindung.ImageWaiters
public import Stage0.Senke.Sperre.Schritta
public import Stage0.Senke.Sperre.Faeden.Maschine
public import Stage0.Senke.Sperre.Warten.Futex
import Stage0.Senke.Bild.Mehr.ImageTransition
import Stage0.Senke.Bild.Mehr.StartupOperands
import Stage0.Senke.Stopp
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

private theorem savedFutex (environment : LE baseline pc fp scratch base code)
    (slots : LS baseline (machine.ms.1.view thread) fp scratch base registers old serving waiting)
    {index : Nat} {mode value : W}
    (cell : code[index]? = some (ci 23 ((scratch + 10 + 7 : Nat) : Int) ((scratch + 10 : Nat) : Int) 0))
    (arguments : FutexArgs registers (BitVec.ofNat 64 (base + 8)) mode value)
    (running : machine.ths[thread]? =
      some (some (.next ⟨pc + BitVec.ofNat 64 (16 * index), fp⟩))) :
    let pointer : T := ⟨pc + BitVec.ofNat 64 (16 * index), fp⟩
    let resume : Ans → Res T := fun reply => opt reply fun pair =>
      wr64 (slot fp (sx (II.f (scratch + 10 + 7 : Nat)))) pair.1 (nxt pointer)
    ProcessPrefix imageTSO actI machine [] 11
      ⟨machine.ms, machine.ths.set thread (some
        (.ask (.sys (futexReq (BitVec.ofNat 64 (base + 8)) mode value)) resume))⟩ := by
  intro pointer resume
  obtain ⟨number, address, operation, argument, fourth, fifth, sixth⟩ := arguments
  have instruction := environment.ins slots.ag cell
  have small := environment.small
  have argsSlot := sx_nat (d := scratch + 10) (by omega)
  refine tso_silent_prefix_image
    (tso_sys_prefix (before := imageToTSO machine) (t := pointer) (nr := 202)
      (a1 := BitVec.ofNat 64 (base + 8)) (a2 := mode) (a3 := value) (a4 := 0) (a5 := 0) (a6 := 0)
      running instruction ?_ ?_ ?_ ?_ ?_ ?_ ?_) rfl
  all_goals simp only [ci, pointer, argsSlot, imageToTSO]
  · simpa only [number] using slots.sl 10 (by decide)
  · rw [show (8 : W) = BitVec.ofNat 64 (8 * 1) from rfl, slot_plus]
    simpa only [address, Nat.add_assoc, Nat.reduceAdd] using slots.sl 11 (by decide)
  · rw [show (16 : W) = BitVec.ofNat 64 (8 * 2) from rfl, slot_plus]
    simpa only [operation, Nat.add_assoc, Nat.reduceAdd] using slots.sl 12 (by decide)
  · rw [show (24 : W) = BitVec.ofNat 64 (8 * 3) from rfl, slot_plus]
    simpa only [argument, Nat.add_assoc, Nat.reduceAdd] using slots.sl 13 (by decide)
  · rw [show (32 : W) = BitVec.ofNat 64 (8 * 4) from rfl, slot_plus]
    simpa only [fourth, Nat.add_assoc, Nat.reduceAdd] using slots.sl 14 (by decide)
  · rw [show (40 : W) = BitVec.ofNat 64 (8 * 5) from rfl, slot_plus]
    simpa only [fifth, Nat.add_assoc, Nat.reduceAdd] using slots.sl 15 (by decide)
  · rw [show (48 : W) = BitVec.ofNat 64 (8 * 6) from rfl, slot_plus]
    simpa only [sixth, Nat.add_assoc, Nat.reduceAdd] using slots.sl 16 (by decide)

/-- The relocated contended acquisition code issues WAIT with the saved serving sample. -/
theorem image_ticket_wait_prefix {position sampled : Nat}
    (environment : LE baseline pc fp scratch base code)
    (slots : LS baseline (machine.ms.1.view thread) fp scratch base registers old serving waiting)
    (atCode : At code position (nimmT layout base scratch)) (futex : layout.lockWait = .futex)
    (arguments : FutexArgs registers (BitVec.ofNat 64 (base + 8)) 128 (BitVec.ofNat 64 sampled))
    (running : machine.ths[thread]? =
      some (some (.next ⟨pc + BitVec.ofNat 64 (16 * (position + 26)), fp⟩))) :
    let pointer : T := ⟨pc + BitVec.ofNat 64 (16 * (position + 26)), fp⟩
    let resume : Ans → Res T := fun reply => opt reply fun pair =>
      wr64 (slot fp (sx (II.f (scratch + 10 + 7 : Nat)))) pair.1 (nxt pointer)
    ProcessPrefix imageTSO actI machine [] 11
      ⟨machine.ms, machine.ths.set thread (some
        (.ask (.sys (futexReq (BitVec.ofNat 64 (base + 8)) 128 (BitVec.ofNat 64 sampled))) resume))⟩ :=
  savedFutex environment slots (atCode.get (nimmT_futexW layout base scratch futex).2.2.2)
    arguments running

/-- The relocated release code issues WAKE-all against the same serving word. -/
theorem image_ticket_wake_prefix {position : Nat}
    (environment : LE baseline pc fp scratch base code)
    (slots : LS baseline (machine.ms.1.view thread) fp scratch base registers old serving waiting)
    (atCode : At code position (gibT layout base scratch)) (futex : layout.lockWait = .futex)
    (arguments : FutexArgs registers (BitVec.ofNat 64 (base + 8)) 129 2147483647)
    (running : machine.ths[thread]? =
      some (some (.next ⟨pc + BitVec.ofNat 64 (16 * (position + 15)), fp⟩))) :
    let pointer : T := ⟨pc + BitVec.ofNat 64 (16 * (position + 15)), fp⟩
    let resume : Ans → Res T := fun reply => opt reply fun pair =>
      wr64 (slot fp (sx (II.f (scratch + 10 + 7 : Nat)))) pair.1 (nxt pointer)
    ProcessPrefix imageTSO actI machine [] 11
      ⟨machine.ms, machine.ths.set thread (some
        (.ask (.sys (futexReq (BitVec.ofNat 64 (base + 8)) 129 2147483647)) resume))⟩ :=
  savedFutex environment slots (atCode.get (gibT_schritte layout base scratch futex).2.2.2.2.2.2.2)
    arguments running

/-- Both adjustment loops have the same operand layout in the emitted
    scratch frame. Only the instruction offset and replacement differ. -/
def WaitAdjustment.cellIndex : WaitAdjustment → Nat
  | .register => 16
  | .unregister => 31

theorem image_ticket_waiter_CAS_prefix {position expected : Nat} (mode : WaitAdjustment)
    (environment : LE baseline pc fp scratch base code)
    (slots : LS baseline (machine.ms.1.view thread) fp scratch base registers old serving waiting)
    (atCode : At code position (nimmT layout base scratch)) (futex : layout.lockWait = .futex)
    (address : registers 7 = BitVec.ofNat 64 (base + 16))
    (sample : registers 8 = BitVec.ofNat 64 expected)
    (replacement : registers 9 = BitVec.ofNat 64 (mode.count expected))
    (running : machine.ths[thread]? =
      some (some (.next ⟨pc + BitVec.ofNat 64 (16 * (position + mode.cellIndex)), fp⟩))) :
    let pointer : T := ⟨pc + BitVec.ofNat 64 (16 * (position + mode.cellIndex)), fp⟩
    ProcessPrefix imageTSO actI machine [] 7
      ⟨machine.ms, machine.ths.set thread (some (.ask
        (.cas (BitVec.ofNat 64 (base + 16)) (BitVec.ofNat 64 expected) (BitVec.ofNat 64 (mode.count expected)))
        (fun reply => opt reply fun pair => ret1 pointer pair.1)))⟩ := by
  have cell : code[position + mode.cellIndex]? = some
      (ci 22 ((scratch + 11 : Nat) : Int) ((scratch + 7 : Nat) : Int) ((scratch + 8 : Nat) : Int)) := by
    cases mode
    · exact atCode.get (nimmT_inc layout base scratch futex).2.2
    · exact atCode.get (nimmT_dec layout base scratch).2.1
  simpa only [address, sample, replacement] using
    savedCAS environment slots (address := 7) (expected := 8) (dest := 11)
      (by decide) (by decide) cell running

end Gabbro.Stage0.Senke.Faeden
