module

public import Runner.Beweis.Mehr
public import Runner.IR.Seq
public import Stage0.Senke.Bild.Mehr.StoreBuffer

@[expose] public section

namespace Gabbro.Stage0.Senke.BildMehr

open Runner Runner.IR Runner.Beweis Runner.Mach

/-- The read part of an IR instruction leaves the TSO state and all other
    entries of the thread list unchanged. -/
theorem tso_read_step {layout : Lay} (before : Cfg (TSO layout) (Res T))
    {i : Nat} (inside : i < before.ths.length) {width : Nat} {address value : W}
    (resume : Ans → Res T) (loaded : rdN (before.ms.1.view i) width address = some value) :
    ProcessStep (TSO layout) actI
      ⟨before.ms, before.ths.set i (some (.ask (.rd width address) resume))⟩ []
      ⟨before.ms, before.ths.set i (some (resume (some (value, 0))))⟩ := by
  have step := ProcessStep.ask (act := actI) (i := i)
    (c := ⟨before.ms, before.ths.set i (some (.ask (.rd width address) resume))⟩)
    (List.getElem?_set_self inside) rfl rfl
    (show (TSO layout).ans before.ms i (.rd width address) (some (value, 0)) before.ms from
      ⟨rfl, 0, by rw [loaded]; rfl⟩)
    (t' := resume (some (value, 0))) rfl
  simpa only [List.set_set, Mach.lbl] using step

/-- A permitted word store enqueues its value and resumes the exact
    instruction continuation in one silent process step. -/
theorem tso_write_step {layout : Lay}
    {before : Cfg (TSO layout) (Res T)} {i : Nat} {address value : W} {resume : Ans → Res T}
    (running : before.ths[i]? = some (some (.ask (.wr address value) resume)))
    (writable : Mem.all before.ms.1.m.wr address 8 = true) :
    ∃ after : (TSO layout).St,
      ProcessStep (TSO layout) actI before []
        ⟨after, before.ths.set i (some (resume (some (0, 0))))⟩ ∧
      after.1.m = before.ms.1.m ∧
      after.1.view i = Mem.write (before.ms.1.view i) address 8 value.toNat ∧
      ∀ j, j ≠ i → after.1.view j = before.ms.1.view j := by
  have outsideTable (j : Nat) (inside : j < 8) :
      ¬ TB layout (address + BitVec.ofNat 64 j) := by
    intro touches
    obtain ⟨row, range, byte, width, located⟩ := touches
    have present : byte < (readOnlyBytes layout row).length := by
      rw [readOnlyBytes_length]
      exact width
    have readOnly := (before.ms.2.1 row range byte present).2.2
    have writeAllowed := Beweis.all_spec writable inside
    rw [located, readOnly] at writeAllowed
    cases writeAllowed
  let pending := before.ms.1.buf i ++ [(address, value)]
  let after : (TSO layout).St := ⟨before.ms.1.setBuf i pending, by
    refine ⟨before.ms.2.1, ?_⟩
    intro thread store present
    by_cases writer : thread = i
    · subst thread
      change store ∈ (if i = i then pending else before.ms.1.buf i) at present
      rw [ite_eq_left rfl] at present
      rcases List.mem_append.mp present with old | new
      · exact before.ms.2.2 i store old
      · have same := List.mem_singleton.mp new
        subst store
        exact outsideTable
    · exact before.ms.2.2 thread store (by simpa only [TSt.setBuf, ite_eq_right writer] using present)⟩
  have answered : (TSO layout).ans before.ms i (.wr address value) (some (0, 0)) after :=
    Or.inr ⟨writable, rfl, rfl⟩
  have stored := ProcessStep.ask (act := actI) running rfl rfl answered
    (t' := resume (some (0, 0))) rfl
  refine ⟨after, ?_, rfl, ?_⟩
  · simpa only [Mach.lbl] using stored
  rcases tso_store_updates_view answered with refused | accepted
  · cases refused.1
  · exact accepted.2

/-- Finishing an instruction's result operation reads its destination,
    enqueues the word and advances the program counter. -/
theorem tso_ret1_prefix {layout : Lay}
    {before : Cfg (TSO layout) (Res T)} {i : Nat} {parent : T}
    {dest : BitVec 32} {value : W}
    (running : before.ths[i]? = some (some (ret1 parent value)))
    (destination : (before.ms.1.view i).rd32 (parent.pc + 4) = some dest)
    (writable : Mem.all before.ms.1.m.wr (slot parent.fp (sx dest)) 8 = true) :
    ∃ after : (TSO layout).St,
      ProcessPrefix (TSO layout) actI before [] 2
        ⟨after, before.ths.set i (some (.next (nxt parent)))⟩ ∧
      after.1.m = before.ms.1.m ∧
      after.1.view i = Mem.write (before.ms.1.view i) (slot parent.fp (sx dest)) 8 value.toNat ∧
      ∀ j, j ≠ i → after.1.view j = before.ms.1.view j := by
  let onThread (r : Res T) : Cfg (TSO layout) (Res T) :=
    ⟨before.ms, before.ths.set i (some r)⟩
  obtain ⟨inside, current⟩ := List.getElem?_eq_some_iff.mp running
  have decoded : ProcessStep (TSO layout) actI before []
      (onThread (wr64 (slot parent.fp (sx dest)) value (nxt parent))) := by
    have loaded : rdN (before.ms.1.view i) 4 (parent.pc + 4) = some (dest.setWidth 64) := by
      simp only [rdN, destination, Option.map_some]
    have decoded : ProcessStep (TSO layout) actI (onThread (ret1 parent value)) []
        (onThread (wr64 (slot parent.fp (sx dest)) value (nxt parent))) := by
      simpa [ret1, f1, rd32, onThread] using tso_read_step before inside
        (fun answer => opt answer fun pair =>
          wr64 (slot parent.fp (sx (pair.1.setWidth 32))) value (nxt parent)) loaded
    have original : onThread (ret1 parent value) = before := by
      have threads : before.ths.set i (some (ret1 parent value)) = before.ths := by
        rw [← current]
        exact List.set_getElem_self inside
      simp only [onThread, threads]
    exact original ▸ decoded
  obtain ⟨after, queued, committed, view, others⟩ :=
    tso_write_step (before := onThread (wr64 (slot parent.fp (sx dest)) value (nxt parent)))
      (List.getElem?_set_self inside) writable
  have stored : ProcessStep (TSO layout) actI (onThread (wr64 (slot parent.fp (sx dest)) value (nxt parent))) []
      ⟨after, before.ths.set i (some (.next (nxt parent)))⟩ := by
    simpa only [onThread, List.set_set, wr64, opt_some] using queued
  exact ⟨after, .cons decoded (.cons stored (.nil _)), committed, view, others⟩

/-- The real runner loads an immediate, enqueues its destination store,
    and advances to the next instruction. The issuer can already read
    the written word through its own buffer. -/
theorem tso_const_prefix {layout : Lay}
    {before : Cfg (TSO layout) (Res T)} {i : Nat} {parent : T}
    {dest value pad : BitVec 32}
    (running : before.ths[i]? = some (some (.next parent)))
    (instruction : InsAt (before.ms.1.view i) parent.pc 1 dest value pad)
    (writable : Mem.all before.ms.1.m.wr (slot parent.fp (sx dest)) 8 = true) :
    ∃ after : (TSO layout).St,
      ProcessPrefix (TSO layout) actI before [] 5
        ⟨after, before.ths.set i (some (.next (nxt parent)))⟩ ∧
      after.1.m = before.ms.1.m ∧
      after.1.view i = Mem.write (before.ms.1.view i) (slot parent.fp (sx dest)) 8 (sx value).toNat ∧
      ∀ j, j ≠ i → after.1.view j = before.ms.1.view j := by
  let onThread (r : Res T) : Cfg (TSO layout) (Res T) :=
    ⟨before.ms, before.ths.set i (some r)⟩
  have inside := (List.getElem?_eq_some_iff.mp running).1
  have started : ProcessStep (TSO layout) actI before [] (onThread (IR.step parent)) :=
    .priv running rfl
  have fetched : ProcessStep (TSO layout) actI (onThread (IR.step parent)) [] (onThread (op 1 parent)) := by
    have loaded : rdN (before.ms.1.view i) 1 parent.pc = some ((BitVec.ofNat 8 1).setWidth 64) := by
      simp only [rdN, instruction.op, Option.map_some]
    exact tso_read_step before inside (fun answer => opt answer fun pair =>
      op (pair.1.setWidth 8 |>.setWidth 64).toNat parent) loaded
  have immediate : ProcessStep (TSO layout) actI (onThread (op 1 parent)) []
      (onThread (ret1 parent (sx value))) := by
    have loaded : rdN (before.ms.1.view i) 4 (parent.pc + 8) = some (value.setWidth 64) := by
      simp only [rdN, instruction.f2, Option.map_some]
    simpa [op, f2, rd32, onThread] using tso_read_step before inside
      (fun answer => opt answer fun pair => ret1 parent (sx (pair.1.setWidth 32))) loaded
  have retReady : (onThread (ret1 parent (sx value))).ths[i]? = some (some (ret1 parent (sx value))) :=
    List.getElem?_set_self inside
  obtain ⟨after, result, committed, view, other⟩ := tso_ret1_prefix retReady instruction.f1 writable
  have reads : ProcessPrefix (TSO layout) actI before [] 3 (onThread (ret1 parent (sx value))) :=
    .cons started (.cons fetched (.cons immediate (.nil _)))
  refine ⟨after, ?_, committed, view, other⟩
  simpa only [onThread, List.set_set, List.nil_append] using reads.trans result

theorem tso_fetch_opcode {layout : Runner.Beweis.Lay}
    (before : Cfg (TSO layout) (Res T)) {i : Nat} (inside : i < before.ths.length)
    (o : Nat) (t : T) (byte : (before.ms.1.view i).rd8 t.pc = some (BitVec.ofNat 8 o))
    (range : o < 256) :
    ProcessStep (TSO layout) actI ⟨before.ms, before.ths.set i (some (IR.step t))⟩ []
      ⟨before.ms, before.ths.set i (some (op o t))⟩ := by
  have decoded : ((BitVec.ofNat 8 o).setWidth 64 |>.setWidth 8 |>.setWidth 64).toNat = o := by
    have large : o < 18446744073709551616 := Nat.lt_trans range (by decide)
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow, Nat.mod_eq_of_lt range,
      Nat.mod_eq_of_lt large]
  have loaded : rdN (before.ms.1.view i) 1 t.pc = some ((BitVec.ofNat 8 o).setWidth 64) := by
    simp only [rdN, byte, Option.map_some]
  simpa only [decoded, opt_some, IR.step, rd8] using
    tso_read_step before inside (fun answer => opt answer fun pair =>
      op (pair.1.setWidth 8 |>.setWidth 64).toNat t) loaded

/-- Decode an actual syscall instruction through the issuing thread's TSO
    view. Its argument loads finish before the host request is visible. -/
theorem tso_sys_prefix {layout : Runner.Beweis.Lay}
    {before : Cfg (TSO layout) (Res T)} {i : Nat} {t : T} {dest args pad : BitVec 32}
    (running : before.ths[i]? = some (some (.next t)))
    (instruction : InsAt (before.ms.1.view i) t.pc 23 dest args pad)
    {nr a1 a2 a3 a4 a5 a6 : W}
    (number : (before.ms.1.view i).rd64 (slot t.fp (sx args)) = some nr)
    (first : (before.ms.1.view i).rd64 (slot t.fp (sx args) + 8) = some a1)
    (second : (before.ms.1.view i).rd64 (slot t.fp (sx args) + 16) = some a2)
    (third : (before.ms.1.view i).rd64 (slot t.fp (sx args) + 24) = some a3)
    (fourth : (before.ms.1.view i).rd64 (slot t.fp (sx args) + 32) = some a4)
    (fifth : (before.ms.1.view i).rd64 (slot t.fp (sx args) + 40) = some a5)
    (sixth : (before.ms.1.view i).rd64 (slot t.fp (sx args) + 48) = some a6) :
    let resume : Ans → Res T := fun reply => opt reply fun pair => wr64 (slot t.fp (sx dest)) pair.1 (nxt t)
    ProcessPrefix (TSO layout) actI before [] 11
      ⟨before.ms, before.ths.set i (some (.ask (.sys ⟨nr, a1, a2, a3, a4, a5, a6⟩) resume))⟩ := by
  intro resume
  let onThread (r : Res T) : Cfg (TSO layout) (Res T) := ⟨before.ms, before.ths.set i (some r)⟩
  have inside := (List.getElem?_eq_some_iff.mp running).1
  have load32 {address : W} {value : BitVec 32} (next : BitVec 32 → Res T)
      (read : (before.ms.1.view i).rd32 address = some value) :
      ProcessStep (TSO layout) actI (onThread (rd32 address next)) [] (onThread (next value)) := by
    have loaded : rdN (before.ms.1.view i) 4 address = some (value.setWidth 64) := by
      simp only [rdN, read, Option.map_some]
    simpa [onThread, rd32] using tso_read_step before inside
      (fun answer => opt answer fun pair => next (pair.1.setWidth 32)) loaded
  have load64 {address value : W} (next : W → Res T)
      (read : (before.ms.1.view i).rd64 address = some value) :
      ProcessStep (TSO layout) actI (onThread (rd64 address next)) [] (onThread (next value)) := by
    simpa only [onThread, rd64, opt_some] using tso_read_step before inside
      (fun answer => opt answer fun pair => next pair.1) (show rdN (before.ms.1.view i) 8 address = some value from read)
  let request (d n b1 b2 b3 b4 b5 b6 : W) : Res T :=
    .ask (.sys ⟨n, b1, b2, b3, b4, b5, b6⟩) fun reply => opt reply fun pair => wr64 (slot t.fp d) pair.1 (nxt t)
  let fetchArgs (d a : W) : Res T :=
    rd64 (slot t.fp a) fun n => rd64 (slot t.fp a + 8) fun b1 =>
      rd64 (slot t.fp a + 16) fun b2 => rd64 (slot t.fp a + 24) fun b3 =>
      rd64 (slot t.fp a + 32) fun b4 => rd64 (slot t.fp a + 40) fun b5 =>
      rd64 (slot t.fp a + 48) fun b6 => request d n b1 b2 b3 b4 b5 b6
  have operand1 : ProcessStep (TSO layout) actI (onThread (op 23 t)) []
      (onThread (f2 t (fetchArgs (sx dest)))) :=
    load32 (fun d => f2 t (fetchArgs (sx d))) instruction.f1
  have operand2 : ProcessStep (TSO layout) actI (onThread (f2 t (fetchArgs (sx dest)))) []
      (onThread (fetchArgs (sx dest) (sx args))) :=
    load32 (fun a => fetchArgs (sx dest) (sx a)) instruction.f2
  refine .cons (.priv running rfl) (.cons (tso_fetch_opcode before inside instruction.op (by decide))
    (.cons operand1 (.cons operand2 (.cons (load64 _ number) (.cons (load64 _ first)
      (.cons (load64 _ second) (.cons (load64 _ third) (.cons (load64 _ fourth)
        (.cons (load64 _ fifth) (.cons (load64 _ sixth) (.nil _))))))))))

/-- A successful binary instruction reads both slots from the issuing
    view and buffers its exact result at the decoded destination. -/
theorem tso_binary_prefix {layout : Runner.Beweis.Lay}
    {before : Cfg (TSO layout) (Res T)} {i : Nat} {parent : T}
    {dest lhs rhs : BitVec 32} {a b value : W} {opcode : Nat}
    {compute : W → W → Option W}
    (decoded : op opcode parent = bin compute parent) (range : opcode < 256)
    (running : before.ths[i]? = some (some (.next parent)))
    (instruction : InsAt (before.ms.1.view i) parent.pc opcode dest lhs rhs)
    (left : (before.ms.1.view i).rd64 (slot parent.fp (sx lhs)) = some a)
    (right : (before.ms.1.view i).rd64 (slot parent.fp (sx rhs)) = some b)
    (computed : compute a b = some value)
    (writable : Mem.all before.ms.1.m.wr (slot parent.fp (sx dest)) 8 = true) :
    ∃ after : (TSO layout).St,
      ProcessPrefix (TSO layout) actI before [] 8
        ⟨after, before.ths.set i (some (.next (nxt parent)))⟩ ∧
      after.1.m = before.ms.1.m ∧
      after.1.view i = Mem.write (before.ms.1.view i) (slot parent.fp (sx dest)) 8 value.toNat ∧
      ∀ j, j ≠ i → after.1.view j = before.ms.1.view j := by
  let onThread (r : Res T) : Cfg (TSO layout) (Res T) :=
    ⟨before.ms, before.ths.set i (some r)⟩
  have inside := (List.getElem?_eq_some_iff.mp running).1
  let result (lhs rhs : W) := opt (compute lhs rhs) (ret1 parent)
  let readRight (index : BitVec 32) (left : W) :=
    ld parent (sx index) (result left)
  let afterLeft (left : W) := rd32 (parent.pc + 12) fun index => readRight index left
  let readLeft (index : BitVec 32) := ld parent (sx index) afterLeft
  have started : ProcessStep (TSO layout) actI before [] (onThread (IR.step parent)) :=
    .priv running rfl
  have firstIndex : ProcessStep (TSO layout) actI (onThread (op opcode parent)) []
      (onThread (readLeft lhs)) := by
    have field : rdN (before.ms.1.view i) 4 (parent.pc + 8) = some (lhs.setWidth 64) := by
      simp only [rdN, instruction.f2, Option.map_some]
    simpa [onThread, decoded, bin, f2, f3, rd32, ld, readLeft, afterLeft, readRight, result, opt] using
      tso_read_step before inside (fun answer => opt answer fun pair => readLeft (pair.1.setWidth 32)) field
  have firstRead : ProcessStep (TSO layout) actI (onThread (readLeft lhs)) []
      (onThread (afterLeft a)) :=
    tso_read_step before inside (width := 8) (address := slot parent.fp (sx lhs))
      (fun answer => opt answer fun pair => afterLeft pair.1) left
  have secondIndex : ProcessStep (TSO layout) actI (onThread (afterLeft a)) []
      (onThread (readRight rhs a)) := by
    have field : rdN (before.ms.1.view i) 4 (parent.pc + 12) = some (rhs.setWidth 64) := by
      simp only [rdN, instruction.f3, Option.map_some]
    simpa [onThread, afterLeft, rd32] using tso_read_step before inside
      (fun answer => opt answer fun pair => readRight (pair.1.setWidth 32) a) field
  have secondRead : ProcessStep (TSO layout) actI (onThread (readRight rhs a)) []
      (onThread (ret1 parent value)) := by
    have read := tso_read_step before inside (width := 8) (address := slot parent.fp (sx rhs))
      (fun answer => opt answer fun pair => result a pair.1) right
    simpa only [onThread, readRight, ld, rd64, result, computed, opt_some] using read
  have read : ProcessPrefix (TSO layout) actI before [] 6 (onThread (ret1 parent value)) :=
    .cons started (.cons (tso_fetch_opcode before inside opcode parent instruction.op range) (.cons firstIndex
      (.cons firstRead (.cons secondIndex (.cons secondRead (.nil _))))))
  have ready : (onThread (ret1 parent value)).ths[i]? = some (some (ret1 parent value)) :=
    List.getElem?_set_self inside
  obtain ⟨after, result, memory, view, other⟩ :=
    tso_ret1_prefix (before := onThread (ret1 parent value)) (i := i) ready instruction.f1 writable
  refine ⟨after, ?_, memory, view, other⟩
  simpa only [onThread, List.set_set, List.nil_append] using read.trans result

/-- The call instruction reads its actual target, buffers the return PC
    and caller frame, and enters the callee with its decoded frame pointer. -/
theorem tso_call_prefix {layout : Lay}
    {before : Cfg (TSO layout) (Res T)} {i : Nat} {caller : T}
    {targetSlot frameSlot unused : BitVec 32} {target : W}
    (running : before.ths[i]? = some (some (.next caller)))
    (instruction : InsAt (before.ms.1.view i) caller.pc 20 targetSlot frameSlot unused)
    (address : (before.ms.1.view i).rd64 (slot caller.fp (sx targetSlot)) = some target)
    (writablePC : Mem.all before.ms.1.m.wr (slot caller.fp (sx frameSlot)) 8 = true)
    (writableFP : Mem.all before.ms.1.m.wr (slot caller.fp (sx frameSlot) + 8) 8 = true) :
    let frame := slot caller.fp (sx frameSlot)
    ∃ after : (TSO layout).St,
      ProcessPrefix (TSO layout) actI before [] 7
        ⟨after, before.ths.set i (some (.next ⟨target, frame⟩))⟩ ∧
      after.1.m = before.ms.1.m ∧
      after.1.view i = Mem.write (Mem.write (before.ms.1.view i) frame 8 (nxt caller).pc.toNat)
        (frame + 8) 8 caller.fp.toNat ∧
      ∀ j, j ≠ i → after.1.view j = before.ms.1.view j := by
  intro frame
  let onThread (r : Res T) : Cfg (TSO layout) (Res T) := ⟨before.ms, before.ths.set i (some r)⟩
  let enter : T := ⟨target, frame⟩
  let storeFrame := wr64 (frame + 8) caller.fp enter
  let stores (base : W) (callee : W) : Res T :=
    .ask (.wr (slot caller.fp base) (nxt caller).pc) fun answer => opt answer fun _ =>
      wr64 (slot caller.fp base + 8) caller.fp ⟨callee, slot caller.fp base⟩
  let decodeFrame (callee : W) := f2 caller (fun base => stores base callee)
  let readTarget (index : BitVec 32) := ld caller (sx index) decodeFrame
  have inside := (List.getElem?_eq_some_iff.mp running).1
  have started : ProcessStep (TSO layout) actI before [] (onThread (IR.step caller)) := .priv running rfl
  have decoded : ProcessStep (TSO layout) actI (onThread (op 20 caller)) [] (onThread (readTarget targetSlot)) := by
    have field : rdN (before.ms.1.view i) 4 (caller.pc + 4) = some (targetSlot.setWidth 64) := by
      simp only [rdN, instruction.f1, Option.map_some]
    simpa [onThread, op, f1, rd32, readTarget, decodeFrame, stores, nxt] using
      tso_read_step before inside (fun answer => opt answer fun pair => readTarget (pair.1.setWidth 32)) field
  have selected : ProcessStep (TSO layout) actI (onThread (readTarget targetSlot)) [] (onThread (decodeFrame target)) :=
    tso_read_step before inside (width := 8) (address := slot caller.fp (sx targetSlot))
      (fun answer => opt answer fun pair => decodeFrame pair.1) address
  have chosen : ProcessStep (TSO layout) actI (onThread (decodeFrame target)) []
      (onThread (stores (sx frameSlot) target)) := by
    have field : rdN (before.ms.1.view i) 4 (caller.pc + 8) = some (frameSlot.setWidth 64) := by
      simp only [rdN, instruction.f2, Option.map_some]
    simpa [onThread, decodeFrame, f2, rd32] using
      tso_read_step before inside (fun answer => opt answer fun pair => stores (sx (pair.1.setWidth 32)) target) field
  let afterDecode := onThread (stores (sx frameSlot) target)
  have decodedCall : ProcessPrefix (TSO layout) actI before [] 5 afterDecode :=
    .cons started (.cons (tso_fetch_opcode before inside 20 caller instruction.op (by decide))
      (.cons decoded (.cons selected (.cons chosen (.nil _)))))
  obtain ⟨first, savedPC, committed, firstView, firstOthers⟩ :=
    tso_write_step (before := afterDecode) (List.getElem?_set_self inside) writablePC
  let afterPC : Cfg (TSO layout) (Res T) := ⟨first, before.ths.set i (some storeFrame)⟩
  have savePC : ProcessStep (TSO layout) actI afterDecode [] afterPC := by
    simpa only [afterDecode, onThread, stores, opt_some, frame, enter, storeFrame, List.set_set] using savedPC
  have secondWritable : Mem.all afterPC.ms.1.m.wr (frame + 8) 8 = true := by
    change Mem.all first.1.m.wr _ 8 = true
    rw [committed]
    exact writableFP
  obtain ⟨after, savedFP, finalMemory, finalView, finalOthers⟩ :=
    tso_write_step (before := afterPC) (List.getElem?_set_self inside) secondWritable
  have saveFP : ProcessStep (TSO layout) actI afterPC []
      ⟨after, before.ths.set i (some (.next enter))⟩ := by
    simpa only [afterPC, storeFrame, wr64, opt_some, List.set_set] using savedFP
  exact ⟨after, decodedCall.trans (.cons savePC (.cons saveFP (.nil _))),
    finalMemory.trans committed, finalView.trans (congrArg (fun m => Mem.write m (frame + 8) 8 caller.fp.toNat) firstView),
    fun j different => (finalOthers j different).trans (firstOthers j different)⟩

end Gabbro.Stage0.Senke.BildMehr
