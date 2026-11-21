module

public import Stage0.Senke.Start
public import Stage0.Senke.Bild.Mehr.StartupOperands

@[expose] public section

namespace Gabbro.Stage0.Senke

open Runner Runner.IR Runner.Beweis Runner.Mach Gabbro.Stage0.Senke.BildMehr

private theorem fetch {layout : Runner.Beweis.Lay}
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

/-- A true guard in the actual TSO runner follows its two branch
    instructions and skips the emitted stop code. No operand store or
    system call is made by either branch. -/
theorem tso_guard_pass [Kern] {layout : Runner.Beweis.Lay}
    {before : Cfg (TSO layout) (Res T)} {i : Nat} {pc fp : W} {a c scratch : Nat} {flag : W}
    (running : before.ths[i]? = some (some (.next ⟨pc, fp⟩)))
    (guard : CodeAt (before.ms.1.view i) pc (guardC a c scratch))
    (word : (before.ms.1.view i).rd64 (slot fp (sx (II.f a))) = some flag)
    (nonzero : flag ≠ 0) :
    ProcessPrefix (TSO layout) actI before [] 7
      ⟨before.ms, before.ths.set i (some (.next ⟨pc + BitVec.ofNat 64 (16 * 5), fp⟩))⟩ := by
  let onThread (r : Res T) : Cfg (TSO layout) (Res T) :=
    ⟨before.ms, before.ths.set i (some r)⟩
  let start : T := ⟨pc, fp⟩
  let jump := nxt start
  have inside := (List.getElem?_eq_some_iff.mp running).1
  have atBranch : InsAt (before.ms.1.view i) pc 19 (II.f a) (II.f 32) (II.f 0) := by
    have instruction := guard 0 (by simp [guardC])
    simp only [Nat.mul_zero, BitVec.add_zero] at instruction
    exact instruction
  have atJump : InsAt (before.ms.1.view i) jump.pc 18 (II.f 64) (II.f 0) (II.f 0) :=
    guard 1 (by simp [guardC])
  have started : ProcessStep (TSO layout) actI before [] (onThread (IR.step start)) :=
    .priv running rfl
  let branch (index : BitVec 32) : Res T :=
    ld start (sx index) fun result =>
      if result = 0 then f2 start fun offset => .next { start with pc := start.pc + offset }
      else .next jump
  have indexed : ProcessStep (TSO layout) actI (onThread (op 19 start)) []
      (onThread (branch (II.f a))) := by
    have loaded : rdN (before.ms.1.view i) 4 (pc + 4) = some ((II.f a).setWidth 64) := by
      simp only [rdN, atBranch.f1, Option.map_some]
    simpa [onThread, op, branch, f1, rd32] using
      tso_read_step before inside (fun answer => opt answer fun pair => branch (pair.1.setWidth 32)) loaded
  have passed : ProcessStep (TSO layout) actI (onThread (branch (II.f a))) []
      (onThread (.next jump)) := by
    simpa only [branch, ld, rd64, onThread, opt_some, ite_eq_right nonzero] using
      tso_read_step before inside (width := 8) (address := slot fp (sx (II.f a))) (fun answer => opt answer fun pair =>
        if pair.1 = 0 then f2 start fun offset => .next { start with pc := start.pc + offset }
        else .next jump) word
  have jumped : ProcessStep (TSO layout) actI (onThread (.next jump)) [] (onThread (IR.step jump)) := by
    have move := ProcessStep.priv (act := actI) (c := onThread (.next jump)) (i := i)
      (List.getElem?_set_self inside) rfl
    simpa only [onThread, List.set_set] using move
  have target : ProcessStep (TSO layout) actI (onThread (op 18 jump)) []
      (onThread (.next ⟨pc + BitVec.ofNat 64 (16 * 5), fp⟩)) := by
    have loaded : rdN (before.ms.1.view i) 4 (jump.pc + 4) = some ((II.f 64).setWidth 64) := by
      simp only [rdN, atJump.f1, Option.map_some]
    have advance : jump.pc + Runner.X86.sx32 (II.f 64) = pc + BitVec.ofNat 64 (16 * 5) :=
      pcN pc 1 4 5 rfl
    have frame : jump.fp = fp := rfl
    simpa [onThread, op, f1, rd32, advance, frame] using
      tso_read_step before inside (fun answer => opt answer fun pair =>
        .next { jump with pc := jump.pc + sx (pair.1.setWidth 32) }) loaded
  exact .cons started (.cons (fetch before inside 19 start atBranch.op (by decide)) (.cons indexed
    (.cons passed (.cons jumped (.cons (fetch before inside 18 jump atJump.op (by decide)) (.cons target (.nil _)))))))

/-- The signed comparison instruction reads both operands in the current
    TSO view, computes the runner's Boolean word, and writes that word
    to its decoded destination. -/
theorem tso_slt_prefix {layout : Runner.Beweis.Lay}
    {before : Cfg (TSO layout) (Res T)} {i : Nat} {parent : T}
    {dest lhs rhs : BitVec 32} {a b : W}
    (running : before.ths[i]? = some (some (.next parent)))
    (instruction : InsAt (before.ms.1.view i) parent.pc 13 dest lhs rhs)
    (left : (before.ms.1.view i).rd64 (slot parent.fp (sx lhs)) = some a)
    (right : (before.ms.1.view i).rd64 (slot parent.fp (sx rhs)) = some b)
    (writable : Mem.all before.ms.1.m.wr (slot parent.fp (sx dest)) 8 = true) :
    ∃ after : (TSO layout).St,
      ProcessPrefix (TSO layout) actI before [] 8
        ⟨after, before.ths.set i (some (.next (nxt parent)))⟩ ∧
      after.1.m = before.ms.1.m ∧
      after.1.view i = Mem.write (before.ms.1.view i) (slot parent.fp (sx dest)) 8 (bool (a.slt b)).toNat ∧
      ∀ j, j ≠ i → after.1.view j = before.ms.1.view j := by
  let onThread (r : Res T) : Cfg (TSO layout) (Res T) :=
    ⟨before.ms, before.ths.set i (some r)⟩
  have inside := (List.getElem?_eq_some_iff.mp running).1
  let readRight (index : BitVec 32) (value : W) :=
    ld parent (sx index) fun other => ret1 parent (bool (value.slt other))
  let afterLeft (value : W) := rd32 (parent.pc + 12) fun index => readRight index value
  let readLeft (index : BitVec 32) := ld parent (sx index) afterLeft
  have started : ProcessStep (TSO layout) actI before [] (onThread (IR.step parent)) :=
    .priv running rfl
  have firstIndex : ProcessStep (TSO layout) actI (onThread (op 13 parent)) []
      (onThread (readLeft lhs)) := by
    have field : rdN (before.ms.1.view i) 4 (parent.pc + 8) = some (lhs.setWidth 64) := by
      simp only [rdN, instruction.f2, Option.map_some]
    simpa [onThread, op, bin, f2, f3, rd32, ld, readLeft, afterLeft, readRight, opt] using
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
      (onThread (ret1 parent (bool (a.slt b)))) :=
    tso_read_step before inside (width := 8) (address := slot parent.fp (sx rhs))
      (fun answer => opt answer fun pair => ret1 parent (bool (a.slt pair.1))) right
  have read : ProcessPrefix (TSO layout) actI before [] 6 (onThread (ret1 parent (bool (a.slt b)))) :=
    .cons started (.cons (fetch before inside 13 parent instruction.op (by decide)) (.cons firstIndex
      (.cons firstRead (.cons secondIndex (.cons secondRead (.nil _))))))
  have ready : (onThread (ret1 parent (bool (a.slt b)))).ths[i]? = some (some (ret1 parent (bool (a.slt b)))) :=
    List.getElem?_set_self inside
  obtain ⟨after, result, memory, view, other⟩ :=
    tso_ret1_prefix (before := onThread (ret1 parent (bool (a.slt b)))) (i := i) ready instruction.f1 writable
  refine ⟨after, ?_, memory, view, other⟩
  simpa only [onThread, List.set_set, List.nil_append] using read.trans result

end Gabbro.Stage0.Senke
