module

public import Stage0.Senke.Start
public import Stage0.Senke.Bild.Mehr.StartupOperands
public import Stage0.Senke.Bild.Mehr.BootClone
import Lean.Elab.Tactic.Omega

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

/-- On a successful clone, the compiled check reads the returned thread
    ID, sets the signed comparison flag, and advances to the next site.
    All changes remain confined to the two flag words in parent scratch. -/
theorem tso_spawn_check_pass [Kern] {layout : Runner.Beweis.Lay}
    {before : Cfg (TSO layout) (Res T)} {i : Nat} {pc fp : W} {K scratch : Nat} {id : W}
    (running : before.ths[i]? = some (some (.next ⟨pc, fp⟩)))
    (code : CodeAt (before.ms.1.view i) pc
      ([ci 1 ((scratch + 3 : Nat) : Int) 0 0,
        ci 13 ((scratch + 4 : Nat) : Int) ((scratch + 3 : Nat) : Int) ((scratch + 2 : Nat) : Int)] ++
        guardC (scratch + 4) cloneCode scratch))
    (frame : FrameOK (before.ms.1.view i) fp K) (far : CodeFar pc 7 fp K)
    (room : scratch + 5 ≤ K) (slots : K < 2 ^ 31)
    (stored : (before.ms.1.view i).rd64 (slot fp (BitVec.ofNat 64 (scratch + 2))) = some id)
    (success : 0 < id.toInt) :
    ∃ after : (TSO layout).St,
      ProcessPrefix (TSO layout) actI before [] 20
        ⟨after, before.ths.set i (some (.next ⟨pc + BitVec.ofNat 64 (16 * 7), fp⟩))⟩ ∧
      after.1.m = before.ms.1.m ∧
      Agree fp (scratch + 3) K (before.ms.1.view i) (after.1.view i) ∧
      ∀ j, j ≠ i → after.1.view j = before.ms.1.view j := by
  let fill : II := ci 1 ((scratch + 3 : Nat) : Int) 0 0
  let compare : II := ci 13 ((scratch + 4 : Nat) : Int) ((scratch + 3 : Nat) : Int) ((scratch + 2 : Nat) : Int)
  let guard := guardC (scratch + 4) cloneCode scratch
  have inside := (List.getElem?_eq_some_iff.mp running).1
  have zeroIndex : sx (II.f ((scratch + 3 : Nat) : Int)) = BitVec.ofNat 64 (scratch + 3) := sx_nat (by omega)
  have flagIndex : sx (II.f ((scratch + 4 : Nat) : Int)) = BitVec.ofNat 64 (scratch + 4) := sx_nat (by omega)
  have idIndex : sx (II.f ((scratch + 2 : Nat) : Int)) = BitVec.ofNat 64 (scratch + 2) := sx_nat (by omega)
  have zeroCode : InsAt (before.ms.1.view i) pc 1 (II.f ((scratch + 3 : Nat) : Int)) (II.f 0) (II.f 0) := by
    have first := code 0 (by simp)
    simp only [Nat.mul_zero, BitVec.add_zero] at first
    exact first
  have zeroWritable : Mem.all before.ms.1.m.wr (slot fp (sx (II.f ((scratch + 3 : Nat) : Int)))) 8 = true := by
    rw [zeroIndex, ← foldl_wr (before.ms.1.buf i) before.ms.1.m]
    exact frame.wr (scratch + 3) (by omega)
  obtain ⟨middle, zeroRun, same0, view0, others0⟩ := tso_const_prefix running zeroCode zeroWritable
  rw [zeroIndex] at view0
  have safe0 : Agree fp (scratch + 3) K (before.ms.1.view i) (middle.1.view i) := by
    rw [view0]
    exact agree_write frame.room (Nat.le_refl _) (by omega) _
  have size : ([fill, compare] ++ guard).length = 7 := rfl
  have allCode : CodeAt (middle.1.view i) pc ([fill, compare] ++ guard) :=
    code.agree safe0 (size ▸ far)
  have compareCode : InsAt (middle.1.view i) (pc + 16) 13 (II.f ((scratch + 4 : Nat) : Int))
      (II.f ((scratch + 3 : Nat) : Int)) (II.f ((scratch + 2 : Nat) : Int)) :=
    allCode 1 (by rw [size]; decide)
  have leftRead : (middle.1.view i).rd64 (slot fp (sx (II.f ((scratch + 3 : Nat) : Int)))) = some 0 := by
    rw [zeroIndex, view0]
    exact Mem.rd64_wr64 (Mem.wr64_some (frame.wr _ (by omega))) (frame.rd _ (by omega))
  have rightRead : (middle.1.view i).rd64 (slot fp (sx (II.f ((scratch + 2 : Nat) : Int)))) = some id := by
    rw [idIndex, view0, Mem.rd64_write_far (slot_far frame.room (by omega) (by omega) (by omega))]
    exact stored
  let middleCfg : Cfg (TSO layout) (Res T) := ⟨middle, before.ths.set i (some (.next ⟨pc + 16, fp⟩))⟩
  have compareReady : middleCfg.ths[i]? = some (some (.next ⟨pc + 16, fp⟩)) := List.getElem?_set_self inside
  have flagWritable : Mem.all middle.1.m.wr (slot fp (sx (II.f ((scratch + 4 : Nat) : Int)))) 8 = true := by
    rw [flagIndex, same0, ← foldl_wr (before.ms.1.buf i) before.ms.1.m]
    exact frame.wr (scratch + 4) (by omega)
  obtain ⟨after, comparison, same1, view1, others1⟩ :=
    tso_slt_prefix (before := middleCfg) (i := i) compareReady compareCode leftRead rightRead flagWritable
  rw [flagIndex] at view1
  have safe1 : Agree fp (scratch + 3) K (middle.1.view i) (after.1.view i) := by
    rw [view1]
    exact agree_write frame.room (Nat.le_succ _) (by omega) _
  let guardPc := pc + BitVec.ofNat 64 (16 * 2)
  have compareNext : pc + 16 + 16 = guardPc := pcN pc 1 1 2 rfl
  have guardView : CodeAt (after.1.view i) guardPc guard :=
    codeAt_right (a := [fill, compare]) (allCode.agree safe1 (size ▸ far))
  have flagRead : (after.1.view i).rd64 (slot fp (sx (II.f ((scratch + 4 : Nat) : Int)))) = some (spawnFlag id) := by
    rw [flagIndex, view1]
    have current := frame.agree safe0
    exact Mem.rd64_wr64 (Mem.wr64_some (current.wr _ (by omega))) (current.rd _ (by omega))
  let guardCfg : Cfg (TSO layout) (Res T) := ⟨after, before.ths.set i (some (.next ⟨guardPc, fp⟩))⟩
  have guardReady : guardCfg.ths[i]? = some (some (.next ⟨guardPc, fp⟩)) := List.getElem?_set_self inside
  have nonzero : spawnFlag id ≠ 0 := by rw [spawnFlag_pos success]; decide
  have passed := tso_guard_pass (before := guardCfg) (i := i) guardReady guardView flagRead nonzero
  have firstTwo : ProcessPrefix (TSO layout) actI before [] 13 guardCfg := by
    simpa only [middleCfg, guardCfg, nxt, compareNext, List.nil_append, List.set_set, Nat.reduceAdd] using
      zeroRun.trans comparison
  have nextSite : guardPc + BitVec.ofNat 64 (16 * 5) = pc + BitVec.ofNat 64 (16 * 7) := pcN pc 2 5 7 rfl
  refine ⟨after, ?_, same1.trans same0, safe0.trans safe1,
    fun j different => (others1 j different).trans (others0 j different)⟩
  simpa only [guardCfg, nextSite, List.set_set, List.nil_append, Nat.reduceAdd] using firstTwo.trans passed

/-- The complete successful site runs both the clone and its compiled
    check. It reaches the next ten-instruction site, preserves the code
    owner's view outside scratch, and leaves all other views unchanged. -/
theorem tso_spawn_site_pass [Kern] {layout : Runner.Beweis.Lay}
    {before : Cfg (TSO layout) (Res T)} {i : Nat} {pc fp : W} {K scratch entry stack : Nat}
    (running : before.ths[i]? = some (some (.next ⟨pc, fp⟩)))
    (code : CodeAt (before.ms.1.view i) pc (spawnOne scratch entry stack))
    (frame : FrameOK (before.ms.1.view i) fp K) (far : CodeFar pc 10 fp K)
    (room : scratch + 8 ≤ K) (slots : K < 2 ^ 31) (address : entry < 2 ^ 31) (stackBound : stack < 2 ^ 31)
    {id extra : W} (positive : 0 < id.toInt) :
    let child : T := ⟨BitVec.ofNat 64 entry, BitVec.ofNat 64 stack⟩
    let threads := before.ths.set i (some (.next ⟨pc + BitVec.ofNat 64 (16 * 10), fp⟩)) ++ [some (.next child)]
    ∃ after : (TSO layout).St,
      ProcessPrefix (TSO layout) actI before [(i, cloneReq, some (id, extra))] 38 ⟨after, threads⟩ ∧
      threads[before.ths.length]? = some (some (.next child)) ∧
      after.1.m = before.ms.1.m ∧
      Agree fp scratch K (before.ms.1.view i) (after.1.view i) ∧
      ∀ j, j ≠ i → after.1.view j = before.ms.1.view j := by
  intro child threads
  have inside := (List.getElem?_eq_some_iff.mp running).1
  obtain ⟨spawned, run, _, beforeGuard, same, stored, otherViews⟩ :=
    bootSpawn_run (before := before) (i := i) (extra := extra) running code frame far
      (by omega) slots address stackBound positive
  let guardPc := pc + BitVec.ofNat 64 (16 * 3)
  let parent : T := ⟨guardPc, fp⟩
  let afterClone : Cfg (TSO layout) (Res T) :=
    ⟨spawned, before.ths.set i (some (.next parent)) ++ [some (.next child)]⟩
  have within : i < (before.ths.set i (some (.next parent))).length := by
    simpa only [List.length_set] using inside
  have next : afterClone.ths[i]? = some (some (.next parent)) := by
    simp only [afterClone, List.getElem?_append_left within, List.getElem?_set_self inside]
  have allCode : CodeAt (spawned.1.view i) pc
      ([ci 1 scratch entry 0, ci 1 ((scratch + 1 : Nat) : Int) stack 0, ci 24 ((scratch + 2 : Nat) : Int) scratch 0] ++
        ([ci 1 ((scratch + 3 : Nat) : Int) 0 0,
          ci 13 ((scratch + 4 : Nat) : Int) ((scratch + 3 : Nat) : Int) ((scratch + 2 : Nat) : Int)] ++
          guardC (scratch + 4) cloneCode scratch)) :=
    code.agree same (spawnOne_len scratch entry stack ▸ far)
  have guardFar := codeFar_right (n := 3) (k := 7) far
  obtain ⟨after, checkRun, committed, checked, otherChecked⟩ :=
    tso_spawn_check_pass (before := afterClone) (i := i) next (codeAt_right allCode)
      (frame.agree same) guardFar (by omega) slots stored positive
  have advanced : guardPc + BitVec.ofNat 64 (16 * 7) = pc + BitVec.ofNat 64 (16 * 10) :=
    pcN pc 3 7 10 rfl
  refine ⟨after, ?_, ?_, committed.trans beforeGuard, same.trans (checked.mono (Nat.le_add_right _ _)),
    fun j different => (otherChecked j different).trans (otherViews j different)⟩
  · simpa only [afterClone, threads, List.set_append_left _ _ within, List.set_set, List.append_nil,
      advanced, Nat.reduceAdd] using run.trans checkRun
  · change (before.ths.set i _ ++ [some (.next child)])[before.ths.length]? = _
    rw [List.getElem?_append_right (by rw [List.length_set]), List.length_set, Nat.sub_self]
    rfl

end Gabbro.Stage0.Senke
