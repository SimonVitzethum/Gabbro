module

public import Stage0.Senke.Start
public import Stage0.Senke.Bild.Mehr.StartupOperands
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace Gabbro.Stage0.Senke

open Runner Runner.IR Runner.Beweis Runner.Mach Gabbro.Stage0.Senke.BildMehr

private theorem tso_guard_read {layout : Runner.Beweis.Lay}
    {before : Cfg (TSO layout) (Res T)} {i : Nat} {pc fp : W} {a c scratch : Nat} {flag : W}
    (running : before.ths[i]? = some (some (.next ⟨pc, fp⟩)))
    (guard : CodeAt (before.ms.1.view i) pc (guardC a c scratch))
    (word : (before.ms.1.view i).rd64 (slot fp (sx (II.f a))) = some flag) :
    let start : T := ⟨pc, fp⟩
    let selected := if flag = 0 then f2 start fun offset => .next { start with pc := pc + offset }
      else .next (nxt start)
    ProcessPrefix (TSO layout) actI before [] 4 ⟨before.ms, before.ths.set i (some selected)⟩ := by
  intro start selected
  let onThread (r : Res T) : Cfg (TSO layout) (Res T) :=
    ⟨before.ms, before.ths.set i (some r)⟩
  let jump := nxt start
  have inside := (List.getElem?_eq_some_iff.mp running).1
  have atBranch : InsAt (before.ms.1.view i) pc 19 (II.f a) (II.f 32) (II.f 0) := by
    have instruction := guard 0 (by simp [guardC])
    simp only [Nat.mul_zero, BitVec.add_zero] at instruction
    exact instruction
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
  have evaluated : ProcessStep (TSO layout) actI (onThread (branch (II.f a))) []
      (onThread selected) := by
    simpa only [branch, ld, rd64, onThread, opt_some] using
      tso_read_step before inside (width := 8) (address := slot fp (sx (II.f a))) (fun answer => opt answer fun pair =>
        if pair.1 = 0 then f2 start fun offset => .next { start with pc := start.pc + offset }
        else .next jump) word
  exact .cons started (.cons (tso_fetch_opcode before inside 19 start atBranch.op (by decide)) (.cons indexed
    (.cons evaluated (.nil _))))

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
  let jump := nxt ⟨pc, fp⟩
  have inside := (List.getElem?_eq_some_iff.mp running).1
  have atJump : InsAt (before.ms.1.view i) jump.pc 18 (II.f 64) (II.f 0) (II.f 0) :=
    guard 1 (by simp [guardC])
  have first : ProcessPrefix (TSO layout) actI before [] 4 (onThread (.next jump)) := by
    simpa only [ite_eq_right nonzero] using tso_guard_read running guard word
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
  have tail : ProcessPrefix (TSO layout) actI (onThread (.next jump)) [] 3 _ :=
    .cons jumped (.cons (tso_fetch_opcode before inside 18 jump atJump.op (by decide)) (.cons target (.nil _)))
  exact first.trans tail

/-- The false condition reaches the actual first instruction of the
    emitted stop, without changing any memory or issuing a host request. -/
theorem tso_guard_fail {layout : Runner.Beweis.Lay}
    {before : Cfg (TSO layout) (Res T)} {i : Nat} {pc fp : W} {a c scratch : Nat}
    (running : before.ths[i]? = some (some (.next ⟨pc, fp⟩)))
    (guard : CodeAt (before.ms.1.view i) pc (guardC a c scratch))
    (word : (before.ms.1.view i).rd64 (slot fp (sx (II.f a))) = some 0) :
    ProcessPrefix (TSO layout) actI before [] 5
      ⟨before.ms, before.ths.set i (some (.next ⟨pc + 32, fp⟩))⟩ := by
  let start : T := ⟨pc, fp⟩
  let pending := f2 start fun offset => .next { start with pc := pc + offset }
  have inside := (List.getElem?_eq_some_iff.mp running).1
  have first : ProcessPrefix (TSO layout) actI before [] 4 ⟨before.ms, before.ths.set i (some pending)⟩ := by
    simpa only [ite_true] using tso_guard_read running guard word
  have branch : InsAt (before.ms.1.view i) pc 19 (II.f a) (II.f 32) (II.f 0) := by
    have instruction := guard 0 (by simp [guardC])
    simp only [Nat.mul_zero, BitVec.add_zero] at instruction
    exact instruction
  have loaded : rdN (before.ms.1.view i) 4 (pc + 8) = some ((II.f 32).setWidth 64) := by
    simp only [rdN, branch.f2, Option.map_some]
  have offset : sx (((II.f 32).setWidth 64).setWidth 32) = 32 := rfl
  have chosen : ProcessStep (TSO layout) actI ⟨before.ms, before.ths.set i (some pending)⟩ []
      ⟨before.ms, before.ths.set i (some (.next ⟨pc + 32, fp⟩))⟩ := by
    simpa only [pending, start, f2, rd32, opt_some, offset] using
      tso_read_step before inside (fun answer => opt answer fun pair =>
        .next { start with pc := pc + sx (pair.1.setWidth 32) }) loaded
  exact first.trans (ProcessPrefix.ofStep chosen)

/-- The compiled clone comparison writes the signed comparison word. -/
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
      ∀ j, j ≠ i → after.1.view j = before.ms.1.view j :=
  tso_binary_prefix (compute := fun x y => some (bool (x.slt y))) rfl (by decide)
    running instruction left right rfl writable

/-- The compiled clone check branches on the signed returned word. It
    reaches the next site for a positive ID and the first instruction
    of the emitted stop otherwise. Only parent scratch changes. -/
theorem tso_spawn_check_outcome [Kern] {layout : Runner.Beweis.Lay}
    {before : Cfg (TSO layout) (Res T)} {i : Nat} {pc fp : W} {K scratch : Nat} {id : W}
    (running : before.ths[i]? = some (some (.next ⟨pc, fp⟩)))
    (code : CodeAt (before.ms.1.view i) pc
      ([ci 1 ((scratch + 3 : Nat) : Int) 0 0,
        ci 13 ((scratch + 4 : Nat) : Int) ((scratch + 3 : Nat) : Int) ((scratch + 2 : Nat) : Int)] ++
        guardC (scratch + 4) cloneCode scratch))
    (frame : FrameOK (before.ms.1.view i) fp K) (far : CodeFar pc 7 fp K)
    (room : scratch + 5 ≤ K) (slots : K < 2 ^ 31)
    (stored : (before.ms.1.view i).rd64 (slot fp (BitVec.ofNat 64 (scratch + 2))) = some id) :
    ∃ after : (TSO layout).St,
      ProcessPrefix (TSO layout) actI before [] (if 0 < id.toInt then 20 else 18)
        ⟨after, before.ths.set i (some (.next
          ⟨pc + BitVec.ofNat 64 (16 * (if 0 < id.toInt then 7 else 4)), fp⟩))⟩ ∧
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
  have firstTwo : ProcessPrefix (TSO layout) actI before [] 13 guardCfg := by
    simpa only [middleCfg, guardCfg, nxt, compareNext, List.nil_append, List.set_set, Nat.reduceAdd] using
      zeroRun.trans comparison
  refine ⟨after, ?_, same1.trans same0, safe0.trans safe1,
    fun j different => (others1 j different).trans (others0 j different)⟩
  by_cases success : 0 < id.toInt
  · have nonzero : spawnFlag id ≠ 0 := by rw [spawnFlag_pos success]; decide
    have passed := tso_guard_pass (before := guardCfg) (i := i) guardReady guardView flagRead nonzero
    have nextSite : guardPc + BitVec.ofNat 64 (16 * 5) = pc + BitVec.ofNat 64 (16 * 7) := pcN pc 2 5 7 rfl
    simpa only [guardCfg, ite_eq_left success, nextSite, List.set_set, List.nil_append, Nat.reduceAdd] using
      firstTwo.trans passed
  · rw [spawnFlag_nonpos (le_of_not_gt success)] at flagRead
    have failed := tso_guard_fail (before := guardCfg) (i := i) guardReady guardView flagRead
    have toStop : guardPc + 32 = pc + BitVec.ofNat 64 (16 * 4) := pcN pc 2 2 4 rfl
    simpa only [guardCfg, ite_eq_right success, toStop, List.set_set, List.nil_append, Nat.reduceAdd] using
      firstTwo.trans failed

/-- The positive case reaches the next startup site. -/
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
  simpa only [ite_eq_left success] using tso_spawn_check_outcome running code frame far room slots stored

end Gabbro.Stage0.Senke
