module

public import Stage0.Senke.Start
public import Stage0.Senke.Bild.Mehr.StartupOperands

@[expose] public section

namespace Gabbro.Stage0.Senke

open Runner Runner.IR Runner.Beweis Runner.Mach Gabbro.Stage0.Senke.BildMehr

/-- A true guard in the actual TSO runner follows its two branch
    instructions and skips the emitted stop code. No operand store or
    system call is made by either branch. -/
theorem tso_guard_pass {layout : Runner.Beweis.Lay}
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
  have fetch (o : Nat) (t : T) (byte : (before.ms.1.view i).rd8 t.pc = some (BitVec.ofNat 8 o))
      (range : o < 256) : ProcessStep (TSO layout) actI (onThread (IR.step t)) [] (onThread (op o t)) := by
    have decoded : ((BitVec.ofNat 8 o).setWidth 64 |>.setWidth 8 |>.setWidth 64).toNat = o := by
      simp [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt range, show o < 2 ^ 64 from
        Nat.lt_trans range (by decide)]
    have loaded : rdN (before.ms.1.view i) 1 t.pc = some ((BitVec.ofNat 8 o).setWidth 64) := by
      simp only [rdN, byte, Option.map_some]
    simpa only [decoded] using tso_read_step before inside (fun answer => opt answer fun pair =>
      op (pair.1.setWidth 8 |>.setWidth 64).toNat t) loaded
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
    simpa only [opt_some, ite_eq_right nonzero] using
      tso_read_step before inside (fun answer => opt answer fun pair =>
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
    have offset : sx (II.f 64) = BitVec.ofNat 64 (16 * 4) := rfl
    have advance : jump.pc + BitVec.ofNat 64 (16 * 4) = pc + BitVec.ofNat 64 (16 * 5) :=
      pcN pc 1 4 5 rfl
    simpa [op, f1, rd32, offset, advance] using
      tso_read_step before inside (fun answer => opt answer fun pair =>
        .next { jump with pc := jump.pc + sx (pair.1.setWidth 32) }) loaded
  exact .cons started (.cons (fetch 19 start atBranch.op (by decide)) (.cons indexed
    (.cons passed (.cons jumped (.cons (fetch 18 jump atJump.op (by decide)) (.cons target (.nil _)))))))

end Gabbro.Stage0.Senke
