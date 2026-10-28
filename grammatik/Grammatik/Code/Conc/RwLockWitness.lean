import Grammatik.Code.Conc.RwLockRel
import Grammatik.Code.Conc.LockWitness

/-
  File:      Grammatik/Code/Conc/RwLockWitness.lean
  Subject:   TRACK L, PHASE L3 -- A WITNESS of the reader/writer lock as `Code`: two readers and a writer contend,
             the step theorems of `Conc/RwLockRel.lean` run.

  On the declaration of `Conc/Witness.lean` (one lock) at the 64-bit target, with the IR function

      1: rdLoad (rs := state; rs = 1 ? goto 1 : goto 2)      2: rdTake (rn := rs + 2; cas(state, rs, rn); ok ? 5 : 1)
      5: rdRel (fetch_sub(state, 2))                         6: ret
     10: wrTake (cas(state, 0, 1); ok ? 11 : 10)             11: wrRel (state := 0)

  Threads 0 and 1 are readers (`lese t _ := t ≠ 2`), thread 2 is the writer; all three start at their first block, the
  state word is `0`.
    * threads 0 and 1 load the word (`0`); thread 0's take wins (the layer's SHARED ACQUISITION: word `2`);
      thread 1's take LOSES the race (the word is `2`, not `0`; G silent), it loads again (`2`) and its take wins:
      BOTH READERS HOLD AT ONCE (word `4`) -- the step machine G alone cannot take;
    * the writer's take finds the word `4`, not `0`: it waits (G silent);
    * both readers release (word `2`, then `0`); the writer's take wins (`RufFreiG` holds: G's `dannLocks`; word `1`).
  `RwRel` holds after every step; the final machine holds the lock in thread 2 alone, and at the machine where both
  readers hold, `rwRel_exkl` gives the layer's exclusion invariant.
-/

namespace Gabbro.Code.Lower.WitC

open Gabbro.Grammatik
open Gabbro.Grammatik.Zielsatz (Lese RwExkl)

section C64R

local instance confR64 : Conf := ⟨64, false, Or.inr rfl⟩

/-- The IR function: readers enter at 1, the writer at 10. -/
def rwMod : Modl :=
  ⟨[], [⟨"rw", [], .void, [⟨0, [], [], .jmp 1⟩, rdLoad cLay () 1 1 2, rdTake cLay () 1 2 3 4 2 5 1,
    rdRel cLay () 5 5 6, ⟨6, [], [], .ret none⟩, wrTake cLay () 1 2 10 11, wrRel cLay () 11 6]⟩]⟩

theorem rw_blk1 : rwMod.blk 0 1 = some (rdLoad cLay () 1 1 2) := rfl
theorem rw_blk2 : rwMod.blk 0 2 = some (rdTake cLay () 1 2 3 4 2 5 1) := rfl
theorem rw_blk5 : rwMod.blk 0 5 = some (rdRel cLay () 5 5 6) := rfl
theorem rw_blk6 : rwMod.blk 0 6 = some ⟨6, [], [], .ret none⟩ := rfl
theorem rw_blk10 : rwMod.blk 0 10 = some (wrTake cLay () 1 2 10 11) := rfl
theorem rw_blk11 : rwMod.blk 0 11 = some (wrRel cLay () 11 6) := rfl

/-- Threads 0 and 1 are readers, thread 2 is the writer. -/
def rwLese : Lese cD := fun t _ => t ≠ 2

theorem rwLese_pos {t : Faden} (h : t ≠ 2) : rwLese t () := h

/-- The word interface answers the lock cell (it is no shared global). -/
theorem rw_sees {m : Mem} {b : Nat} {x : Val} (h : m.load b 0 lw = some x) (o : Order) :
    Sees.shared cLay m b 0 lw o x := Or.inr h

/-- Machine G after thread `u` took the lock / released it. -/
def mAdd (M : RufMaschineG cD) (u : Faden) : RufMaschineG cD :=
  { M with faeden := fun v => if v = u then
      { M.faeden v with spur := Ereignis.nimmt lcL [] :: (M.faeden v).spur } else M.faeden v }

def mDel (M : RufMaschineG cD) (u : Faden) : RufMaschineG cD :=
  { M with faeden := fun v => if v = u then
      { M.faeden v with spur := Ereignis.gibt lcL :: (M.faeden v).spur } else M.faeden v }

theorem mAdd_offen (M : RufMaschineG cD) (u v : Faden) : offen ((mAdd M u).faeden v).spur =
    if v = u then lcL :: offen (M.faeden v).spur else offen (M.faeden v).spur := by
  by_cases h : v = u <;> simp only [mAdd, h, ↓reduceIte, offen]

theorem mDel_offen (M : RufMaschineG cD) (u v : Faden) : offen ((mDel M u).faeden v).spur =
    if v = u then (offen (M.faeden v).spur).erase lcL else offen (M.faeden v).spur := by
  by_cases h : v = u <;> simp only [mDel, h, ↓reduceIte, offen]

/-- With one lock the ghost state is a constant. -/
theorem updR_unit (gh : cD.Lock → Rw) (g : Rw) : updR gh () g = fun _ => g :=
  funext fun L => by cases L; exact updR_self gh () g

/-- The ghost states of the run. -/
def ga : Rw := Rw.free
def gb : Rw := ga.addR 0
def gc : Rw := gb.addR 1
def gd : Rw := gc.delR 0
def ge : Rw := gd.delR 1
def gf : Rw := Rw.mkW 2

theorem ga_cv : ga.cellv = 0 := rfl
theorem gb_cv : gb.cellv = 2 := rfl
theorem gc_cv : gc.cellv = 4 := rfl
theorem gd_cv : gd.cellv = 2 := rfl
theorem ge_cv : ge.cellv = 0 := rfl
theorem ge_eq : ge = Rw.free := rfl

theorem rwRel0 : RwRel rwLese cLay lcM0 mem0 (fun _ => ga) := by
  intro L
  cases L
  refine ⟨⟨List.nodup_nil, fun h => absurd h (by simp only [ga, Rw.free, Option.isSome_none, Bool.false_eq_true, not_false_eq_true]), by decide⟩,
    by show mem0.load (cLay.lblk ()) 0 lw = some (tk ga.cellv); decide +kernel, fun v => ?_,
    ⟨fun _ h => absurd h List.not_mem_nil, fun w h => absurd h (by simp only [ga, Rw.free, reduceCtorEq, not_false_eq_true])⟩⟩
  rw [lcM0_offen]
  simp only [Rw.holdsB, ga, Rw.free, List.not_mem_nil, decide_false, reduceCtorEq, Bool.or_self,
  Bool.false_eq_true, ↓reduceIte] <;> rfl

/-- All three threads stand at their first block. -/
def rwT0 : TM := ⟨mem0, fun t => if t = 2 then .run ⟨0, 10, 0, fun _ => none, none⟩ [] else
  .run ⟨0, 1, 0, fun _ => none, none⟩ []⟩

theorem rwT0_0 : AtB rwT0 0 0 1 (fun _ => none) [] none := rfl
theorem rwT0_1 : AtB rwT0 1 0 1 (fun _ => none) [] none := rfl
theorem rwT0_2 : AtB rwT0 2 0 10 (fun _ => none) [] none := rfl

/-- **The reader/writer lock, two readers and a writer.** -/
theorem rw_witness :
    ∃ (T : TM) (M : RufMaschineG cD),
      -- both readers hold at once, and the invariant is the layer's exclusion
      (∃ (T2 : TM) (M2 : RufMaschineG cD), RwRel rwLese cLay M2 T2.m (fun _ => gc) ∧
        lcL ∈ offen (M2.faeden 0).spur ∧ lcL ∈ offen (M2.faeden 1).spur ∧ RwExkl rwLese M2 ∧
        T2.m.load (cLay.lblk ()) 0 lw = some (tk 4)) ∧
      -- the writer takes the lock with nobody holding, and holds it alone
      RufFreiG (mDel (mDel (mAdd (mAdd lcM0 0) 1) 0) 1) 2 () ∧ RwRel rwLese cLay M T.m (fun _ => gf) ∧
      lcL ∈ offen (M.faeden 2).spur ∧ lcL ∉ offen (M.faeden 0).spur ∧ lcL ∉ offen (M.faeden 1).spur ∧
      T.m.load (cLay.lblk ()) 0 lw = some (tk 1) := by
  -- both readers load the free word
  obtain ⟨T1, r1, a1, o1, m1⟩ := rd_load_go_step (S := Sees.shared cLay) rwRel0 () rw_blk1 rw_blk2 rfl
    (rw_sees (rwRel0 ()).2.1 _) 0 (rs := fun _ => none) (ks := []) (dst := none) (T := rwT0) rwT0_0 rfl
  have b1 : AtB T1 1 0 1 (fun _ => none) [] none := (o1 1 (by decide)).trans rwT0_1
  have R1 : RwRel rwLese cLay lcM0 T1.m (fun _ => ga) := by rw [m1]; exact rwRel0
  obtain ⟨T2, r2, a2, o2, m2⟩ := rd_load_go_step (S := Sees.shared cLay) R1 () rw_blk1 rw_blk2 rfl
    (rw_sees (R1 ()).2.1 _) 1 (rs := fun _ => none) (ks := []) (dst := none) (T := T1) b1 rfl
  have R2 : RwRel rwLese cLay lcM0 T2.m (fun _ => ga) := by rw [m2]; exact R1
  have c0 : AtB T2 0 0 2 (Regs.set (fun _ => none) 1 (tk ga.cellv)) [] none := (o2 0 (by decide)).trans a1
  have c1 : AtB T2 1 0 2 (Regs.set (fun _ => none) 1 (tk ga.cellv)) [] none := a2
  -- thread 0's take wins: the shared acquisition (the word becomes 2)
  obtain ⟨hl0, hs0, ho0, T3, r3, a3, o3, st3, R3⟩ := rd_take_ok_step cLayOk (S := Sees.shared cLay) R2 ()
    rw_blk2 rw_blk5 rfl 0 c0 (x := 0) (regs_set_same _ _ _) (by decide) (by decide) rfl
    (rwLese_pos (by decide)) (by rw [lcM0_offen]; exact List.not_mem_nil) (by decide +kernel)
  have R3' : RwRel rwLese cLay (mAdd lcM0 0) T3.m (fun _ => gb) := by
    have := R3 (mAdd lcM0 0) (mAdd_offen lcM0 0)
    rw [updR_unit] at this
    exact this
  have c1' : AtB T3 1 0 2 (Regs.set (fun _ => none) 1 (tk ga.cellv)) [] none := (o3 1 (by decide)).trans c1
  have d2 : AtB T3 2 0 10 (fun _ => none) [] none :=
    (o3 2 (by decide)).trans ((o2 2 (by decide)).trans ((o1 2 (by decide)).trans rwT0_2))
  -- thread 1's take LOSES the race: the word is 2, it loaded 0 (G silent)
  obtain ⟨T4, r4, a4, o4, m4⟩ := rd_take_fail_step (S := Sees.shared cLay) R3' () rw_blk2 rw_blk1 rfl 1 c1'
    (x := 0) (regs_set_same _ _ _) (by decide) (by decide +kernel)
  have R4 : RwRel rwLese cLay (mAdd lcM0 0) T4.m (fun _ => gb) := by rw [m4]; exact R3'
  -- thread 1 loads again: the word is 2
  obtain ⟨T5, r5, a5, o5, m5⟩ := rd_load_go_step (S := Sees.shared cLay) R4 () rw_blk1 rw_blk2 rfl
    (rw_sees (R4 ()).2.1 _) 1 a4 (rfl : gb.writer = none)
  have R5 : RwRel rwLese cLay (mAdd lcM0 0) T5.m (fun _ => gb) := by rw [m5]; exact R4
  -- thread 1's take wins: BOTH READERS HOLD (the word becomes 4)
  obtain ⟨hl1, hs1, ho1, T6, r6, a6, o6, st6, R6⟩ := rd_take_ok_step cLayOk (S := Sees.shared cLay) R5 ()
    rw_blk2 rw_blk5 rfl 1 a5 (x := 2) (regs_set_same _ _ _) (by decide) (by decide +kernel) rfl
    (rwLese_pos (by decide))
    (by rw [mAdd_offen, if_neg (show (1 : Faden) ≠ 0 by decide), lcM0_offen]; exact List.not_mem_nil)
    (by decide +kernel)
  have R6' : RwRel rwLese cLay (mAdd (mAdd lcM0 0) 1) T6.m (fun _ => gc) := by
    have := R6 (mAdd (mAdd lcM0 0) 1) (mAdd_offen _ 1)
    rw [updR_unit] at this
    exact this
  -- the writer's take finds the word 4: it waits (G silent)
  have d6 : AtB T6 2 0 10 (fun _ => none) [] none :=
    (o6 2 (by decide)).trans ((o5 2 (by decide)).trans ((o4 2 (by decide)).trans d2))
  obtain ⟨T7, r7, a7, o7, m7⟩ := wr_take_fail_step (S := Sees.shared cLay) R6' () rw_blk10 rfl 2 d6
    (by decide +kernel)
  have R7 : RwRel rwLese cLay (mAdd (mAdd lcM0 0) 1) T7.m (fun _ => gc) := by rw [m7]; exact R6'
  -- thread 0 releases (word 2)
  have e0 := (o7 0 (by decide)).trans ((o6 0 (by decide)).trans ((o5 0 (by decide)).trans
    ((o4 0 (by decide)).trans a3)))
  obtain ⟨n8, hn8, T8, r8, a8, o8, st8, R8⟩ := rd_rel_step cLayOk (S := Sees.shared cLay) R7 () rw_blk5 rw_blk6
    rfl 0 e0 (by simp only [gc, Rw.addR, gb, ga, Rw.free, List.mem_cons, Nat.zero_ne_one, List.not_mem_nil, or_false, or_true])
  have R8' : RwRel rwLese cLay (mDel (mAdd (mAdd lcM0 0) 1) 0) T8.m (fun _ => gd) := by
    have := R8 (mDel (mAdd (mAdd lcM0 0) 1) 0) (mDel_offen _ 0)
    rw [updR_unit] at this
    exact this
  -- thread 1 releases (word 0)
  have e1 := (o8 1 (by decide)).trans ((o7 1 (by decide)).trans a6)
  obtain ⟨n9, hn9, T9, r9, a9, o9, st9, R9⟩ := rd_rel_step cLayOk (S := Sees.shared cLay) R8' () rw_blk5 rw_blk6
    rfl 1 e1 (by simp only [gd, Rw.delR, gc, Rw.addR, gb, ga, Rw.free, Nat.reduceBEq, Bool.false_eq_true, not_false_eq_true,
  List.erase_cons_tail, List.erase_cons_head, List.mem_cons, List.not_mem_nil, or_false])
  have R9' : RwRel rwLese cLay (mDel (mDel (mAdd (mAdd lcM0 0) 1) 0) 1) T9.m (fun _ => ge) := by
    have := R9 (mDel (mDel (mAdd (mAdd lcM0 0) 1) 0) 1) (mDel_offen _ 1)
    rw [updR_unit] at this
    exact this
  -- the writer's take wins: nobody holds
  have d9 := (o9 2 (by decide)).trans ((o8 2 (by decide)).trans a7)
  obtain ⟨hfree, hl2, hw2, T10, r10, a10, o10, st10, R10⟩ := wr_take_ok_step cLayOk (S := Sees.shared cLay)
    R9' () rw_blk10 rw_blk11 rfl 2 d9 (fun h => h rfl) rfl
  have R10' : RwRel rwLese cLay (mAdd (mDel (mDel (mAdd (mAdd lcM0 0) 1) 0) 1) 2) T10.m (fun _ => gf) := by
    have := R10 (mAdd (mDel (mDel (mAdd (mAdd lcM0 0) 1) 0) 1) 2) (mAdd_offen _ 2)
    rw [updR_unit] at this
    exact this
  refine ⟨T10, mAdd (mDel (mDel (mAdd (mAdd lcM0 0) 1) 0) 1) 2,
    ⟨T6, mAdd (mAdd lcM0 0) 1, R6', ?_, ?_, rwRel_exkl R6', (R6' ()).2.1⟩, hfree, R10', ?_, ?_, ?_,
    (R10' ()).2.1⟩
  · rw [mAdd_offen, if_neg (show (0 : Faden) ≠ 1 by decide), mAdd_offen, if_pos rfl]
    exact List.mem_cons_self
  · rw [mAdd_offen, if_pos rfl]
    exact List.mem_cons_self
  · rw [mAdd_offen, if_pos rfl]
    exact List.mem_cons_self
  · simp only [mAdd_offen, reduceCtorEq, ↓reduceIte, mDel_offen, Nat.zero_ne_one, lcL, lcM0_offen] <;> exact fun h => nomatch h
  · simp only [mAdd_offen, Nat.reduceEqDiff, ↓reduceIte, mDel_offen, Nat.succ_ne_self, lcL, lcM0_offen] <;> exact fun h => nomatch h

end C64R

end Gabbro.Code.Lower.WitC

#print axioms Gabbro.Code.Lower.WitC.rw_witness
