import Grammatik.Code.Conc.LockRel
import Grammatik.Code.Conc.SharedWitness

/-
  File:      Grammatik/Code/Conc/LockWitness.lean
  Subject:   TRACK L, PHASE L3 -- A WITNESS of the ticket lock: two threads contend, the four step theorems run.

  On the declaration of `Conc/Witness.lean` (one lock) at the 64-bit target, with the IR function

      1: take   (rt := fetch_add next)      2: spin (rd := serving; rt = rd ? goto 3 : goto 2)
      3: release (serving := rt + 1)        4: ret

  and the start machine of machine G (two threads, no lock held). Thread 0 and thread 1 both stand at label 1.
    * thread 0 takes ticket 0, thread 1 takes ticket 1 (`take_step` twice);
    * thread 0 spins, finds its ticket served, and G takes the lock (`spin_enter_step`: `RufFreiG` holds);
    * thread 1 spins and finds ticket 0 served, not its own 1 (`spin_wait_step`): it waits;
    * thread 0 releases (`release_step`), thread 1 spins again and enters.
  The relation `LockRel` holds after every step; at the end G holds the lock in thread 1 only, and the cells read
  `next = 2`, `serving = 1`.
-/

namespace Gabbro.Code.Lower.WitC

open Gabbro.Grammatik

section C64

local instance confL64 : Conf := ⟨64, false, Or.inr rfl⟩

/-- The program: a function with an empty body (the lock code is IR only). -/
def lcP : Programm cD where
  invariante := fun i => nomatch i
  requires := fun _ => .tru
  ensures := fun _ => .tru
  rumpf := fun _ => .ret .empty (List.Perm.refl _)

/-- The start machine: two threads (all of them), no lock held. -/
def lcM0 : RufMaschineG cD := RufStartG lcP wld5.speicher (fun _ => ⟨(), .nil⟩)

theorem lcM0_offen (v : Faden) : offen (lcM0.faeden v).spur = [] := rfl

/-- The IR function: entry 0, take 1, spin 2, release 3 (the body is empty), return 4. -/
def lcMod : Modl :=
  ⟨[], [⟨"lock", [], .void, [⟨0, [], [], .jmp 1⟩, lockTake cLay () 1 1 2, lockSpin cLay () 1 2 2 3,
    lockRel cLay () 1 3 3 4, ⟨4, [], [], .ret none⟩]⟩]⟩

/-- The ghost state at the start: nothing handed out, nothing served. -/
def gh0 : cD.Lock → Tkt := fun _ => ⟨0, 0, fun _ => none, false⟩

theorem gh0_ok : (gh0 ()).Ok :=
  ⟨Nat.le_refl _, by decide, fun _ h1 h2 => absurd h2 (by simp only [gh0, Nat.zero_le, Nat.not_lt_zero, not_false_eq_true] at h1 ⊢), fun i _ _ h1 h2 _ _ _ _ =>
    absurd h2 (by simp only [gh0, Nat.zero_le, Nat.not_lt_zero, not_false_eq_true] at h1 ⊢), fun h => absurd h (by simp only [gh0, Bool.false_eq_true, not_false_eq_true])⟩

theorem lcRel0 : LockRel cLay lcM0 mem0 gh0 := by
  intro L
  cases L
  refine ⟨gh0_ok, ⟨by decide +kernel, by decide +kernel⟩, fun v => ?_⟩
  rw [lcM0_offen]
  simp only [Tkt.holdsB, gh0, reduceCtorEq, decide_false, Bool.and_self, Bool.false_eq_true, ↓reduceIte]
  rfl

/-- Both threads stand at the take block. -/
def lcT0 : TM := ⟨mem0, fun _ => .run ⟨0, 1, 0, fun _ => none, none⟩ []⟩

/-- The one lock of the declaration. -/
abbrev lcL : cD.Lock := ()

/-- The machine after thread 0 took the lock: its trace gained the `nimmt`. -/
def lcM1 : RufMaschineG cD :=
  { lcM0 with faeden := fun v => if v = 0 then
      { lcM0.faeden v with spur := Ereignis.nimmt lcL [] :: (lcM0.faeden v).spur } else lcM0.faeden v }

/-- ... and after thread 0 released it: the `gibt`. -/
def lcM2 : RufMaschineG cD :=
  { lcM1 with faeden := fun v => if v = 0 then
      { lcM1.faeden v with spur := Ereignis.gibt lcL :: (lcM1.faeden v).spur } else lcM1.faeden v }

/-- ... and after thread 1 took it. -/
def lcM3 : RufMaschineG cD :=
  { lcM2 with faeden := fun v => if v = 1 then
      { lcM2.faeden v with spur := Ereignis.nimmt lcL [] :: (lcM2.faeden v).spur } else lcM2.faeden v }

theorem lcM1_offen (v : Faden) : offen (lcM1.faeden v).spur = if v = 0 then lcL :: offen (lcM0.faeden v).spur
    else offen (lcM0.faeden v).spur := by
  by_cases h : v = 0 <;> simp only [lcM1, h, ↓reduceIte, offen] <;> rfl

theorem lcM2_offen (v : Faden) : offen (lcM2.faeden v).spur =
    if v = 0 then (offen (lcM1.faeden v).spur).erase lcL else offen (lcM1.faeden v).spur := by
  by_cases h : v = 0 <;> simp only [lcM2, h, ↓reduceIte, offen]

theorem lcM3_offen (v : Faden) : offen (lcM3.faeden v).spur =
    if v = 1 then lcL :: offen (lcM2.faeden v).spur else offen (lcM2.faeden v).spur := by
  by_cases h : v = 1 <;> simp only [lcM3, h, ↓reduceIte, offen] <;> rfl

theorem lc_blk1 : lcMod.blk 0 1 = some (lockTake cLay () 1 1 2) := rfl
theorem lc_blk2 : lcMod.blk 0 2 = some (lockSpin cLay () 1 2 2 3) := rfl
theorem lc_blk3 : lcMod.blk 0 3 = some (lockRel cLay () 1 3 3 4) := rfl
theorem lc_blk4 : lcMod.blk 0 4 = some ⟨4, [], [], .ret none⟩ := rfl

/-- The word interface answers the lock cells (they are no shared global). -/
theorem lc_sees {m : Mem} {b : Nat} {x : Val} (h : m.load b 0 lw = some x) :
    Sees.shared cLay m b 0 lw .acq x := Or.inr h

/-- With one lock the ghost state is a constant. -/
theorem upd_unit (gh : cD.Lock → Tkt) (t : Tkt) : upd gh () t = fun _ => t :=
  funext fun L => by cases L; exact upd_self gh () t

/-- The ghost states of the run. -/
noncomputable def g1 : Tkt := (gh0 ()).take 0
noncomputable def g2 : Tkt := g1.take 1
noncomputable def g3 : Tkt := g2.enter
noncomputable def g5 : Tkt := g3.leave
noncomputable def g6 : Tkt := g5.enter

/-- **The ticket lock, two threads.** Thread 0 takes ticket 0, thread 1 ticket 1; thread 0 finds its ticket served and
    G takes the lock (`RufFreiG`); thread 1 finds ticket 0 served and waits; thread 0 releases; thread 1 finds ticket 1
    served and G takes the lock for it. `LockRel` holds after every step. At the end G holds the lock in thread 1
    only, and the cells read `next = 2`, `serving = 1`. -/
theorem lock_witness :
    ∃ (T : TM) (M : RufMaschineG cD), RufFreiG lcM0 0 () ∧ RufFreiG lcM2 1 () ∧ LockRel cLay M T.m (fun _ => g6) ∧
      T.m.load (cLay.lblk ()) 0 lw = some (tk 2) ∧ T.m.load (cLay.lsrv ()) 0 lw = some (tk 1) ∧
      lcL ∈ offen (M.faeden 1).spur ∧ lcL ∉ offen (M.faeden 0).spur := by
  -- thread 0 takes ticket 0
  obtain ⟨T1, r1, a1, o1, _, R1⟩ := take_step (S := Sees.shared cLay) cLayOk lcRel0 () lc_blk1 lc_blk2 rfl 0
    (rs := fun _ => none) (ks := []) (dst := none) (T := lcT0) rfl (fun i _ h2 => absurd h2 (Nat.not_lt_zero _))
    (by decide)
  rw [upd_unit] at R1
  have h1 : AtB T1 1 0 1 (fun _ => none) [] none := (o1 1 (by decide)).trans rfl
  -- thread 1 takes ticket 1
  obtain ⟨T2, r2, a2, o2, _, R2⟩ := take_step (S := Sees.shared cLay) cLayOk R1 () lc_blk1 lc_blk2 rfl 1 h1
    (fun i h1 h2 => by
      have : i = 0 := by simp only [g1, Tkt.take, gh0] at h1 h2; omega
      subst this
      simp only [Tkt.take, gh0, Nat.zero_add, ↓reduceIte, ne_eq, Option.some.injEq, Nat.zero_ne_one,
  not_false_eq_true])
    (by simp only [g1, Tkt.take, gh0]; decide)
  rw [upd_unit] at R2
  have a1' : AtB T2 0 0 2 (Regs.set (fun _ => none) 1 (tk 0)) [] none := (o2 0 (by decide)).trans a1
  -- thread 0 spins, finds ticket 0 served: G takes the lock
  obtain ⟨hfree0, T3, r3, a3, o3, m3, R3⟩ := spin_enter_step (S := Sees.shared cLay) R2 () lc_blk2 lc_blk3 rfl
    (lc_sees (R2 ()).2.1.2) 0 a1' (a := 0) (regs_set_same _ _ _)
    ⟨by simp only [Tkt.take, gh0, Nat.zero_add, Nat.reduceAdd, Std.le_refl], by simp only [Tkt.take, gh0, Nat.zero_add, Nat.reduceAdd, Nat.zero_lt_succ],
      by simp only [Tkt.take, gh0, Nat.zero_add, Nat.reduceAdd, Nat.zero_ne_one, ↓reduceIte]⟩ (by simp only [Tkt.take, gh0, Nat.zero_add, Nat.reduceAdd]) (by decide)
    (by rw [lcM0_offen]; exact List.not_mem_nil)
  have R3' : LockRel cLay lcM1 T3.m (fun _ => g3) := by
    have := R3 lcM1 lcM1_offen
    rw [upd_unit] at this
    exact this
  -- thread 1 spins: ticket 1, served 0: it waits
  have a2' : AtB T3 1 0 2 (Regs.set (fun _ => none) 1 (tk 1)) [] none := (o3 1 (by decide)).trans a2
  obtain ⟨T4, r4, a4, o4, m4⟩ := spin_wait_step (S := Sees.shared cLay) R3' () lc_blk2
    (lc_sees (R3' ()).2.1.2) 1 a2' (a := 1) (regs_set_same _ _ _) ⟨by decide, by decide⟩ (by decide) (by decide)
  -- thread 0 releases
  have a3' : AtB T4 0 0 3 (Regs.set (Regs.set (fun _ => none) 1 (tk 0)) 2 (tk 0)) [] none :=
    (o4 0 (by decide)).trans a3
  have R4 : LockRel cLay lcM1 T4.m (fun _ => g3) := by rw [m4]; exact R3'
  obtain ⟨T5, r5, a5, o5, m5, R5⟩ := release_step (S := Sees.shared cLay) cLayOk R4 () lc_blk3 lc_blk4 rfl 0 a3'
    (by rw [regs_set_ne _ _ _ _ (by decide)]; exact regs_set_same _ _ _) rfl
    (by simp only [g3, Tkt.enter, g2, Tkt.take, g1, gh0, Nat.zero_add, Nat.reduceAdd, Nat.zero_ne_one, ↓reduceIte])
  have R5' : LockRel cLay lcM2 T5.m (fun _ => g5) := by
    have := R5 lcM2 lcM2_offen
    rw [upd_unit] at this
    exact this
  -- thread 1 spins again: ticket 1 is served now
  have a4' : AtB T5 1 0 2 (Regs.set (Regs.set (fun _ => none) 1 (tk 1)) 2 (tk 0)) [] none :=
    (o5 1 (by decide)).trans a4
  obtain ⟨hfree1, T6, r6, a6, o6, m6, R6⟩ := spin_enter_step (S := Sees.shared cLay) R5' () lc_blk2 lc_blk3 rfl
    (lc_sees (R5' ()).2.1.2) 1 a4' (a := 1) (by rw [regs_set_ne _ _ _ _ (by decide)]; exact regs_set_same _ _ _)
    ⟨by decide, by decide, by simp only [g5, Tkt.leave, g3, Tkt.enter, g2, Tkt.take, g1, gh0, Nat.zero_add, Nat.reduceAdd, ↓reduceIte]⟩ (by decide) (by decide)
    (by rw [lcM2_offen, if_neg (show (1 : Faden) ≠ 0 by decide), lcM1_offen, if_neg (show (1 : Faden) ≠ 0 by decide),
      lcM0_offen]; exact List.not_mem_nil)
  have R6' : LockRel cLay lcM3 T6.m (fun _ => g6) := by
    have := R6 lcM3 lcM3_offen
    rw [upd_unit] at this
    exact this
  refine ⟨T6, lcM3, hfree0, hfree1, R6', (R6' ()).2.1.1, (R6' ()).2.1.2, ?_, ?_⟩
  · rw [lcM3_offen, if_pos (rfl : (1 : Faden) = 1)]
    exact List.mem_cons_self
  · rw [lcM3_offen, if_neg (show (0 : Faden) ≠ 1 by decide), lcM2_offen, if_pos (rfl : (0 : Faden) = 0), lcM1_offen,
      if_pos (rfl : (0 : Faden) = 0), lcM0_offen]
    simp only [List.erase_cons_head, List.not_mem_nil, not_false_eq_true]

end C64

end Gabbro.Code.Lower.WitC
