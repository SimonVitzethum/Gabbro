import Grammatik.Code.Conc.MaskRel
import Grammatik.Code.Conc.LockWitness

/-
  File:      Grammatik/Code/Conc/MaskWitness.lean
  Subject:   TRACK L, PHASE L3 -- A WITNESS of the masked lock: one thread runs the lowered section, the mask word and
             machine G's mask list move together, and the hardware assumption is satisfiable and not vacuous.

  The declaration of `Conc/LockWitness.lean` with its one lock DECLARED `masks irqs` (`mD`), the 64-bit target, the
  ticket-lock cells in blocks 2 and 3 and the mask word of core 0 in block 4 (`mbF 0`). The IR function

      1: maskOn (rm := imsk(mask, 1))   2: take   3: spin   4: release   5: maskOff (imsk(mask, rm))   6: ret

  and the start machine of machine G (every thread a declared start, no lock held). Thread 0 runs the section:
    * `mask_on_step`: the mask word reads `1`, the old word `0` is saved in `rm`;
    * `take_step`, `spin_enter_step`: the ticket lock of `LockWitness`; G takes the lock and its mask list for core 0
      becomes `[(0, ())]` -- `maskCells_nach`: the cover holds (the word is already `1`);
    * `release_step`: G releases, its list empties; the cover holds;
    * `mask_off_step`: the saved word `0` comes back.
  `mask_witness` states the end: the word reads `0` again and G's list is empty. `maskHw_witness`: the obligations
  `MaskHw` hold for a CPU that IS the memory (so the assumption is satisfiable), and `maskHw_planted` is the planted
  defect: a CPU that takes an interrupt on a masked core cannot meet it.
-/

namespace Gabbro.Code.Lower.WitC

open Gabbro.Grammatik
open Gabbro.Grammatik.Zielsatz (MaskeKern maskeNach maskEintr)

section C64

local instance confM64 : Conf := ⟨64, false, Or.inr rfl⟩

/-- The lock witness's declaration, its lock declared `masks irqs`. -/
def mD : Deklaration := { cD with maskiert := fun _ => true }

def mLay : Layout mD where
  gblk := fun _ => 0
  tty := fun _ => .arr 1 (.fld (.int 8) .unit)
  rty := fun _ => .fld (.int 8) .unit
  fidx := fun _ _ => 0
  ggblk := fun _ => 1
  lblk := fun _ => 2
  lsrv := fun _ => 3
  shared := fun _ => true
  fno := fun _ => 0

theorem mLayOk : LayoutOk mLay where
  tab := fun _ => rfl
  fld := fun t f _ => by cases t; cases f; exact ⟨0, by decide +kernel⟩
  inj := fun _ _ _ _ _ _ => rfl
  tinj := fun _ _ _ => rfl
  gdis := fun t g => by cases t; cases g; decide
  lkT := fun L t => by cases L; cases t; exact ⟨by decide, by decide⟩
  lkG := fun L g => by cases L; cases g; exact ⟨by decide, by decide⟩
  lkX := fun L L' => by cases L; cases L'; decide
  lkN := fun _ _ _ => rfl
  lkS := fun _ _ _ => rfl
  ginj := fun _ _ _ => rfl
  shAtomic := fun _ _ => rfl
  fsm := fun _ _ => Nat.two_pow_pos _

/-- The mask word of core `c`: block `4 + c`. -/
def mbF (c : Nat) : Nat := 4 + c

theorem mDisj : MaskDisj mLay mbF where
  lk := fun c L => by cases L; unfold mbF; exact ⟨by simp only [mLay, ne_eq]; try omega, by simp only [mLay, ne_eq]; try omega⟩
  tab := fun c t => by cases t; unfold mbF; simp only [mLay, ne_eq, Nat.add_eq_zero_iff, reduceCtorEq, false_and, not_false_eq_true]; try omega
  glob := fun c g => by cases g; unfold mbF; simp only [mLay, ne_eq]; try omega
  inj := fun c c' h => by unfold mbF at h; omega

/-- The table, the global, the two lock cells and the mask word of core 0, all zero. -/
def memM : Mem := (Mem.alloc mem0 8 true).1

def mP : Programm mD where
  invariante := fun i => nomatch i
  requires := fun _ => .tru
  ensures := fun _ => .tru
  rumpf := fun _ => .ret .empty (List.Perm.refl _)

def mSp : Speicher mD := ⟨fun _ _ _ => ⟨0, by decide, by decide⟩, fun _ => ⟨5, by decide, by decide⟩⟩

def mM0 : RufMaschineG mD := RufStartG mP mSp (fun _ => ⟨(), .nil⟩)

theorem mM0_offen (v : Faden) : offen (mM0.faeden v).spur = [] := rfl

def gm0 : mD.Lock → Tkt := fun _ => ⟨0, 0, fun _ => none, false⟩

theorem gm0_ok : (gm0 ()).Ok :=
  ⟨Nat.le_refl _, by decide, fun _ h1 h2 => absurd h2 (by simp only [gm0, Nat.zero_le, Nat.not_lt_zero, not_false_eq_true] at h1 ⊢), fun i _ _ h1 h2 _ _ _ _ =>
    absurd h2 (by simp only [gm0, Nat.zero_le, Nat.not_lt_zero, not_false_eq_true] at h1 ⊢), fun h => absurd h (by simp only [gm0, Bool.false_eq_true, not_false_eq_true])⟩

theorem mRel0 : LockRel mLay mM0 memM gm0 := by
  intro L
  cases L
  refine ⟨gm0_ok, ⟨by decide +kernel, by decide +kernel⟩, fun v => ?_⟩
  rw [mM0_offen]
  simp only [Tkt.holdsB, gm0, reduceCtorEq, decide_false, Bool.and_self, Bool.false_eq_true, ↓reduceIte]
  rfl

/-- The IR function. -/
def mMod : Modl :=
  ⟨[], [⟨"mlock", [], .void, [⟨0, [], [], .jmp 1⟩, maskOn (mbF 0) 3 1 2, lockTake mLay () 1 2 3,
    lockSpin mLay () 1 2 3 4, lockRel mLay () 1 5 4 5, maskOff (mbF 0) 3 6 5 6, ⟨6, [], [], .ret none⟩]⟩]⟩

theorem m_blk1 : mMod.blk 0 1 = some (maskOn (mbF 0) 3 1 2) := rfl
theorem m_blk2 : mMod.blk 0 2 = some (lockTake mLay () 1 2 3) := rfl
theorem m_blk3 : mMod.blk 0 3 = some (lockSpin mLay () 1 2 3 4) := rfl
theorem m_blk4 : mMod.blk 0 4 = some (lockRel mLay () 1 5 4 5) := rfl
theorem m_blk5 : mMod.blk 0 5 = some (maskOff (mbF 0) 3 6 5 6) := rfl
theorem m_blk6 : mMod.blk 0 6 = some ⟨6, [], [], .ret none⟩ := rfl

/-- The machine after thread 0 took the lock: its trace gained the `nimmt`. -/
def mM1 : RufMaschineG mD :=
  { mM0 with faeden := fun v => if v = 0 then
      { mM0.faeden v with spur := Ereignis.nimmt () [] :: (mM0.faeden v).spur } else mM0.faeden v }

/-- ... and after it released it: the `gibt`. -/
def mM2 : RufMaschineG mD :=
  { mM1 with faeden := fun v => if v = 0 then
      { mM1.faeden v with spur := Ereignis.gibt () :: (mM1.faeden v).spur } else mM1.faeden v }

theorem mM1_offen (v : Faden) : offen (mM1.faeden v).spur = if v = 0 then () :: offen (mM0.faeden v).spur
    else offen (mM0.faeden v).spur := by
  by_cases h : v = 0 <;> simp only [mM1, h, ↓reduceIte, offen] <;> rfl

theorem mM2_offen (v : Faden) : offen (mM2.faeden v).spur =
    if v = 0 then (offen (mM1.faeden v).spur).erase () else offen (mM1.faeden v).spur := by
  by_cases h : v = 0 <;> simp only [mM2, h, ↓reduceIte, offen]

theorem upd_unitM (gh : mD.Lock → Tkt) (t : Tkt) : upd gh () t = fun _ => t :=
  funext fun L => by cases L; exact upd_self gh () t

/-- The ghost states of the ticket lock along the run. -/
noncomputable def gm1 : Tkt := (gm0 ()).take 0
noncomputable def gm3 : Tkt := gm1.enter
noncomputable def gm5 : Tkt := gm3.leave

/-- One core. -/
def kernM : Faden → Nat := fun _ => 0

/-- G's mask list at the start, after the lock is taken, after it is released. -/
def mk0 : MaskeKern mD := fun _ => []
def mk1 : MaskeKern mD := maskeNach kernM mk0 0 (mM1.faeden 0).spur
def mk2 : MaskeKern mD := maskeNach kernM mk1 0 (mM2.faeden 0).spur

theorem mM1_spur : (mM1.faeden 0).spur = [Ereignis.nimmt () []] := rfl

theorem mM2_spur : (mM2.faeden 0).spur = [Ereignis.gibt (), Ereignis.nimmt () []] := rfl

theorem erase_unit : ([()] : List Unit).erase () = [] := rfl

theorem erase_unitM : ([()] : List mD.Lock).erase () = [] := rfl

theorem mk1_zero : mk1 0 = [(0, ())] := by
  simp only [mk1, maskeNach, kernM, ↓reduceIte, ne_eq, decide_not, mk0, List.filter_nil, maskEintr, mM1_spur,
  offen, List.nil_append]
  rfl

theorem mk2_zero : mk2 0 = [] := by
  simp only [mk2, maskeNach, kernM, ↓reduceIte, ne_eq, decide_not, mk1, mk0, List.filter_nil, maskEintr,
  mM1_spur, offen, List.nil_append, mM2_spur, List.append_eq_nil_iff, List.filter_eq_nil_iff, List.mem_map,
  List.mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, Decidable.not_not,
  forall_exists_index, and_imp, Prod.forall, Prod.mk.injEq, List.map_eq_nil_iff, Bool.not_eq_true]
  refine ⟨fun a b x _ _ h _ => h.symm, fun a ha => ?_⟩
  rw [erase_unitM] at ha
  exact absurd ha List.not_mem_nil

/-- **THE MASKED LOCK, ONE THREAD.** Thread 0 runs the section. While it holds the lock G's mask list of core 0 is
    `[(0, ())]` and the mask word reads `1`; after the release G's list is empty and the saved word `0` is back. The
    ticket-lock relation `LockRel` and the cover `MaskCells` hold at both stops. -/
theorem mask_witness :
    ∃ (T1 : TM) (M1 : RufMaschineG mD) (mkA : MaskeKern mD) (T2 : TM) (M2 : RufMaschineG mD)
      (mkB : MaskeKern mD),
      LockRel mLay M1 T1.m (fun _ => gm3) ∧ MaskCells mbF T1.m mkA ∧ mkA 0 = [(0, ())] ∧
        T1.m.load (mbF 0) 0 lw = some (tk 1) ∧ () ∈ offen (M1.faeden 0).spur ∧
      LockRel mLay M2 T2.m (fun _ => gm5) ∧ MaskCells mbF T2.m mkB ∧ mkB 0 = [] ∧
        T2.m.load (mbF 0) 0 lw = some (tk 0) ∧ () ∉ offen (M2.faeden 0).spur := by
  have hc0 : MaskCells mbF memM mk0 := fun c h => absurd rfl h
  have hex0 : ∃ x, memM.load (mbF 0) 0 lw = some x := ⟨tk 0, by decide +kernel⟩
  -- the mask: the word reads 1, the old word is saved
  obtain ⟨T1, x, r1, a1, o1, hx0, hs1, hx1, hc1⟩ := mask_on_step (S := Sees.shared mLay) mDisj.inj hc0 0 hex0
    (rm := 3) m_blk1 m_blk2 rfl 0 (T := ⟨memM, fun _ => .run ⟨0, 1, 0, fun _ => none, none⟩ []⟩) rfl
  have hx : x = tk 0 := by
    have h0 : memM.load (mbF 0) 0 lw = some (tk 0) := by decide +kernel
    have h1 : memM.load (mbF 0) 0 lw = some x := hx0
    rw [h0] at h1
    exact (Option.some.inj h1).symm
  subst hx
  have R1 : LockRel mLay mM0 T1.m gm0 := lockRel_mask_store mRel0 hs1 (fun L => mDisj.lk 0 L)
  -- the ticket is taken
  obtain ⟨T2, r2, a2, o2, m2, R2⟩ := take_step (S := Sees.shared mLay) mLayOk R1 () m_blk2 m_blk3 rfl 0 a1
    (fun i _ h2 => absurd h2 (Nat.not_lt_zero _)) (by decide)
  rw [upd_unitM] at R2
  have hc2 : MaskCells mbF T2.m mk0 := maskCells_ticket (L := ()) mDisj hc1 (Or.inl rfl) m2
  have hv2 : T2.m.load (mbF 0) 0 lw = some (tk 1) := by
    rw [load_store_other m2 (Or.inl (mDisj.lk 0 ()).1)]
    exact hx1
  -- the spin finds its ticket served: G takes the lock, its mask list gains (0, ())
  obtain ⟨hfree, T3, r3, a3, o3, m3, R3⟩ := spin_enter_step (S := Sees.shared mLay) R2 () m_blk3 m_blk4 rfl
    (sees_shared_lock (lay := mLay) (R2 ()).2.1.2 .acq) 0 a2 (a := 0) (regs_set_same _ _ _)
    ⟨by simp only [Tkt.take, gm0, Nat.zero_add, Std.le_refl], by simp only [Tkt.take, gm0, Nat.zero_add, Nat.lt_add_one], by simp only [Tkt.take, gm0, Nat.zero_add, ↓reduceIte]⟩
    (by simp only [Tkt.take, gm0, Nat.zero_add]) (by decide) (by rw [mM0_offen]; exact List.not_mem_nil)
  have R3' : LockRel mLay mM1 T3.m (fun _ => gm3) := by
    have := R3 mM1 mM1_offen
    rw [upd_unitM] at this
    exact this
  have hc3 : MaskCells mbF T3.m mk1 := by
    have h := maskCells_nach (mb := mbF) (m := T3.m) (mk := mk0) (by rw [m3]; exact hc2) kernM 0
      (mM1.faeden 0).spur (fun _ => ⟨tk 1, by rw [m3]; exact hv2, tk_one_ne⟩)
    exact h
  have hv3 : T3.m.load (mbF 0) 0 lw = some (tk 1) := by rw [m3]; exact hv2
  -- the release: G drops the lock, its list empties
  have a3' : AtB T3 0 0 4 _ [] none := a3
  obtain ⟨T4, r4, a4, o4, m4, R4⟩ := release_step (S := Sees.shared mLay) mLayOk R3' () m_blk4 m_blk5 rfl 0 a3'
    (by rw [regs_set_ne _ _ _ _ (by decide)]; exact regs_set_same _ _ _) rfl
    (by simp only [gm3, Tkt.enter, gm1, Tkt.take, gm0, Nat.zero_add, ↓reduceIte])
  have R4' : LockRel mLay mM2 T4.m (fun _ => gm5) := by
    have := R4 mM2 mM2_offen
    rw [upd_unitM] at this
    exact this
  have hc4 : MaskCells mbF T4.m mk1 := maskCells_ticket (L := ()) mDisj hc3 (Or.inr rfl) m4
  have hv4 : T4.m.load (mbF 0) 0 lw = some (tk 1) := by
    rw [load_store_other m4 (Or.inl (mDisj.lk 0 ()).2)]
    exact hv3
  have hc4' : MaskCells mbF T4.m mk2 := by
    have h := maskCells_nach (mb := mbF) (m := T4.m) (mk := mk1) hc4 kernM 0 (mM2.faeden 0).spur
      (fun hne => absurd (by
        simp only [maskEintr, mM2_spur, offen, List.map_eq_nil_iff, List.filter_eq_nil_iff, Bool.not_eq_true]
        intro a ha
        first | rw [erase_unitM] at ha | rw [erase_unit] at ha
        exact absurd ha List.not_mem_nil) hne)
    exact h
  -- the saved word comes back
  obtain ⟨T5, y, r5, a5, o5, hy, hs5, hy5, hc5⟩ := mask_off_step (S := Sees.shared mLay) mDisj.inj hc4' 0
    ⟨tk 1, hv4⟩ (rm := 3) (rx := 6) m_blk5 m_blk6 rfl 0 a4 (x := tk 0)
    (by rw [regs_set_ne _ _ _ _ (by decide), regs_set_ne _ _ _ _ (by decide), regs_set_ne _ _ _ _ (by decide)]
        exact regs_set_same _ _ _)
    (tk_ty 0) (fun h => absurd mk2_zero h)
  have R5 : LockRel mLay mM2 T5.m (fun _ => gm5) := lockRel_mask_store R4' hs5 (fun L => mDisj.lk 0 L)
  refine ⟨T3, mM1, mk1, T5, mM2, mk2, R3', hc3, mk1_zero, hv3, ?_, R5, hc5, mk2_zero, hy5, ?_⟩
  · rw [mM1_offen]
    simp only [↓reduceIte]
    exact List.mem_cons_self
  · rw [mM2_offen, mM1_offen, mM0_offen]
    simp only [↓reduceIte]
    exact fun h => List.not_mem_nil (show () ∈ ([] : List _) from h)

/-- **The hardware assumption is satisfiable**: a CPU that IS the memory (its state is the `Code` memory, a core is masked
    when its word is nonzero, an interrupt or a switch happens only on an unmasked core) meets `MaskHw`. -/
theorem maskHw_witness :
    MaskHw Mem (fun m _ x => x = m) mbF (fun c x => ∃ v, x.load (mbF c) 0 lw = some v ∧ v ≠ tk 0)
      (fun c x y => (¬ ∃ v, x.load (mbF c) 0 lw = some v ∧ v ≠ tk 0) ∧ y = x)
      (fun c x y => (¬ ∃ v, x.load (mbF c) 0 lw = some v ∧ v ≠ tk 0) ∧ y = x) where
  masked_of_cell := fun c m rs x v hrel hv hnz => by subst hrel; exact ⟨v, hv, hnz⟩
  irq_unmasked := fun c x y h => h.1
  switch_unmasked := fun c x y h => h.1

/-- **PLANTED DEFECT: a CPU that takes an interrupt on a masked core meets no `MaskHw`.** -/
theorem maskHw_planted (m : Mem) (hm : ∃ v, m.load (mbF 0) 0 lw = some v ∧ v ≠ tk 0) :
    ¬ MaskHw Mem (fun m' _ x => x = m') mbF (fun c x => ∃ v, x.load (mbF c) 0 lw = some v ∧ v ≠ tk 0)
      (fun _ _ _ => True) (fun _ _ _ => True) :=
  fun h => h.irq_unmasked 0 m m trivial hm

/-- **The guard, on the state the witness reaches**: inside the section the CPU of `maskHw_witness` takes no interrupt
    on core 0, and `irq_guard` says that is G's guard: had it entered a handler, G's list would be empty -- it is not. -/
theorem irq_refused_inside :
    ∃ (T1 : TM) (mkA : MaskeKern mD), mkA 0 ≠ [] ∧
      ∀ (y : Mem), ¬ ((¬ ∃ v, T1.m.load (mbF 0) 0 lw = some v ∧ v ≠ tk 0) ∧ y = T1.m) := by
  obtain ⟨T1, M1, mkA, -, -, -, -, hc, h0, hv, -⟩ := mask_witness
  refine ⟨T1, mkA, by rw [h0]; exact List.cons_ne_nil _ _, fun y h => h.1 ⟨tk 1, hv, tk_one_ne⟩⟩

#print axioms Gabbro.Code.Lower.WitC.mask_witness
#print axioms Gabbro.Code.Lower.WitC.maskHw_witness
#print axioms Gabbro.Code.Lower.WitC.maskHw_planted
#print axioms Gabbro.Code.Lower.WitC.irq_refused_inside

end C64

end Gabbro.Code.Lower.WitC
