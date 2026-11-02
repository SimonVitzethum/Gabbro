module

public import Grammatik.Code.Conc.RwLock
public import Grammatik.Zielsatz.Eigenschaften.Rw.RwSchritt
public import Grammatik.Code.Conc.RwLockRel.Teil1

@[expose] public section

namespace Gabbro.Code.Lower
variable [Conf]
open Gabbro.Grammatik (Deklaration Faden RufMaschineG RufFreiG offen)
open Gabbro.Grammatik.Zielsatz (Lese RwExkl)
variable {D : Deklaration}

/-- **The writer's take that finds the lock free** (G's `dannLocks`): the word is `0`, so no reader and no writer
    holds: `RufFreiG`. The thread is not a reader of `L`. Afterwards it holds alone. -/
theorem wr_take_ok_step {lay : Layout D} (hL : LayoutOk lay) {lese : Lese D} {M : RufMaschineG D} {T : TM}
    {gh : D.Lock → Rw} (hrel : RwRel lese lay M T.m gh) (L : D.Lock) {rd rk : Reg} {S : Sees} {Mod : Modl}
    {fn : Nat} {lb kb : Lbl} {bk : Block} (hb : Mod.blk fn lb = some (wrTake lay L rd rk lb kb))
    (hk : Mod.blk fn kb = some bk) (hkp : bk.phis = []) (u : Faden) {rs : Regs} {ks : List Frame}
    {dst : Option Reg} (hth : AtB T u fn lb rs ks dst) (hw : ¬ lese u L)
    (h0 : BitVec.ofNat Conf.wbits (gh L).cellv = BitVec.ofNat Conf.wbits 0) :
    RufFreiG M u L ∧ L ∉ offen (M.faeden u).spur ∧ ¬ lese u L ∧
      ∃ T' : TM, TReach Mod S T T' ∧
        AtB T' u fn kb ((rs.set rd (tk 0)).set rk (Val.bool true)) ks dst ∧
        (∀ v, v ≠ u → T'.th v = T.th v) ∧ T.m.store (lay.lblk L) 0 lw (tk 1) = some T'.m ∧
        ∀ M' : RufMaschineG D,
          (∀ v, offen (M'.faeden v).spur =
            if v = u then L :: offen (M.faeden v).spur else offen (M.faeden v).spur) →
          RwRel lese lay M' T'.m (updR gh L (Rw.mkW u)) := by
  classical
  obtain ⟨hok, hcell, hG, hmode⟩ := hrel L
  have hcv0 : (gh L).cellv = 0 := by
    have h2 := ofNat_eq_iff.mp h0
    rw [Nat.mod_eq_of_lt (Rw.cellv_lt hok), Nat.mod_eq_of_lt (by have := wbits_big; omega)] at h2
    exact h2
  have hwn : (gh L).writer = none := by
    cases hw' : (gh L).writer with
    | none => rfl
    | some w => rw [Rw.cellv_writer hw'] at hcv0; omega
  have hrd : (gh L).readers = [] := by
    have := Rw.cellv_free hwn
    rw [hcv0] at this
    cases hr : (gh L).readers with
    | nil => rfl
    | cons a l => rw [hr] at this; simp only [List.length_cons, reduceCtorEq] at this
  have hnobody : ∀ v, L ∉ offen (M.faeden v).spur := by
    intro v hv
    have := Rw.holdsB_iff.mp ((ghold_mem hG v).mp hv)
    rw [hrd, hwn] at this
    simp only [List.not_mem_nil, reduceCtorEq, or_self] at this
  have hfree : RufFreiG M u L := fun g _ => hnobody g
  have hcell0 : T.m.load (lay.lblk L) 0 lw = some (tk 0) := by
    have h := hcell
    unfold RwCells at h
    rw [hcv0] at h; exact h
  obtain ⟨m', hm'⟩ := store_of_load hcell0 (tk_ty 1)
  have hreach := wr_take_ok (S := S) hb hk hkp hcell0 hm' (rs := rs) (ks := ks) (dst := dst)
  refine ⟨hfree, hnobody u, hw, T.upd u (.run m' ⟨fn, kb, 0, (rs.set rd (tk 0)).set rk (Val.bool true), dst⟩ ks),
    treach_solo hreach T (cfg_of_atB hth), by simp only [AtB, TM.upd, ↓reduceIte], fun v hv => upd_other T _ hv, hm', ?_⟩
  intro M' hM'
  refine rwRel_step hL hrel hm' u (List.cons L) (fun L' hLL s => count_cons_ne hLL) hM'
    (Rw.mkW u) ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨List.nodup_nil, fun _ => rfl, ?_⟩
    have := wbits_big
    simp only [Rw.mkW, List.length_nil, Nat.mul_zero, Nat.zero_add, gt_iff_lt]; omega
  · show m'.load (lay.lblk L) 0 lw = some (tk (Rw.mkW u).cellv)
    have e1 : (Rw.mkW u).cellv = 1 := by simp only [Rw.cellv, Rw.mkW, Option.isSome_some, ↓reduceIte]
    rw [e1]
    exact load_store_of hm' (dec_enc_tk' _)
  · intro v
    rw [hM' v]
    by_cases hv : v = u
    · subst hv
      rw [if_pos rfl, count_cons_self_zero (hnobody v)]
      have : (Rw.mkW v).holdsB v = true := by simp only [Rw.holdsB, Rw.mkW, List.not_mem_nil, decide_false, decide_true, Bool.or_true]
      rw [this]; rfl
    · rw [if_neg hv]
      have h1 := hG v
      have hf : (gh L).holdsB v = false := by simp only [Rw.holdsB, hrd, List.not_mem_nil, decide_false, hwn, reduceCtorEq, Bool.or_self]
      have : (Rw.mkW u).holdsB v = false := by simp only [Rw.holdsB, Rw.mkW, List.not_mem_nil, decide_false, Option.some.injEq, Ne.symm hv, Bool.or_self]
      rw [this]
      rw [hf] at h1
      exact h1
  · refine ⟨fun v hv => absurd hv List.not_mem_nil, fun w hw' => ?_⟩
    simp only [Rw.mkW, Option.some.injEq] at hw'
    subst hw'
    exact hw

/-- **The writer's take that finds the lock held** (by readers or a writer): the word is not `0`; nothing is stored,
    it takes again (G silent). -/
theorem wr_take_fail_step {lay : Layout D} {lese : Lese D} {M : RufMaschineG D} {T : TM} {gh : D.Lock → Rw}
    (hrel : RwRel lese lay M T.m gh) (L : D.Lock) {rd rk : Reg} {S : Sees} {Mod : Modl} {fn : Nat}
    {lb kb : Lbl} (hb : Mod.blk fn lb = some (wrTake lay L rd rk lb kb))
    (hp : (wrTake lay L rd rk lb kb).phis = []) (u : Faden) {rs : Regs} {ks : List Frame} {dst : Option Reg}
    (hth : AtB T u fn lb rs ks dst) (hne : BitVec.ofNat Conf.wbits (gh L).cellv ≠ BitVec.ofNat Conf.wbits 0) :
    ∃ T' : TM, TReach Mod S T T' ∧
      AtB T' u fn lb ((rs.set rd (tk (gh L).cellv)).set rk (Val.bool false)) ks dst ∧
      (∀ v, v ≠ u → T'.th v = T.th v) ∧ T'.m = T.m := by
  obtain ⟨hok, hld, _, _⟩ := hrel L
  have hne' : tk (gh L).cellv ≠ tk 0 := by
    intro h
    apply hne
    have h2 : Val.int Conf.wbits (BitVec.ofNat Conf.wbits (gh L).cellv) =
        Val.int Conf.wbits (BitVec.ofNat Conf.wbits 0) := h
    injection h2
  have hreach := wr_take_fail (S := S) hb hp hld hne' (rs := rs) (ks := ks) (dst := dst)
  exact ⟨T.upd u (.run T.m ⟨fn, lb, 0, (rs.set rd (tk (gh L).cellv)).set rk (Val.bool false), dst⟩ ks),
    treach_solo hreach T (cfg_of_atB hth), by simp only [AtB, TM.upd, ↓reduceIte], fun v hv => upd_other T _ hv, rfl⟩

/-- **The writer's release** (G's `freiGib`): the word becomes `0`; the relation holds for the machine whose
    `offen` lost `L` for the writer. -/
theorem wr_rel_step {lay : Layout D} (hL : LayoutOk lay) {lese : Lese D} {M : RufMaschineG D} {T : TM}
    {gh : D.Lock → Rw} (hrel : RwRel lese lay M T.m gh) (L : D.Lock) {S : Sees} {Mod : Modl} {fn : Nat}
    {lb k : Lbl} {bk : Block} (hb : Mod.blk fn lb = some (wrRel lay L lb k)) (hk : Mod.blk fn k = some bk)
    (hkp : bk.phis = []) (u : Faden) {rs : Regs} {ks : List Frame} {dst : Option Reg}
    (hth : AtB T u fn lb rs ks dst) (hin : (gh L).writer = some u) :
    ∃ T' : TM, TReach Mod S T T' ∧ AtB T' u fn k rs ks dst ∧ (∀ v, v ≠ u → T'.th v = T.th v) ∧
      T.m.store (lay.lblk L) 0 lw (tk 0) = some T'.m ∧
      ∀ M' : RufMaschineG D,
        (∀ v, offen (M'.faeden v).spur =
          if v = u then (offen (M.faeden v).spur).erase L else offen (M.faeden v).spur) →
        RwRel lese lay M' T'.m (updR gh L Rw.free) := by
  classical
  obtain ⟨hok, hcell, hG, hmode⟩ := hrel L
  have hrd : (gh L).readers = [] := hok.excl (by rw [hin]; rfl)
  have hcell1 : T.m.load (lay.lblk L) 0 lw = some (tk 1) := by
    have h := hcell
    unfold RwCells at h
    rw [Rw.cellv_writer hin] at h; exact h
  obtain ⟨m', hm'⟩ := store_of_load hcell1 (tk_ty 0)
  have hreach := wr_rel_run (S := S) hb hk hkp hm' (rs := rs) (ks := ks) (dst := dst)
  refine ⟨T.upd u (.run m' ⟨fn, k, 0, rs, dst⟩ ks), treach_solo hreach T (cfg_of_atB hth),
    by simp only [AtB, TM.upd, ↓reduceIte], fun v hv => upd_other T _ hv, hm', ?_⟩
  intro M' hM'
  refine rwRel_step hL hrel hm' u (fun s => s.erase L)
    (fun L' hLL s => List.count_erase_of_ne hLL) hM' Rw.free ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨List.nodup_nil, fun h => by simp only [Rw.free, Option.isSome_none, Bool.false_eq_true] at h, ?_⟩
    have := wbits_big
    simp only [Rw.free, List.length_nil, Nat.mul_zero, Nat.zero_add, gt_iff_lt]; omega
  · show m'.load (lay.lblk L) 0 lw = some (tk Rw.free.cellv)
    have e1 : Rw.free.cellv = 0 := by simp only [Rw.cellv, Rw.free, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, List.length_nil,
  Nat.mul_zero]
    rw [e1]
    exact load_store_of hm' (dec_enc_tk' _)
  · intro v
    rw [hM' v]
    have hfalse : Rw.free.holdsB v = false := by simp only [Rw.holdsB, Rw.free, List.not_mem_nil, decide_false, reduceCtorEq, Bool.or_self]
    by_cases hv : v = u
    · subst hv
      rw [if_pos rfl]
      have h1 : (offen (M.faeden v).spur).count L = 1 := by
        have := hG v
        have hb' : (gh L).holdsB v = true := by simp only [Rw.holdsB, hin, decide_true, Bool.or_true]
        simpa [hb'] using this
      rw [hfalse, List.count_erase_self, h1]
      rfl
    · rw [if_neg hv]
      have h1 := hG v
      have hf : (gh L).holdsB v = false := by
        simp only [Rw.holdsB, hrd, List.not_mem_nil, decide_false, hin, Option.some.injEq, Ne.symm hv, Bool.or_self]
      rw [hfalse]
      rw [hf] at h1
      exact h1
  · refine ⟨fun v hv => absurd hv List.not_mem_nil, fun w hw' => ?_⟩
    simp only [Rw.free, reduceCtorEq] at hw'

#print axioms Gabbro.Code.Lower.rwRel_exkl
#print axioms Gabbro.Code.Lower.rd_take_ok_step
#print axioms Gabbro.Code.Lower.rd_rel_step
#print axioms Gabbro.Code.Lower.wr_take_ok_step
#print axioms Gabbro.Code.Lower.wr_rel_step

end Gabbro.Code.Lower
