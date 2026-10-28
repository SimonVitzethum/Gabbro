import Grammatik.Code.Conc.GXStep

/-
  File:      Grammatik/Code/Conc/Lock.lean
  Subject:   TRACK L, PHASE L3 -- THE TICKET LOCK AS `Code`: the three blocks of an acquisition and a release, and the
             runs of a single thread through them.

  Lock `L` of machine G has no memory in G: it is a pair of events in the trace (`nimmt L`, `gibt L`) and the scheduler
  rule `RufFreiG` (no other thread holds it). The IR realises it as a TICKET LOCK on two word cells, the blocks
  `lay.lblk L` (the next ticket to hand out) and `lay.lsrv L` (the ticket now served), both zero at the start:

      take  : rt := fetch_add(next, 1)               (`armw add`, acquire)         -- block `lockTake`
      spin  : rs := serving                          (`aload`, acquire)            -- block `lockSpin`
              if rs = rt then goto body else spin    (`brc eq`)
      body  : ...                                     (the guarded section)
      rel   : serving := rt + 1                      (`astor`, release)            -- block `lockRel`

  A ticket is a word, `tk n` (`n` modulo `2 ^ wbits`); the serving cell is written only by the holder. The runs here
  are the thread-local facts; the invariant over all threads and its simulation of G's `nimmt`/`gibt` steps are in
  `Conc/LockRel.lean`. The cells are no table, no global and no local (`LayoutOk.lkT/lkG/lkX`, `Fresh`), so no
  statement of `Refine/` ever sees them.
-/

namespace Gabbro.Code.Lower

variable [Conf]

open Gabbro.Grammatik (Deklaration)

variable {D : Deklaration}

/-- The word type of the lock cells. -/
def lw : Ty := .int Conf.wbits

/-- The ticket `n` as a word (modulo `2 ^ wbits`). -/
def tk (n : Nat) : Val := .int Conf.wbits (BitVec.ofNat Conf.wbits n)

/-- **Take a ticket**: `rt := fetch_add(next, 1)` (acquire), then spin. -/
def lockTake (lay : Layout D) (L : D.Lock) (rt : Reg) (lb lsp : Lbl) : Block :=
  ⟨lb, [], [.armw rt .add lw (.glob (lay.lblk L)) (.int Conf.wbits 1) .acq], .jmp lsp⟩

/-- **Spin**: `rs := serving` (acquire); enter the body if it is the ticket, else spin again. -/
def lockSpin (lay : Layout D) (L : D.Lock) (rt rs : Reg) (lsp kb : Lbl) : Block :=
  ⟨lsp, [], [.aload rs lw (.glob (lay.lsrv L)) .acq], .brc .eq Conf.wbits (.reg rt) (.reg rs) kb lsp⟩

/-- **Release**: `serving := rt + 1` (release store: only the holder writes the cell), then continue. -/
def lockRel (lay : Layout D) (L : D.Lock) (rt ru : Reg) (lb k : Lbl) : Block :=
  ⟨lb, [], [.bin ru .add Conf.wbits (.reg rt) (.int Conf.wbits 1),
    .astor lw (.reg ru) (.glob (lay.lsrv L)) .rel], .jmp k⟩

/-! ## 1. The instructions -/

theorem atomicOk_lw : atomicOk lw = true := by
  unfold atomicOk lw Ty.store Conf.wb
  rcases Conf.wide with h | h <;> simp only [h, Nat.reduceAdd, Nat.reduceDiv, decide_true]

theorem tk_add_one (n : Nat) : BitVec.ofNat Conf.wbits n + 1#Conf.wbits = BitVec.ofNat Conf.wbits (n + 1) := by
  rw [BitVec.ofNat_add]

theorem icmp_tk (a b : Nat) : Val.icmp .eq Conf.wbits (tk a) (tk b) =
    some (Val.bool (decide (BitVec.ofNat Conf.wbits a = BitVec.ofNat Conf.wbits b))) := by
  simp only [Val.icmp, tk, ↓reduceDIte, IPred.ap]

theorem tk_ty (n : Nat) : (tk n).ty = lw := rfl

/-- `fetch_add(next, 1)` returns the old ticket and stores the next. -/
theorem stepI_take {m m' : Mem} {rs : Regs} {d : Reg} {b : Nat} {n : Nat} {o : Order}
    (hl : m.load b 0 lw = some (tk n)) (hs : m.store b 0 lw (tk (n + 1)) = some m') :
    stepI (.armw d .add lw (.glob b) (.int Conf.wbits 1) o) m rs = some (m', rs.set d (tk n)) := by
  have hap : RmwOp.ap .add (tk n) (Val.ofInt Conf.wbits 1) = some (tk (n + 1)) := by
    simp only [RmwOp.ap, tk, Val.ofInt, BitVec.ofInt_ofNat, ↓reduceDIte, tk_add_one]
  simp only [stepI, Opd.ev, atomicOk_lw, if_true, hl, hap, hs, Option.map_some]

/-- The release's sum. -/
theorem stepI_succ {m : Mem} {rs : Regs} {d : Reg} {r : Reg} {a : Nat} (hr : rs r = some (tk a)) :
    stepI (.bin d .add Conf.wbits (.reg r) (.int Conf.wbits 1)) m rs = some (m, rs.set d (tk (a + 1))) := by
  simp only [stepI, Opd.ev, hr, tk, Val.ofInt, BitVec.ofInt_ofNat, Val.bin, ↓reduceDIte, BinOp.ap, tk_add_one,
  Option.map_some]

theorem stepI_astor_tk {m m' : Mem} {rs : Regs} {r : Reg} {b : Nat} {a : Nat} {o : Order}
    (hr : rs r = some (tk a)) (hs : m.store b 0 lw (tk a) = some m') :
    stepI (.astor lw (.reg r) (.glob b) o) m rs = some (m', rs) := by
  simp only [stepI, Opd.ev, hr, atomicOk_lw, if_true, hs, Option.map_some]

/-! ## 2. The runs of a thread -/

/-- **Take a ticket**: from `lockTake` to the spin block; the ticket register holds the old `next`. -/
theorem take_run {lay : Layout D} {L : D.Lock} {rt : Reg} {M : Modl} {S : Sees} {fn : Nat} {lb lsp : Lbl}
    {bsp : Block} (hb : M.blk fn lb = some (lockTake lay L rt lb lsp)) (hsp : M.blk fn lsp = some bsp)
    (hp : bsp.phis = []) {m m' : Mem} {rs : Regs} {ks : List Frame} {dst : Option Reg} {n : Nat}
    (hl : m.load (lay.lblk L) 0 lw = some (tk n)) (hs : m.store (lay.lblk L) 0 lw (tk (n + 1)) = some m') :
    Reach M S (.run m ⟨fn, lb, 0, rs, dst⟩ ks) (.run m' ⟨fn, lsp, 0, rs.set rt (tk n), dst⟩ ks) :=
  reach_block_jmp (b := lockTake lay L rt lb lsp) hb rfl hsp hp (by
    simp only [lockTake, seqI, stepI_take hl hs])

/-- **A spin that finds its ticket served** goes to the body, with the serving word in its register. -/
theorem spin_enter {lay : Layout D} {L : D.Lock} {rt rs' : Reg} {M : Modl} {S : Sees} {fn : Nat} {lsp kb : Lbl}
    {bk : Block} (hb : M.blk fn lsp = some (lockSpin lay L rt rs' lsp kb)) (hk : M.blk fn kb = some bk)
    (hkp : bk.phis = []) {m : Mem} {rs : Regs} {ks : List Frame} {dst : Option Reg} {a x : Nat}
    (hrt : rs rt = some (tk a)) (hld : m.load (lay.lsrv L) 0 lw = some (tk x)) (hS : S m (lay.lsrv L) 0 lw .acq (tk x))
    (heq : BitVec.ofNat Conf.wbits a = BitVec.ofNat Conf.wbits x) (hne : rt ≠ rs') :
    Reach M S (.run m ⟨fn, lsp, 0, rs, dst⟩ ks) (.run m ⟨fn, kb, 0, rs.set rs' (tk x), dst⟩ ks) := by
  have hbody : (lockSpin lay L rt rs' lsp kb).body[0]? = some (.aload rs' lw (.glob (lay.lsrv L)) .acq) := rfl
  have h1 := step_aload (M := M) (S := S) (f := ⟨fn, lsp, 0, rs, dst⟩) (blk := lockSpin lay L rt rs' lsp kb)
    (d := rs') (p := .glob (lay.lsrv L)) (ord := .acq) (m := m) (b := lay.lsrv L) (o := 0) (x := tk x) ks hb hbody rfl
    atomicOk_lw (inside_of_load hld) hS rfl
  have h2 : Step M S (.run m ⟨fn, lsp, 1, rs.set rs' (tk x), dst⟩ ks)
      (.run m ⟨fn, kb, 0, rs.set rs' (tk x), dst⟩ ks) := by
    refine step_term (blk := lockSpin lay L rt rs' lsp kb) ⟨hb, by simp only [lockSpin, List.length_cons, List.length_nil, Nat.zero_add, Std.le_refl], rfl⟩ ?_
    have e1 : (Opd.reg rt).ev (rs.set rs' (tk x)) = some (tk a) := by
      simp only [Opd.ev, Regs.set, hne, ↓reduceIte, hrt]
    have e2 : (Opd.reg rs').ev (rs.set rs' (tk x)) = some (tk x) := by
      simp only [Opd.ev, Regs.set, ↓reduceIte]
    have hbool : Val.bool (decide (BitVec.ofNat Conf.wbits a = BitVec.ofNat Conf.wbits x)) = .int 1 1 := by
      simp only [Val.bool, heq, decide_true, ↓reduceIte, BitVec.ofNat_eq_ofNat]
    simp only [lockSpin, stepTerm, e1, e2, icmp_tk, hbool, if_true]
    simp only [Frame.enter, hk, hkp, List.mapM_nil, Option.pure_def, List.foldl_nil, Option.map_some]
  exact Reach.trans (Reach.one h1) (Reach.one h2)

/-- **A spin that finds another ticket served** spins again. -/
theorem spin_wait {lay : Layout D} {L : D.Lock} {rt rs' : Reg} {M : Modl} {S : Sees} {fn : Nat} {lsp kb : Lbl}
    (hb : M.blk fn lsp = some (lockSpin lay L rt rs' lsp kb)) {m : Mem} {rs : Regs} {ks : List Frame}
    {dst : Option Reg} {a x : Nat} (hrt : rs rt = some (tk a)) (hld : m.load (lay.lsrv L) 0 lw = some (tk x))
    (hS : S m (lay.lsrv L) 0 lw .acq (tk x))
    (hne' : BitVec.ofNat Conf.wbits a ≠ BitVec.ofNat Conf.wbits x) (hne : rt ≠ rs') :
    Reach M S (.run m ⟨fn, lsp, 0, rs, dst⟩ ks) (.run m ⟨fn, lsp, 0, rs.set rs' (tk x), dst⟩ ks) := by
  have hbody : (lockSpin lay L rt rs' lsp kb).body[0]? = some (.aload rs' lw (.glob (lay.lsrv L)) .acq) := rfl
  have h1 := step_aload (M := M) (S := S) (f := ⟨fn, lsp, 0, rs, dst⟩) (blk := lockSpin lay L rt rs' lsp kb)
    (d := rs') (p := .glob (lay.lsrv L)) (ord := .acq) (m := m) (b := lay.lsrv L) (o := 0) (x := tk x) ks hb hbody rfl
    atomicOk_lw (inside_of_load hld) hS rfl
  have h2 : Step M S (.run m ⟨fn, lsp, 1, rs.set rs' (tk x), dst⟩ ks)
      (.run m ⟨fn, lsp, 0, rs.set rs' (tk x), dst⟩ ks) := by
    refine step_term (blk := lockSpin lay L rt rs' lsp kb) ⟨hb, by simp only [lockSpin, List.length_cons, List.length_nil, Nat.zero_add, Std.le_refl], rfl⟩ ?_
    have e1 : (Opd.reg rt).ev (rs.set rs' (tk x)) = some (tk a) := by
      simp only [Opd.ev, Regs.set, hne, ↓reduceIte, hrt]
    have e2 : (Opd.reg rs').ev (rs.set rs' (tk x)) = some (tk x) := by
      simp only [Opd.ev, Regs.set, ↓reduceIte]
    have hdec : decide (BitVec.ofNat Conf.wbits a = BitVec.ofNat Conf.wbits x) = false := decide_eq_false hne'
    have hbool : Val.bool (decide (BitVec.ofNat Conf.wbits a = BitVec.ofNat Conf.wbits x)) = .int 1 0 := by
      simp only [Val.bool, hne', decide_false, Bool.false_eq_true, ↓reduceIte, BitVec.ofNat_eq_ofNat]
    simp only [lockSpin, stepTerm, e1, e2, icmp_tk, hbool]
    simp only [Frame.enter, BitVec.ofNat_eq_ofNat, BitVec.zero_eq_one_iff, Nat.succ_ne_self, ↓reduceIte, hb,
  lockSpin, List.mapM_nil, Option.pure_def, List.foldl_nil, Option.map_some]
  exact Reach.trans (Reach.one h1) (Reach.one h2)

/-- **Release**: from `lockRel` to the continuation, the serving cell now `a + 1`. -/
theorem rel_run {lay : Layout D} {L : D.Lock} {rt ru : Reg} {M : Modl} {S : Sees} {fn : Nat} {lb k : Lbl}
    {bk : Block} (hb : M.blk fn lb = some (lockRel lay L rt ru lb k)) (hk : M.blk fn k = some bk)
    (hkp : bk.phis = []) {m m' : Mem} {rs : Regs} {ks : List Frame} {dst : Option Reg} {a : Nat}
    (hrt : rs rt = some (tk a)) (hs : m.store (lay.lsrv L) 0 lw (tk (a + 1)) = some m') :
    Reach M S (.run m ⟨fn, lb, 0, rs, dst⟩ ks) (.run m' ⟨fn, k, 0, rs.set ru (tk (a + 1)), dst⟩ ks) :=
  reach_block_jmp (b := lockRel lay L rt ru lb k) hb rfl hk hkp (by
    simp only [lockRel, seqI, stepI_succ hrt]
    rw [stepI_astor_tk (regs_set_same rs ru _) hs])

end Gabbro.Code.Lower
