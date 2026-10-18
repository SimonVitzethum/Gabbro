import Grammatik.Code.Conc.LockRel

/-
  File:      Grammatik/Code/Conc/RwLock.lean
  Subject:   THE READER/WRITER LOCK AS `Code` (Simon's decision, 2026-10-18; the model is the layer `RwSchritt`,
             `Zielsatz/Eigenschaften/RwSchritt.lean`): the blocks of a shared and an exclusive acquisition and of
             both releases, and the runs of a single thread through them.

  A lock `L` taken shared or exclusive is realised by ONE word cell, the state word, a cell that is no table, no
  global and no local (`lay.lblk L`, the cell the ticket lock calls "next"; a lock is either a ticket lock or a
  reader/writer lock, and the serving cell `lay.lsrv L` of a reader/writer lock stays unused):

      0      free
      2 k    held by k readers  (k ≥ 1)
      1      held by the writer

  ISA-neutral, release/acquire, no fences, no ISA instruction named:

      writer take  : (old, ok) := cas(state, 0, 1)            (acquire on success)    -- block `wrTake`
                     if ok then enter the section else take again
      writer rel   : state := 0                                (`astor`, release)      -- block `wrRel`
      reader load  : rs := state                               (`aload`, relaxed)      -- block `rdLoad`
                     if rs = 1 then load again else go to take
      reader take  : rn := rs + 2                                                       -- block `rdTake`
                     (old, ok) := cas(state, rs, rn)           (acquire on success)
                     if ok then enter the section else load again
      reader rel   : fetch_sub(state, 2)                       (`armw sub`, release)   -- block `rdRel`

  The odd word `1` marks the writer and the even words count the readers, so the writer's value needs no
  wrap-around argument: a reader count below `2 ^ (wbits - 1)` never collides with it. The unlocked words are
  stored modulo `2 ^ wbits` (`tk`), exactly as the ticket lock's; the counter bound is the one NAMED assumption of
  the take step (`rwRoom`).

  The runs here are the thread-local facts; the invariant over all threads and its simulation of the layer's steps
  (`RwSchritt`: G's `nimmt`/`gibt` for the writer, the shared acquisition for a reader) is in `Conc/RwLockRel.lean`.
-/

namespace Gabbro.Code.Lower

variable [Conf]

open Gabbro.Grammatik (Deklaration)

variable {D : Deklaration}

/-! ## 1. The blocks -/

/-- **Writer take**: `(rd, rk) := cas(state, 0, 1)`; on success enter the section `kb`, else take again. -/
def wrTake (lay : Layout D) (L : D.Lock) (rd rk : Reg) (lb kb : Lbl) : Block :=
  ⟨lb, [], [.cas rd rk lw (.glob (lay.lblk L)) (.int Conf.wbits 0) (.int Conf.wbits 1) .acq .rlx],
    .br (.reg rk) kb lb⟩

/-- **Writer release**: `state := 0` (release store: only the writer writes a held state), then continue. -/
def wrRel (lay : Layout D) (L : D.Lock) (lb k : Lbl) : Block :=
  ⟨lb, [], [.astor lw (.int Conf.wbits 0) (.glob (lay.lblk L)) .rel], .jmp k⟩

/-- **Reader load**: `rs := state`; load again while the writer holds (`rs = 1`), else go to the take. -/
def rdLoad (lay : Layout D) (L : D.Lock) (rs : Reg) (lb kc : Lbl) : Block :=
  ⟨lb, [], [.aload rs lw (.glob (lay.lblk L)) .rlx], .brc .eq Conf.wbits (.reg rs) (.int Conf.wbits 1) lb kc⟩

/-- **Reader take**: `rn := rs + 2`, `(rd, rk) := cas(state, rs, rn)`; on success enter the section `kb`, else
    load again at `lb0`. -/
def rdTake (lay : Layout D) (L : D.Lock) (rs rn rd rk : Reg) (lb kb lb0 : Lbl) : Block :=
  ⟨lb, [], [.bin rn .add Conf.wbits (.reg rs) (.int Conf.wbits 2),
    .cas rd rk lw (.glob (lay.lblk L)) (.reg rs) (.reg rn) .acq .rlx], .br (.reg rk) kb lb0⟩

/-- **Reader release**: `fetch_sub(state, 2)` (release), then continue. -/
def rdRel (lay : Layout D) (L : D.Lock) (rd : Reg) (lb k : Lbl) : Block :=
  ⟨lb, [], [.armw rd .sub lw (.glob (lay.lblk L)) (.int Conf.wbits 2) .rel], .jmp k⟩

/-! ## 2. The words -/

theorem ofInt_tk (n : Nat) : Val.ofInt Conf.wbits (n : Int) = tk n := by
  simp [Val.ofInt, tk]

theorem tk_ne_of_lt {a b : Nat} (ha : a < 2 ^ Conf.wbits) (hb : b < 2 ^ Conf.wbits) (h : a ≠ b) :
    tk a ≠ tk b := by
  intro e
  have e2 : BitVec.ofNat Conf.wbits a = BitVec.ofNat Conf.wbits b := by simpa [tk] using e
  have := ofNat_eq_iff.mp e2
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
  exact h this

theorem tk_inj {a b : Nat} (ha : a < 2 ^ Conf.wbits) (hb : b < 2 ^ Conf.wbits) (h : tk a = tk b) : a = b :=
  Classical.byContradiction fun hne => tk_ne_of_lt ha hb hne h

theorem wbits_big : 4 ≤ 2 ^ Conf.wbits := by
  rcases Conf.wide with h | h <;> rw [h] <;> decide

theorem tk_add (n k : Nat) : BitVec.ofNat Conf.wbits n + BitVec.ofNat Conf.wbits k = BitVec.ofNat Conf.wbits (n + k) := by
  rw [BitVec.ofNat_add]

theorem bv_sub2 (n : Nat) :
    BitVec.ofNat Conf.wbits (n + 2) - BitVec.ofNat Conf.wbits 2 = BitVec.ofNat Conf.wbits n := by
  rw [← tk_add n 2]
  exact BitVec.add_sub_cancel _ _

/-! ## 3. The instructions -/

/-- A successful `cas`: the expected word is there, the new one is stored, the flag is true. -/
theorem stepI_cas_ok {m m' : Mem} {rs : Regs} {d k : Reg} {b : Nat} {e n : Opd} {x y : Val} {o1 o2 : Order}
    (he : e.ev rs = some x) (hn : n.ev rs = some y) (hl : m.load b 0 lw = some x)
    (hs : m.store b 0 lw y = some m') :
    stepI (.cas d k lw (.glob b) e n o1 o2) m rs = some (m', (rs.set d x).set k (Val.bool true)) := by
  have h1 : (Opd.glob b).ev rs = some (.ptr b 0) := rfl
  simp only [stepI, h1, he, hn, atomicOk_lw, if_true, hl, hs, Option.map_some]

/-- A failed `cas`: another word is there; memory is untouched, the flag is false. -/
theorem stepI_cas_fail {m : Mem} {rs : Regs} {d k : Reg} {b : Nat} {e n : Opd} {x y z : Val} {o1 o2 : Order}
    (he : e.ev rs = some x) (hn : n.ev rs = some y) (hl : m.load b 0 lw = some z) (hne : z ≠ x) :
    stepI (.cas d k lw (.glob b) e n o1 o2) m rs = some (m, (rs.set d z).set k (Val.bool false)) := by
  have h1 : (Opd.glob b).ev rs = some (.ptr b 0) := rfl
  simp only [stepI, h1, he, hn, atomicOk_lw, if_true, hl, if_neg hne]

/-- `fetch_sub(state, 2)` returns the old word and stores the smaller. -/
theorem stepI_sub2 {m m' : Mem} {rs : Regs} {d : Reg} {b : Nat} {n : Nat} {o : Order}
    (hl : m.load b 0 lw = some (tk (n + 2))) (hs : m.store b 0 lw (tk n) = some m') :
    stepI (.armw d .sub lw (.glob b) (.int Conf.wbits 2) o) m rs = some (m', rs.set d (tk (n + 2))) := by
  have hap : RmwOp.ap .sub (tk (n + 2)) (Val.ofInt Conf.wbits 2) = some (tk n) := by
    have h2 : Val.ofInt Conf.wbits 2 = tk 2 := ofInt_tk 2
    rw [h2]
    simp [RmwOp.ap, tk, bv_sub2]
  have h1 : (Opd.glob b).ev rs = some (.ptr b 0) := rfl
  simp only [stepI, Opd.ev, atomicOk_lw, if_true, hl, hap, hs, Option.map_some]

/-- The constants of the blocks. -/
theorem opd_n (n : Nat) (rs : Regs) : (Opd.int Conf.wbits (n : Int)).ev rs = some (tk n) := by
  simp [Opd.ev, ofInt_tk]

theorem opd_0 (rs : Regs) : (Opd.int Conf.wbits 0).ev rs = some (tk 0) := opd_n 0 rs
theorem opd_1 (rs : Regs) : (Opd.int Conf.wbits 1).ev rs = some (tk 1) := opd_n 1 rs
theorem opd_2 (rs : Regs) : (Opd.int Conf.wbits 2).ev rs = some (tk 2) := opd_n 2 rs

/-- A release store of a word the operand evaluates to. -/
theorem stepI_astor_opd {m m' : Mem} {rs : Regs} {b : Nat} {v : Opd} {x : Val} {o : Order}
    (hv : v.ev rs = some x) (hs : m.store b 0 lw x = some m') :
    stepI (.astor lw v (.glob b) o) m rs = some (m', rs) := by
  have h1 : (Opd.glob b).ev rs = some (.ptr b 0) := rfl
  simp only [stepI, hv, h1, atomicOk_lw, if_true, hs, Option.map_some]

/-- `rn := rs + 2` for a register that holds the word `x`. -/
theorem stepI_add2 {m : Mem} {rs : Regs} {d r : Reg} {x : Nat} (hr : rs r = some (tk x)) :
    stepI (.bin d .add Conf.wbits (.reg r) (.int Conf.wbits 2)) m rs = some (m, rs.set d (tk (x + 2))) := by
  have h2 : (Opd.int Conf.wbits 2).ev rs = some (tk 2) := opd_2 rs
  have h1 : (Opd.reg r).ev rs = some (tk x) := hr
  simp only [stepI, h1, h2]
  simp [Val.bin, tk, BinOp.ap, BitVec.ofNat_add]

theorem bool_true : Val.bool true = .int 1 1 := rfl
theorem bool_false : Val.bool false = .int 1 0 := rfl

/-! ## 4. The runs of a thread: the writer -/

/-- **A writer's take that finds the lock free** enters the section, the state word now `1`. -/
theorem wr_take_ok {lay : Layout D} {L : D.Lock} {rd rk : Reg} {M : Modl} {S : Sees} {fn : Nat} {lb kb : Lbl}
    {bk : Block} (hb : M.blk fn lb = some (wrTake lay L rd rk lb kb)) (hk : M.blk fn kb = some bk)
    (hkp : bk.phis = []) {m m' : Mem} {rs : Regs} {ks : List Frame} {dst : Option Reg}
    (hl : m.load (lay.lblk L) 0 lw = some (tk 0)) (hs : m.store (lay.lblk L) 0 lw (tk 1) = some m') :
    Reach M S (.run m ⟨fn, lb, 0, rs, dst⟩ ks)
      (.run m' ⟨fn, kb, 0, (rs.set rd (tk 0)).set rk (Val.bool true), dst⟩ ks) := by
  have hseq : seqI (wrTake lay L rd rk lb kb).body m rs =
      some (m', (rs.set rd (tk 0)).set rk (Val.bool true)) := by
    simp only [wrTake, seqI, stepI_cas_ok (opd_0 rs) (opd_1 rs) hl hs]
  have hc : (Opd.reg rk).ev ((rs.set rd (tk 0)).set rk (Val.bool true)) = some (.int 1 1) := by
    rw [bool_true]; exact regs_set_same _ _ _
  have hk' : M.blk fn (if (1 : BitVec 1) = 1 then kb else lb) = some bk := by
    rw [if_pos rfl]; exact hk
  have := reach_block_br (S := S) (ks := ks) (dst := dst) hb rfl hseq hc hk' hkp
  rw [if_pos rfl] at this
  exact this

/-- **A writer's take that finds the lock held** (by readers or a writer) tries again, memory untouched. -/
theorem wr_take_fail {lay : Layout D} {L : D.Lock} {rd rk : Reg} {M : Modl} {S : Sees} {fn : Nat} {lb kb : Lbl}
    (hb : M.blk fn lb = some (wrTake lay L rd rk lb kb)) (hp : (wrTake lay L rd rk lb kb).phis = [])
    {m : Mem} {rs : Regs} {ks : List Frame} {dst : Option Reg} {y : Nat}
    (hl : m.load (lay.lblk L) 0 lw = some (tk y)) (hne : tk y ≠ tk 0) :
    Reach M S (.run m ⟨fn, lb, 0, rs, dst⟩ ks)
      (.run m ⟨fn, lb, 0, (rs.set rd (tk y)).set rk (Val.bool false), dst⟩ ks) := by
  have hseq : seqI (wrTake lay L rd rk lb kb).body m rs =
      some (m, (rs.set rd (tk y)).set rk (Val.bool false)) := by
    simp only [wrTake, seqI, stepI_cas_fail (opd_0 rs) (opd_1 rs) hl hne]
  have hc : (Opd.reg rk).ev ((rs.set rd (tk y)).set rk (Val.bool false)) = some (.int 1 0) := by
    rw [bool_false]; exact regs_set_same _ _ _
  have hk' : M.blk fn (if (0 : BitVec 1) = 1 then kb else lb) = some (wrTake lay L rd rk lb kb) := by
    rw [if_neg (by decide)]; exact hb
  have := reach_block_br (S := S) (ks := ks) (dst := dst) hb rfl hseq hc hk' hp
  rw [if_neg (by decide)] at this
  exact this

/-- **The writer's release** stores the free word. -/
theorem wr_rel_run {lay : Layout D} {L : D.Lock} {M : Modl} {S : Sees} {fn : Nat} {lb k : Lbl} {bk : Block}
    (hb : M.blk fn lb = some (wrRel lay L lb k)) (hk : M.blk fn k = some bk) (hkp : bk.phis = [])
    {m m' : Mem} {rs : Regs} {ks : List Frame} {dst : Option Reg}
    (hs : m.store (lay.lblk L) 0 lw (tk 0) = some m') :
    Reach M S (.run m ⟨fn, lb, 0, rs, dst⟩ ks) (.run m' ⟨fn, k, 0, rs, dst⟩ ks) :=
  reach_block_jmp (b := wrRel lay L lb k) hb rfl hk hkp (by
    simp only [wrRel, seqI, stepI_astor_opd (opd_0 rs) hs])

/-! ## 5. The runs of a thread: the reader -/

/-- **A reader's load that finds the writer** (`state = 1`) loads again. -/
theorem rd_load_wait {lay : Layout D} {L : D.Lock} {rs' : Reg} {M : Modl} {S : Sees} {fn : Nat} {lb kc : Lbl}
    (hb : M.blk fn lb = some (rdLoad lay L rs' lb kc)) {m : Mem} {rs : Regs} {ks : List Frame}
    {dst : Option Reg} (hld : m.load (lay.lblk L) 0 lw = some (tk 1))
    (hS : S m (lay.lblk L) 0 lw .rlx (tk 1)) :
    Reach M S (.run m ⟨fn, lb, 0, rs, dst⟩ ks) (.run m ⟨fn, lb, 0, rs.set rs' (tk 1), dst⟩ ks) := by
  have hbody : (rdLoad lay L rs' lb kc).body[0]? = some (.aload rs' lw (.glob (lay.lblk L)) .rlx) := rfl
  have h1 := step_aload (M := M) (S := S) (f := ⟨fn, lb, 0, rs, dst⟩) (blk := rdLoad lay L rs' lb kc)
    (d := rs') (p := .glob (lay.lblk L)) (ord := .rlx) (m := m) (b := lay.lblk L) (o := 0) (x := tk 1) ks hb
    hbody rfl atomicOk_lw (inside_of_load hld) hS rfl
  have h2 : Step M S (.run m ⟨fn, lb, 1, rs.set rs' (tk 1), dst⟩ ks)
      (.run m ⟨fn, lb, 0, rs.set rs' (tk 1), dst⟩ ks) := by
    refine step_term (blk := rdLoad lay L rs' lb kc) ⟨hb, by simp [rdLoad], rfl⟩ ?_
    have e1 : (Opd.reg rs').ev (rs.set rs' (tk 1)) = some (tk 1) := regs_set_same _ _ _
    have e2 : (Opd.int Conf.wbits 1).ev (rs.set rs' (tk 1)) = some (tk 1) := opd_1 _
    simp [rdLoad, stepTerm, e1, e2, icmp_tk, bool_true, Frame.enter, hb]
  exact Reach.trans (Reach.one h1) (Reach.one h2)

/-- **A reader's load that finds no writer** (`state = x`, `x ≠ 1`) goes to the take, with the word in its
    register. -/
theorem rd_load_go {lay : Layout D} {L : D.Lock} {rs' : Reg} {M : Modl} {S : Sees} {fn : Nat} {lb kc : Lbl}
    {bk : Block} (hb : M.blk fn lb = some (rdLoad lay L rs' lb kc)) (hk : M.blk fn kc = some bk)
    (hkp : bk.phis = []) {m : Mem} {rs : Regs} {ks : List Frame} {dst : Option Reg} {x : Nat}
    (hld : m.load (lay.lblk L) 0 lw = some (tk x)) (hS : S m (lay.lblk L) 0 lw .rlx (tk x))
    (hne : BitVec.ofNat Conf.wbits x ≠ BitVec.ofNat Conf.wbits 1) :
    Reach M S (.run m ⟨fn, lb, 0, rs, dst⟩ ks) (.run m ⟨fn, kc, 0, rs.set rs' (tk x), dst⟩ ks) := by
  have hbody : (rdLoad lay L rs' lb kc).body[0]? = some (.aload rs' lw (.glob (lay.lblk L)) .rlx) := rfl
  have h1 := step_aload (M := M) (S := S) (f := ⟨fn, lb, 0, rs, dst⟩) (blk := rdLoad lay L rs' lb kc)
    (d := rs') (p := .glob (lay.lblk L)) (ord := .rlx) (m := m) (b := lay.lblk L) (o := 0) (x := tk x) ks hb
    hbody rfl atomicOk_lw (inside_of_load hld) hS rfl
  have h2 : Step M S (.run m ⟨fn, lb, 1, rs.set rs' (tk x), dst⟩ ks)
      (.run m ⟨fn, kc, 0, rs.set rs' (tk x), dst⟩ ks) := by
    refine step_term (blk := rdLoad lay L rs' lb kc) ⟨hb, by simp [rdLoad], rfl⟩ ?_
    have e1 : (Opd.reg rs').ev (rs.set rs' (tk x)) = some (tk x) := regs_set_same _ _ _
    have e2 : (Opd.int Conf.wbits 1).ev (rs.set rs' (tk x)) = some (tk 1) := opd_1 _
    have hbool : Val.bool (decide (BitVec.ofNat Conf.wbits x = BitVec.ofNat Conf.wbits 1)) = .int 1 0 := by
      simp [Val.bool, hne]
    simp only [rdLoad, stepTerm, e1, e2, icmp_tk, hbool]
    simp [Frame.enter, hk, hkp, rdLoad]
  exact Reach.trans (Reach.one h1) (Reach.one h2)

/-- **A reader's take that wins the race**: the state word is still `x`, becomes `x + 2`; the section is
    entered. -/
theorem rd_take_ok {lay : Layout D} {L : D.Lock} {rs' rn rd rk : Reg} {M : Modl} {S : Sees} {fn : Nat}
    {lb kb lb0 : Lbl} {bk : Block} (hb : M.blk fn lb = some (rdTake lay L rs' rn rd rk lb kb lb0))
    (hk : M.blk fn kb = some bk) (hkp : bk.phis = []) {m m' : Mem} {rs : Regs} {ks : List Frame}
    {dst : Option Reg} {x : Nat} (hrs : rs rs' = some (tk x)) (hne : rs' ≠ rn)
    (hl : m.load (lay.lblk L) 0 lw = some (tk x)) (hs : m.store (lay.lblk L) 0 lw (tk (x + 2)) = some m') :
    Reach M S (.run m ⟨fn, lb, 0, rs, dst⟩ ks)
      (.run m' ⟨fn, kb, 0, (((rs.set rn (tk (x + 2))).set rd (tk x)).set rk (Val.bool true)), dst⟩ ks) := by
  have e1 : (Opd.reg rs').ev (rs.set rn (tk (x + 2))) = some (tk x) := by
    show (rs.set rn (tk (x + 2))) rs' = some (tk x)
    rw [regs_set_ne _ _ _ _ hne]; exact hrs
  have e2 : (Opd.reg rn).ev (rs.set rn (tk (x + 2))) = some (tk (x + 2)) := regs_set_same _ _ _
  have hseq : seqI (rdTake lay L rs' rn rd rk lb kb lb0).body m rs =
      some (m', (((rs.set rn (tk (x + 2))).set rd (tk x)).set rk (Val.bool true))) := by
    simp only [rdTake, seqI, stepI_add2 hrs, stepI_cas_ok e1 e2 hl hs]
  have hc : (Opd.reg rk).ev (((rs.set rn (tk (x + 2))).set rd (tk x)).set rk (Val.bool true)) =
      some (.int 1 1) := by
    rw [bool_true]; exact regs_set_same _ _ _
  have hk' : M.blk fn (if (1 : BitVec 1) = 1 then kb else lb0) = some bk := by
    rw [if_pos rfl]; exact hk
  have := reach_block_br (S := S) (ks := ks) (dst := dst) hb rfl hseq hc hk' hkp
  rw [if_pos rfl] at this
  exact this

/-- **A reader's take that loses the race**: the state word is `y ≠ x`; nothing is stored; load again. -/
theorem rd_take_fail {lay : Layout D} {L : D.Lock} {rs' rn rd rk : Reg} {M : Modl} {S : Sees} {fn : Nat}
    {lb kb lb0 : Lbl} {bk : Block} (hb : M.blk fn lb = some (rdTake lay L rs' rn rd rk lb kb lb0))
    (hk : M.blk fn lb0 = some bk) (hkp : bk.phis = []) {m : Mem} {rs : Regs} {ks : List Frame}
    {dst : Option Reg} {x y : Nat} (hrs : rs rs' = some (tk x)) (hne : rs' ≠ rn)
    (hl : m.load (lay.lblk L) 0 lw = some (tk y)) (hyx : tk y ≠ tk x) :
    Reach M S (.run m ⟨fn, lb, 0, rs, dst⟩ ks)
      (.run m ⟨fn, lb0, 0, (((rs.set rn (tk (x + 2))).set rd (tk y)).set rk (Val.bool false)), dst⟩ ks) := by
  have e1 : (Opd.reg rs').ev (rs.set rn (tk (x + 2))) = some (tk x) := by
    show (rs.set rn (tk (x + 2))) rs' = some (tk x)
    rw [regs_set_ne _ _ _ _ hne]; exact hrs
  have e2 : (Opd.reg rn).ev (rs.set rn (tk (x + 2))) = some (tk (x + 2)) := regs_set_same _ _ _
  have hseq : seqI (rdTake lay L rs' rn rd rk lb kb lb0).body m rs =
      some (m, (((rs.set rn (tk (x + 2))).set rd (tk y)).set rk (Val.bool false))) := by
    simp only [rdTake, seqI, stepI_add2 hrs, stepI_cas_fail e1 e2 hl hyx]
  have hc : (Opd.reg rk).ev (((rs.set rn (tk (x + 2))).set rd (tk y)).set rk (Val.bool false)) =
      some (.int 1 0) := by
    rw [bool_false]; exact regs_set_same _ _ _
  have hk' : M.blk fn (if (0 : BitVec 1) = 1 then kb else lb0) = some bk := by
    rw [if_neg (by decide)]; exact hk
  have := reach_block_br (S := S) (ks := ks) (dst := dst) hb rfl hseq hc hk' hkp
  rw [if_neg (by decide)] at this
  exact this

/-- **The reader's release** takes its two off the state word. -/
theorem rd_rel_run {lay : Layout D} {L : D.Lock} {rd : Reg} {M : Modl} {S : Sees} {fn : Nat} {lb k : Lbl}
    {bk : Block} (hb : M.blk fn lb = some (rdRel lay L rd lb k)) (hk : M.blk fn k = some bk)
    (hkp : bk.phis = []) {m m' : Mem} {rs : Regs} {ks : List Frame} {dst : Option Reg} {n : Nat}
    (hl : m.load (lay.lblk L) 0 lw = some (tk (n + 2))) (hs : m.store (lay.lblk L) 0 lw (tk n) = some m') :
    Reach M S (.run m ⟨fn, lb, 0, rs, dst⟩ ks) (.run m' ⟨fn, k, 0, rs.set rd (tk (n + 2)), dst⟩ ks) :=
  reach_block_jmp (b := rdRel lay L rd lb k) hb rfl hk hkp (by
    simp only [rdRel, seqI, stepI_sub2 hl hs])

#print axioms Gabbro.Code.Lower.wr_take_ok
#print axioms Gabbro.Code.Lower.wr_take_fail
#print axioms Gabbro.Code.Lower.wr_rel_run
#print axioms Gabbro.Code.Lower.rd_load_wait
#print axioms Gabbro.Code.Lower.rd_load_go
#print axioms Gabbro.Code.Lower.rd_take_ok
#print axioms Gabbro.Code.Lower.rd_take_fail
#print axioms Gabbro.Code.Lower.rd_rel_run

end Gabbro.Code.Lower
