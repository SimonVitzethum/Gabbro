import Grammatik.Code.Conc.Lock

/-
  File:      Grammatik/Code/Conc/LockRel.lean
  Subject:   TRACK L, PHASE L3 -- THE TICKET LOCK AGAINST MACHINE G'S LOCKS: the invariant over all threads, and the
             four steps that preserve it, three of them silent in G and two of them G's `nimmt`/`gibt`.

  GHOST STATE of one lock (`Tkt`): `s` tickets served (releases so far), `n` tickets handed out, `who i` the thread that
  took ticket `i`, `inside` whether the holder of ticket `s` entered the body. The counters are unbounded naturals; the
  CELLS hold them modulo `2 ^ wbits` (`tk`). The ONE assumption that makes the word compare faithful is NAMED and
  appears as a premise of the take step only: **fewer than `2 ^ wbits` tickets are outstanding on a lock at once**
  (`n - s < 2 ^ wbits`); no bound on the number of acquisitions over time is needed.

  THE INVARIANT `LockRel M T gh`, for every lock `L` (the ghost `gh L`):
    * `Tkt.ok`: `s ≤ n`, `n - s` below the word, the tickets of `[s, n)` have owners, one ticket per thread,
      `inside` only with a holder;
    * `LockCells`: the next cell holds `tk n`, the serving cell `tk s`;
    * `GHold`: machine G's held locks (`offen` of every thread's trace, counted) are exactly the holder: `L` is held once
      by the thread that owns ticket `s` while `inside`, by nobody else.

  THE STEPS (each a run of ONE thread, `treach_solo`; the other threads and the G machine are untouched unless said):
    * `take_step`   -- the ticket is taken (G silent): `n + 1`, the thread queued;
    * `spin_wait_step` -- a spin that finds another ticket (G silent);
    * `spin_enter_step` -- the spin that finds ITS ticket: here G takes the lock (`dannLocks`): `RufFreiG` holds, and the
      relation holds for the machine after the `nimmt` (`offen` gained `L` for this thread);
    * `release_step` -- the release store: G's `freiGib` (`offen` lost `L`), `s + 1`.
  `lockRel_exclusive`: two threads that hold `L` are one (mutual exclusion in G's own terms).
-/

namespace Gabbro.Code.Lower

variable [Conf]

open Gabbro.Grammatik (Deklaration Faden RufMaschineG RufFreiG offen)

variable {D : Deklaration}

/-! ## 1. The ghost state -/

/-- The ghost state of one ticket lock. -/
structure Tkt where
  /-- tickets served: the number of releases so far -/
  s : Nat
  /-- tickets handed out -/
  n : Nat
  /-- the thread that took ticket `i` (meaningful on `[s, n)`) -/
  who : Nat → Option Faden
  /-- the holder of ticket `s` has entered the body -/
  inside : Bool

/-- Does thread `u` hold the lock: it owns the served ticket and has entered. -/
def Tkt.holdsB (t : Tkt) (u : Faden) : Bool := t.inside && decide (t.who t.s = some u)

/-- The well-formedness of the ghost state. -/
structure Tkt.Ok (t : Tkt) : Prop where
  le : t.s ≤ t.n
  room : t.n - t.s < 2 ^ Conf.wbits
  owned : ∀ i, t.s ≤ i → i < t.n → ∃ u, t.who i = some u
  one : ∀ i j u, t.s ≤ i → i < t.n → t.s ≤ j → j < t.n → t.who i = some u → t.who j = some u → i = j
  held : t.inside = true → t.s < t.n

/-- The cells hold the counters. -/
def LockCells (lay : Layout D) (L : D.Lock) (m : Mem) (t : Tkt) : Prop :=
  m.load (lay.lblk L) 0 lw = some (tk t.n) ∧ m.load (lay.lsrv L) 0 lw = some (tk t.s)

/-- Machine G's held locks are the holder. -/
def GHold (M : RufMaschineG D) (L : D.Lock) (t : Tkt) : Prop :=
  ∀ u, (offen (M.faeden u).spur).count L = if t.holdsB u then 1 else 0

/-- **The invariant**: for every lock, the ghost state is well formed, the cells hold it, G agrees. -/
def LockRel (lay : Layout D) (M : RufMaschineG D) (m : Mem) (gh : D.Lock → Tkt) : Prop :=
  ∀ L, (gh L).Ok ∧ LockCells lay L m (gh L) ∧ GHold M L (gh L)

/-! ## 2. Facts -/

/-- The word compare is faithful: a ticket among the outstanding ones equals the served one iff the words do. -/
theorem ticket_eq {a s P : Nat} (hsa : s ≤ a) (hlt : a - s < P)
    (h : a % P = s % P) : a = s := by
  have h1 : (a - s) % P = 0 := Nat.sub_mod_eq_zero_of_mod_eq h
  have h2 : a - s = 0 := Nat.eq_zero_of_dvd_of_lt (Nat.dvd_of_mod_eq_zero h1) hlt
  omega

theorem ofNat_eq_iff {a b : Nat} :
    BitVec.ofNat Conf.wbits a = BitVec.ofNat Conf.wbits b ↔ a % 2 ^ Conf.wbits = b % 2 ^ Conf.wbits := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simpa [BitVec.toNat_ofNat] using this
  · intro h
    apply BitVec.eq_of_toNat_eq
    simpa [BitVec.toNat_ofNat] using h

/-- Mutual exclusion in G's terms: two threads that hold `L` are one. -/
theorem lockRel_exclusive {lay : Layout D} {M : RufMaschineG D} {m : Mem} {gh : D.Lock → Tkt}
    (h : LockRel lay M m gh) (L : D.Lock) {u v : Faden} (hu : L ∈ offen (M.faeden u).spur)
    (hv : L ∈ offen (M.faeden v).spur) : u = v := by
  have cu := (h L).2.2 u
  have cv := (h L).2.2 v
  have pu : 0 < (offen (M.faeden u).spur).count L := List.count_pos_iff.mpr hu
  have pv : 0 < (offen (M.faeden v).spur).count L := List.count_pos_iff.mpr hv
  have bu : (gh L).holdsB u = true := by
    cases hb : (gh L).holdsB u
    · rw [hb] at cu; simp [cu] at pu
    · rfl
  have bv : (gh L).holdsB v = true := by
    cases hb : (gh L).holdsB v
    · rw [hb] at cv; simp [cv] at pv
    · rfl
  simp only [Tkt.holdsB, Bool.and_eq_true, decide_eq_true_eq] at bu bv
  rw [bu.2] at bv
  exact Option.some.inj bv.2

theorem cells_other {lay : Layout D} {L : D.Lock} {m m' : Mem} {t : Tkt} {b : Nat} {o : Int} {ty : Ty} {x : Val}
    (h : LockCells lay L m t) (hs : m.store b o ty x = some m') (h1 : b ≠ lay.lblk L) (h2 : b ≠ lay.lsrv L) :
    LockCells lay L m' t :=
  ⟨by rw [load_store_other hs (Or.inl (fun e => h1 e.symm))]; exact h.1,
   by rw [load_store_other hs (Or.inl (fun e => h2 e.symm))]; exact h.2⟩

/-- A word interface answers the cell it holds: the interface `Sees.shared` on a lock cell. -/
theorem sees_shared_lock {lay : Layout D} {m : Mem} {b : Nat} {x : Val} (h : m.load b 0 lw = some x) (o : Order) :
    Sees.shared lay m b 0 lw o x := Or.inr h


/-! ## 3. The steps -/

open Classical in
/-- The ghost state after a ticket is taken by `u`. -/
noncomputable def Tkt.take (t : Tkt) (u : Faden) : Tkt :=
  { t with n := t.n + 1, who := fun i => if i = t.n then some u else t.who i }

/-- The ghost state after the holder entered. -/
def Tkt.enter (t : Tkt) : Tkt := { t with inside := true }

/-- The ghost state after the holder released. -/
def Tkt.leave (t : Tkt) : Tkt := { t with s := t.s + 1, inside := false }

open Classical in
/-- One lock's ghost state replaced. -/
noncomputable def upd (gh : D.Lock → Tkt) (L : D.Lock) (t : Tkt) : D.Lock → Tkt :=
  fun L' => if L' = L then t else gh L'

theorem upd_self (gh : D.Lock → Tkt) (L : D.Lock) (t : Tkt) : upd gh L t L = t := by
  simp [upd]

theorem upd_ne (gh : D.Lock → Tkt) {L L' : D.Lock} (t : Tkt) (h : L' ≠ L) : upd gh L t L' = gh L' := by
  simp [upd, h]

theorem take_ok {t : Tkt} (h : t.Ok) (u : Faden) (hnq : ∀ i, t.s ≤ i → i < t.n → t.who i ≠ some u)
    (hroom : t.n + 1 - t.s < 2 ^ Conf.wbits) : (t.take u).Ok := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show t.s ≤ t.n + 1
    have := h.le; omega
  · exact hroom
  · intro i h1 h2
    show ∃ v, (if i = t.n then some u else t.who i) = some v
    by_cases e : i = t.n
    · exact ⟨u, by simp [e]⟩
    · rw [if_neg e]
      exact h.owned i h1 (by simp only [Tkt.take] at h2; omega)
  · intro i j v h1 h2 h3 h4 e1 e2
    simp only [Tkt.take] at h2 h4 e1 e2 h1 h3
    by_cases ei : i = t.n <;> by_cases ej : j = t.n
    · omega
    · rw [if_pos ei] at e1
      rw [if_neg ej] at e2
      have hv : v = u := (Option.some.inj e1).symm
      subst hv
      exact absurd e2 (hnq j h3 (by omega))
    · rw [if_neg ei] at e1
      rw [if_pos ej] at e2
      have hv : v = u := (Option.some.inj e2).symm
      subst hv
      exact absurd e1 (hnq i h1 (by omega))
    · rw [if_neg ei] at e1
      rw [if_neg ej] at e2
      exact h.one i j v h1 (by omega) h3 (by omega) e1 e2
  · intro hin
    show t.s < t.n + 1
    have := h.held hin; omega

theorem take_holdsB (t : Tkt) (h : t.Ok) (u v : Faden) : (t.take u).holdsB v = t.holdsB v := by
  classical
  simp only [Tkt.holdsB, Tkt.take]
  by_cases hin : t.inside = true
  · have hs : t.s < t.n := h.held hin
    have : t.s ≠ t.n := by omega
    simp [if_neg this]
  · simp [hin]

theorem enter_ok {t : Tkt} (h : t.Ok) (hs : t.s < t.n) : t.enter.Ok :=
  ⟨h.le, h.room, h.owned, h.one, fun _ => hs⟩

theorem leave_ok {t : Tkt} (h : t.Ok) (hin : t.inside = true) : t.leave.Ok := by
  have hs := h.held hin
  refine ⟨?_, ?_, ?_, ?_, fun e => absurd e (by simp [Tkt.leave])⟩
  · show t.s + 1 ≤ t.n
    omega
  · show t.n - (t.s + 1) < 2 ^ Conf.wbits
    have := h.room; omega
  · intro i h1 h2
    exact h.owned i (by simp only [Tkt.leave] at h1; omega) h2
  · intro i j u h1 h2 h3 h4 e1 e2
    exact h.one i j u (by simp only [Tkt.leave] at h1; omega) h2 (by simp only [Tkt.leave] at h3; omega) h4 e1 e2

/-- A thread of the machine stands at the entry of a block. -/
def AtB (T : TM) (u : Faden) (fn : Nat) (lbl : Lbl) (rs : Regs) (ks : List Frame) (dst : Option Reg) : Prop :=
  T.th u = .run ⟨fn, lbl, 0, rs, dst⟩ ks

theorem cfg_of_atB {T : TM} {u : Faden} {fn : Nat} {lbl : Lbl} {rs : Regs} {ks : List Frame} {dst : Option Reg}
    (h : AtB T u fn lbl rs ks dst) : T.cfg u = .run T.m ⟨fn, lbl, 0, rs, dst⟩ ks := by
  have h' : T.th u = .run ⟨fn, lbl, 0, rs, dst⟩ ks := h
  simp [TM.cfg, h']

theorem dec_enc_tk (n : Nat) : Ty.dec lw (Val.enc (tk n)) = some (tk n) := dec_enc_int _ _

/-- **Take a ticket** (G silent). The thread is not queued on `L`, and fewer than `2 ^ wbits` tickets are
    outstanding afterwards (the one named assumption). -/
theorem take_step {lay : Layout D} (hL : LayoutOk lay) {M : RufMaschineG D} {T : TM} {gh : D.Lock → Tkt}
    (hrel : LockRel lay M T.m gh) (L : D.Lock) {rt : Reg} {S : Sees} {Mod : Modl} {fn : Nat} {lb lsp : Lbl}
    {bsp : Block} (hb : Mod.blk fn lb = some (lockTake lay L rt lb lsp)) (hsp : Mod.blk fn lsp = some bsp)
    (hp : bsp.phis = []) (u : Faden) {rs : Regs} {ks : List Frame} {dst : Option Reg}
    (hth : AtB T u fn lb rs ks dst) (hnq : ∀ i, (gh L).s ≤ i → i < (gh L).n → (gh L).who i ≠ some u)
    (hroom : (gh L).n + 1 - (gh L).s < 2 ^ Conf.wbits) :
    ∃ T' : TM, TReach Mod S T T' ∧ AtB T' u fn lsp (rs.set rt (tk (gh L).n)) ks dst ∧
      (∀ v, v ≠ u → T'.th v = T.th v) ∧ T.m.store (lay.lblk L) 0 lw (tk ((gh L).n + 1)) = some T'.m ∧
      LockRel lay M T'.m (upd gh L ((gh L).take u)) := by
  obtain ⟨hok, ⟨hcn, hcs⟩, hG⟩ := hrel L
  obtain ⟨m', hm'⟩ := store_of_load hcn (tk_ty _)
  have hreach := take_run (S := S) hb hsp hp (rs := rs) (ks := ks) (dst := dst) hcn hm'
  refine ⟨T.upd u (.run m' ⟨fn, lsp, 0, rs.set rt (tk (gh L).n), dst⟩ ks), treach_solo hreach T (cfg_of_atB hth),
    ?_, fun v hv => upd_other T _ hv, hm', ?_⟩
  · simp [AtB, TM.upd]
  · intro L'
    by_cases hLL : L' = L
    · subst hLL
      rw [upd_self]
      refine ⟨take_ok hok u hnq hroom, ⟨?_, ?_⟩, fun v => ?_⟩
      · exact load_store_of hm' (dec_enc_tk _)
      · show m'.load (lay.lsrv L') 0 lw = some (tk (gh L').s)
        rw [load_store_other hm' (Or.inl (fun e => (hL.lkX L' L') e.symm))]
        exact hcs
      · rw [take_holdsB _ hok]
        exact hG v
    · rw [upd_ne _ _ hLL]
      obtain ⟨hok', hc', hG'⟩ := hrel L'
      exact ⟨hok', cells_other hc' hm' (fun e => hLL (hL.lkN _ _ e.symm)) (fun e => hL.lkX _ _ e), hG'⟩

/-- The queued thread's ticket is the served one iff the words are equal. -/
theorem ticket_cmp {t : Tkt} (h : t.Ok) {a : Nat} (hq : t.s ≤ a ∧ a < t.n)
    (heq : BitVec.ofNat Conf.wbits a = BitVec.ofNat Conf.wbits t.s) : a = t.s :=
  ticket_eq (P := 2 ^ Conf.wbits) hq.1 (by have := h.room; omega) (ofNat_eq_iff.mp heq)

/-- **A spin that finds another ticket served** (G silent). -/
theorem spin_wait_step {lay : Layout D} {M : RufMaschineG D} {T : TM} {gh : D.Lock → Tkt}
    (hrel : LockRel lay M T.m gh) (L : D.Lock) {rt rd : Reg} {S : Sees} {Mod : Modl} {fn : Nat} {lsp kb : Lbl}
    (hb : Mod.blk fn lsp = some (lockSpin lay L rt rd lsp kb)) (hS : S T.m (lay.lsrv L) 0 lw .acq (tk (gh L).s))
    (u : Faden) {rs : Regs} {ks : List Frame} {dst : Option Reg} (hth : AtB T u fn lsp rs ks dst)
    {a : Nat} (hrt : rs rt = some (tk a)) (hq : (gh L).s ≤ a ∧ a < (gh L).n) (hne : rt ≠ rd)
    (hlt : a ≠ (gh L).s) :
    ∃ T' : TM, TReach Mod S T T' ∧ AtB T' u fn lsp (rs.set rd (tk (gh L).s)) ks dst ∧
      (∀ v, v ≠ u → T'.th v = T.th v) ∧ T'.m = T.m := by
  have hne' : BitVec.ofNat Conf.wbits a ≠ BitVec.ofNat Conf.wbits (gh L).s := fun h =>
    hlt (ticket_cmp (hrel L).1 hq h)
  have hreach := spin_wait (S := S) hb hrt (hrel L).2.1.2 hS hne' hne (ks := ks) (dst := dst)
  exact ⟨T.upd u (.run T.m ⟨fn, lsp, 0, rs.set rd (tk (gh L).s), dst⟩ ks),
    treach_solo hreach T (cfg_of_atB hth), by simp [AtB, TM.upd], fun v hv => upd_other T _ hv, rfl⟩

/-- **The spin that finds ITS ticket served** (G's `dannLocks`): the lock is free in G's terms, and after the `nimmt`
    the relation holds for the machine whose `offen` gained `L` for this thread. -/
theorem spin_enter_step {lay : Layout D} {M : RufMaschineG D} {T : TM} {gh : D.Lock → Tkt}
    (hrel : LockRel lay M T.m gh) (L : D.Lock) {rt rd : Reg} {S : Sees} {Mod : Modl} {fn : Nat} {lsp kb : Lbl}
    {bk : Block} (hb : Mod.blk fn lsp = some (lockSpin lay L rt rd lsp kb)) (hk : Mod.blk fn kb = some bk)
    (hkp : bk.phis = []) (hS : S T.m (lay.lsrv L) 0 lw .acq (tk (gh L).s))
    (u : Faden) {rs : Regs} {ks : List Frame} {dst : Option Reg} (hth : AtB T u fn lsp rs ks dst)
    {a : Nat} (hrt : rs rt = some (tk a)) (hq : (gh L).s ≤ a ∧ a < (gh L).n ∧ (gh L).who a = some u)
    (ha : a = (gh L).s) (hne : rt ≠ rd) (hself : L ∉ offen (M.faeden u).spur) :
    RufFreiG M u L ∧ ∃ T' : TM, TReach Mod S T T' ∧ AtB T' u fn kb (rs.set rd (tk (gh L).s)) ks dst ∧
      (∀ v, v ≠ u → T'.th v = T.th v) ∧ T'.m = T.m ∧
      ∀ M' : RufMaschineG D,
        (∀ v, offen (M'.faeden v).spur = if v = u then L :: offen (M.faeden v).spur else offen (M.faeden v).spur) →
        LockRel lay M' T'.m (upd gh L (gh L).enter) := by
  classical
  obtain ⟨hok, ⟨hcn, hcs⟩, hG⟩ := hrel L
  have hwho : (gh L).who (gh L).s = some u := by rw [← ha]; exact hq.2.2
  have hnin : (gh L).inside = false := by
    cases hin : (gh L).inside
    · rfl
    · exfalso
      have h1 := hG u
      have h2 : (gh L).holdsB u = true := by simp [Tkt.holdsB, hin, hwho]
      rw [h2] at h1
      have : 0 < (offen (M.faeden u).spur).count L := by simp [h1]
      exact hself (List.count_pos_iff.mp this)
  have hfree : RufFreiG M u L := by
    intro g hg hgl
    have h1 := hG g
    have h2 : (gh L).holdsB g = false := by simp [Tkt.holdsB, hnin]
    rw [h2] at h1
    have : (offen (M.faeden g).spur).count L = 0 := by simpa using h1
    exact (List.count_eq_zero.mp this) hgl
  have hreach := spin_enter (S := S) hb hk hkp hrt hcs hS (by rw [ha]) hne (ks := ks) (dst := dst)
  refine ⟨hfree, T.upd u (.run T.m ⟨fn, kb, 0, rs.set rd (tk (gh L).s), dst⟩ ks),
    treach_solo hreach T (cfg_of_atB hth), by simp [AtB, TM.upd], fun v hv => upd_other T _ hv, rfl, ?_⟩
  intro M' hM' L'
  by_cases hLL : L' = L
  · subst hLL
    rw [upd_self]
    refine ⟨enter_ok hok (by have := hq.2.1; omega), ⟨hcn, hcs⟩, fun v => ?_⟩
    rw [hM' v]
    by_cases hv : v = u
    · subst hv
      have hz : (offen (M.faeden v).spur).count L' = 0 := List.count_eq_zero.mpr hself
      have : (gh L').enter.holdsB v = true := by simp [Tkt.holdsB, Tkt.enter, hwho]
      simp [this, hz]
    · have h2 : (gh L').holdsB v = false := by simp [Tkt.holdsB, hnin]
      have h3 : (gh L').enter.holdsB v = false := by
        simp [Tkt.holdsB, Tkt.enter, hwho, Ne.symm hv]
      have h1 := hG v
      rw [h2] at h1
      simp [hv, h3, h1]
  · rw [upd_ne _ _ hLL]
    obtain ⟨hok', hc', hG'⟩ := hrel L'
    refine ⟨hok', hc', fun v => ?_⟩
    rw [hM' v]
    by_cases hv : v = u
    · subst hv
      have := hG' v
      simp [this, Ne.symm hLL]
    · simp [hv, hG' v]

/-- **The release** (G's `freiGib`): the serving cell becomes `s + 1`; the relation holds for the machine whose `offen`
    lost `L` for this thread. -/
theorem release_step {lay : Layout D} (hL : LayoutOk lay) {M : RufMaschineG D} {T : TM} {gh : D.Lock → Tkt}
    (hrel : LockRel lay M T.m gh) (L : D.Lock) {rt ru : Reg} {S : Sees} {Mod : Modl} {fn : Nat} {lb k : Lbl}
    {bk : Block} (hb : Mod.blk fn lb = some (lockRel lay L rt ru lb k)) (hk : Mod.blk fn k = some bk)
    (hkp : bk.phis = []) (u : Faden) {rs : Regs} {ks : List Frame} {dst : Option Reg}
    (hth : AtB T u fn lb rs ks dst) (hrt : rs rt = some (tk (gh L).s)) (hin : (gh L).inside = true)
    (hwho : (gh L).who (gh L).s = some u) :
    ∃ T' : TM, TReach Mod S T T' ∧ AtB T' u fn k (rs.set ru (tk ((gh L).s + 1))) ks dst ∧
      (∀ v, v ≠ u → T'.th v = T.th v) ∧ T.m.store (lay.lsrv L) 0 lw (tk ((gh L).s + 1)) = some T'.m ∧
      ∀ M' : RufMaschineG D,
        (∀ v, offen (M'.faeden v).spur = if v = u then (offen (M.faeden v).spur).erase L else offen (M.faeden v).spur) →
        LockRel lay M' T'.m (upd gh L (gh L).leave) := by
  classical
  obtain ⟨hok, ⟨hcn, hcs⟩, hG⟩ := hrel L
  obtain ⟨m', hm'⟩ := store_of_load hcs (tk_ty _)
  have hreach := rel_run (S := S) hb hk hkp hrt hm' (ks := ks) (dst := dst)
  refine ⟨T.upd u (.run m' ⟨fn, k, 0, rs.set ru (tk ((gh L).s + 1)), dst⟩ ks),
    treach_solo hreach T (cfg_of_atB hth), by simp [AtB, TM.upd], fun v hv => upd_other T _ hv, hm', ?_⟩
  intro M' hM' L'
  by_cases hLL : L' = L
  · subst hLL
    rw [upd_self]
    refine ⟨leave_ok hok hin, ⟨?_, ?_⟩, fun v => ?_⟩
    · show m'.load (lay.lblk L') 0 lw = some (tk (gh L').n)
      rw [load_store_other hm' (Or.inl (fun e => (hL.lkX L' L') e))]
      exact hcn
    · exact load_store_of hm' (dec_enc_tk _)
    · rw [hM' v]
      have hL1 : (offen (M.faeden u).spur).count L' = 1 := by
        have := hG u
        have h2 : (gh L').holdsB u = true := by simp [Tkt.holdsB, hin, hwho]
        simpa [h2] using this
      have hfalse : (gh L').leave.holdsB v = false := by simp [Tkt.holdsB, Tkt.leave]
      by_cases hv : v = u
      · subst hv
        simp [hfalse, List.count_erase_self, hL1]
      · have h2 : (gh L').holdsB v = false := by
          simp [Tkt.holdsB, hin, hwho, Ne.symm hv]
        have h1 := hG v
        rw [h2] at h1
        simp [hv, hfalse, h1]
  · rw [upd_ne _ _ hLL]
    obtain ⟨hok', hc', hG'⟩ := hrel L'
    refine ⟨hok', cells_other hc' hm' (fun e => hL.lkX L' L e.symm) (fun e => hLL (hL.lkS _ _ e.symm)), fun v => ?_⟩
    rw [hM' v]
    by_cases hv : v = u
    · subst hv
      rw [if_pos rfl, List.count_erase_of_ne hLL]
      exact hG' v
    · simp [hv, hG' v]

end Gabbro.Code.Lower
