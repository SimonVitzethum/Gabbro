import Grammatik.Code.Conc.RwLock
import Grammatik.Zielsatz.Eigenschaften.RwSchritt

/-
  File:      Grammatik/Code/Conc/RwLockRel.lean
  Subject:   THE READER/WRITER LOCK AS `Code` AGAINST THE LAYER `RwSchritt`: the invariant over all threads and the
             steps that preserve it -- a reader's take is the layer's SHARED ACQUISITION, a writer's take is machine
             G's `dannLocks`, both releases are G's `freiGib`; the loads and the failed takes are silent.

  GHOST STATE of one lock (`Rw`): `readers`, the threads that took it shared and have not released; `writer`, the
  thread that took it exclusively. The state WORD holds `cellv` modulo `2 ^ wbits` (`tk`): `1` while a writer holds,
  else `2 * |readers|`.

  THE ONE NAMED ASSUMPTION (the counterpart of the ticket lock's `n - s < 2 ^ wbits`): **fewer than `2 ^ (wbits - 1) - 1`
  readers hold a lock at once** (`Rw.Ok.room`: `2 * |readers| + 2 < 2 ^ wbits`, and the take step's premise for the
  reader that joins). It keeps the even words below the word size, so the word compare of `cas` is faithful.

  THE INVARIANT `RwRel lese M m gh`, for every lock `L` (the ghost `gh L`):
    * `Rw.Ok`: the readers are distinct, a writer holds alone, the room;
    * the state word holds `cellv`;
    * `GHoldR`: machine G's held locks (`offen` of every thread's trace, counted) are exactly the holders: a thread
      holds `L` once if it is a reader or the writer, else not at all;
    * `RwModeR`: the readers of the ghost are readers of the layer (`lese`), the writer is not.

  THE STEPS (each a run of ONE thread, `treach_solo`; the other threads are untouched):
    * `rd_load_wait_step`, `rd_load_go_step` -- the load (G silent);
    * `rd_take_ok_step` -- the take that wins: the layer's SHARED ACQUISITION (`lese u L`, every other holder of `L` is a
      reader, `u` did not hold), and the relation holds for the machine whose `offen` gained `L` for `u`;
    * `rd_take_fail_step` -- the take that loses (G silent);
    * `rd_rel_step` -- the reader's release (G's `freiGib`);
    * `wr_take_ok_step` -- the writer's take: G's `dannLocks`: `RufFreiG` holds (nobody holds);
    * `wr_take_fail_step` -- the writer finds the lock held (G silent);
    * `wr_rel_step` -- the writer's release (G's `freiGib`).
  `rwRel_exkl`: the invariant IMPLIES the layer's exclusion invariant `RwExkl` -- two different holders are readers.
-/

namespace Gabbro.Code.Lower

variable [Conf]

open Gabbro.Grammatik (Deklaration Faden RufMaschineG RufFreiG offen)
open Gabbro.Grammatik.Zielsatz (Lese RwExkl)

variable {D : Deklaration}

/-! ## 1. The ghost state -/

/-- The ghost state of one reader/writer lock. -/
structure Rw where
  readers : List Faden
  writer : Option Faden

/-- The state word, as a number (modulo `2 ^ wbits` it is the cell). -/
def Rw.cellv (g : Rw) : Nat := if g.writer.isSome then 1 else 2 * g.readers.length

/-- Does thread `u` hold the lock. -/
def Rw.holdsB (g : Rw) (u : Faden) : Bool := decide (u ∈ g.readers) || decide (g.writer = some u)

def Rw.addR (g : Rw) (u : Faden) : Rw := { g with readers := u :: g.readers }
def Rw.delR (g : Rw) (u : Faden) : Rw := { g with readers := g.readers.erase u }
def Rw.mkW (u : Faden) : Rw := ⟨[], some u⟩
def Rw.free : Rw := ⟨[], none⟩

/-- Well-formedness: distinct readers, a writer holds alone, room for one more reader's word. -/
structure Rw.Ok (g : Rw) : Prop where
  nodup : g.readers.Nodup
  excl : g.writer.isSome = true → g.readers = []
  room : 2 * g.readers.length + 2 < 2 ^ Conf.wbits

/-- The cell holds the state word. -/
def RwCells (lay : Layout D) (L : D.Lock) (m : Mem) (g : Rw) : Prop :=
  m.load (lay.lblk L) 0 lw = some (tk g.cellv)

/-- Machine G's held locks are the holders. -/
def GHoldR (M : RufMaschineG D) (L : D.Lock) (g : Rw) : Prop :=
  ∀ u, (offen (M.faeden u).spur).count L = if g.holdsB u then 1 else 0

/-- The readers of the ghost are readers of the layer; the writer is not. -/
def RwModeR (lese : Lese D) (L : D.Lock) (g : Rw) : Prop :=
  (∀ u ∈ g.readers, lese u L) ∧ (∀ w, g.writer = some w → ¬ lese w L)

/-- **The invariant**. -/
def RwRel (lese : Lese D) (lay : Layout D) (M : RufMaschineG D) (m : Mem) (gh : D.Lock → Rw) : Prop :=
  ∀ L, (gh L).Ok ∧ RwCells lay L m (gh L) ∧ GHoldR M L (gh L) ∧ RwModeR lese L (gh L)

open Classical in
/-- One lock's ghost state replaced. -/
noncomputable def updR (gh : D.Lock → Rw) (L : D.Lock) (g : Rw) : D.Lock → Rw :=
  fun L' => if L' = L then g else gh L'

theorem updR_self (gh : D.Lock → Rw) (L : D.Lock) (g : Rw) : updR gh L g L = g := by
  simp only [updR, ↓reduceIte]

theorem updR_ne (gh : D.Lock → Rw) {L L' : D.Lock} (g : Rw) (h : L' ≠ L) : updR gh L g L' = gh L' := by
  simp only [updR, h, ↓reduceIte]

/-! ## 2. Facts -/

theorem Rw.cellv_free {g : Rw} (h : g.writer = none) : g.cellv = 2 * g.readers.length := by
  simp only [cellv, h, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]

theorem Rw.cellv_writer {g : Rw} {w : Faden} (h : g.writer = some w) : g.cellv = 1 := by
  simp only [cellv, h, Option.isSome_some, ↓reduceIte]

theorem Rw.cellv_lt {g : Rw} (h : g.Ok) : g.cellv < 2 ^ Conf.wbits := by
  have hb := wbits_big
  have hr := h.room
  unfold Rw.cellv
  split <;> omega

/-- Holding in G's terms is holding in the ghost's. -/
theorem ghold_mem {M : RufMaschineG D} {L : D.Lock} {g : Rw} (h : GHoldR M L g) (u : Faden) :
    L ∈ offen (M.faeden u).spur ↔ g.holdsB u = true := by
  have hu := h u
  constructor
  · intro hm
    have : 0 < (offen (M.faeden u).spur).count L := List.count_pos_iff.mpr hm
    cases hb : g.holdsB u
    · rw [hb] at hu; simp only [hu, Bool.false_eq_true, ↓reduceIte, Nat.lt_irrefl] at this
    · rfl
  · intro hb
    rw [hb] at hu
    have : 0 < (offen (M.faeden u).spur).count L := by simp only [hu, ↓reduceIte, Nat.lt_add_one]
    exact List.count_pos_iff.mp this

theorem Rw.holdsB_iff {g : Rw} {u : Faden} : g.holdsB u = true ↔ u ∈ g.readers ∨ g.writer = some u := by
  simp only [holdsB, Bool.or_eq_true, decide_eq_true_eq]

/-- **The invariant implies the layer's exclusion invariant**: two different holders of a lock are both
    readers of it. -/
theorem rwRel_exkl {lese : Lese D} {lay : Layout D} {M : RufMaschineG D} {m : Mem} {gh : D.Lock → Rw}
    (h : RwRel lese lay M m gh) : RwExkl lese M := by
  intro t u L htu ht hu
  obtain ⟨hok, _, hG, hmode⟩ := h L
  have bt := Rw.holdsB_iff.mp ((ghold_mem hG t).mp ht)
  have bu := Rw.holdsB_iff.mp ((ghold_mem hG u).mp hu)
  have key : ∀ a b : Faden, a ≠ b → (a ∈ (gh L).readers ∨ (gh L).writer = some a) →
      (b ∈ (gh L).readers ∨ (gh L).writer = some b) → lese a L ∧ lese b L := by
    intro a b hab ba bb
    rcases ba with ra | wa
    · rcases bb with rb | wb
      · exact ⟨hmode.1 a ra, hmode.1 b rb⟩
      · have := hok.excl (by rw [wb]; rfl)
        rw [this] at ra
        exact absurd ra List.not_mem_nil
    · have := hok.excl (by rw [wa]; rfl)
      rcases bb with rb | wb
      · rw [this] at rb
        exact absurd rb List.not_mem_nil
      · rw [wa] at wb
        exact absurd (Option.some.inj wb) hab
  exact key t u htu bt bu

theorem cells_other_rw {lay : Layout D} {L : D.Lock} {m m' : Mem} {g : Rw} {b : Nat} {o : Int} {ty : Ty} {x : Val}
    (h : RwCells lay L m g) (hs : m.store b o ty x = some m') (h1 : b ≠ lay.lblk L) : RwCells lay L m' g := by
  show m'.load (lay.lblk L) 0 lw = some (tk g.cellv)
  rw [load_store_other hs (Or.inl (fun e => h1 e.symm))]
  exact h

theorem dec_enc_tk' (n : Nat) : lw.dec (Val.enc (tk n)) = some (tk n) := dec_enc_int _ _

/-- **A step that changes one lock**: a store into its state word, and the holding of one thread. Every other lock
    keeps its ghost, its cell and its holders. -/
theorem rwRel_step {lay : Layout D} (hL : LayoutOk lay) {lese : Lese D} {M M' : RufMaschineG D} {m m' : Mem}
    {gh : D.Lock → Rw} {L : D.Lock} {x : Val} (hrel : RwRel lese lay M m gh)
    (hs : m.store (lay.lblk L) 0 lw x = some m') (u : Faden) (f : List D.Lock → List D.Lock)
    (hf : ∀ L', L' ≠ L → ∀ s : List D.Lock, (f s).count L' = s.count L')
    (hM' : ∀ v, offen (M'.faeden v).spur = if v = u then f (offen (M.faeden v).spur) else offen (M.faeden v).spur)
    (g' : Rw) (hLp : g'.Ok ∧ RwCells lay L m' g' ∧ GHoldR M' L g' ∧ RwModeR lese L g') :
    RwRel lese lay M' m' (updR gh L g') := by
  intro L'
  by_cases hLL : L' = L
  · subst hLL
    rw [updR_self]
    exact hLp
  · rw [updR_ne _ _ hLL]
    obtain ⟨hok, hc, hG, hmode⟩ := hrel L'
    refine ⟨hok, cells_other_rw hc hs (fun e => hLL (hL.lkN _ _ e.symm)), fun v => ?_, hmode⟩
    rw [hM' v]
    by_cases hv : v = u
    · subst hv
      rw [if_pos rfl, hf L' hLL]
      exact hG v
    · rw [if_neg hv]
      exact hG v

/-- A store into a state word leaves the representation alone (the cells are no table, no global, no local):
    the ticket lock's `lock_store_post`, for the cell `lblk`. -/
theorem rw_store_post {lay : Layout D} (hL : LayoutOk lay) {L : D.Lock} {m m' : Mem} {o : Int} {t : Ty}
    {v : Val} (hs : m.store (lay.lblk L) o t v = some m') :
    (∀ σ : Gabbro.Grammatik.World D, Rep lay σ m → Rep lay σ m') ∧ (WfL lay m → WfL lay m') ∧
      (∀ (rs : Regs) (cenv : List Reg) {Γ : Gabbro.Grammatik.Ctx} (ρ : Gabbro.Grammatik.Env D Γ),
        EnvRep lay rs m cenv ρ → EnvRep lay rs m' cenv ρ) :=
  lock_store_post hL (Or.inl rfl) hs

/-! ## 3. The steps: the reader -/

theorem count_cons_self_zero {s : List D.Lock} {L : D.Lock} (h : L ∉ s) : (L :: s).count L = 1 := by
  simp only [List.count_cons_self, List.count_eq_zero.mpr h, Nat.zero_add]

theorem count_cons_ne {s : List D.Lock} {L L' : D.Lock} (h : L' ≠ L) : (L :: s).count L' = s.count L' := by
  simp only [ne_eq, h.symm, not_false_eq_true, List.count_cons_of_ne]

/-- **The reader's load** (G silent): the word it loads is the state word. If a writer holds, it loads again. -/
theorem rd_load_wait_step {lay : Layout D} {lese : Lese D} {M : RufMaschineG D} {T : TM} {gh : D.Lock → Rw}
    (hrel : RwRel lese lay M T.m gh) (L : D.Lock) {rs' : Reg} {S : Sees} {Mod : Modl} {fn : Nat} {lb kc : Lbl}
    (hb : Mod.blk fn lb = some (rdLoad lay L rs' lb kc)) (hS : S T.m (lay.lblk L) 0 lw .rlx (tk (gh L).cellv))
    (u : Faden) {rs : Regs} {ks : List Frame} {dst : Option Reg} (hth : AtB T u fn lb rs ks dst)
    {w : Faden} (hw : (gh L).writer = some w) :
    ∃ T' : TM, TReach Mod S T T' ∧ AtB T' u fn lb (rs.set rs' (tk 1)) ks dst ∧
      (∀ v, v ≠ u → T'.th v = T.th v) ∧ T'.m = T.m := by
  have hcv := Rw.cellv_writer hw
  have hld := (hrel L).2.1
  have hld' : T.m.load (lay.lblk L) 0 lw = some (tk 1) := by
    have h := hld; unfold RwCells at h; rw [hcv] at h; exact h
  have hS' : S T.m (lay.lblk L) 0 lw .rlx (tk 1) := by rw [hcv] at hS; exact hS
  have hreach := rd_load_wait (S := S) hb hld' hS' (rs := rs) (ks := ks) (dst := dst)
  exact ⟨T.upd u (.run T.m ⟨fn, lb, 0, rs.set rs' (tk 1), dst⟩ ks),
    treach_solo hreach T (cfg_of_atB hth), by simp only [AtB, TM.upd, ↓reduceIte], fun v hv => upd_other T _ hv, rfl⟩

/-- **The reader's load that finds no writer** goes to the take with the word (`2 * |readers|`) in its register. -/
theorem rd_load_go_step {lay : Layout D} {lese : Lese D} {M : RufMaschineG D} {T : TM} {gh : D.Lock → Rw}
    (hrel : RwRel lese lay M T.m gh) (L : D.Lock) {rs' : Reg} {S : Sees} {Mod : Modl} {fn : Nat} {lb kc : Lbl}
    {bk : Block} (hb : Mod.blk fn lb = some (rdLoad lay L rs' lb kc)) (hk : Mod.blk fn kc = some bk)
    (hkp : bk.phis = []) (hS : S T.m (lay.lblk L) 0 lw .rlx (tk (gh L).cellv))
    (u : Faden) {rs : Regs} {ks : List Frame} {dst : Option Reg} (hth : AtB T u fn lb rs ks dst)
    (hw : (gh L).writer = none) :
    ∃ T' : TM, TReach Mod S T T' ∧ AtB T' u fn kc (rs.set rs' (tk (gh L).cellv)) ks dst ∧
      (∀ v, v ≠ u → T'.th v = T.th v) ∧ T'.m = T.m := by
  obtain ⟨hok, hld, _, _⟩ := hrel L
  have hne : BitVec.ofNat Conf.wbits (gh L).cellv ≠ BitVec.ofNat Conf.wbits 1 := by
    intro h
    have h2 := ofNat_eq_iff.mp h
    have hb' := wbits_big
    have hlt := Rw.cellv_lt hok
    rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by omega)] at h2
    rw [Rw.cellv_free hw] at h2
    omega
  have hreach := rd_load_go (S := S) hb hk hkp hld hS hne (rs := rs) (ks := ks) (dst := dst)
  exact ⟨T.upd u (.run T.m ⟨fn, kc, 0, rs.set rs' (tk (gh L).cellv), dst⟩ ks),
    treach_solo hreach T (cfg_of_atB hth), by simp only [AtB, TM.upd, ↓reduceIte], fun v hv => upd_other T _ hv, rfl⟩

/-- **The reader's take that wins** (the layer's SHARED ACQUISITION). The word the thread loaded (`x`) is not the
    writer's and equals the state word; so no writer holds. The thread is a reader of `L`, did not hold it, every
    other holder is a reader; afterwards it holds, and the relation holds for the machine whose `offen` gained `L`
    for it. The one named assumption is `hroom`. -/
theorem rd_take_ok_step {lay : Layout D} (hL : LayoutOk lay) {lese : Lese D} {M : RufMaschineG D} {T : TM}
    {gh : D.Lock → Rw} (hrel : RwRel lese lay M T.m gh) (L : D.Lock) {rs' rn rd rk : Reg} {S : Sees}
    {Mod : Modl} {fn : Nat} {lb kb lb0 : Lbl} {bk : Block}
    (hb : Mod.blk fn lb = some (rdTake lay L rs' rn rd rk lb kb lb0)) (hk : Mod.blk fn kb = some bk)
    (hkp : bk.phis = []) (u : Faden) {rs : Regs} {ks : List Frame} {dst : Option Reg}
    (hth : AtB T u fn lb rs ks dst) {x : Nat} (hrs : rs rs' = some (tk x)) (hne : rs' ≠ rn)
    (hx1 : BitVec.ofNat Conf.wbits x ≠ BitVec.ofNat Conf.wbits 1)
    (hmatch : BitVec.ofNat Conf.wbits x = BitVec.ofNat Conf.wbits (gh L).cellv)
    (hu : lese u L) (hself : L ∉ offen (M.faeden u).spur)
    (hroom : 2 * ((gh L).readers.length + 1) + 2 < 2 ^ Conf.wbits) :
    lese u L ∧ L ∉ offen (M.faeden u).spur ∧
      (∀ g, g ≠ u → L ∈ offen (M.faeden g).spur → lese g L) ∧
      ∃ T' : TM, TReach Mod S T T' ∧
        AtB T' u fn kb (((rs.set rn (tk (x + 2))).set rd (tk x)).set rk (Val.bool true)) ks dst ∧
        (∀ v, v ≠ u → T'.th v = T.th v) ∧ T.m.store (lay.lblk L) 0 lw (tk (x + 2)) = some T'.m ∧
        ∀ M' : RufMaschineG D,
          (∀ v, offen (M'.faeden v).spur =
            if v = u then L :: offen (M.faeden v).spur else offen (M.faeden v).spur) →
          RwRel lese lay M' T'.m (updR gh L ((gh L).addR u)) := by
  obtain ⟨hok, hcell, hG, hmode⟩ := hrel L
  -- no writer holds: the writer's word is the one the reader refused
  have hw : (gh L).writer = none := by
    cases hw : (gh L).writer with
    | none => rfl
    | some w =>
        exfalso
        apply hx1
        rw [hmatch, Rw.cellv_writer hw]
  have hcv := Rw.cellv_free hw
  have hnot : (gh L).holdsB u = false := by
    cases hb' : (gh L).holdsB u
    · rfl
    · exact absurd ((ghold_mem hG u).mpr hb') hself
  have hnr : u ∉ (gh L).readers := by
    intro h; rw [Rw.holdsB] at hnot; simp only [h, decide_true, Bool.true_or, Bool.true_eq_false] at hnot
  have hcell' : T.m.load (lay.lblk L) 0 lw = some (tk x) := by
    have h := hcell
    unfold RwCells at h
    have e : tk x = tk (gh L).cellv := by
      show Val.int Conf.wbits _ = Val.int Conf.wbits _
      rw [hmatch]
    rw [e]; exact h
  obtain ⟨m', hm'⟩ := store_of_load hcell' (tk_ty (x + 2))
  have hreach := rd_take_ok (S := S) hb hk hkp hrs hne hcell' hm' (ks := ks) (dst := dst)
  have hothers : ∀ g, g ≠ u → L ∈ offen (M.faeden g).spur → lese g L := by
    intro g _ hg
    rcases Rw.holdsB_iff.mp ((ghold_mem hG g).mp hg) with hr | hwr
    · exact hmode.1 g hr
    · rw [hw] at hwr; cases hwr
  refine ⟨hu, hself, hothers, T.upd u (.run m' ⟨fn, kb, 0, (((rs.set rn (tk (x + 2))).set rd (tk x)).set rk
      (Val.bool true)), dst⟩ ks), treach_solo hreach T (cfg_of_atB hth), by simp only [AtB, TM.upd, ↓reduceIte],
    fun v hv => upd_other T _ hv, hm', ?_⟩
  intro M' hM'
  refine rwRel_step hL hrel hm' u (List.cons L) (fun L' hLL s => count_cons_ne hLL) hM'
    ((gh L).addR u) ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨List.nodup_cons.mpr ⟨hnr, hok.nodup⟩, fun h => ?_, hroom⟩
    simp only [Rw.addR, hw, Option.isSome_none, Bool.false_eq_true] at h
  · show m'.load (lay.lblk L) 0 lw = some (tk ((gh L).addR u).cellv)
    have e1 : ((gh L).addR u).cellv = 2 * ((gh L).readers.length + 1) := by
      simp only [Rw.cellv, Rw.addR, hw, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, List.length_cons]
    have e2 : tk (x + 2) = tk (2 * ((gh L).readers.length + 1)) := by
      show Val.int Conf.wbits _ = Val.int Conf.wbits _
      rw [← tk_add x 2, hmatch, hcv, tk_add]
      congr 2
    rw [e1, ← e2]
    exact load_store_of hm' (dec_enc_tk' _)
  · intro v
    rw [hM' v]
    by_cases hv : v = u
    · subst hv
      rw [if_pos rfl, count_cons_self_zero hself]
      have : ((gh L).addR v).holdsB v = true := by simp only [Rw.holdsB, Rw.addR, List.mem_cons, true_or, decide_true, Bool.true_or]
      rw [this]; rfl
    · rw [if_neg hv]
      have h1 := hG v
      have : ((gh L).addR u).holdsB v = (gh L).holdsB v := by
        rw [Bool.eq_iff_iff, Rw.holdsB_iff, Rw.holdsB_iff]
        simp only [Rw.addR, List.mem_cons, hv, false_or]
      rw [this]; exact h1
  · refine ⟨fun v hv => ?_, fun w hw' => ?_⟩
    · rcases List.mem_cons.mp hv with rfl | hv
      · exact hu
      · exact hmode.1 v hv
    · simp only [Rw.addR] at hw'
      rw [hw] at hw'
      cases hw'

/-- **The reader's take that loses**: the word it loaded is not the state word; nothing is stored, it loads again
    (G silent). -/
theorem rd_take_fail_step {lay : Layout D} {lese : Lese D} {M : RufMaschineG D} {T : TM} {gh : D.Lock → Rw}
    (hrel : RwRel lese lay M T.m gh) (L : D.Lock) {rs' rn rd rk : Reg} {S : Sees} {Mod : Modl} {fn : Nat}
    {lb kb lb0 : Lbl} {bk : Block} (hb : Mod.blk fn lb = some (rdTake lay L rs' rn rd rk lb kb lb0))
    (hk : Mod.blk fn lb0 = some bk) (hkp : bk.phis = []) (u : Faden) {rs : Regs} {ks : List Frame}
    {dst : Option Reg} (hth : AtB T u fn lb rs ks dst) {x : Nat} (hrs : rs rs' = some (tk x)) (hne : rs' ≠ rn)
    (hdiff : BitVec.ofNat Conf.wbits (gh L).cellv ≠ BitVec.ofNat Conf.wbits x) :
    ∃ T' : TM, TReach Mod S T T' ∧
      AtB T' u fn lb0 (((rs.set rn (tk (x + 2))).set rd (tk (gh L).cellv)).set rk (Val.bool false)) ks dst ∧
      (∀ v, v ≠ u → T'.th v = T.th v) ∧ T'.m = T.m := by
  obtain ⟨hok, hld, _, _⟩ := hrel L
  have hyx : tk (gh L).cellv ≠ tk x := by
    intro h
    apply hdiff
    have h2 : Val.int Conf.wbits (BitVec.ofNat Conf.wbits (gh L).cellv) =
        Val.int Conf.wbits (BitVec.ofNat Conf.wbits x) := h
    injection h2
  have hreach := rd_take_fail (S := S) hb hk hkp hrs hne hld hyx (ks := ks) (dst := dst)
  exact ⟨T.upd u (.run T.m ⟨fn, lb0, 0, (((rs.set rn (tk (x + 2))).set rd (tk (gh L).cellv)).set rk
      (Val.bool false)), dst⟩ ks), treach_solo hreach T (cfg_of_atB hth), by simp only [AtB, TM.upd, ↓reduceIte],
    fun v hv => upd_other T _ hv, rfl⟩

/-- **The reader's release** (G's `freiGib`): the thread is a ghost reader; its two comes off the word; the
    relation holds for the machine whose `offen` lost `L` for it. -/
theorem rd_rel_step {lay : Layout D} (hL : LayoutOk lay) {lese : Lese D} {M : RufMaschineG D} {T : TM}
    {gh : D.Lock → Rw} (hrel : RwRel lese lay M T.m gh) (L : D.Lock) {rd : Reg} {S : Sees} {Mod : Modl}
    {fn : Nat} {lb k : Lbl} {bk : Block} (hb : Mod.blk fn lb = some (rdRel lay L rd lb k))
    (hk : Mod.blk fn k = some bk) (hkp : bk.phis = []) (u : Faden) {rs : Regs} {ks : List Frame}
    {dst : Option Reg} (hth : AtB T u fn lb rs ks dst) (hin : u ∈ (gh L).readers) :
    ∃ n : Nat, 2 * (n + 1) = (gh L).cellv ∧ ∃ T' : TM, TReach Mod S T T' ∧
      AtB T' u fn k (rs.set rd (tk (2 * n + 2))) ks dst ∧ (∀ v, v ≠ u → T'.th v = T.th v) ∧
      T.m.store (lay.lblk L) 0 lw (tk (2 * n)) = some T'.m ∧
      ∀ M' : RufMaschineG D,
        (∀ v, offen (M'.faeden v).spur =
          if v = u then (offen (M.faeden v).spur).erase L else offen (M.faeden v).spur) →
        RwRel lese lay M' T'.m (updR gh L ((gh L).delR u)) := by
  classical
  obtain ⟨hok, hcell, hG, hmode⟩ := hrel L
  have hw : (gh L).writer = none := by
    cases hw : (gh L).writer with
    | none => rfl
    | some w =>
        have := hok.excl (by rw [hw]; rfl)
        rw [this] at hin
        exact absurd hin List.not_mem_nil
  have hlen : 0 < (gh L).readers.length := List.length_pos_of_mem hin
  obtain ⟨n, hn⟩ : ∃ n, (gh L).readers.length = n + 1 := ⟨(gh L).readers.length - 1, by omega⟩
  have hcv : (gh L).cellv = 2 * n + 2 := by rw [Rw.cellv_free hw]; omega
  have hcell' : T.m.load (lay.lblk L) 0 lw = some (tk (2 * n + 2)) := by
    have h := hcell
    unfold RwCells at h
    rw [hcv] at h; exact h
  obtain ⟨m', hm'⟩ := store_of_load hcell' (tk_ty (2 * n))
  have hreach := rd_rel_run (S := S) hb hk hkp hcell' hm' (rs := rs) (ks := ks) (dst := dst)
  refine ⟨n, by omega, T.upd u (.run m' ⟨fn, k, 0, rs.set rd (tk (2 * n + 2)), dst⟩ ks),
    treach_solo hreach T (cfg_of_atB hth), by simp only [AtB, TM.upd, ↓reduceIte], fun v hv => upd_other T _ hv, hm', ?_⟩
  intro M' hM'
  refine rwRel_step hL hrel hm' u (fun s => s.erase L)
    (fun L' hLL s => List.count_erase_of_ne hLL) hM' ((gh L).delR u) ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨hok.nodup.erase u, fun h => ?_, ?_⟩
    · simp only [Rw.delR, hw, Option.isSome_none, Bool.false_eq_true] at h
    · have := hok.room
      simp only [Rw.delR, List.length_erase_of_mem hin]
      omega
  · show m'.load (lay.lblk L) 0 lw = some (tk ((gh L).delR u).cellv)
    have e1 : ((gh L).delR u).cellv = 2 * n := by
      simp only [Rw.cellv, Rw.delR, hw, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
  List.length_erase_of_mem hin, hn, Nat.add_one_sub_one]
    rw [e1]
    exact load_store_of hm' (dec_enc_tk' _)
  · intro v
    rw [hM' v]
    by_cases hv : v = u
    · subst hv
      rw [if_pos rfl]
      have h1 : (offen (M.faeden v).spur).count L = 1 := by
        have := hG v
        have hb' : (gh L).holdsB v = true := by simp only [Rw.holdsB, hin, decide_true, Bool.true_or]
        simpa [hb'] using this
      have hfalse : ((gh L).delR v).holdsB v = false := by
        simp only [Rw.holdsB, Rw.delR, hw, hok.nodup.not_mem_erase, decide_false, reduceCtorEq, Bool.or_self]
      rw [hfalse, List.count_erase_self, h1]
      rfl
    · rw [if_neg hv]
      have h1 := hG v
      have : ((gh L).delR u).holdsB v = (gh L).holdsB v := by
        simp only [Rw.holdsB, Rw.delR, hw, List.mem_erase_of_ne hv, reduceCtorEq, decide_false, Bool.or_false]
      rw [this]; exact h1
  · refine ⟨fun v hv => hmode.1 v (List.mem_of_mem_erase hv), fun w hw' => ?_⟩
    simp only [Rw.delR, hw, reduceCtorEq] at hw'

/-! ## 4. The steps: the writer -/

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
