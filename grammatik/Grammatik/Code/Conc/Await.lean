import Grammatik.Code.Conc.Publish

/-
  File:      Grammatik/Code/Conc/Await.lean
  Subject:   TRACK L, PHASE L3 (START) -- THE REFINEMENT OF `await`: an acquire load of the cell of the atomic
             global, whose answer the memory-model interface `S` allows.

  In machine G `let x = g awaits {..}` reads the global `g` of the current world (when the visibility oracle says
  it is visible, `O.sichtbar`; else a hardware outcome). In machine GX the world a thread reads is a PRESENTED
  world that differs from the actual one only at the shared atomics. The lowering reads the cell with `aload ..
  acquire`, which the IR runs against an interface `S`: the answer is any value `S` allows at that cell.

  `await_ok` is stated for ONE world `σ` -- the world the thread reads, the presented world of GX -- and the
  value `S` answers: **if `S` allows the image of `σ`'s value of `g` at the cell, and the memory represents
  `σ`, the lowered code refines G's `await` run on `σ`**, for every continuation that refines (`BOk`).
  For `S = Sees.sc` and a global that is not shared the hypothesis on `S` is `Rep` itself (`await_ok_sc`): the exact
  refinement of G. A SHARED atomic (`lay.shared`) has its cell free in `Rep`, so a weakly answered load whose answer
  differs from the cell is covered with no further relaxation: `await_ok_gx` for the presented world, and
  `Conc/Shared.lean` (`await_ok_shared`) against the GX interface for every presented value.
-/

namespace Gabbro.Code.Lower

variable [Conf]

open Gabbro.Grammatik (Deklaration World Env Wert Ctx Res Vertrag Orakel Ausgang EndAusgang RufAusgang
  ErgVal ErgExpr execStmt execBlock execEnd eval evalErg Zahl gdarf)

variable {D : Deklaration} {V : Vertrag D}

/-- **An atomic load is one step** when the interface allows the answer. -/
theorem step_aload {M : Modl} {S : Sees} {f : Frame} {blk : Block} {d : Reg} {t : Ty} {p : Opd}
    {ord : Order} {m : Mem} {b : Nat} {o : Int} {x : Val} (ks : List Frame)
    (hb : M.blk f.fn f.lbl = some blk) (hi : blk.body[f.pc]? = some (.aload d t p ord))
    (hp : p.ev f.regs = some (.ptr b o)) (hat : atomicOk t = true)
    (hin : Mem.inside (((m.blks b).map Blk.size).getD 0) o t) (hS : S m b o t ord x) (hty : x.ty = t) :
    Step M S (.run m f ks) (.run m { f with regs := f.regs.set d x, pc := f.pc + 1 } ks) := by
  have hnext : Cfg.nextI M (.run m f ks) = some (.aload d t p ord) := by simp [Cfg.nextI, hb, hi]
  refine ⟨⟨fun _ _ _ _ _ => some x⟩, ?_, ?_⟩
  · simp only [Oracle.legal, hnext]
    intro b' o' v hp' hv
    have e := Option.some.inj (hp.symm.trans hp')
    injection e with e1 e2
    subst e1
    subst e2
    have := Option.some.inj hv
    subst this
    exact hS
  · simp only [step, hb, hi, hp, hat, hin, hty, and_self, if_true, Option.map_some]
    rfl

/-- A load that succeeded was inside its block. -/
theorem inside_of_load {m : Mem} {b : Nat} {o : Int} {t : Ty} {v : Val} (h : m.load b o t = some v) :
    Mem.inside (((m.blks b).map Blk.size).getD 0) o t := by
  unfold Mem.load at h
  cases hb : m.blks b with
  | none => simp [hb] at h
  | some blk =>
      simp only [hb] at h
      by_cases hi : Mem.inside blk.size o t
      · simpa [hb] using hi
      · simp [hi] at h

/-- **`await` refines G's `await`** on the world the thread reads, for the value the interface answers. -/
theorem await_ok (lay : Layout D) (hL : LayoutOk lay) (cenv : List Reg) (lv : Lbl × Lbl) (O : Orakel D)
    (passes : Nat) (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (g : D.Glob) (payload : List D.Glob)
    (hp : payload = D.nutzlast g) (hgd : gdarf D g Λ)
    (rest : Gabbro.Grammatik.Block D V l (D.gtyp g :: Γ) Λ Λ')
    (IH : ∀ a, BOk lay (a :: cenv) lv O passes R rest)
    (lb k : Lbl) (st st' : St) (blks : List Block)
    (h : lowerAwait lay cenv lv g rest lb k st = some (blks, st'))
    (M : Modl) (S : Sees) (fn : Nat) (hM : InM M fn blks) (hk : KOk M fn k) (hlv : LvOk M fn lv)
    (hFn : FnOk lay M) (hCall : CallRef lay M S R)
    (σ : World D) (ρ : Env D Γ) (m : Mem) (rs : Regs) (ks : List Frame) (dst : Option Reg)
    (hR : Rep lay σ m) (hE : EnvRep lay rs m cenv ρ) (hW : WfL lay m) (hc : ∀ x ∈ cenv, x < st.r)
    (hS : S m (lay.ggblk g) 0 (memTy (D.gtyp g)) .acq (encM lay (D.gtyp g) (σ.globs g))) :
    OutOk lay cenv lv M S fn lb k st.r st'.r m rs ks dst
      (execBlock O passes R (Gabbro.Grammatik.Block.awaits g payload hp hgd rest) σ ρ) := by
  unfold lowerAwait at h
  have hat : atomicG (D.gtyp g) = true := by
    apply Classical.byContradiction
    intro hn
    rw [if_neg hn] at h
    simp at h
  rw [if_pos hat] at h
  have hs := atomicG_supp hat
  rcases hb : bindCode (D.gtyp g) (.reg st.r) (st.r + 1) with _ | ⟨cb, a, r2⟩
  · simp [hb] at h
  have m3 := bindCode_mono hb
  simp only [hb] at h
  rcases hb1 : lowerB lay (a :: cenv) lv rest st.l k ⟨r2, st.l + 1⟩ with _ | ⟨bo, s1⟩
  · simp [hb1] at h
  have S1 := lowerB_shape lay (a :: cenv) lv rest st.l k ⟨r2, st.l + 1⟩ s1 bo hb1
  simp only [hb1] at h
  have h' := Option.some.inj h
  simp only [Prod.mk.injEq] at h'
  obtain ⟨rfl, rfl⟩ := h'
  have hb0 := hM _ (List.mem_cons_self ..)
  have hMo : InM M fn bo := fun b hb' => hM b (List.mem_cons_of_mem _ hb')
  obtain ⟨bk2, hbk2, hkp2⟩ := kok_of_shape S1 hMo
  simp only [execBlock]
  by_cases hvis : O.sichtbar g σ = true
  · rw [if_pos hvis]
    have hnb := atomicG_nonbool hat
    -- the load
    have hgl : (Opd.glob (lay.ggblk g)).ev rs = some (.ptr (lay.ggblk g) 0) := rfl
    obtain ⟨x0, hx0⟩ : ∃ x0, m.load (lay.ggblk g) 0 (memTy (D.gtyp g)) = some x0 := (hR.2 g hs).1
    have hty : (encM lay (D.gtyp g) (σ.globs g)).ty = memTy (D.gtyp g) := encM_ty lay _ hs
    have hstep := step_aload (M := M) (S := S) (f := ⟨fn, lb, 0, rs, dst⟩) (blk := _) (d := st.r) (ks := ks)
      (p := .glob (lay.ggblk g)) (ord := .acq) (m := m) (b := lay.ggblk g) (o := 0) (hb := hb0) (hi := rfl)
      hgl (atomicG_ok hat) (inside_of_load hx0) hS hty
    -- the word becomes a local
    have hR1 : (Opd.reg st.r).ev (rs.set st.r (encM lay (D.gtyp g) (σ.globs g)))
        = some (encR lay (D.gtyp g) (σ.globs g)) := by
      rw [Opd.ev, regs_set_same, encM_eq_encR lay hnb]
    have hE1 : EnvRep lay (rs.set st.r (encM lay (D.gtyp g) (σ.globs g))) m cenv ρ :=
      envRep_regs cenv ρ (fun x hx => regs_set_ne rs st.r x _ (Nat.ne_of_lt (hc x hx))) hE
    obtain ⟨m1, rs4, hs4, hRn, hEnew, hWn, hra, hr4e, hag4, hFb, hcell⟩ :=
      bindCode_run lay (σ := σ.lese Λ [.inr g]) (σ.globs g) (.reg st.r) (st.r + 1) m
        (rs.set st.r (encM lay (D.gtyp g) (σ.globs g))) hR hE1 hW hR1 (opdlt_reg st.r (st.r + 1) (Nat.lt_succ_self _))
        (fun x hx => Nat.lt_succ_of_lt (hc x hx)) hb
    subst hr4e
    have hstr : Stretch M fn lb 1 cb := ⟨_, hb0, fun i hi => by
      show (Instr.aload st.r (memTy (D.gtyp g)) (.glob (lay.ggblk g)) .acq :: cb)[1 + i]? = some cb[i]
      simp [List.getElem?_eq_getElem hi, show 1 + i = i + 1 by omega]⟩
    have hseqb := reach_seq M S cb m ⟨fn, lb, 1, rs.set st.r (encM lay (D.gtyp g) (σ.globs g)), dst⟩ ks m1 rs4 hstr hs4
    have hjmp := reach_jmp (S := S) (m := m1) (ks := ks)
      (f := ⟨fn, lb, 1 + cb.length, rs4, dst⟩) (l := st.l)
      (blk := ⟨lb, [], .aload st.r (memTy (D.gtyp g)) (.glob (lay.ggblk g)) .acq :: cb, .jmp st.l⟩)
      ⟨hb0, by simp; omega, rfl⟩ hbk2 hkp2
    have hbound : ∀ x ∈ a :: cenv, x < a + 1 := fun x hx => by
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact Nat.lt_succ_self _
      · exact Nat.lt_succ_of_lt (Nat.lt_of_lt_of_le (hc x hx') (Nat.le_trans (Nat.le_succ _) hra))
    have IHr := IH a st.l k ⟨a + 1, st.l + 1⟩ s1 bo hb1 M S fn hMo hk hlv hFn hCall (σ.lese Λ [.inr g])
      (Env.cons (σ.globs g) ρ) m1 rs4 ks dst hRn hEnew hWn hbound
    have hFs : Fr lay cenv st.r m rs m (rs.set st.r (encM lay (D.gtyp g) (σ.globs g))) :=
      fr_regs (fun x hx => regs_set_ne rs st.r x _ (Nat.ne_of_lt hx))
    have hFtot : Fr lay cenv st.r m rs m1 rs4 :=
      fr_trans hFs hFb (Nat.le_succ _) hc
    have hcell' : ∀ b, rs4 a = some (.ptr b 0) → m.next ≤ b := hcell
    have hreach : Reach M S (.run m ⟨fn, lb, 0, rs, dst⟩ ks) (.run m1 ⟨fn, st.l, 0, rs4, dst⟩ ks) := by
      have h1 := Reach.trans (Reach.one hstep) hseqb
      have := Reach.trans h1 hjmp
      simpa using this
    have hca : ∀ x ∈ cenv, x < st.r := hc
    exact outok_bind hreach hFtot hcell' hca (Nat.le_trans (Nat.le_succ _) (Nat.le_trans m3.1 (Nat.le_succ a))) _ IHr
  · rw [if_neg hvis]
    simp [OutOk]

/-- A successful lowering of `await` is a lowering of an atomic global. -/
theorem lowerAwait_atomic {lay : Layout D} {cenv : List Reg} {lv : Lbl × Lbl} {g : D.Glob} {l : Bool}
    {Γ : Ctx} {Λ Λ' : List (Res D)} {rest : Gabbro.Grammatik.Block D V l (D.gtyp g :: Γ) Λ Λ'}
    {lb k : Lbl} {st : St} {r : List Block × St} (h : lowerAwait lay cenv lv g rest lb k st = some r) :
    atomicG (D.gtyp g) = true := by
  unfold lowerAwait at h
  apply Classical.byContradiction
  intro hn
  rw [if_neg hn] at h
  simp at h

/-- **The sequentially consistent reading is exact**: with `Sees.sc` the interface answers what the memory holds,
    which `Rep` says is the image of the world's value, so the lowered `await` refines G's `await`. -/
theorem await_ok_sc (lay : Layout D) (hL : LayoutOk lay) (cenv : List Reg) (lv : Lbl × Lbl) (O : Orakel D)
    (passes : Nat) (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (g : D.Glob) (payload : List D.Glob)
    (hp : payload = D.nutzlast g) (hgd : gdarf D g Λ)
    (rest : Gabbro.Grammatik.Block D V l (D.gtyp g :: Γ) Λ Λ')
    (IH : ∀ a, BOk lay (a :: cenv) lv O passes R rest)
    (lb k : Lbl) (st st' : St) (blks : List Block)
    (h : lowerAwait lay cenv lv g rest lb k st = some (blks, st'))
    (M : Modl) (fn : Nat) (hM : InM M fn blks) (hk : KOk M fn k) (hlv : LvOk M fn lv)
    (hFn : FnOk lay M) (hCall : CallRef lay M Sees.sc R)
    (σ : World D) (ρ : Env D Γ) (m : Mem) (rs : Regs) (ks : List Frame) (dst : Option Reg)
    (hsh : lay.shared g = false)
    (hR : Rep lay σ m) (hE : EnvRep lay rs m cenv ρ) (hW : WfL lay m) (hc : ∀ x ∈ cenv, x < st.r) :
    OutOk lay cenv lv M Sees.sc fn lb k st.r st'.r m rs ks dst
      (execBlock O passes R (Gabbro.Grammatik.Block.awaits g payload hp hgd rest) σ ρ) :=
  await_ok lay hL cenv lv O passes R g payload hp hgd rest IH lb k st st' blks h M Sees.sc fn hM hk hlv hFn hCall
    σ ρ m rs ks dst hR hE hW hc ((hR.2 g (atomicG_supp (lowerAwait_atomic h))).2 hsh)

/-- A presented world of machine GX at one shared atomic: the same slots, the same globals but `g`, whose value is
    the one read. (Machine GX allows a presented memory to differ from the actual one exactly at the shared
    atomics, `RufSchrittGX`.) -/
def PresentedAt (g : D.Glob) (σ σ' : World D) : Prop :=
  σ'.slots = σ.slots ∧ ∀ h, h ≠ g → σ'.globs h = σ.globs h

theorem presentedAt_storeGlob (σ : World D) (g : D.Glob) (xg : Wert D (D.gtyp g)) :
    PresentedAt g σ (σ.storeGlob g xg) := ⟨rfl, fun h hh => by simp [World.storeGlob, hh]⟩

theorem storeGlob_globs_self (σ : World D) (g : D.Glob) (xg : Wert D (D.gtyp g)) :
    (σ.storeGlob g xg).globs g = xg := by simp [World.storeGlob]

/-- **The reading in machine GX's terms**: for every value `xg` the interface answers at the cell, when the memory
    represents the presented world (the world with the shared atomic `g` holding `xg`), the lowered `await`
    refines G's `await` on that presented world. -/
theorem await_ok_gx (lay : Layout D) (hL : LayoutOk lay) (cenv : List Reg) (lv : Lbl × Lbl) (O : Orakel D)
    (passes : Nat) (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (g : D.Glob) (payload : List D.Glob)
    (hp : payload = D.nutzlast g) (hgd : gdarf D g Λ)
    (rest : Gabbro.Grammatik.Block D V l (D.gtyp g :: Γ) Λ Λ')
    (IH : ∀ a, BOk lay (a :: cenv) lv O passes R rest)
    (lb k : Lbl) (st st' : St) (blks : List Block)
    (h : lowerAwait lay cenv lv g rest lb k st = some (blks, st'))
    (M : Modl) (S : Sees) (fn : Nat) (hM : InM M fn blks) (hk : KOk M fn k) (hlv : LvOk M fn lv)
    (hFn : FnOk lay M) (hCall : CallRef lay M S R)
    (σ : World D) (xg : Wert D (D.gtyp g)) (ρ : Env D Γ) (m : Mem) (rs : Regs) (ks : List Frame)
    (dst : Option Reg) (hRp : Rep lay (σ.storeGlob g xg) m) (hE : EnvRep lay rs m cenv ρ) (hW : WfL lay m)
    (hc : ∀ x ∈ cenv, x < st.r) (hS : S m (lay.ggblk g) 0 (memTy (D.gtyp g)) .acq (encM lay (D.gtyp g) xg)) :
    PresentedAt g σ (σ.storeGlob g xg) ∧
    OutOk lay cenv lv M S fn lb k st.r st'.r m rs ks dst
      (execBlock O passes R (Gabbro.Grammatik.Block.awaits g payload hp hgd rest) (σ.storeGlob g xg) ρ) :=
  ⟨presentedAt_storeGlob σ g xg,
    await_ok lay hL cenv lv O passes R g payload hp hgd rest IH lb k st st' blks h M S fn hM hk hlv hFn hCall
      (σ.storeGlob g xg) ρ m rs ks dst hRp hE hW hc (by rw [storeGlob_globs_self]; exact hS)⟩

end Gabbro.Code.Lower
