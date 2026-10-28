import Grammatik.Code.Refine.Calls.CallDef

/-
  File:      Grammatik/Code/Refine/CallRun.lean
  Subject:   TRACK L, PHASE L1 -- THE RUN OF A LOWERED CALL.

  `call_run`: a block whose body is `pre ++ [call d f ops] ++ post`, entered with `pre` run and the
  operands `ops` holding the images of the arguments `ρa`, runs the call: the callee frame (the
  arguments in its first registers), the callee's run (`CallRef`), the `ret`, and back in the caller
  frame one instruction further, with the result in the destination register `d` if there is one.
-/

namespace Gabbro.Code.Lower

variable [Conf]

open Gabbro.Grammatik (Deklaration World Env Wert Ctx Res Vertrag ErgVal RufAusgang)

variable {D : Deklaration}

/-- A `call` instruction is one step: the callee frame is pushed above the caller. -/
theorem step_call {M : Modl} {S : Sees} {f : Frame} {blk : Block} {d : Option Reg} {fi : Nat}
    {args : List Opd} {vs : List Val} {g : Frame} {m : Mem} {ks : List Frame}
    (hb : M.blk f.fn f.lbl = some blk) (hi : blk.body[f.pc]? = some (.call d fi args))
    (hargs : args.mapM (Opd.ev f.regs) = some vs) (hg : Frame.callee M fi vs d = some g) :
    Step M S (.run m f ks) (.run m g (f :: ks)) := by
  have hnext : Cfg.nextI M (.run m f ks) = some (.call d fi args) := by simp only [Cfg.nextI, hb, Option.bind_some, hi]
  refine ⟨⟨fun _ _ _ _ _ => none⟩, legal_of_not_oracular S M _ _ ?_, ?_⟩
  · intro j hj
    rw [hnext] at hj
    cases hj
    rfl
  · simp only [step, hb, hi, hargs, hg]

/-- A `ret` with a caller goes back to the caller, one instruction on, with the result in the
    destination register if there is one. -/
theorem reach_ret_back {M : Modl} {S : Sees} {f' k : Frame} {ks : List Frame} {m : Mem}
    {vo : Option Val} (h : RetAt M f' vo) :
    (f'.dst = none → Reach M S (.run m f' (k :: ks)) (.run m k.adv ks)) ∧
    (∀ r w, f'.dst = some r → vo = some w →
      Reach M S (.run m f' (k :: ks)) (.run m (k.adv.setr r w) ks)) := by
  obtain ⟨blk, hb, hl, h2⟩ := h
  rcases h2 with ⟨ht, rfl⟩ | ⟨o, v, ht, rfl, hv⟩
  · refine ⟨fun hd => Reach.one (step_term ⟨hb, hl, ht⟩ (by simp only [stepTerm, finish, hd])), ?_⟩
    intro r w _ hw
    cases hw
  · refine ⟨fun hd => Reach.one (step_term ⟨hb, hl, ht⟩ (by simp only [stepTerm, hv, finish, hd])), ?_⟩
    intro r w hd hw
    have hvw : v = w := Option.some.inj hw
    subst hvw
    exact Reach.one (step_term ⟨hb, hl, ht⟩ (by simp only [stepTerm, hv, finish, hd]))

/-- **The core of a lowered call**: the caller has run `pre`, the call instruction fires, the callee
    runs to its `ret`. -/
theorem call_core {lay : Layout D} {M : Modl} {S : Sees}
    {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    (hFn : FnOk lay M) (hCall : CallRef lay M S R) {f : D.Fn} {σl σ' : World D}
    {ρa : Env D (D.params f)} {v : ErgVal D (D.erg f)} (hRf : R f σl ρa = RufAusgang.ok σ' v)
    {fn : Nat} {lb : Lbl} {blk : Block} (hb : M.blk fn lb = some blk) {pre post : List Instr}
    {d : Option Reg} {ops : List Opd} (hbody : blk.body = pre ++ Instr.call d (lay.fno f) ops :: post)
    {m : Mem} {rs rs1 : Regs} {ks : List Frame} {dst : Option Reg}
    (hpre : seqI pre m rs = some (m, rs1)) (hops : ops.mapM (Opd.ev rs1) = some (argImgs lay ρa))
    (hR : Rep lay σl m) (hW : WfL lay m) :
    ∃ m' f', Reach M S (.run m ⟨fn, lb, 0, rs, dst⟩ ks) (.run m' f' (⟨fn, lb, pre.length, rs1, dst⟩ :: ks)) ∧
      f'.dst = d ∧ RetAt M f' (retImg lay (D.gruende f) (D.erg f) v) ∧ Rep lay σ' m' ∧ WfL lay m' ∧
        Keep lay m m' := by
  have hstr : Stretch M fn lb 0 pre := ⟨blk, hb, fun i hi => by
    simp only [hbody, Nat.zero_add, List.getElem?_append_left hi, getElem?_eq_some_getElem_iff]⟩
  have h1 := reach_seq M S pre m ⟨fn, lb, 0, rs, dst⟩ ks m rs1 hstr hpre
  have hi : blk.body[pre.length]? = some (.call d (lay.fno f) ops) := by simp only [hbody, List.length_append, List.length_cons, Nat.lt_add_right_iff_pos, Nat.zero_lt_succ,
  getElem?_pos, Std.le_refl, List.getElem_append_right, Nat.sub_self, List.getElem_cons_zero]
  obtain ⟨g, hg, hgfn, hgl, hgpc, hgd, hgA⟩ := callee_frame hFn f ρa d
  have h2 := step_call (M := M) (S := S) (f := ⟨fn, lb, pre.length, rs1, dst⟩) (blk := blk) (m := m)
    (ks := ks) hb hi hops hg
  obtain ⟨m', f', hr, hf1, hf2, hret, hRn, hWn, hK⟩ := hCall.ok f σl ρa σ' v hRf m g.regs
    (⟨fn, lb, pre.length, rs1, dst⟩ :: ks) d hR hW hgA
  have hgeq : g = ⟨lay.fno f, 0, 0, g.regs, d⟩ := by
    cases g
    simp_all
  rw [← hgeq] at hr
  refine ⟨m', f', Reach.trans (by simpa using h1) (Reach.trans (Reach.one h2) hr), hf2, hret, hRn, hWn, hK⟩

/-- **The core of a lowered call that the source answers with a reason.** -/
theorem call_core_why {lay : Layout D} {M : Modl} {S : Sees}
    {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    (hFn : FnOk lay M) (hCall : CallRef lay M S R) {f : D.Fn} {σl σ' : World D}
    {ρa : Env D (D.params f)} {r : Fin (D.gruende f)} (hRf : R f σl ρa = RufAusgang.why σ' r)
    {fn : Nat} {lb : Lbl} {blk : Block} (hb : M.blk fn lb = some blk) {pre post : List Instr}
    {d : Option Reg} {ops : List Opd} (hbody : blk.body = pre ++ Instr.call d (lay.fno f) ops :: post)
    {m : Mem} {rs rs1 : Regs} {ks : List Frame} {dst : Option Reg}
    (hpre : seqI pre m rs = some (m, rs1)) (hops : ops.mapM (Opd.ev rs1) = some (argImgs lay ρa))
    (hR : Rep lay σl m) (hW : WfL lay m) :
    ∃ m' f', Reach M S (.run m ⟨fn, lb, 0, rs, dst⟩ ks) (.run m' f' (⟨fn, lb, pre.length, rs1, dst⟩ :: ks)) ∧
      f'.dst = d ∧ RetAt M f' (whyImg (D.gruende f) (D.erg f) r.val) ∧ Rep lay σ' m' ∧ WfL lay m' ∧
        Keep lay m m' := by
  have hstr : Stretch M fn lb 0 pre := ⟨blk, hb, fun i hi => by
    simp only [hbody, Nat.zero_add, List.getElem?_append_left hi, getElem?_eq_some_getElem_iff]⟩
  have h1 := reach_seq M S pre m ⟨fn, lb, 0, rs, dst⟩ ks m rs1 hstr hpre
  have hi : blk.body[pre.length]? = some (.call d (lay.fno f) ops) := by simp only [hbody, List.length_append, List.length_cons, Nat.lt_add_right_iff_pos, Nat.zero_lt_succ,
  getElem?_pos, Std.le_refl, List.getElem_append_right, Nat.sub_self, List.getElem_cons_zero]
  obtain ⟨g, hg, hgfn, hgl, hgpc, hgd, hgA⟩ := callee_frame hFn f ρa d
  have h2 := step_call (M := M) (S := S) (f := ⟨fn, lb, pre.length, rs1, dst⟩) (blk := blk) (m := m)
    (ks := ks) hb hi hops hg
  obtain ⟨m', f', hr, hf1, hf2, hret, hRn, hWn, hK⟩ := hCall.why f σl ρa σ' r hRf m g.regs
    (⟨fn, lb, pre.length, rs1, dst⟩ :: ks) d hR hW hgA
  have hgeq : g = ⟨lay.fno f, 0, 0, g.regs, d⟩ := by
    cases g
    simp_all
  rw [← hgeq] at hr
  refine ⟨m', f', Reach.trans (by simpa using h1) (Reach.trans (Reach.one h2) hr), hf2, hret, hRn, hWn, hK⟩

/-- A lowered call whose result is not wanted. -/
theorem call_run_none {lay : Layout D} {M : Modl} {S : Sees}
    {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    (hFn : FnOk lay M) (hCall : CallRef lay M S R) {f : D.Fn} {σl σ' : World D}
    {ρa : Env D (D.params f)} {v : ErgVal D (D.erg f)} (hRf : R f σl ρa = RufAusgang.ok σ' v)
    {fn : Nat} {lb : Lbl} {blk : Block} (hb : M.blk fn lb = some blk) {pre post : List Instr}
    {ops : List Opd} (hbody : blk.body = pre ++ Instr.call none (lay.fno f) ops :: post)
    {m : Mem} {rs rs1 : Regs} {ks : List Frame} {dst : Option Reg}
    (hpre : seqI pre m rs = some (m, rs1)) (hops : ops.mapM (Opd.ev rs1) = some (argImgs lay ρa))
    (hR : Rep lay σl m) (hW : WfL lay m) :
    ∃ m', Reach M S (.run m ⟨fn, lb, 0, rs, dst⟩ ks) (.run m' ⟨fn, lb, pre.length + 1, rs1, dst⟩ ks) ∧
      Rep lay σ' m' ∧ WfL lay m' ∧ Keep lay m m' := by
  obtain ⟨m', f', hr, hd, hret, hRn, hWn, hK⟩ := call_core hFn hCall hRf hb hbody hpre hops hR hW
  exact ⟨m', Reach.trans hr ((reach_ret_back hret).1 hd), hRn, hWn, hK⟩

/-- A lowered call whose result goes to register `r`. -/
theorem call_run_some {lay : Layout D} {M : Modl} {S : Sees}
    {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    (hFn : FnOk lay M) (hCall : CallRef lay M S R) {f : D.Fn} {σl σ' : World D}
    {ρa : Env D (D.params f)} {v : ErgVal D (D.erg f)} (hRf : R f σl ρa = RufAusgang.ok σ' v)
    {fn : Nat} {lb : Lbl} {blk : Block} (hb : M.blk fn lb = some blk) {pre post : List Instr}
    {r : Reg} {ops : List Opd} (hbody : blk.body = pre ++ Instr.call (some r) (lay.fno f) ops :: post)
    {m : Mem} {rs rs1 : Regs} {ks : List Frame} {dst : Option Reg} {w : Val}
    (hw : retImg lay (D.gruende f) (D.erg f) v = some w)
    (hpre : seqI pre m rs = some (m, rs1)) (hops : ops.mapM (Opd.ev rs1) = some (argImgs lay ρa))
    (hR : Rep lay σl m) (hW : WfL lay m) :
    ∃ m', Reach M S (.run m ⟨fn, lb, 0, rs, dst⟩ ks)
        (.run m' ⟨fn, lb, pre.length + 1, rs1.set r w, dst⟩ ks) ∧
      Rep lay σ' m' ∧ WfL lay m' ∧ Keep lay m m' := by
  obtain ⟨m', f', hr, hd, hret, hRn, hWn, hK⟩ := call_core hFn hCall hRf hb hbody hpre hops hR hW
  exact ⟨m', Reach.trans hr ((reach_ret_back hret).2 r w hd hw), hRn, hWn, hK⟩

/-- A lowered call that the source answers with a reason, whose answer word goes to register `r`. -/
theorem call_run_why_some {lay : Layout D} {M : Modl} {S : Sees}
    {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    (hFn : FnOk lay M) (hCall : CallRef lay M S R) {f : D.Fn} {σl σ' : World D}
    {ρa : Env D (D.params f)} {rr : Fin (D.gruende f)} (hRf : R f σl ρa = RufAusgang.why σ' rr)
    {fn : Nat} {lb : Lbl} {blk : Block} (hb : M.blk fn lb = some blk) {pre post : List Instr}
    {r : Reg} {ops : List Opd} (hbody : blk.body = pre ++ Instr.call (some r) (lay.fno f) ops :: post)
    {m : Mem} {rs rs1 : Regs} {ks : List Frame} {dst : Option Reg} {w : Val}
    (hw : whyImg (D.gruende f) (D.erg f) rr.val = some w)
    (hpre : seqI pre m rs = some (m, rs1)) (hops : ops.mapM (Opd.ev rs1) = some (argImgs lay ρa))
    (hR : Rep lay σl m) (hW : WfL lay m) :
    ∃ m', Reach M S (.run m ⟨fn, lb, 0, rs, dst⟩ ks)
        (.run m' ⟨fn, lb, pre.length + 1, rs1.set r w, dst⟩ ks) ∧
      Rep lay σ' m' ∧ WfL lay m' ∧ Keep lay m m' := by
  obtain ⟨m', f', hr, hd, hret, hRn, hWn, hK⟩ := call_core_why hFn hCall hRf hb hbody hpre hops hR hW
  exact ⟨m', Reach.trans hr ((reach_ret_back hret).2 r w hd hw), hRn, hWn, hK⟩

/-! ## The arguments of a call -/

/-- **The lowered arguments run**: the operands hold the register images of the evaluated arguments. -/
theorem lowerArgs_ok (lay : Layout D) (hL : LayoutOk lay) (cenv : List Reg) :
    ∀ {Γ : Ctx} {Λ : List (Res D)} {τs : List GTy} (args : Gabbro.Grammatik.Args D Γ Λ τs) (r : Nat)
      (c : List Instr × List Opd × Nat), lowerArgs lay cenv args r = some c →
      ∀ (σ₀ σ : World D) (ρ : Env D Γ) (m : Mem) (rs : Regs), Rep lay σ m → EnvRep lay rs m cenv ρ →
        (∀ x ∈ cenv, x < r) →
        ∃ rs', seqI c.1 m rs = some (m, rs') ∧ r ≤ c.2.2 ∧ (∀ x, x < r → rs' x = rs x) ∧
          c.2.1.mapM (Opd.ev rs') = some (argImgs lay (Gabbro.Grammatik.evalArgs σ₀ args σ ρ))
  | _, _, _, .nil, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc => by
      simp only [lowerArgs, Option.some.injEq] at h
      subst h
      exact ⟨rs, rfl, Nat.le_refl _, fun _ _ => rfl, rfl⟩
  | _, _, _, .cons e rest, r, c, h, σ₀, σ, ρ, m, rs, hR, hE, hc => by
      simp only [lowerArgs] at h
      rcases he : lowerE lay cenv e r with _ | ⟨ce, oe, r1⟩
      · simp only [he, reduceCtorEq] at h
      simp only [he] at h
      rcases hr : lowerArgs lay cenv rest r1 with _ | ⟨cr, os, r2⟩
      · simp only [hr, reduceCtorEq] at h
      simp only [hr, Option.some.injEq] at h
      subst h
      obtain ⟨Fe, _⟩ := lowerE_ok lay hL e cenv r (ce, oe, r1) he σ₀ σ ρ m rs hR hE hc
      obtain ⟨rs1, hs1, hr1, hag1, hlt1, hev1⟩ := Fe
      have hs1' : seqI ce m rs = some (m, rs1) := hs1
      have hE1 := envRep_regs cenv ρ (fun x hx => hag1 x (hc x hx)) hE
      have hc1 : ∀ x ∈ cenv, x < r1 := fun x hx => Nat.lt_of_lt_of_le (hc x hx) hr1
      obtain ⟨rs2, hs2, hr2, hag2, hmap⟩ := lowerArgs_ok lay hL cenv rest r1 _ hr σ₀ σ ρ m rs1 hR hE1 hc1
      refine ⟨rs2, ?_, Nat.le_trans hr1 hr2, fun x hx => by
        rw [hag2 x (Nat.lt_of_lt_of_le hx hr1), hag1 x hx], ?_⟩
      · show seqI (ce ++ cr) m rs = some (m, rs2)
        rw [seqI_append, hs1', Option.bind_some]
        exact hs2
      · have hev : oe.ev rs2 = some (encR lay _ (Gabbro.Grammatik.eval σ₀ e σ ρ)) := by
          rw [ev_agree hag2 hlt1]; exact hev1
        show (oe :: os).mapM (Opd.ev rs2) = some (encR lay _ (Gabbro.Grammatik.eval σ₀ e σ ρ) ::
          argImgs lay (Gabbro.Grammatik.evalArgs σ₀ rest σ ρ))
        simp only [List.mapM_cons, hev, hmap, Option.bind_some]
        rfl

/-- The image of a returned value, as the image of the local it is bound to. -/
theorem ergImg_ergWert (lay : Layout D) {e : Option GTy} {τ : GTy} (he : e = some τ) (v : ErgVal D e) :
    ergImg lay e v = some (encR lay τ (Gabbro.Grammatik.ergWert he v)) := by
  subst he
  rfl

end Gabbro.Code.Lower
