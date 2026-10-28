import Grammatik.Code.Refine.Calls.CallRun
import Grammatik.Code.Refine.Match.PayCode
import Grammatik.Code.Refine.Match.Scope
import Grammatik.Code.Refine.Struct.Labels

/-
  File:      Grammatik/Code/Refine/Match/Else.lean
  Subject:   TRACK L, PHASE L1 -- THE CALL WITH A FAILURE CHANNEL: `let x = f(..) else (r) { .. }`
             (`Block.bindCallElse`).

  The lowering (`lowerElse`): the call, the case number `t := word urem (n + 1)`, and a branch on `t`:
    * `t = 0` (`st.l`): the value is the word divided by `n + 1` plus `lo` (`payCode`), a new local, then the
      rest of the block (entry `st.l + 2`);
    * `t > 0` (`st.l + 1`): the reason is `t - 1`, a new local, then the `else` end block (entry `st.l + 3`).
  `else_after_call` runs the case number and the branch; `bindCallElse_ok` takes the refinement of the rest and of the
  `else` block (`BOk`, `EOk`), the call's two outcomes from `CallRef` (`ok` and `why`), and proves the statement.
-/

namespace Gabbro.Code.Lower

variable [Conf]

open Gabbro.Grammatik (Deklaration World Env Wert Ctx Res Vertrag Orakel Ausgang EndAusgang RufAusgang
  ErgVal ErgExpr execStmt execBlock execEnd eval evalErg Zahl wahr? Args evalArgs ergWert)

variable {D : Deklaration} {V : Vertrag D}

/-- The answer word of a value, for an answer type that is an integer range. -/
theorem retImg_int (lay : Layout D) (n : Nat) (hn : n ≠ 0) {eo : Option GTy} {lo hi : Int}
    (he : eo = some (.int lo hi)) (v : ErgVal D eo) :
    retImg lay n eo v = some (Val.ofInt (retW n (some (.int lo hi)))
      (((n + 1 : Nat) : Int) * ((ergWert he v : Zahl lo hi).n - lo))) := by
  subst he
  simp only [retImg, if_neg hn]
  rfl

/-- **After the call**: the case number is computed and the branch taken. The word `z` is below `2 ^ W` and the
    number of cases `L` is above zero and below `2 ^ W`. -/
theorem else_after_call {M : Modl} {S : Sees} {fn : Nat} {lb tl el : Lbl} {blk : Block}
    {ca : List Instr} {fno r1 W L : Nat} {ops : List Opd}
    (hb0 : M.blk fn lb = some blk)
    (hbody : blk.body = ca ++ [Instr.call (some r1) fno ops,
      Instr.bin (r1 + 1) .urem W (.reg r1) (.int W (L : Int))])
    (hterm : blk.term = Term.brc .eq W (.reg (r1 + 1)) (.int W 0) tl el)
    (z : Int) (hz0 : 0 ≤ z) (hzW : z < 2 ^ W) (hW0 : 0 < W) (hLpos : 0 < L) (hLW : (L : Int) < 2 ^ W)
    {tblk eblk : Block} (hbt : M.blk fn tl = some tblk) (hpt : tblk.phis = [])
    (hbe : M.blk fn el = some eblk) (hpe : eblk.phis = [])
    {m' : Mem} {rs1 : Regs} {ks : List Frame} {dst : Option Reg} :
    Reach M S (.run m' ⟨fn, lb, ca.length + 1, rs1.set r1 (Val.ofInt W z), dst⟩ ks)
      (.run m' ⟨fn, (if z % (L : Int) = 0 then tl else el), 0,
        (rs1.set r1 (Val.ofInt W z)).set (r1 + 1) (Val.ofInt W (z % (L : Int))), dst⟩ ks) := by
  have hLpos' : (0 : Int) < L := by exact_mod_cast hLpos
  have hmod0 : 0 ≤ z % (L : Int) := Int.emod_nonneg _ (Int.ne_of_gt hLpos')
  have hmodL : z % (L : Int) < L := Int.emod_lt_of_pos _ hLpos'
  have hurem := val_bin_urem W z L hz0 hzW hLpos' hLW
  rw [Int.tmod_eq_emod_of_nonneg hz0] at hurem
  have e1 : (Opd.int W (L : Int)).ev (rs1.set r1 (Val.ofInt W z)) = some (Val.ofInt W (L : Int)) := rfl
  have hr : (Opd.reg r1).ev (rs1.set r1 (Val.ofInt W z)) = some (Val.ofInt W z) := by
    simp only [Opd.ev, regs_set_same]
  have hstep : stepI (.bin (r1 + 1) .urem W (.reg r1) (.int W (L : Int))) m' (rs1.set r1 (Val.ofInt W z))
      = some (m', (rs1.set r1 (Val.ofInt W z)).set (r1 + 1) (Val.ofInt W (z % (L : Int)))) := by
    simp only [stepI, hr, e1, hurem, Option.map_some]
  have hseq : seqI [Instr.bin (r1 + 1) .urem W (.reg r1) (.int W (L : Int))] m'
      (rs1.set r1 (Val.ofInt W z))
      = some (m', (rs1.set r1 (Val.ofInt W z)).set (r1 + 1) (Val.ofInt W (z % (L : Int)))) := by
    simp only [seqI, hstep]
  have hstr : Stretch M fn lb (ca.length + 1)
      [Instr.bin (r1 + 1) .urem W (.reg r1) (.int W (L : Int))] := ⟨blk, hb0, fun i hi => by
    have hi0 : i = 0 := by simpa using hi
    subst hi0
    rw [hbody]
    simp only [Nat.add_zero, List.length_append, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd,
  Nat.lt_add_one, getElem?_pos, Nat.le_add_right, List.getElem_append_right, Nat.add_sub_cancel_left,
  List.getElem_cons_succ, List.getElem_cons_zero]⟩
  have h1 := reach_seq M S [Instr.bin (r1 + 1) .urem W (.reg r1) (.int W (L : Int))] m'
    ⟨fn, lb, ca.length + 1, rs1.set r1 (Val.ofInt W z), dst⟩ ks m' _ hstr hseq
  have hat : Frame.atTerm M ⟨fn, lb, ca.length + 1 + 1, (rs1.set r1 (Val.ofInt W z)).set (r1 + 1)
      (Val.ofInt W (z % (L : Int))), dst⟩ (.brc .eq W (.reg (r1 + 1)) (.int W 0) tl el) blk :=
    ⟨hb0, by rw [hbody]; simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Std.le_refl], hterm⟩
  have ha : (Opd.reg (r1 + 1)).ev ((rs1.set r1 (Val.ofInt W z)).set (r1 + 1) (Val.ofInt W (z % (L : Int))))
      = some (Val.ofInt W (z % (L : Int))) := by simp only [Opd.ev, regs_set_same]
  have hb : (Opd.int W 0).ev ((rs1.set r1 (Val.ofInt W z)).set (r1 + 1) (Val.ofInt W (z % (L : Int))))
      = some (Val.ofInt W 0) := rfl
  have f1 : FitS false W (z % (L : Int)) := by
    simp only [FitS, Bool.false_eq_true, if_false]
    exact ⟨hmod0, by omega⟩
  have hp2 : (0 : Int) < 2 ^ W := by exact_mod_cast Nat.two_pow_pos W
  have f0 : FitS false W 0 := by
    simp only [FitS, Bool.false_eq_true, if_false]
    exact ⟨Int.le_refl _, hp2⟩
  have hic := val_icmp_eq false W (z % (L : Int)) 0 hW0 f1 f0
  simp only [Bool.false_eq_true, if_false] at hic
  by_cases hz : z % (L : Int) = 0
  · have hic1 : Val.icmp .eq W (Val.ofInt W (z % (L : Int))) (Val.ofInt W 0) = some (.int 1 (1 : BitVec 1)) := by
      rw [hic, decide_eq_true hz]; rfl
    have := reach_brc (S := S) (m := m') (ks := ks) hat ha hb hic1 (by simpa using hbt) hpt
    rw [if_pos hz]
    have h2 := Reach.trans (by simpa using h1) this
    simpa using h2
  · have hic0 : Val.icmp .eq W (Val.ofInt W (z % (L : Int))) (Val.ofInt W 0) = some (.int 1 (0 : BitVec 1)) := by
      rw [hic, decide_eq_false hz]; rfl
    have h01 : ¬ ((0 : BitVec 1) = 1) := by decide
    have := reach_brc (S := S) (m := m') (ks := ks) hat ha hb hic0 (by simpa [h01] using hbe) hpe
    rw [if_neg hz]
    have h2 := Reach.trans (by simpa using h1) this
    simpa [h01] using h2

/-- **The refinement of a call with a failure channel.** -/
theorem bindCallElse_ok (lay : Layout D) (hL : LayoutOk lay) (cenv : List Reg) (lv : Lbl × Lbl)
    (O : Orakel D) (passes : Nat)
    (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {τ : GTy} (f : D.Fn) (args : Args D Γ Λ (D.params f))
    (he : D.erg f = some τ) (hp : Gabbro.Grammatik.RufPasst D V (D.signatur f) Λ) (hr : 0 < D.gruende f)
    (err : Gabbro.Grammatik.Endblock D V l (.why (D.gruende f) :: Γ) (Gabbro.Grammatik.nach D f Λ))
    (rest : Gabbro.Grammatik.Block D V l (τ :: Γ) (Gabbro.Grammatik.nach D f Λ) Λ')
    (IHrest : ∀ a, BOk lay (a :: cenv) lv O passes R rest) (IHerr : ∀ a, EOk lay (a :: cenv) lv O passes R err)
    (lb k : Lbl) (st st' : St) (blks : List Block)
    (h : lowerB lay cenv lv (Gabbro.Grammatik.Block.bindCallElse f args he hp hr err rest) lb k st
      = some (blks, st'))
    (M : Modl) (S : Sees) (fn : Nat) (hM : InM M fn blks) (hk : KOk M fn k) (hlv : LvOk M fn lv)
    (hFn : FnOk lay M) (hCall : CallRef lay M S R)
    (σ : World D) (ρ : Env D Γ) (m : Mem) (rs : Regs) (ks : List Frame) (dst : Option Reg)
    (hR : Rep lay σ m) (hE : EnvRep lay rs m cenv ρ) (hW : WfL lay m) (hc : ∀ x ∈ cenv, x < st.r) :
    OutOk lay cenv lv M S fn lb k st.r st'.r m rs ks dst
      (execBlock O passes R (Gabbro.Grammatik.Block.bindCallElse f args he hp hr err rest) σ ρ) := by
  unfold lowerB at h
  rcases hla : lowerArgs lay cenv args st.r with _ | ⟨ca, ops, r1⟩
  · simp only [hla, reduceCtorEq] at h
  have hm1 := lowerArgs_mono lay cenv args st.r _ hla
  simp only [hla] at h
  unfold lowerElse at h
  cases τ with
  | int lo hi =>
      simp only at h
      have hfit : failOk (D.gruende f) (some (.int lo hi)) = true ∧ Ar.Fits 0 ((D.gruende f : Int) - 1) 128 := by
        apply Classical.byContradiction
        intro hn
        rw [if_neg hn] at h
        simp only [reduceCtorEq] at h
      rw [if_pos hfit] at h
      rcases hpc : payCode (failTop (D.gruende f) (some (.int lo hi))) (retW (D.gruende f) (some (.int lo hi)))
          (D.gruende f + 1) lo hi (.reg r1) (r1 + 2) with _ | ⟨cp, op, r2⟩
      · simp only [hpc, reduceCtorEq] at h
      have m2 := payCode_mono hpc
      simp only [hpc] at h
      rcases hb : bindCode (.int lo hi) op r2 with _ | ⟨cb, a, r3⟩
      · simp only [hb, reduceCtorEq] at h
      have m3 := bindCode_mono hb
      simp only [hb] at h
      rcases hb1 : lowerB lay (a :: cenv) lv rest (st.l + 2) k ⟨r3, st.l + 4⟩ with _ | ⟨bo, s1⟩
      · simp only [hb1, reduceCtorEq] at h
      have S1 := lowerB_shape lay (a :: cenv) lv rest (st.l + 2) k ⟨r3, st.l + 4⟩ s1 bo hb1
      simp only [hb1] at h
      rcases hc' : cvt (retW (D.gruende f) (some (.int lo hi))) (Ar.wid 0 ((D.gruende f : Int) - 1)) false
          (.reg s1.r) (s1.r + 1) with ⟨cv, ov, r4⟩
      have m4 := cvt_mono (retW (D.gruende f) (some (.int lo hi))) (Ar.wid 0 ((D.gruende f : Int) - 1)) false
        (.reg s1.r) (s1.r + 1)
      rw [hc'] at m4 h
      simp only at m4 h
      rcases hb2 : bindCode (.why (D.gruende f)) ov r4 with _ | ⟨cb2, a2, r5⟩
      · simp only [hb2, reduceCtorEq] at h
      have m5 := bindCode_mono hb2
      simp only [hb2] at h
      rcases hb3 : lowerEnd lay (a2 :: cenv) lv err (st.l + 3) ⟨r5, s1.l⟩ with _ | ⟨be, s2⟩
      · simp only [hb3, reduceCtorEq] at h
      have S2 := lowerEnd_shape lay (a2 :: cenv) lv err (st.l + 3) ⟨r5, s1.l⟩ s2 be hb3
      simp only [hb3] at h
      have h' := Option.some.inj h
      simp only [Prod.mk.injEq] at h'
      obtain ⟨rfl, rfl⟩ := h'
      -- the numbers
      have hFt : Ar.Fits 0 (failTop (D.gruende f) (some (.int lo hi))) 128 := by
        have := hfit.1
        unfold failOk at this
        simp only [Bool.and_eq_true, decide_eq_true_eq] at this
        exact this.1
      have hlh : lo ≤ hi := by
        have := hfit.1
        unfold failOk at this
        simp only [Bool.and_eq_true, decide_eq_true_eq] at this
        exact this.2
      have hTW : failTop (D.gruende f) (some (.int lo hi)) < 2 ^ (retW (D.gruende f) (some (.int lo hi))) :=
        fits_hi_lt (Ar.wid_fits hFt)
      have hW0 : 0 < retW (D.gruende f) (some (.int lo hi)) := by
        unfold retW
        have := Ar.wid_pos 0 (failTop (D.gruende f) (some (.int lo hi)))
        omega
      have hn1 : 0 < D.gruende f + 1 := Nat.succ_pos _
      have hLtop : ((D.gruende f + 1 : Nat) : Int) ≤ failTop (D.gruende f) (some (.int lo hi)) := by
        unfold failTop failS
        have hp1 : (0 : Int) ≤ ((D.gruende f + 1 : Nat) : Int) := Int.natCast_nonneg _
        have := Int.mul_le_mul_of_nonneg_left (show (1 : Int) ≤ hi - lo + 1 by omega) hp1
        rw [Int.mul_one] at this
        exact this
      have hLW : ((D.gruende f + 1 : Nat) : Int) < 2 ^ (retW (D.gruende f) (some (.int lo hi))) :=
        Int.lt_of_le_of_lt hLtop hTW
      -- blocks
      have hb0 := hM _ (List.mem_cons_self ..)
      have hbA := hM _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      have hbB := hM _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
      have hMo : InM M fn bo := fun b hb' =>
        hM b (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ hb'))))
      have hMe : InM M fn be := fun b hb' =>
        hM b (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_right _ hb'))))
      have hKo := kok_of_shape S1 hMo
      have hKe := kok_of_shape S2 hMe
      -- the arguments
      have hRl : Rep lay (σ.lese Λ args.orte) m := hR
      obtain ⟨rs1, hs1, hr1, hag1, hmap⟩ := lowerArgs_ok lay hL cenv args st.r (ca, ops, r1) hla
        (σ.lese Λ args.orte) (σ.lese Λ args.orte) ρ m rs hRl hE hc
      have hs1' : seqI ca m rs = some (m, rs1) := hs1
      have hc1 : ∀ x ∈ cenv, x < r1 := fun x hx => Nat.lt_of_lt_of_le (hc x hx) hr1
      have hr1' : st.r ≤ r1 := hr1
      have hs12 : s1.r ≤ s2.r := by
        have a1 := S1.2.2
        have a2' := S2.2.2
        simp only at m2 m3 m4 m5 a1 a2' ⊢
        omega
      simp only [execBlock]
      rcases hRf : R f (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
        ⟨σ', v⟩ | ⟨σ', rr⟩ | e | e
      · -- the callee answered a value
        simp only [hRf]
        have hw := retImg_int lay (D.gruende f) (Nat.pos_iff_ne_zero.mp hr) he v
        have hv1 := (ergWert he v : Zahl lo hi).lo_le
        have hv2 := (ergWert he v : Zahl lo hi).le_hi
        generalize hvz : (ergWert he v : Zahl lo hi).n = vz at hw hv1 hv2
        obtain ⟨m', hreach, hRn, hWn, hK⟩ := call_run_some hFn hCall hRf hb0 (pre := ca)
          (post := [Instr.bin (r1 + 1) .urem (retW (D.gruende f) (some (.int lo hi))) (.reg r1)
            (.int (retW (D.gruende f) (some (.int lo hi))) ((D.gruende f + 1 : Nat) : Int))])
          (r := r1) (ks := ks) (dst := dst) rfl hw hs1' hmap hRl hW
        have hz0 : 0 ≤ ((D.gruende f + 1 : Nat) : Int) * (vz - lo) :=
          Int.mul_nonneg (Int.natCast_nonneg _) (by omega)
        have hzT : ((D.gruende f + 1 : Nat) : Int) * (vz - lo) < failTop (D.gruende f) (some (.int lo hi)) := by
          have hS : failTop (D.gruende f) (some (.int lo hi)) = ((D.gruende f + 1 : Nat) : Int) * (hi - lo + 1) := rfl
          rw [hS]
          exact Int.mul_lt_mul_of_pos_left (by omega) (by exact_mod_cast hn1)
        have hzmod : ((D.gruende f + 1 : Nat) : Int) * (vz - lo) % ((D.gruende f + 1 : Nat) : Int) = 0 :=
          Int.mul_emod_right _ _
        have hafter := else_after_call (S := S) (lb := lb) (tl := st.l) (el := st.l + 1) (ks := ks) (dst := dst)
          (m' := m') (rs1 := rs1) hb0 rfl rfl (((D.gruende f + 1 : Nat) : Int) * (vz - lo)) hz0
          (Int.lt_trans hzT hTW) hW0 hn1 hLW (tblk := ⟨st.l, [], cp ++ cb, .jmp (st.l + 2)⟩) hbA rfl
          (eblk := ⟨st.l + 1, [], Instr.bin s1.r .sub (retW (D.gruende f) (some (.int lo hi))) (.reg (r1 + 1))
            (.int (retW (D.gruende f) (some (.int lo hi))) 1) :: (cv ++ cb2), .jmp (st.l + 3)⟩) hbB rfl
        rw [if_pos hzmod] at hafter
        -- the payload
        have hRl' : Rep lay σ' m' := hRn
        have hE1 := envRep_regs cenv ρ (fun x hx => hag1 x (hc x hx)) hE
        have hEm : EnvRep lay rs1 m' cenv ρ := envRep_load cenv ρ
          (fun r hr' b hb' hf o t w hl => hK.2 b hf (envRep_blocks_lt hW.1 cenv ρ hE1 r hr' b hb') o t w hl) hE1
        have hagS : ∀ x, x < r1 → ((rs1.set r1 (Val.ofInt (retW (D.gruende f) (some (.int lo hi)))
            (((D.gruende f + 1 : Nat) : Int) * (vz - lo)))).set (r1 + 1) (Val.ofInt
            (retW (D.gruende f) (some (.int lo hi))) (((D.gruende f + 1 : Nat) : Int) * (vz - lo) %
            ((D.gruende f + 1 : Nat) : Int))) ) x = rs1 x := fun x hx => by
          rw [regs_set_ne _ (r1 + 1) x _ (Nat.ne_of_lt (by omega)), regs_set_ne _ r1 x _ (Nat.ne_of_lt hx)]
        have hEs := envRep_regs cenv ρ (fun x hx => hagS x (hc1 x hx)) hEm
        have hrw : (Opd.reg r1).ev ((rs1.set r1 (Val.ofInt (retW (D.gruende f) (some (.int lo hi)))
            (((D.gruende f + 1 : Nat) : Int) * (vz - lo)))).set (r1 + 1) (Val.ofInt
            (retW (D.gruende f) (some (.int lo hi))) (((D.gruende f + 1 : Nat) : Int) * (vz - lo) %
            ((D.gruende f + 1 : Nat) : Int)))) = some (Val.ofInt (retW (D.gruende f) (some (.int lo hi)))
            (((0 : Nat) : Int) + ((D.gruende f + 1 : Nat) : Int) * (vz - lo))) := by
          rw [Opd.ev, regs_set_ne _ (r1 + 1) r1 _ (Nat.ne_of_lt (Nat.lt_succ_self r1)), regs_set_same]
          simp only [Int.natCast_add, Int.cast_ofNat_Int, Int.zero_add]
        have F := payCode_frag (failTop (D.gruende f) (some (.int lo hi))) (retW (D.gruende f) (some (.int lo hi)))
          (D.gruende f + 1) lo hi (.reg r1) (r1 + 2) m' _ 0 vz (payCode_fits hpc) hn1 hv1 hv2
          (by simpa using hzT) hTW hLtop hrw (opdlt_reg r1 (r1 + 2) (by omega)) (cp, op, r2) hpc
        have F' : Frag m' ((rs1.set r1 (Val.ofInt (retW (D.gruende f) (some (.int lo hi)))
            (((D.gruende f + 1 : Nat) : Int) * (vz - lo)))).set (r1 + 1) (Val.ofInt
            (retW (D.gruende f) (some (.int lo hi))) (((D.gruende f + 1 : Nat) : Int) * (vz - lo) %
            ((D.gruende f + 1 : Nat) : Int)))) (r1 + 2) (cp, op, r2) (encR lay (.int lo hi) (ergWert he v)) := by
          have e : encR lay (.int lo hi) (ergWert he v) = Val.ofInt (Ar.wid lo hi) vz := by
            rw [← hvz]; rfl
          rw [e]
          exact F
        have hFa : Fr lay cenv st.r m rs m' rs1 := ⟨hag1, hK.1,
          fun b hf hb' _ o t w hl => hK.2 b hf hb' o t w hl⟩
        have hFs : Fr lay cenv st.r m' rs1 m' ((rs1.set r1 (Val.ofInt (retW (D.gruende f) (some (.int lo hi)))
            (((D.gruende f + 1 : Nat) : Int) * (vz - lo)))).set (r1 + 1) (Val.ofInt
            (retW (D.gruende f) (some (.int lo hi))) (((D.gruende f + 1 : Nat) : Int) * (vz - lo) %
            ((D.gruende f + 1 : Nat) : Int)))) := fr_regs (fun x hx => hagS x (Nat.lt_of_lt_of_le hx hr1'))
        have hFtot := fr_trans hFa hFs (Nat.le_refl _) hc
        have hcP : ∀ x ∈ cenv, x < r1 + 2 := fun x hx => Nat.lt_of_lt_of_le (hc1 x hx) (Nat.le_add_right _ _)
        have hscope := scope_ok (τ := .int lo hi) (l := l) (V := V) (lv := lv) (M := M) (S := S) (fn := fn)
          (k := k) (ks := ks) (dst := dst) ρ (ergWert he v) (lb1 := st.l) (bd := st.l + 2) (cv := cp) (cb := cb)
          (ov := op) (r0 := r1 + 2) (r1 := r2) (r2 := r3) (a := a) (ri := r3) (r' := s1.r) m' _ hRl' hEs hWn hcP
          hbA hKo F' hb (Nat.le_refl _) _
          (fun m1 rs4 hRn' hEn hWn' hbound => IHrest a (st.l + 2) k ⟨r3, st.l + 4⟩ s1 bo hb1 M S fn hMo hk hlv hFn
            hCall σ' (Env.cons (ergWert he v) ρ) m1 rs4 ks dst hRn' hEn hWn' hbound)
        exact outok_mono hs12 _ (outok_lift (Reach.trans hreach hafter) hFtot (by omega) hc _ hscope)
      · -- the callee answered a reason
        simp only [hRf]
        have hW' : retW (D.gruende f) (D.erg f) = retW (D.gruende f) (some (.int lo hi)) := by rw [he]
        have hwhy : whyImg (D.gruende f) (D.erg f) rr.val
            = some (Val.ofInt (retW (D.gruende f) (some (.int lo hi))) ((rr.val : Int) + 1)) := by
          unfold whyImg
          rw [hW']
        have hrr := rr.isLt
        obtain ⟨m', hreach, hRn, hWn, hK⟩ := call_run_why_some hFn hCall hRf hb0 (pre := ca)
          (post := [Instr.bin (r1 + 1) .urem (retW (D.gruende f) (some (.int lo hi))) (.reg r1)
            (.int (retW (D.gruende f) (some (.int lo hi))) ((D.gruende f + 1 : Nat) : Int))])
          (r := r1) (ks := ks) (dst := dst) rfl hwhy hs1' hmap hRl hW
        have hz0 : (0 : Int) ≤ (rr.val : Int) + 1 := by omega
        have hzL : (rr.val : Int) + 1 < ((D.gruende f + 1 : Nat) : Int) := by omega
        have hzT : (rr.val : Int) + 1 < failTop (D.gruende f) (some (.int lo hi)) := Int.lt_of_lt_of_le hzL hLtop
        have hzmod : ((rr.val : Int) + 1) % ((D.gruende f + 1 : Nat) : Int) = (rr.val : Int) + 1 :=
          Int.emod_eq_of_lt hz0 hzL
        have hne : ¬ (((rr.val : Int) + 1) % ((D.gruende f + 1 : Nat) : Int) = 0) := by
          rw [hzmod]; omega
        have hafter := else_after_call (S := S) (lb := lb) (tl := st.l) (el := st.l + 1) (ks := ks) (dst := dst)
          (m' := m') (rs1 := rs1) hb0 rfl rfl ((rr.val : Int) + 1) hz0
          (Int.lt_trans hzT hTW) hW0 hn1 hLW (tblk := ⟨st.l, [], cp ++ cb, .jmp (st.l + 2)⟩) hbA rfl
          (eblk := ⟨st.l + 1, [], Instr.bin s1.r .sub (retW (D.gruende f) (some (.int lo hi))) (.reg (r1 + 1))
            (.int (retW (D.gruende f) (some (.int lo hi))) 1) :: (cv ++ cb2), .jmp (st.l + 3)⟩) hbB rfl
        rw [if_neg hne] at hafter
        have hRl' : Rep lay σ' m' := hRn
        have hE1 := envRep_regs cenv ρ (fun x hx => hag1 x (hc x hx)) hE
        have hEm : EnvRep lay rs1 m' cenv ρ := envRep_load cenv ρ
          (fun r hr' b hb' hf o t w hl => hK.2 b hf (envRep_blocks_lt hW.1 cenv ρ hE1 r hr' b hb') o t w hl) hE1
        have hagS : ∀ x, x < r1 → ((rs1.set r1 (Val.ofInt (retW (D.gruende f) (some (.int lo hi)))
            ((rr.val : Int) + 1))).set (r1 + 1) (Val.ofInt (retW (D.gruende f) (some (.int lo hi)))
            (((rr.val : Int) + 1) % ((D.gruende f + 1 : Nat) : Int)))) x = rs1 x := fun x hx => by
          rw [regs_set_ne _ (r1 + 1) x _ (Nat.ne_of_lt (by omega)), regs_set_ne _ r1 x _ (Nat.ne_of_lt hx)]
        have hEs := envRep_regs cenv ρ (fun x hx => hagS x (hc1 x hx)) hEm
        have hFa : Fr lay cenv st.r m rs m' rs1 := ⟨hag1, hK.1,
          fun b hf hb' _ o t w hl => hK.2 b hf hb' o t w hl⟩
        have hFs : Fr lay cenv st.r m' rs1 m' ((rs1.set r1 (Val.ofInt (retW (D.gruende f) (some (.int lo hi)))
            ((rr.val : Int) + 1))).set (r1 + 1) (Val.ofInt (retW (D.gruende f) (some (.int lo hi)))
            (((rr.val : Int) + 1) % ((D.gruende f + 1 : Nat) : Int)))) :=
          fr_regs (fun x hx => hagS x (Nat.lt_of_lt_of_le hx hr1'))
        have hFtot := fr_trans hFa hFs (Nat.le_refl _) hc
        have hr1s : r1 ≤ s1.r := by
          have a1 := S1.2.2
          simp only at m2 m3 a1
          omega
        have hcQ : ∀ x ∈ cenv, x < s1.r := fun x hx => Nat.lt_of_lt_of_le (hc1 x hx) hr1s
        -- the reason: the case number minus one, moved to its width
        have hst1 : stepI (.bin s1.r .sub (retW (D.gruende f) (some (.int lo hi))) (.reg (r1 + 1))
            (.int (retW (D.gruende f) (some (.int lo hi))) 1)) m'
            ((rs1.set r1 (Val.ofInt (retW (D.gruende f) (some (.int lo hi))) ((rr.val : Int) + 1))).set (r1 + 1)
              (Val.ofInt (retW (D.gruende f) (some (.int lo hi)))
                (((rr.val : Int) + 1) % ((D.gruende f + 1 : Nat) : Int))))
            = some (m', ((rs1.set r1 (Val.ofInt (retW (D.gruende f) (some (.int lo hi))) ((rr.val : Int) + 1))).set
              (r1 + 1) (Val.ofInt (retW (D.gruende f) (some (.int lo hi)))
                (((rr.val : Int) + 1) % ((D.gruende f + 1 : Nat) : Int)))).set s1.r
              (Val.ofInt (retW (D.gruende f) (some (.int lo hi))) (rr.val : Int))) := by
          have hev : (Opd.reg (r1 + 1)).ev ((rs1.set r1 (Val.ofInt (retW (D.gruende f) (some (.int lo hi)))
              ((rr.val : Int) + 1))).set (r1 + 1) (Val.ofInt (retW (D.gruende f) (some (.int lo hi)))
              (((rr.val : Int) + 1) % ((D.gruende f + 1 : Nat) : Int))))
              = some (Val.ofInt (retW (D.gruende f) (some (.int lo hi))) ((rr.val : Int) + 1)) := by
            rw [Opd.ev, regs_set_same, hzmod]
          have e1 : (Opd.int (retW (D.gruende f) (some (.int lo hi))) 1).ev ((rs1.set r1 (Val.ofInt
              (retW (D.gruende f) (some (.int lo hi))) ((rr.val : Int) + 1))).set (r1 + 1) (Val.ofInt
              (retW (D.gruende f) (some (.int lo hi))) (((rr.val : Int) + 1) % ((D.gruende f + 1 : Nat) : Int))))
              = some (Val.ofInt (retW (D.gruende f) (some (.int lo hi))) 1) := rfl
          have hsub := val_bin_sub (retW (D.gruende f) (some (.int lo hi))) ((rr.val : Int) + 1) 1
          rw [show (rr.val : Int) + 1 - 1 = (rr.val : Int) by omega] at hsub
          simp only [stepI, hev, e1, hsub, Option.map_some]
        have Fsub := frag_one m' ((rs1.set r1 (Val.ofInt (retW (D.gruende f) (some (.int lo hi)))
            ((rr.val : Int) + 1))).set (r1 + 1) (Val.ofInt (retW (D.gruende f) (some (.int lo hi)))
            (((rr.val : Int) + 1) % ((D.gruende f + 1 : Nat) : Int)))) s1.r
          (Instr.bin s1.r .sub (retW (D.gruende f) (some (.int lo hi))) (.reg (r1 + 1))
            (.int (retW (D.gruende f) (some (.int lo hi))) 1))
          (Val.ofInt (retW (D.gruende f) (some (.int lo hi))) (rr.val : Int)) hst1
        have hFv : Frag m' ((rs1.set r1 (Val.ofInt (retW (D.gruende f) (some (.int lo hi)))
            ((rr.val : Int) + 1))).set (r1 + 1) (Val.ofInt (retW (D.gruende f) (some (.int lo hi)))
            (((rr.val : Int) + 1) % ((D.gruende f + 1 : Nat) : Int)))) s1.r
            (Instr.bin s1.r .sub (retW (D.gruende f) (some (.int lo hi))) (.reg (r1 + 1))
              (.int (retW (D.gruende f) (some (.int lo hi))) 1) :: cv, ov, r4)
            (encR lay (.why (D.gruende f)) rr) := by
          have hfs : FitS false (retW (D.gruende f) (some (.int lo hi))) (rr.val : Int) := by
            simp only [FitS, Bool.false_eq_true, if_false]
            exact ⟨Int.natCast_nonneg _, by omega⟩
          refine frag_two (ca := [Instr.bin s1.r .sub (retW (D.gruende f) (some (.int lo hi))) (.reg (r1 + 1))
              (.int (retW (D.gruende f) (some (.int lo hi))) 1)]) (oa := .reg s1.r) (r1 := s1.r + 1)
            (va := Val.ofInt (retW (D.gruende f) (some (.int lo hi))) (rr.val : Int)) (ct := (cv, ov, r4))
            Fsub (fun rsA hag hoa hlta => ?_)
          have F := cvt_frag (retW (D.gruende f) (some (.int lo hi))) (Ar.wid 0 ((D.gruende f : Int) - 1)) false
            (.reg s1.r) (s1.r + 1) m' rsA (rr.val : Int) hoa hfs hlta
          rw [hc'] at F
          exact F
        have hscope := scope_end_ok (τ := .why (D.gruende f)) (l := l) (V := V) (lv := lv) (M := M) (S := S)
          (fn := fn) (ks := ks) (dst := dst) ρ rr (lb1 := st.l + 1) (bd := st.l + 3)
          (cv := Instr.bin s1.r .sub (retW (D.gruende f) (some (.int lo hi))) (.reg (r1 + 1))
            (.int (retW (D.gruende f) (some (.int lo hi))) 1) :: cv) (cb := cb2) (ov := ov)
          (r0 := s1.r) (r1 := r4) (r2 := r5) (a := a2) (ri := r5) (r' := s2.r) m' _ hRl' hEs hWn hcQ
          hbB hKe hFv hb2 (Nat.le_refl _) _
          (fun m1 rs4 hRn' hEn hWn' hbound => IHerr a2 (st.l + 3) ⟨r5, s1.l⟩ s2 be hb3 M S fn hMe hlv hFn
            hCall σ' (Env.cons rr ρ) m1 rs4 ks dst hRn' hEn hWn' hbound)
        exact outok_lift (Reach.trans hreach hafter) hFtot (by omega) hc _ (outok_of_endok _ hscope)
      · simp only [hRf, OutOk]
      · simp only [hRf, OutOk]
  | _ => simp only [reduceCtorEq] at h

end Gabbro.Code.Lower
