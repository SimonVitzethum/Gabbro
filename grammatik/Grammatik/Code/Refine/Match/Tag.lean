import Grammatik.Code.Refine.Match.Arms
import Grammatik.Code.Refine.Match.Why

/-
  File:      Grammatik/Code/Refine/Match/Tag.lean
  Subject:   TRACK L, PHASE L1 -- THE REFINEMENT OF `match` ON A TAGGED VALUE (`Stmt.onTag`).

  The lowering (`lowerS`, `.onTag`): the scrutinee's word `w` (`Lower/Sum.lean`: `i + L * (n - lo)`), then
    * `lb`        -- `t := w urem L`, `switch t, default st.l, [(0, st.l + 1), (1, st.l + 2), ..]`;
    * `st.l`      -- `dead`;
    * `st.l+1+i`  -- arm `i` (`lowerAr`): the payload of its case, if it has one, as a new local.
  `onTag_ok` takes the refinement of every arm body (`ArmBOk`) and proves the statement's, from
  `arm_ok` and `lowerAr_get`.
-/

namespace Gabbro.Code.Lower

variable [Conf]

open Gabbro.Grammatik (Deklaration World Env Wert Ctx Res Vertrag Orakel Ausgang EndAusgang RufAusgang
  ErgVal ErgExpr execStmt execBlock execEnd execArms eval evalErg Zahl wahr? Nutzlast armEnv)

variable {D : Deklaration} {V : Vertrag D}

theorem onTag_ok (lay : Layout D) (hL : LayoutOk lay) (cenv : List Reg) (lv : Lbl × Lbl)
    (O : Orakel D) (passes : Nat)
    (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option (Int × Int))}
    (v : Gabbro.Grammatik.Expr D Γ Λ (.sum cs))
    (arms : Gabbro.Grammatik.Arms D V l Γ Λ Λ' cs)
    (IH : ∀ i : Fin cs.length, ArmBOk lay cenv lv O passes R (cs.get i) (garmT arms i))
    (lb k : Lbl) (st st' : St) (blks : List Block)
    (h : lowerS lay cenv lv (Gabbro.Grammatik.Stmt.onTag v arms) lb k st = some (blks, st'))
    (M : Modl) (S : Sees) (fn : Nat) (hM : InM M fn blks) (hk : KOk M fn k) (hlv : LvOk M fn lv)
    (hFn : FnOk lay M) (hCall : CallRef lay M S R)
    (σ : World D) (ρ : Env D Γ) (m : Mem) (rs : Regs) (ks : List Frame) (dst : Option Reg)
    (hR : Rep lay σ m) (hE : EnvRep lay rs m cenv ρ) (hW : WfL lay m) (hc : ∀ x ∈ cenv, x < st.r) :
    OutOk lay cenv lv M S fn lb k st.r st'.r m rs ks dst
      (execStmt O passes R (Gabbro.Grammatik.Stmt.onTag v arms) σ ρ) := by
  simp only [lowerS] at h
  rcases hv : lowerE lay cenv v st.r with _ | ⟨cv, ov, r1⟩
  · simp [hv] at h
  simp only [hv] at h
  have hfit : Ar.Fits 0 (sumTop cs) 128 := by
    apply Classical.byContradiction
    intro hn
    rw [if_neg hn] at h
    simp at h
  rw [if_pos hfit] at h
  rcases hga : lowerAr lay cenv lv (sumTop cs) (Ar.wid 0 (sumTop cs)) cs.length ov arms (st.l + 1) k
      ⟨r1 + 1, st.l + 1 + cs.length⟩ with _ | ⟨ba, s1⟩
  · simp [hga] at h
  simp only [hga] at h
  have h' := Option.some.inj h
  simp only [Prod.mk.injEq] at h'
  obtain ⟨rfl, rfl⟩ := h'
  have m1 := lowerE_mono lay cenv v st.r _ hv
  have hb0 := hM _ (List.mem_cons_self ..)
  obtain ⟨σl, hσl⟩ : ∃ σl, σl = σ.lese Λ v.orte := ⟨_, rfl⟩
  simp only [execStmt]
  try rw [← hσl]
  have hRl' : Rep lay σl m := by rw [hσl]; exact hR
  obtain ⟨Fo, _⟩ := lowerE_ok lay hL v cenv st.r (cv, ov, r1) hv σl σl ρ m rs hRl' hE hc
  obtain ⟨rsA, hsA, hrA, hagA, hltA, hevA⟩ := Fo
  have hsA' : seqI cv m rs = some (m, rsA) := hsA
  generalize hve : eval σl v σl ρ = vv at hevA ⊢
  obtain ⟨i, nutz⟩ := vv
  rw [execArms_garmT]
  -- the word, and the numbers about it
  have hev : ov.ev rsA = some (Val.ofInt (Ar.wid 0 (sumTop cs)) (packZ ⟨i, nutz⟩)) := hevA
  have hcw : packZ (cs := cs) ⟨i, nutz⟩ = (i.val : Int) + (cs.length : Int) * payOff (cs.get i) nutz := rfl
  have hc0 := packZ_nonneg (cs := cs) ⟨i, nutz⟩
  have hc1 := packZ_lt (cs := cs) ⟨i, nutz⟩
  have hTW : sumTop cs < 2 ^ (Ar.wid 0 (sumTop cs)) := fits_hi_lt (Ar.wid_fits hfit)
  have hLt : (cs.length : Int) ≤ sumTop cs := by
    unfold sumTop
    have := Int.mul_le_mul_of_nonneg_left (spreadMax_pos cs) (Int.natCast_nonneg cs.length)
    rwa [Int.mul_one] at this
  have hLpos : (0 : Int) < cs.length := by
    have : 0 < cs.length := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
    exact_mod_cast this
  have hurem := val_bin_urem (Ar.wid 0 (sumTop cs)) (packZ ⟨i, nutz⟩) cs.length hc0 (by omega) hLpos (by omega)
  rw [Int.tmod_eq_emod_of_nonneg hc0, packZ_mod] at hurem
  have e1 : (Opd.int (Ar.wid 0 (sumTop cs)) (cs.length : Int)).ev rsA
      = some (Val.ofInt (Ar.wid 0 (sumTop cs)) (cs.length : Int)) := rfl
  have hstep : stepI (.bin r1 .urem (Ar.wid 0 (sumTop cs)) ov (.int (Ar.wid 0 (sumTop cs)) (cs.length : Int))) m rsA
      = some (m, rsA.set r1 (Val.ofInt (Ar.wid 0 (sumTop cs)) (i.val : Int))) := by
    simp only [stepI, hev, e1, hurem, Option.map_some]
  have hseq : seqI (cv ++ [.bin r1 .urem (Ar.wid 0 (sumTop cs)) ov
      (.int (Ar.wid 0 (sumTop cs)) (cs.length : Int))]) m rs
      = some (m, rsA.set r1 (Val.ofInt (Ar.wid 0 (sumTop cs)) (i.val : Int))) := by
    rw [seqI_append, hsA', Option.bind_some]
    simp [seqI, hstep]
  have hagS : ∀ x, x < r1 → (rsA.set r1 (Val.ofInt (Ar.wid 0 (sumTop cs)) (i.val : Int))) x = rsA x :=
    fun x hx => regs_set_ne rsA r1 x _ (Nat.ne_of_lt hx)
  have hovS : ov.ev (rsA.set r1 (Val.ofInt (Ar.wid 0 (sumTop cs)) (i.val : Int)))
      = some (Val.ofInt (Ar.wid 0 (sumTop cs)) (packZ ⟨i, nutz⟩)) := by
    rw [ev_agree hagS hltA]; exact hev
  have hrS : (Opd.reg r1).ev (rsA.set r1 (Val.ofInt (Ar.wid 0 (sumTop cs)) (i.val : Int)))
      = some (.int (Ar.wid 0 (sumTop cs)) (BitVec.ofInt (Ar.wid 0 (sumTop cs)) (i.val : Int))) := by
    simp [Opd.ev, regs_set_same, Val.ofInt]
  -- the arm
  obtain ⟨bi, si, si', hlow, hsub, hle1, hle2⟩ := lowerAr_get lay cenv lv (sumTop cs) (Ar.wid 0 (sumTop cs))
    cs.length ov arms (st.l + 1) k ⟨r1 + 1, st.l + 1 + cs.length⟩ s1 ba hga i
  have hMi : InM M fn bi := fun b hb' =>
    hM b (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hsub b hb')))
  have hKi := armlow_kok lay cenv lv (sumTop cs) (Ar.wid 0 (sumTop cs)) cs.length ov _ _ _ _ _ _ _ M fn hlow hMi
  obtain ⟨bkb, hbkb, hkpb⟩ := hKi
  have hin : cs.length ≤ 2 ^ (Ar.wid 0 (sumTop cs)) := by
    have h2 : (cs.length : Int) ≤ 2 ^ (Ar.wid 0 (sumTop cs)) := by omega
    exact_mod_cast h2
  have hbr := reach_block_sw (S := S) (ks := ks) (dst := dst) (l := st.l + 1 + i.val) hb0 rfl hseq hrS
    (by
      intro c hc'
      rw [find_tbl _ cs.length i.val (st.l + 1) hin i.isLt] at hc'
      have := Option.some.inj hc'
      rw [← this])
    (by
      intro hc'
      rw [find_tbl _ cs.length i.val (st.l + 1) hin i.isLt] at hc'
      exact absurd hc' (by simp))
    hbkb hkpb
  have hagR : ∀ x, x < st.r →
      (rsA.set r1 (Val.ofInt (Ar.wid 0 (sumTop cs)) (i.val : Int))) x = rs x := fun x hx => by
    rw [hagS x (Nat.lt_of_lt_of_le hx hrA), hagA x hx]
  have hE1 := envRep_regs cenv ρ (fun x hx => hagR x (hc x hx)) hE
  have hsiR : r1 + 1 ≤ si.r := hle1
  have hrA' : st.r ≤ r1 := hrA
  have hstsi : st.r ≤ si.r := by omega
  have hlt1 : OpdLt ov si.r := fun x hx => Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (hltA x hx) (Nat.le_succ _)) hsiR
  exact outok_mono hle2 _ (outok_lift hbr (fr_regs hagR) hstsi hc _
    (arm_ok lay hL cenv lv O passes R (sumTop cs) (Ar.wid 0 (sumTop cs)) cs.length ov (cs.get i)
      (garmT arms i) nutz (IH i) (st.l + 1 + i.val) k si si' bi hlow M S fn hMi hk hlv hFn hCall σl ρ m _ ks dst
      hRl' hE1 hW (fun x hx => Nat.lt_of_lt_of_le (hc x hx) hstsi) i.val i.isLt (by rw [← hcw]; exact hovS)
      hlt1 hTW (by rw [← hcw]; exact hc1) hLt))

end Gabbro.Code.Lower
