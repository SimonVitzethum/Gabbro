import Grammatik.Code.Refine.Traverse

/-
  File:      Grammatik/Code/Refine/Retry.lean
  Subject:   TRACK L, PHASE L1 -- THE REFINEMENT OF `retry`: a loop of at most `n` passes that tests
             its condition `bis` first.

  The lowering keeps a pass counter in the register `c = st.r` and has four fixed blocks, the lowered
  body and the lowered overflow block:
    * `lb`  -- `c := 0`, jump to `H`;
    * `H`   -- the code of `bis`; true: jump to `k`, false: to `T`;
    * `T`   -- `if c <u n then BODY else OVERFLOW`;
    * `I`   -- `c := c + 1`, jump to `H` (the end of the body and `next` jump here, `leave` jumps to `k`).
  The source is `retryLauf`, by induction on the passes left; the counter equals the passes made, so
  `T` takes the body exactly while passes are left.
-/

namespace Gabbro.Code.Lower

variable [Conf]

open Gabbro.Grammatik (Deklaration World Env Wert Ctx Res Vertrag Orakel Ausgang EndAusgang RufAusgang
  ErgVal ErgExpr execStmt execBlock execEnd eval evalErg Zahl retryLauf wahr?)

variable {D : Deklaration} {V : Vertrag D}

/-- **The loop, from its test block on.** -/
theorem retry_loop {lay : Layout D} (hL : LayoutOk lay) {cenv : List Reg} {lv : Lbl × Lbl} {O : Orakel D}
    {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f} {M : Modl} {S : Sees}
    {fn : Nat} {k : Lbl} {ks : List Frame} {dst : Option Reg} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (n : Nat) (bis : Gabbro.Grammatik.Expr D Γ Λ .bool) (body : Gabbro.Grammatik.Block D V true Γ Λ Λ)
    (ueb : Gabbro.Grammatik.Block D V l Γ Λ Λ) {c : Nat} {H T OV I BD : Nat} {cb : List Instr} {ob : Opd}
    {r1 rb ro : Nat} (hfit : Ar.Fits 0 (n : Int) 128)
    (hcb : lowerE lay cenv bis (c + 1) = some (cb, ob, r1)) (hrb : r1 ≤ rb) (hro : rb ≤ ro)
    (hMH : M.blk fn H = some ⟨H, [], cb, .br ob k T⟩)
    (hMT : M.blk fn T = some ⟨T, [], [], .brc .ult (Ar.wid 0 (n : Int)) (.reg c)
      (.int (Ar.wid 0 (n : Int)) (n : Int)) BD OV⟩)
    (hMI : M.blk fn I = some ⟨I, [], [.bin c .add (Ar.wid 0 (n : Int)) (.reg c)
      (.int (Ar.wid 0 (n : Int)) 1)], .jmp H⟩)
    (hKk : KOk M fn k) (hKbd : KOk M fn BD) (hKov : KOk M fn OV)
    (IHb : ∀ (σ : World D) (ρ : Env D Γ) (m : Mem) (rs : Regs), Rep lay σ m → EnvRep lay rs m cenv ρ →
      WfL lay m → (∀ x ∈ cenv, x < r1) →
      OutOk lay cenv (k, I) M S fn BD I r1 rb m rs ks dst (execBlock O passes R body σ ρ))
    (IHo : ∀ (σ : World D) (ρ : Env D Γ) (m : Mem) (rs : Regs), Rep lay σ m → EnvRep lay rs m cenv ρ →
      WfL lay m → (∀ x ∈ cenv, x < rb) →
      OutOk lay cenv lv M S fn OV k rb ro m rs ks dst (execBlock O passes R ueb σ ρ)) :
    ∀ (m j : Nat), j + m = n → ∀ (σ : World D) (ρ : Env D Γ) (mem : Mem) (rs : Regs), Rep lay σ mem →
      EnvRep lay rs mem cenv ρ → WfL lay mem → (∀ x ∈ cenv, x < c) →
      rs c = some (Val.ofInt (Ar.wid 0 (n : Int)) j) →
      OutOk lay cenv lv M S fn H k c ro mem rs ks dst
        (retryLauf (fun σ ρ => execBlock O passes R body σ ρ)
          (fun σ ρ => (σ.lese Λ bis.orte, wahr? (eval (σ.lese Λ bis.orte) bis (σ.lese Λ bis.orte) ρ)))
          (fun σ ρ => execBlock O passes R ueb σ ρ) m σ ρ : Ausgang V l Γ) := by
  have hc1 : c + 1 ≤ r1 := by
    have := lowerE_mono lay cenv bis (c + 1) _ hcb
    simpa using this
  have hwpos : 0 < Ar.wid 0 (n : Int) := by have := Ar.wid_pos 0 (n : Int); omega
  have hwfit : Ar.Fits 0 (n : Int) (Ar.wid 0 (n : Int)) := Ar.wid_fits hfit
  have hnn : (0 : Int) ≤ (n : Int) := Int.natCast_nonneg n
  have hKH : KOk M fn H := ⟨_, hMH, rfl⟩
  have hKT : KOk M fn T := ⟨_, hMT, rfl⟩
  -- the block `H`: the test of `bis`; `true` exits, `false` goes on to `T`
  have hHrun : ∀ (σ : World D) (ρ : Env D Γ) (mem : Mem) (rs : Regs), Rep lay σ mem →
      EnvRep lay rs mem cenv ρ → (∀ x ∈ cenv, x < c) →
      ∃ rs1, (∀ x, x < c + 1 → rs1 x = rs x) ∧ EnvRep lay rs1 mem cenv ρ ∧
        ((eval (σ.lese Λ bis.orte) bis (σ.lese Λ bis.orte) ρ : Bool) = true →
          Reach M S (.run mem ⟨fn, H, 0, rs, dst⟩ ks) (.run mem ⟨fn, k, 0, rs1, dst⟩ ks)) ∧
        ((eval (σ.lese Λ bis.orte) bis (σ.lese Λ bis.orte) ρ : Bool) = false →
          Reach M S (.run mem ⟨fn, H, 0, rs, dst⟩ ks) (.run mem ⟨fn, T, 0, rs1, dst⟩ ks)) := by
    intro σ ρ mem rs hR hE hc
    obtain ⟨Fb, _⟩ := lowerE_ok lay hL bis cenv (c + 1) (cb, ob, r1) hcb (σ.lese Λ bis.orte)
      (σ.lese Λ bis.orte) ρ mem rs hR hE (fun x hx => Nat.lt_succ_of_lt (hc x hx))
    obtain ⟨rs1, hs1, hr1, hag1, hlt1, hev1⟩ := Fb
    have hs1' : seqI cb mem rs = some (mem, rs1) := hs1
    refine ⟨rs1, hag1, envRep_regs cenv ρ (fun x hx => hag1 x (Nat.lt_succ_of_lt (hc x hx))) hE, ?_, ?_⟩
    · intro hv
      have hev : ob.ev rs1 = some (.int 1 (1 : BitVec 1)) := by
        rw [hv] at hev1; exact hev1
      obtain ⟨bk, hbk, hkp⟩ := hKk
      have := reach_block_br (S := S) (ks := ks) (dst := dst) (x := (1 : BitVec 1)) hMH rfl hs1' hev
        (by simpa using hbk) hkp
      simpa using this
    · intro hv
      have hev : ob.ev rs1 = some (.int 1 (0 : BitVec 1)) := by
        rw [hv] at hev1; exact hev1
      obtain ⟨bk, hbk, hkp⟩ := hKT
      have h01 : ¬ ((0 : BitVec 1) = 1) := by decide
      have := reach_block_br (S := S) (ks := ks) (dst := dst) (x := (0 : BitVec 1)) hMH rfl hs1' hev
        (by simpa [h01] using hbk) hkp
      simpa [h01] using this
  intro m
  induction m with
  | zero =>
      intro j hj σ ρ mem rs hR hE hW hc hcj
      obtain ⟨rs1, hag1, hE1, hT1, hF1⟩ := hHrun σ ρ mem rs hR hE hc
      have hFa : Fr lay cenv c mem rs mem rs1 := fr_regs (fun x hx => hag1 x (Nat.lt_succ_of_lt hx))
      have hcj1 : rs1 c = some (Val.ofInt (Ar.wid 0 (n : Int)) j) := by
        rw [hag1 c (Nat.lt_succ_self _)]; exact hcj
      simp only [retryLauf]
      by_cases hv : (eval (σ.lese Λ bis.orte) bis (σ.lese Λ bis.orte) ρ : Bool) = true
      · have hv' : wahr? (eval (σ.lese Λ bis.orte) bis (σ.lese Λ bis.orte) ρ) = true := hv
        rw [if_pos hv']
        simp only [OutOk]
        exact ⟨mem, rs1, hT1 hv, ⟨hR, hE1, hW, fun x hx => Nat.lt_of_lt_of_le (hc x hx) (by omega)⟩, hFa⟩
      · have hv0 : (eval (σ.lese Λ bis.orte) bis (σ.lese Λ bis.orte) ρ : Bool) = false :=
          Bool.eq_false_iff.mpr hv
        have hv' : ¬ (wahr? (eval (σ.lese Λ bis.orte) bis (σ.lese Λ bis.orte) ρ) = true) := hv
        rw [if_neg hv']
        obtain ⟨_, hexit⟩ := head_reach (S := S) (m := mem) (dst := dst) (ks := ks) hMT hcj1 hwpos hnn hwfit
          (by omega) hKbd hKov
        have hReach := Reach.trans (hF1 hv0) (hexit (by omega))
        exact outok_lift hReach hFa (by omega) hc _
          (IHo (σ.lese Λ bis.orte) ρ mem rs1 hR hE1 hW (fun x hx => Nat.lt_of_lt_of_le (hc x hx) (by omega)))
  | succ m ih =>
      intro j hj σ ρ mem rs hR hE hW hc hcj
      obtain ⟨rs1, hag1, hE1, hT1, hF1⟩ := hHrun σ ρ mem rs hR hE hc
      have hFa : Fr lay cenv c mem rs mem rs1 := fr_regs (fun x hx => hag1 x (Nat.lt_succ_of_lt hx))
      have hcj1 : rs1 c = some (Val.ofInt (Ar.wid 0 (n : Int)) j) := by
        rw [hag1 c (Nat.lt_succ_self _)]; exact hcj
      simp only [retryLauf]
      by_cases hv : (eval (σ.lese Λ bis.orte) bis (σ.lese Λ bis.orte) ρ : Bool) = true
      · have hv' : wahr? (eval (σ.lese Λ bis.orte) bis (σ.lese Λ bis.orte) ρ) = true := hv
        rw [if_pos hv']
        simp only [OutOk]
        exact ⟨mem, rs1, hT1 hv, ⟨hR, hE1, hW, fun x hx => Nat.lt_of_lt_of_le (hc x hx) (by omega)⟩, hFa⟩
      · have hv0 : (eval (σ.lese Λ bis.orte) bis (σ.lese Λ bis.orte) ρ : Bool) = false :=
          Bool.eq_false_iff.mpr hv
        have hv' : ¬ (wahr? (eval (σ.lese Λ bis.orte) bis (σ.lese Λ bis.orte) ρ) = true) := hv
        rw [if_neg hv']
        obtain ⟨hgo, _⟩ := head_reach (S := S) (m := mem) (dst := dst) (ks := ks) hMT hcj1 hwpos hnn hwfit
          (by omega) hKbd hKov
        have hReach := Reach.trans (hF1 hv0) (hgo (by omega))
        have IH1 := IHb (σ.lese Λ bis.orte) ρ mem rs1 hR hE1 hW
          (fun x hx => Nat.lt_of_lt_of_le (hc x hx) (by omega))
        -- a pass that ends normally (or with `next`): count it and test again
        have cont : ∀ (σ1 : World D) (ρ1 : Env D Γ),
            RunOk lay cenv M S fn BD I r1 rb σ1 ρ1 mem rs1 ks dst →
            OutOk lay cenv lv M S fn H k c ro mem rs ks dst
              (retryLauf (fun σ ρ => execBlock O passes R body σ ρ)
                (fun σ ρ => (σ.lese Λ bis.orte,
                  wahr? (eval (σ.lese Λ bis.orte) bis (σ.lese Λ bis.orte) ρ)))
                (fun σ ρ => execBlock O passes R ueb σ ρ) m σ1 ρ1 : Ausgang V l Γ) := by
          intro σ1 ρ1 hok
          obtain ⟨m', rs', hrch, hP, hF⟩ := hok
          have hcR : rs' c = some (Val.ofInt (Ar.wid 0 (n : Int)) j) := by
            rw [hF.1 c (by omega), hcj1]
          have hinc : seqI [Instr.bin c .add (Ar.wid 0 (n : Int)) (.reg c) (.int (Ar.wid 0 (n : Int)) 1)]
              m' rs' = some (m', rs'.set c (Val.ofInt (Ar.wid 0 (n : Int)) ((j + 1 : Nat) : Int))) := by
            simp [seqI, stepI, Opd.ev, hcR, val_bin_add]
          obtain ⟨bkh, hbkh, hkph⟩ := hKH
          have hI := reach_block_jmp (S := S) (ks := ks) (dst := dst) hMI rfl hbkh hkph hinc
          have hE' := envRep_regs (rs' := rs'.set c (Val.ofInt (Ar.wid 0 (n : Int)) ((j + 1 : Nat) : Int)))
            cenv ρ1 (fun x hx => regs_set_ne rs' c x _ (Nat.ne_of_lt (hc x hx))) hP.2.1
          have hFo : Fr lay cenv c mem rs m' rs' := fr_trans hFa hF (by omega) hc
          have hFinc : Fr lay cenv c m' rs' m' (rs'.set c (Val.ofInt (Ar.wid 0 (n : Int))
              ((j + 1 : Nat) : Int))) := fr_regs (fun x hx => regs_set_ne rs' c x _ (Nat.ne_of_lt hx))
          have hFtot := fr_trans hFo hFinc (Nat.le_refl _) hc
          have IH' := ih (j + 1) (by omega) σ1 ρ1 m'
            (rs'.set c (Val.ofInt (Ar.wid 0 (n : Int)) ((j + 1 : Nat) : Int))) hP.1 hE' hP.2.2.1 hc
            (regs_set_same _ _ _)
          exact outok_lift (Reach.trans hReach (Reach.trans hrch hI)) hFtot (Nat.le_refl _) hc _ IH'
        rcases hx : execBlock O passes R body (σ.lese Λ bis.orte) ρ with ⟨σ1, ρ1⟩ | ⟨σ1, v1⟩ | ⟨σ1, rx⟩ |
          ⟨h1, σ1, ρ1⟩ | ⟨h1, σ1, ρ1⟩ | e1 | e1
        · rw [hx] at IH1
          simp only [hx]
          exact cont σ1 ρ1 IH1
        · rw [hx] at IH1
          simp only [hx, OutOk]
          exact runRet_lift hReach hFa (by omega) hc IH1
        · simp only [hx, OutOk]
        · rw [hx] at IH1
          simp only [hx, OutOk]
          exact runOk_mono hro (runOk_lift hReach hFa (by omega) hc IH1)
        · rw [hx] at IH1
          simp only [hx]
          exact cont σ1 ρ1 IH1
        · simp only [hx, OutOk]
        · simp only [hx, OutOk]

end Gabbro.Code.Lower
