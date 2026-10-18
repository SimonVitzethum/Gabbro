import Grammatik.Code.Refine.Loop

/-
  File:      Grammatik/Code/Refine/Traverse.lean
  Subject:   TRACK L, PHASE L1 -- THE REFINEMENT OF `traverse`: a loop over every index of a table.

  The lowering (`lowerS`, `.traverse`) keeps a COUNTER in the register `c = st.r`, four fixed blocks
  and the lowered body:
    * `lb`    -- `c := 0`, jump to `H`;
    * `H`     -- `if c <u count then B else k`;
    * `B`     -- the counter moved to the index type, a fresh cell holding it, jump to the body;
    * the body, whose normal end and `next` jump to `I`, whose `leave` jumps to `k`;
    * `I`     -- `c := c + 1`, jump to `H`.
  The source runs `traverseLauf` over the list of all indices `0, 1, ..` (`alleIndizes`). The proof
  is by induction on that list, with the counter equal to the number of indices already passed; the
  counter survives the body because the body's frame leaves every register below its entry bound
  (and so `c`) alone (`Fr`).
-/

namespace Gabbro.Code.Lower

variable [Conf]

open Gabbro.Grammatik (Deklaration World Env Wert Ctx Res Vertrag Orakel Ausgang EndAusgang RufAusgang
  ErgVal ErgExpr execStmt execBlock execEnd eval evalErg Zahl traverseLauf alleIndizes wahr?)

variable {D : Deklaration} {V : Vertrag D}

/-- `brc` to a block without phis. -/
theorem reach_brc {M : Modl} {S : Sees} {f : Frame} {p : IPred} {w : Nat} {a b : Opd} {t e : Lbl}
    {blk blk' : Block} {m : Mem} {ks : List Frame} {x y : Val} {x1 : BitVec 1}
    (h : Frame.atTerm M f (.brc p w a b t e) blk) (ha : a.ev f.regs = some x) (hb : b.ev f.regs = some y)
    (hc : Val.icmp p w x y = some (.int 1 x1)) (hk : M.blk f.fn (if x1 = 1 then t else e) = some blk')
    (hp : blk'.phis = []) :
    Reach M S (.run m f ks) (.run m { f with lbl := (if x1 = 1 then t else e), pc := 0 } ks) :=
  Reach.one (step_term h (by
    have he := enter_nophi hk hp
    simp only [stepTerm, ha, hb, hc, he, Option.map_some]))

/-- The indices of a table, as numbers: `0, 1, .., n - 1`. -/
theorem alleIndizes_map (n : Int) :
    (alleIndizes n).map (·.n) = (List.range n.toNat).map (fun k : Nat => (k : Int)) := by
  unfold alleIndizes
  have key : ∀ l : List Nat, (∀ k ∈ l, k < n.toNat) →
      (l.filterMap fun (k : Nat) =>
        if h : ((k : Nat) : Int) ≤ n - 1 then some (⟨((k : Nat) : Int), by omega, h⟩ : Zahl 0 (n - 1))
        else none).map (·.n) = l.map (fun k : Nat => (k : Int)) := by
    intro l
    induction l with
    | nil => intro _; rfl
    | cons k l ih =>
        intro hl
        have hk : ((k : Nat) : Int) ≤ n - 1 := by
          have := hl k (List.mem_cons_self ..); omega
        simp only [List.filterMap_cons, dif_pos hk, List.map_cons]
        rw [ih (fun k' hk' => hl k' (List.mem_cons_of_mem _ hk'))]
  exact key _ (fun k hk => List.mem_range.mp hk)


/-- The head test at counter `j`: the successor block. -/
theorem head_reach {M : Modl} {S : Sees} {fn : Nat} {H Bl k : Lbl} {c : Reg} {wc : Nat} {cnt : Int}
    {dst : Option Reg} {ks : List Frame} {m : Mem} {rs : Regs} {j : Nat}
    (hMH : M.blk fn H = some ⟨H, [], [], .brc .ult wc (.reg c) (.int wc cnt) Bl k⟩)
    (hj : rs c = some (Val.ofInt wc j)) (hw : 0 < wc) (hcnt : 0 ≤ cnt) (hfit : Ar.Fits 0 cnt wc)
    (hjc : (j : Int) ≤ cnt) (hBl : KOk M fn Bl) (hKk : KOk M fn k) :
    ((j : Int) < cnt → Reach M S (.run m ⟨fn, H, 0, rs, dst⟩ ks) (.run m ⟨fn, Bl, 0, rs, dst⟩ ks)) ∧
    (¬ (j : Int) < cnt → Reach M S (.run m ⟨fn, H, 0, rs, dst⟩ ks) (.run m ⟨fn, k, 0, rs, dst⟩ ks)) := by
  have hf2 : cnt < 2 ^ wc := by simpa [Ar.Fits] using hfit
  have hfj : FitS false wc (j : Int) := by
    simp only [FitS, Bool.false_eq_true, if_false]; constructor <;> omega
  have hfc : FitS false wc cnt := by
    simp only [FitS, Bool.false_eq_true, if_false]; constructor <;> omega
  have hcmp : Val.icmp .ult wc (Val.ofInt wc (j : Int)) (Val.ofInt wc cnt)
      = some (Val.bool (decide ((j : Int) < cnt))) :=
    val_icmp_lt false wc (j : Int) cnt hw hfj hfc
  have hat : Frame.atTerm M ⟨fn, H, 0, rs, dst⟩ (.brc .ult wc (.reg c) (.int wc cnt) Bl k)
      ⟨H, [], [], .brc .ult wc (.reg c) (.int wc cnt) Bl k⟩ := ⟨hMH, Nat.le_refl _, rfl⟩
  have ha : (Opd.reg c).ev (⟨fn, H, 0, rs, dst⟩ : Frame).regs = some (Val.ofInt wc (j : Int)) := hj
  have hb : (Opd.int wc cnt).ev (⟨fn, H, 0, rs, dst⟩ : Frame).regs = some (Val.ofInt wc cnt) := rfl
  constructor
  · intro hlt
    obtain ⟨bk, hbk, hkp⟩ := hBl
    have hc1 : Val.icmp .ult wc (Val.ofInt wc (j : Int)) (Val.ofInt wc cnt) = some (.int 1 (1 : BitVec 1)) := by
      rw [hcmp, decide_eq_true hlt]; rfl
    have := reach_brc (S := S) (m := m) (ks := ks) hat ha hb hc1 (by simpa using hbk) hkp
    simpa using this
  · intro hnl
    obtain ⟨bk, hbk, hkp⟩ := hKk
    have hc0 : Val.icmp .ult wc (Val.ofInt wc (j : Int)) (Val.ofInt wc cnt) = some (.int 1 (0 : BitVec 1)) := by
      rw [hcmp, decide_eq_false hnl]; rfl
    have h01 : ¬ ((0 : BitVec 1) = 1) := by decide
    have := reach_brc (S := S) (m := m) (ks := ks) hat ha hb hc0 (by simpa [h01] using hbk) hkp
    simpa [h01] using this

/-- **The loop, from its head block on.** For every list of indices that continues the count (`j`
    passes made, the remaining indices `j, j + 1, ..`), with the counter register at `j`, the loop
    does what `traverseLauf` says. The body's refinement is the hypothesis `IHb`. -/
theorem traverse_loop {lay : Layout D} {cenv : List Reg} {lv : Lbl × Lbl} {O : Orakel D} {passes : Nat}
    {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f} {M : Modl} {S : Sees} {fn : Nat}
    {k : Lbl} {ks : List Frame} {dst : Option Reg} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (t : D.Tab)
    (inv : Gabbro.Grammatik.Expr D Γ Λ .bool)
    (body : Gabbro.Grammatik.Block D V true (.int 0 (D.count t - 1) :: Γ) Λ Λ)
    {c : Nat} {H Bl I Bd : Nat} {cv cb : List Instr} {ov : Opd} {a r1 r2 r' : Nat}
    (hcnt : 0 ≤ D.count t) (hfit : Ar.Fits 0 (D.count t) 128)
    (hcv : cvtG (.int 0 (D.count t)) (.int 0 (D.count t - 1)) (.reg c) (c + 1) = some (cv, ov, r1))
    (hb : bindCode (.int 0 (D.count t - 1)) ov r1 = some (cb, a, r2)) (hcr : r2 ≤ r')
    (hMH : M.blk fn H = some ⟨H, [], [], .brc .ult (Ar.wid 0 (D.count t)) (.reg c)
      (.int (Ar.wid 0 (D.count t)) (D.count t)) Bl k⟩)
    (hMB : M.blk fn Bl = some ⟨Bl, [], cv ++ cb, .jmp Bd⟩)
    (hMI : M.blk fn I = some ⟨I, [], [.bin c .add (Ar.wid 0 (D.count t)) (.reg c)
      (.int (Ar.wid 0 (D.count t)) 1)], .jmp H⟩)
    (hKk : KOk M fn k) (hKbd : KOk M fn Bd)
    (IHb : ∀ (σ : World D) (ρ : Env D (.int 0 (D.count t - 1) :: Γ)) (m : Mem) (rs : Regs), Rep lay σ m →
        EnvRep lay rs m (a :: cenv) ρ → WfL lay m → (∀ x ∈ a :: cenv, x < r2) →
        OutOk lay (a :: cenv) (k, I) M S fn Bd I r2 r' m rs ks dst (execBlock O passes R body σ ρ)) :
    ∀ (L : List (Zahl 0 (D.count t - 1))) (j : Nat),
      L.map (·.n) = (List.range' j ((D.count t).toNat - j)).map (fun k : Nat => (k : Int)) →
      j ≤ (D.count t).toNat →
      ∀ (σ : World D) (ρ : Env D Γ) (m : Mem) (rs : Regs), Rep lay σ m → EnvRep lay rs m cenv ρ → WfL lay m →
        (∀ x ∈ cenv, x < c) → rs c = some (Val.ofInt (Ar.wid 0 (D.count t)) j) →
        OutOk lay cenv lv M S fn H k c r' m rs ks dst
          (traverseLauf (fun σ ρ => execBlock O passes R body σ ρ)
            (fun σ ρ => (σ.lese Λ inv.orte, wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ))) L σ ρ :
            Ausgang V l Γ) := by
  have hc1 : c + 1 ≤ r1 := cvtG_mono hcv
  have hr12 : r1 ≤ r2 := by have := bindCode_mono hb; omega
  have hwfit : Ar.Fits 0 (D.count t) (Ar.wid 0 (D.count t)) := Ar.wid_fits hfit
  have hwpos : 0 < Ar.wid 0 (D.count t) := by have := Ar.wid_pos 0 (D.count t); omega
  have hcn : (((D.count t).toNat : Nat) : Int) = D.count t := Int.toNat_of_nonneg hcnt
  intro L
  induction L with
  | nil =>
      intro j hmap hj σ ρ m rs hR hE hW hc hcj
      have hlen := congrArg List.length hmap
      simp only [List.length_map, List.length_nil, List.length_range'] at hlen
      have hjc : j = (D.count t).toNat := by omega
      have hjI : (j : Int) = D.count t := by rw [hjc]; exact hcn
      have hnl : ¬ (j : Int) < D.count t := by omega
      have hbk : KOk M fn Bl := ⟨_, hMB, rfl⟩
      obtain ⟨_, hexit⟩ := head_reach (S := S) (m := m) (dst := dst) (ks := ks) hMH hcj hwpos hcnt hwfit
        (by omega) hbk hKk
      have hH := hexit hnl
      simp only [traverseLauf]
      split
      · simp only [OutOk]
        exact ⟨m, rs, hH, ⟨hR, hE, hW, fun x hx => Nat.lt_of_lt_of_le (hc x hx) (by omega)⟩,
          fr_regs (fun _ _ => rfl)⟩
      · simp only [OutOk]
  | cons k0 L ih =>
      intro j hmap hj σ ρ m rs hR hE hW hc hcj
      have hne : List.range' j ((D.count t).toNat - j) ≠ [] := by
        intro h0; rw [h0] at hmap; simp at hmap
      have hjlt : j < (D.count t).toNat := by
        apply Nat.lt_of_not_le
        intro hge
        apply hne
        have : (D.count t).toNat - j = 0 := by omega
        rw [this]; rfl
      obtain ⟨d, hd⟩ : ∃ d, (D.count t).toNat - j = d + 1 := ⟨(D.count t).toNat - j - 1, by omega⟩
      rw [hd, List.range'_succ] at hmap
      simp only [List.map_cons, List.cons.injEq] at hmap
      obtain ⟨hk0, hL⟩ := hmap
      have hL' : L.map (·.n) = (List.range' (j + 1) ((D.count t).toNat - (j + 1))).map
          (fun k : Nat => (k : Int)) := by
        have : (D.count t).toNat - (j + 1) = d := by omega
        rw [this]; exact hL
      have hjlt' : (j : Int) < D.count t := by omega
      have hbk : KOk M fn Bl := ⟨_, hMB, rfl⟩
      have hKH : KOk M fn H := ⟨_, hMH, rfl⟩
      obtain ⟨hgo, _⟩ := head_reach (S := S) (m := m) (dst := dst) (ks := ks) hMH hcj hwpos hcnt hwfit
        (by omega) hbk hKk
      have hH := hgo hjlt'
      -- the block B: the counter as an index, a fresh cell
      obtain ⟨cV, hcV, FV⟩ := cvtG_frag (la := 0) (ha := D.count t) (lb := 0) (hb := D.count t - 1)
        (o := .reg c) (r := c + 1) (m := m) (rs := rs) (z := (j : Int)) hfit (by omega) (by omega)
        (by simpa [Opd.ev] using hcj) (opdlt_reg c (c + 1) (Nat.lt_succ_self _))
      rw [hcv] at hcV
      have hcV' := Option.some.inj hcV
      subst hcV'
      obtain ⟨rs2, hs2, hr2, hag2, hlt2, hev2⟩ := FV
      have hs2' : seqI cv m rs = some (m, rs2) := hs2
      have hE2 := envRep_regs cenv ρ (fun x hx => hag2 x (Nat.lt_succ_of_lt (hc x hx))) hE
      have hcc1 : ∀ x ∈ cenv, x < r1 := fun x hx => Nat.lt_of_lt_of_le (hc x hx) (by omega)
      obtain ⟨m1, rs4, hs4, hRn, hEnew, hWn, hra, hr2e, hag4, hFb, hcell⟩ :=
        bindCode_run lay (τ := .int 0 (D.count t - 1)) k0 ov r1 m rs2 hR hE2 hW
          (by show ov.ev rs2 = some (Val.ofInt _ k0.n); rw [hk0]; exact hev2) hlt2 hcc1 hb
      subst hr2e
      have hseq : seqI (cv ++ cb) m rs = some (m1, rs4) := by
        rw [seqI_append, hs2', Option.bind_some]; exact hs4
      obtain ⟨bkd, hbkd, hkpd⟩ := hKbd
      have hB := reach_block_jmp (S := S) (ks := ks) (dst := dst) hMB rfl hbkd hkpd hseq
      have hFbind : Fr lay cenv c m rs m1 rs4 :=
        fr_trans (fr_regs (fun x hx => hag2 x (Nat.lt_succ_of_lt hx))) hFb (by omega) hc
      have hbound : ∀ x ∈ a :: cenv, x < a + 1 := fun x hx => by
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact Nat.lt_succ_self _
        · exact Nat.lt_succ_of_lt (Nat.lt_of_lt_of_le (hcc1 x hx') hra)
      have IH1 := IHb (σ.lese Λ inv.orte) (Env.cons k0 ρ) m1 rs4 hRn hEnew hWn hbound
      simp only [traverseLauf]
      by_cases hinv : wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ) = false
      · simp [hinv, OutOk]
      · rw [if_neg hinv]
        rcases hx : execBlock O passes R body (σ.lese Λ inv.orte) (Env.cons k0 ρ) with ⟨σ1, ρ1⟩ |
          ⟨σ1, v1⟩ | ⟨σ1, rx⟩ | ⟨h1, σ1, ρ1⟩ | ⟨h1, σ1, ρ1⟩ | e1 | e1
        · -- the body fell through: next pass
          rw [hx] at IH1
          obtain ⟨m', rs', hrch, hP, hF⟩ := IH1
          simp only [hx]
          have hcR : rs' c = some (Val.ofInt (Ar.wid 0 (D.count t)) j) := by
            rw [hF.1 c (by omega), hag4 c (by omega), hag2 c (Nat.lt_succ_self _)]; exact hcj
          have hinc : seqI [Instr.bin c .add (Ar.wid 0 (D.count t)) (.reg c)
              (.int (Ar.wid 0 (D.count t)) 1)] m' rs'
              = some (m', rs'.set c (Val.ofInt (Ar.wid 0 (D.count t)) ((j + 1 : Nat) : Int))) := by
            simp [seqI, stepI, Opd.ev, hcR, val_bin_add]
          obtain ⟨bkh, hbkh, hkph⟩ := hKH
          have hI := reach_block_jmp (S := S) (ks := ks) (dst := dst) hMI rfl hbkh hkph hinc
          have hPt := post_tail ρ1 hP
          have hE' := envRep_regs (rs' := rs'.set c (Val.ofInt (Ar.wid 0 (D.count t)) ((j + 1 : Nat) : Int)))
            cenv ρ1.tail (fun x hx => regs_set_ne rs' c x _ (Nat.ne_of_lt (hc x hx))) hPt.2.1
          have hFo : Fr lay cenv c m rs m' rs' := fr_bind hFbind hcell hc (by omega) hF
          have hFinc : Fr lay cenv c m' rs' m' (rs'.set c (Val.ofInt (Ar.wid 0 (D.count t))
              ((j + 1 : Nat) : Int))) := fr_regs (fun x hx => regs_set_ne rs' c x _ (Nat.ne_of_lt hx))
          have hFtot := fr_trans hFo hFinc (Nat.le_refl _) hc
          have IH' := ih (j + 1) hL' (Nat.succ_le_of_lt hjlt) σ1 ρ1.tail m'
            (rs'.set c (Val.ofInt (Ar.wid 0 (D.count t)) ((j + 1 : Nat) : Int))) hPt.1 hE' hPt.2.2.1 hc
            (regs_set_same _ _ _)
          exact outok_lift (Reach.trans hH (Reach.trans hB (Reach.trans hrch hI))) hFtot (Nat.le_refl _) hc _
            IH'
        · rw [hx] at IH1
          simp only [hx, OutOk]
          exact runRet_bind (Reach.trans hH hB) hFbind hcell hc (by omega) IH1
        · rw [hx] at IH1
          simp only [hx, OutOk]
          exact runRet_bind (Reach.trans hH hB) hFbind hcell hc (by omega) IH1
        · -- `leave`: the loop ends
          rw [hx] at IH1
          simp only [hx]
          split
          · simp only [OutOk]
            exact runOk_bind (Reach.trans hH hB) hFbind hcell hc (by omega) IH1
          · simp only [OutOk]
        · -- `next`: the same as falling through
          rw [hx] at IH1
          obtain ⟨m', rs', hrch, hP, hF⟩ := IH1
          simp only [hx]
          have hcR : rs' c = some (Val.ofInt (Ar.wid 0 (D.count t)) j) := by
            rw [hF.1 c (by omega), hag4 c (by omega), hag2 c (Nat.lt_succ_self _)]; exact hcj
          have hinc : seqI [Instr.bin c .add (Ar.wid 0 (D.count t)) (.reg c)
              (.int (Ar.wid 0 (D.count t)) 1)] m' rs'
              = some (m', rs'.set c (Val.ofInt (Ar.wid 0 (D.count t)) ((j + 1 : Nat) : Int))) := by
            simp [seqI, stepI, Opd.ev, hcR, val_bin_add]
          obtain ⟨bkh, hbkh, hkph⟩ := hKH
          have hI := reach_block_jmp (S := S) (ks := ks) (dst := dst) hMI rfl hbkh hkph hinc
          have hPt := post_tail ρ1 hP
          have hE' := envRep_regs (rs' := rs'.set c (Val.ofInt (Ar.wid 0 (D.count t)) ((j + 1 : Nat) : Int)))
            cenv ρ1.tail (fun x hx => regs_set_ne rs' c x _ (Nat.ne_of_lt (hc x hx))) hPt.2.1
          have hFo : Fr lay cenv c m rs m' rs' := fr_bind hFbind hcell hc (by omega) hF
          have hFinc : Fr lay cenv c m' rs' m' (rs'.set c (Val.ofInt (Ar.wid 0 (D.count t))
              ((j + 1 : Nat) : Int))) := fr_regs (fun x hx => regs_set_ne rs' c x _ (Nat.ne_of_lt hx))
          have hFtot := fr_trans hFo hFinc (Nat.le_refl _) hc
          have IH' := ih (j + 1) hL' (Nat.succ_le_of_lt hjlt) σ1 ρ1.tail m'
            (rs'.set c (Val.ofInt (Ar.wid 0 (D.count t)) ((j + 1 : Nat) : Int))) hPt.1 hE' hPt.2.2.1 hc
            (regs_set_same _ _ _)
          exact outok_lift (Reach.trans hH (Reach.trans hB (Reach.trans hrch hI))) hFtot (Nat.le_refl _) hc _
            IH'
        · simp only [hx, OutOk]
        · simp only [hx, OutOk]

end Gabbro.Code.Lower
