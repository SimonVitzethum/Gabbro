import Grammatik.Code.Refine.Match.Scope
import Grammatik.Code.Refine.Labels

/-
  File:      Grammatik/Code/Refine/Match/Why.lean
  Subject:   TRACK L, PHASE L1 -- THE REFINEMENT OF `match` ON A REASON (`Stmt.onWhy`).

  The lowering (`lowerS`, `.onWhy`): the reason's number `i` in `Ar.wid 0 (n - 1)` bits, then
    * `lb`        -- `switch i, default st.l, [(0, st.l + 1), (1, st.l + 2), ..]`;
    * `st.l`      -- `dead`: never entered, the default of numbers that are no reason's;
    * `st.l+1+i`  -- the lowered arm `i`, each arm lowered at its own entry label, one after the other
                     (`lowerGA`).
  The source picks the arm by the number (`execGrund`); `garm` is that arm as a plain block and
  `lowerGA_get` finds its lowering inside the lowering of all arms, so the proof needs the
  refinement of ONE block at a time (`BOk`), which the mutual theorem supplies for every arm.
-/

namespace Gabbro.Code.Lower

variable [Conf]

open Gabbro.Grammatik (Deklaration World Env Wert Ctx Res Vertrag Orakel Ausgang EndAusgang RufAusgang
  ErgVal ErgExpr execStmt execBlock execEnd execGrund eval evalErg Zahl wahr?)

variable {D : Deklaration} {V : Vertrag D}

/-- Arm number `i` of the arms of a match on a reason, as a block. -/
def garm : {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} → {n : Nat} →
    Gabbro.Grammatik.GrundArms D V l Γ Λ Λ' n → Fin n → Gabbro.Grammatik.Block D V l Γ Λ Λ'
  | _, _, _, _, _, .cons b _, ⟨0, _⟩ => b
  | _, _, _, _, _, .cons _ rest, ⟨i + 1, h⟩ => garm rest ⟨i, Nat.lt_of_succ_lt_succ h⟩

/-- The source runs the arm the number names. -/
theorem execGrund_garm (O : Orakel D) (passes : Nat)
    (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f) :
    ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat}
      (arms : Gabbro.Grammatik.GrundArms D V l Γ Λ Λ' n) (i : Fin n) (σ : World D) (ρ : Env D Γ),
      execGrund O passes R arms i σ ρ = execBlock O passes R (garm arms i) σ ρ
  | _, _, _, _, _, .cons b _, ⟨0, _⟩, σ, ρ => rfl
  | _, _, _, _, _, .cons _ rest, ⟨i + 1, h⟩, σ, ρ =>
      execGrund_garm O passes R rest ⟨i, Nat.lt_of_succ_lt_succ h⟩ σ ρ

/-- **Arm `i` inside the lowering of all arms**: it was lowered at entry label `lb + i` from some state
    `si` (above the counter the arms started at) to `si'` (below where all arms end), and its blocks are
    among theirs. -/
theorem lowerGA_get (lay : Layout D) (cenv : List Reg) (lv : Lbl × Lbl) :
    ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat}
      (arms : Gabbro.Grammatik.GrundArms D V l Γ Λ Λ' n) (lb k : Nat) (s s' : St) (blks : List Block),
      lowerGA lay cenv lv arms lb k s = some (blks, s') →
      ∀ i : Fin n, ∃ (bi : List Block) (si si' : St),
        lowerB lay cenv lv (garm arms i) (lb + i.val) k si = some (bi, si') ∧ (∀ b ∈ bi, b ∈ blks) ∧
        s.r ≤ si.r ∧ si'.r ≤ s'.r
  | _, _, _, _, _, .nil, lb, k, s, s', blks, h, i => Fin.elim0 i
  | _, _, _, _, _, .cons b rest, lb, k, s, s', blks, h, ⟨0, hi⟩ => by
      simp only [lowerGA] at h
      rcases hb : lowerB lay cenv lv b lb k s with _ | ⟨b1, s1⟩
      · simp [hb] at h
      simp only [hb] at h
      rcases hr : lowerGA lay cenv lv rest (lb + 1) k s1 with _ | ⟨b2, s2⟩
      · simp [hr] at h
      have G := lowerGA_shape lay cenv lv rest (lb + 1) k s1 s2 b2 hr
      simp only [hr, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨b1, s, s1, by simpa [garm] using hb, fun x hx => List.mem_append_left _ hx,
        Nat.le_refl _, G.2⟩
  | _, _, _, _, _, .cons b rest, lb, k, s, s', blks, h, ⟨i + 1, hi⟩ => by
      simp only [lowerGA] at h
      rcases hb : lowerB lay cenv lv b lb k s with _ | ⟨b1, s1⟩
      · simp [hb] at h
      have S1 := lowerB_shape lay cenv lv b lb k s s1 b1 hb
      simp only [hb] at h
      rcases hr : lowerGA lay cenv lv rest (lb + 1) k s1 with _ | ⟨b2, s2⟩
      · simp [hr] at h
      simp only [hr, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨bi, si, si', hbi, hsub, hle1, hle2⟩ :=
        lowerGA_get lay cenv lv rest (lb + 1) k s1 s2 b2 hr ⟨i, Nat.lt_of_succ_lt_succ hi⟩
      have e : lb + (i + 1) = lb + 1 + i := by omega
      refine ⟨bi, si, si', ?_, fun x hx => List.mem_append_right _ (hsub x hx),
        Nat.le_trans S1.2.2 hle1, hle2⟩
      show lowerB lay cenv lv (garm rest ⟨i, Nat.lt_of_succ_lt_succ hi⟩) (lb + (i + 1)) k si = some (bi, si')
      rw [e]
      exact hbi

/-! ## The `switch` -/

/-- A block whose body runs and whose terminator is a `switch`, to a block without phis. -/
theorem reach_block_sw {M : Modl} {S : Sees} {fn : Nat} {lb d : Lbl} {cs : List (Int × Lbl)} {b bk : Block}
    {m m' : Mem} {rs rs' : Regs} {ks : List Frame} {dst : Option Reg} {w : Nat} {o : Opd} {x : BitVec w}
    {l : Lbl}
    (hb : M.blk fn lb = some b) (hbt : b.term = .sw w o d cs) (hs : seqI b.body m rs = some (m', rs'))
    (ho : o.ev rs' = some (.int w x))
    (hl : ∀ c, cs.find? (fun c => decide (BitVec.ofInt w c.1 = x)) = some c → c.2 = l)
    (hn : cs.find? (fun c => decide (BitVec.ofInt w c.1 = x)) = none → d = l)
    (hk : M.blk fn l = some bk) (hkp : bk.phis = []) :
    Reach M S (.run m ⟨fn, lb, 0, rs, dst⟩ ks) (.run m' ⟨fn, l, 0, rs', dst⟩ ks) := by
  have h1 := reach_seq M S b.body m ⟨fn, lb, 0, rs, dst⟩ ks m' rs'
    ⟨b, hb, fun i h => by simp⟩ hs
  have h2 : Reach M S (.run m' ⟨fn, lb, 0 + b.body.length, rs', dst⟩ ks) (.run m' ⟨fn, l, 0, rs', dst⟩ ks) :=
    Reach.one (step_term (f := ⟨fn, lb, 0 + b.body.length, rs', dst⟩) (blk := b)
      ⟨hb, (show b.body.length ≤ 0 + b.body.length by omega), hbt⟩ (by
        have he := enter_nophi (f := (⟨fn, lb, 0 + b.body.length, rs', dst⟩ : Frame)) hk hkp
        simp only [stepTerm, ho]
        rw [dif_pos trivial]
        split
        · rename_i c hc
          rw [hl c hc, he]
          rfl
        · rename_i hc
          rw [hn hc, he]
          rfl))
  exact Reach.trans h1 h2

theorem toNat_ofInt_nat {w r : Nat} (h : r < 2 ^ w) : (BitVec.ofInt w (r : Int)).toNat = r := by
  rw [Ar.toNat_ofInt_lt (Int.natCast_nonneg r) (by exact_mod_cast h)]
  rfl

/-- The table of the `switch` finds entry `r` for the number `r`. -/
theorem find_tbl (w n r base : Nat) (hn : n ≤ 2 ^ w) (hr : r < n) :
    (((List.range n).map fun (i : Nat) => ((i : Int), (base + i : Nat))).find?
      fun c => decide (BitVec.ofInt w c.1 = BitVec.ofInt w (r : Int))) = some ((r : Int), (base + r : Nat)) := by
  induction n with
  | zero => exact absurd hr (Nat.not_lt_zero _)
  | succ n ih =>
      rw [List.range_succ, List.map_append, List.find?_append]
      by_cases hlt : r < n
      · rw [ih (by omega) hlt]; rfl
      · have hrn : r = n := by omega
        subst hrn
        have hnone : (((List.range r).map fun (i : Nat) => ((i : Int), (base + i : Nat))).find?
            fun c => decide (BitVec.ofInt w c.1 = BitVec.ofInt w (r : Int))) = none := by
          rw [List.find?_eq_none]
          intro c hc
          obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc
          have hi' := List.mem_range.mp hi
          simp only [decide_eq_true_eq]
          intro heq
          have := congrArg BitVec.toNat heq
          rw [toNat_ofInt_nat (by omega), toNat_ofInt_nat (by omega)] at this
          omega
        rw [hnone]
        simp

/-! ## The statement -/

theorem onWhy_ok (lay : Layout D) (hL : LayoutOk lay) (cenv : List Reg) (lv : Lbl × Lbl)
    (O : Orakel D) (passes : Nat)
    (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat}
    (r : Gabbro.Grammatik.Expr D Γ Λ (.why n))
    (arms : Gabbro.Grammatik.GrundArms D V l Γ Λ Λ' n)
    (IH : ∀ i : Fin n, BOk lay cenv lv O passes R (garm arms i))
    (lb k : Lbl) (st st' : St) (blks : List Block)
    (h : lowerS lay cenv lv (Gabbro.Grammatik.Stmt.onWhy r arms) lb k st = some (blks, st'))
    (M : Modl) (S : Sees) (fn : Nat) (hM : InM M fn blks) (hk : KOk M fn k) (hlv : LvOk M fn lv)
    (hFn : FnOk lay M) (hCall : CallRef lay M S R)
    (σ : World D) (ρ : Env D Γ) (m : Mem) (rs : Regs) (ks : List Frame) (dst : Option Reg)
    (hR : Rep lay σ m) (hE : EnvRep lay rs m cenv ρ) (hW : WfL lay m) (hc : ∀ x ∈ cenv, x < st.r) :
    OutOk lay cenv lv M S fn lb k st.r st'.r m rs ks dst
      (execStmt O passes R (Gabbro.Grammatik.Stmt.onWhy r arms) σ ρ) := by
  simp only [lowerS] at h
  rcases hr : lowerE lay cenv r st.r with _ | ⟨cr, orr, r1⟩
  · simp [hr] at h
  simp only [hr] at h
  have hfit : Ar.Fits 0 ((n : Int) - 1) 128 := by
    apply Classical.byContradiction
    intro hn
    rw [if_neg hn] at h
    simp at h
  rw [if_pos hfit] at h
  rcases hga : lowerGA lay cenv lv arms (st.l + 1) k ⟨r1, st.l + 1 + n⟩ with _ | ⟨ba, s1⟩
  · simp [hga] at h
  simp only [hga] at h
  have h' := Option.some.inj h
  simp only [Prod.mk.injEq] at h'
  obtain ⟨rfl, rfl⟩ := h'
  have m1 := lowerE_mono lay cenv r st.r _ hr
  have hb0 := hM _ (List.mem_cons_self ..)
  obtain ⟨σl, hσl⟩ : ∃ σl, σl = σ.lese Λ r.orte := ⟨_, rfl⟩
  simp only [execStmt]
  try rw [← hσl]
  have hRl' : Rep lay σl m := by rw [hσl]; exact hR
  obtain ⟨Fo, _⟩ := lowerE_ok lay hL r cenv st.r (cr, orr, r1) hr σl σl ρ m rs hRl' hE hc
  obtain ⟨rs1, hs1, hr1, hag1, hlt1, hev1⟩ := Fo
  have hs1' : seqI cr m rs = some (m, rs1) := hs1
  have hE1 := envRep_regs cenv ρ (fun x hx => hag1 x (hc x hx)) hE
  have hc1 : ∀ x ∈ cenv, x < r1 := fun x hx => Nat.lt_of_lt_of_le (hc x hx) hr1
  have e : execGrund O passes R arms (eval σl r σl ρ) σl ρ
      = execBlock O passes R (garm arms (eval σl r σl ρ)) σl ρ := execGrund_garm O passes R arms _ σl ρ
  rw [e]
  generalize hve : (eval σl r σl ρ : Fin n) = i at hev1 ⊢
  obtain ⟨bi, si, si', hbi, hsub, hle1, hle2⟩ := lowerGA_get lay cenv lv arms (st.l + 1) k
    ⟨r1, st.l + 1 + n⟩ s1 ba hga i
  have Si := lowerB_shape lay cenv lv (garm arms i) (st.l + 1 + i.val) k si si' bi hbi
  have hMi : InM M fn bi := fun b hb' =>
    hM b (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hsub b hb')))
  have hKi := kok_of_shape Si hMi
  obtain ⟨bkb, hbkb, hkpb⟩ := hKi
  have hin : n ≤ 2 ^ (Ar.wid 0 ((n : Int) - 1)) := by
    have hw := Ar.wid_fits hfit
    unfold Ar.Fits at hw
    by_cases hn0 : n = 0
    · subst hn0; exact Nat.zero_le _
    · rw [if_pos (by omega)] at hw
      have h2 : (n : Int) ≤ 2 ^ (Ar.wid 0 ((n : Int) - 1)) := by omega
      exact_mod_cast h2
  have hev : orr.ev rs1 = some (.int (Ar.wid 0 ((n : Int) - 1))
      (BitVec.ofInt (Ar.wid 0 ((n : Int) - 1)) (i.val : Int))) := hev1
  have hbr := reach_block_sw (S := S) (ks := ks) (dst := dst) (l := st.l + 1 + i.val) hb0 rfl hs1' hev
    (by
      intro c hc
      rw [find_tbl _ n i.val (st.l + 1) hin i.isLt] at hc
      have := Option.some.inj hc
      rw [← this])
    (by
      intro hc
      rw [find_tbl _ n i.val (st.l + 1) hin i.isLt] at hc
      exact absurd hc (by simp))
    hbkb hkpb
  exact outok_mono hle2 _ (outok_lift hbr (fr_regs hag1) (Nat.le_trans hr1 hle1) hc _
    (IH i (st.l + 1 + i.val) k si si' bi hbi M S fn hMi hk hlv hFn hCall σl ρ m rs1 ks dst hRl' hE1 hW
      (fun x hx => Nat.lt_of_lt_of_le (hc1 x hx) hle1)))

end Gabbro.Code.Lower
