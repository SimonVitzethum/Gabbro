import Grammatik.Code.Refine.Match.PayCode
import Grammatik.Code.Refine.Match.Scope

/-
  File:      Grammatik/Code/Refine/Match/Arms.lean
  Subject:   TRACK L, PHASE L1 -- THE ARMS OF A `match` ON A TAGGED VALUE, one arm at a time.

  `garmT` is arm number `i` as a block (in the context its case gives it), `execArms_garmT` says the
  source runs exactly that arm; `ArmLow` is what the lowering did for ONE arm (the block alone for a case
  without payload; the prologue block and the body in the extended context for a case with one), and
  `lowerAr_get` finds the lowering of arm `i` inside the lowering of all arms, from the state the
  arms before it left. `arm_ok` is the refinement of one arm: it takes `ArmBOk`, the statement of
  `lowerB_ok` for the arm's body, and the word of the scrutinee.
-/

namespace Gabbro.Code.Lower

variable [Conf]

open Gabbro.Grammatik (Deklaration World Env Wert Ctx Res Vertrag Orakel Ausgang EndAusgang RufAusgang
  ErgVal ErgExpr execStmt execBlock execEnd execArms eval evalErg Zahl wahr? Nutzlast armEnv)

variable {D : Deklaration} {V : Vertrag D}

/-- Arm number `i` of the arms of a match on a tagged value, as a block. -/
def garmT : {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} → {cs : List (Option (Int × Int))} →
    Gabbro.Grammatik.Arms D V l Γ Λ Λ' cs → (i : Fin cs.length) →
      Gabbro.Grammatik.Block D V l (Gabbro.Grammatik.ArmCtx Γ (cs.get i)) Λ Λ'
  | _, _, _, _, _, .cons b _, ⟨0, _⟩ => b
  | _, _, _, _, _, .cons _ rest, ⟨i + 1, h⟩ => garmT rest ⟨i, Nat.lt_of_succ_lt_succ h⟩

/-- The source runs the arm the case number names, in the environment its payload extends. -/
theorem execArms_garmT (O : Orakel D) (passes : Nat)
    (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f) :
    ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option (Int × Int))}
      (arms : Gabbro.Grammatik.Arms D V l Γ Λ Λ' cs) (i : Fin cs.length) (nutz : Nutzlast (cs.get i))
      (σ : World D) (ρ : Env D Γ),
      execArms O passes R arms ⟨i, nutz⟩ σ ρ
        = (execBlock O passes R (garmT arms i) σ (armEnv nutz ρ)).schrumpfArm (cs.get i)
  | _, _, _, _, _, .cons b _, ⟨0, _⟩, nutz, σ, ρ => rfl
  | _, _, _, _, _, .cons _ rest, ⟨i + 1, h⟩, nutz, σ, ρ =>
      execArms_garmT O passes R rest ⟨i, Nat.lt_of_succ_lt_succ h⟩ nutz σ ρ

/-- **`BOk` for the body of an arm**: in the context the case gives it (a payload is a new local, whose
    cell register is any register `a`). -/
def ArmBOk (lay : Layout D) (cenv : List Reg) (lv : Lbl × Lbl) (O : Orakel D) (passes : Nat)
    (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    (c : Option (Int × Int)) → Gabbro.Grammatik.Block D V l (Gabbro.Grammatik.ArmCtx Γ c) Λ Λ' → Prop
  | none, b => BOk lay cenv lv O passes R b
  | some (_, _), b => ∀ a, BOk lay (a :: cenv) lv O passes R b

/-- **What the lowering made of one arm**, case `c`, entry label `lb`, from state `s` to state `s'`. -/
def ArmLow (lay : Layout D) (cenv : List Reg) (lv : Lbl × Lbl) (top : Int) (W L : Nat) (ov : Opd)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    (c : Option (Int × Int)) → Gabbro.Grammatik.Block D V l (Gabbro.Grammatik.ArmCtx Γ c) Λ Λ' →
      Lbl → Lbl → St → List Block → St → Prop
  | none, b, lb, k, s, bi, s' => lowerB lay cenv lv b lb k s = some (bi, s')
  | some (lo, hi), b, lb, k, s, bi, s' =>
      ∃ (cp : List Instr) (op : Opd) (r1 : Nat) (cb : List Instr) (a : Reg) (r2 : Nat) (bb : List Block)
        (s1 : St),
        payCode top W L lo hi ov s.r = some (cp, op, r1) ∧ bindCode (.int lo hi) op r1 = some (cb, a, r2) ∧
        lowerB lay (a :: cenv) lv b s.l k ⟨r2, s.l + 1⟩ = some (bb, s1) ∧
        bi = ⟨lb, [], cp ++ cb, .jmp s.l⟩ :: bb ∧ s' = s1

/-- **Arm `i` inside the lowering of all arms.** -/
theorem lowerAr_get (lay : Layout D) (cenv : List Reg) (lv : Lbl × Lbl) (top : Int) (W L : Nat)
    (ov : Opd) :
    ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option (Int × Int))}
      (arms : Gabbro.Grammatik.Arms D V l Γ Λ Λ' cs) (lb k : Nat) (s s' : St) (blks : List Block),
      lowerAr lay cenv lv top W L ov arms lb k s = some (blks, s') →
      ∀ i : Fin cs.length, ∃ (bi : List Block) (si si' : St),
        ArmLow lay cenv lv top W L ov (cs.get i) (garmT arms i) (lb + i.val) k si bi si' ∧
        (∀ b ∈ bi, b ∈ blks) ∧ s.r ≤ si.r ∧ si'.r ≤ s'.r
  | _, _, _, _, _, .nil, lb, k, s, s', blks, h, i => Fin.elim0 i
  | _, _, _, _, _, .cons (c := none) b rest, lb, k, s, s', blks, h, ⟨0, hi⟩ => by
      simp only [lowerAr] at h
      rcases hb : lowerB lay cenv lv b lb k s with _ | ⟨b1, s1⟩
      · simp [hb] at h
      simp only [hb] at h
      rcases hr : lowerAr lay cenv lv top W L ov rest (lb + 1) k s1 with _ | ⟨b2, s2⟩
      · simp [hr] at h
      have G := lowerAr_shape lay cenv lv top W L ov rest (lb + 1) k s1 s2 b2 hr
      simp only [hr, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨b1, s, s1, hb, fun x hx => List.mem_append_left _ hx, Nat.le_refl _, G.2⟩
  | _, _, _, _, _, .cons (c := some (lo, hi)) b rest, lb, k, s, s', blks, h, ⟨0, hi'⟩ => by
      simp only [lowerAr] at h
      rcases hp : payCode top W L lo hi ov s.r with _ | ⟨cp, op, r1⟩
      · simp [hp] at h
      simp only [hp] at h
      rcases hb : bindCode (.int lo hi) op r1 with _ | ⟨cb, a, r2⟩
      · simp [hb] at h
      simp only [hb] at h
      rcases hb1 : lowerB lay (a :: cenv) lv b s.l k ⟨r2, s.l + 1⟩ with _ | ⟨bb, s1⟩
      · simp [hb1] at h
      simp only [hb1] at h
      rcases hr : lowerAr lay cenv lv top W L ov rest (lb + 1) k s1 with _ | ⟨b2, s2⟩
      · simp [hr] at h
      have G := lowerAr_shape lay cenv lv top W L ov rest (lb + 1) k s1 s2 b2 hr
      simp only [hr, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨⟨lb, [], cp ++ cb, .jmp s.l⟩ :: bb, s, s1, ⟨cp, op, r1, cb, a, r2, bb, s1, hp, hb, hb1, rfl, rfl⟩,
        fun x hx => List.mem_append_left _ hx, Nat.le_refl _, G.2⟩
  | _, _, _, _, _, .cons (c := none) b rest, lb, k, s, s', blks, h, ⟨i + 1, hi⟩ => by
      simp only [lowerAr] at h
      rcases hb : lowerB lay cenv lv b lb k s with _ | ⟨b1, s1⟩
      · simp [hb] at h
      have S1 := lowerB_shape lay cenv lv b lb k s s1 b1 hb
      simp only [hb] at h
      rcases hr : lowerAr lay cenv lv top W L ov rest (lb + 1) k s1 with _ | ⟨b2, s2⟩
      · simp [hr] at h
      simp only [hr, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨bi, si, si', hbi, hsub, hle1, hle2⟩ :=
        lowerAr_get lay cenv lv top W L ov rest (lb + 1) k s1 s2 b2 hr ⟨i, Nat.lt_of_succ_lt_succ hi⟩
      have e : lb + (i + 1) = lb + 1 + i := by omega
      refine ⟨bi, si, si', ?_, fun x hx => List.mem_append_right _ (hsub x hx),
        Nat.le_trans S1.2.2 hle1, hle2⟩
      show ArmLow lay cenv lv top W L ov _ (garmT rest ⟨i, Nat.lt_of_succ_lt_succ hi⟩) (lb + (i + 1)) k si bi si'
      rw [e]
      exact hbi
  | _, _, _, _, _, .cons (c := some (lo, hi)) b rest, lb, k, s, s', blks, h, ⟨i + 1, hi'⟩ => by
      simp only [lowerAr] at h
      rcases hp : payCode top W L lo hi ov s.r with _ | ⟨cp, op, r1⟩
      · simp [hp] at h
      have m1 := payCode_mono hp
      simp only [hp] at h
      rcases hb : bindCode (.int lo hi) op r1 with _ | ⟨cb, a, r2⟩
      · simp [hb] at h
      have m2 := bindCode_mono hb
      simp only [hb] at h
      rcases hb1 : lowerB lay (a :: cenv) lv b s.l k ⟨r2, s.l + 1⟩ with _ | ⟨bb, s1⟩
      · simp [hb1] at h
      have S1 := lowerB_shape lay (a :: cenv) lv b s.l k ⟨r2, s.l + 1⟩ s1 bb hb1
      simp only [hb1] at h
      rcases hr : lowerAr lay cenv lv top W L ov rest (lb + 1) k s1 with _ | ⟨b2, s2⟩
      · simp [hr] at h
      simp only [hr, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨bi, si, si', hbi, hsub, hle1, hle2⟩ :=
        lowerAr_get lay cenv lv top W L ov rest (lb + 1) k s1 s2 b2 hr ⟨i, Nat.lt_of_succ_lt_succ hi'⟩
      have e : lb + (i + 1) = lb + 1 + i := by omega
      have a1 := S1.2.2
      refine ⟨bi, si, si', ?_, fun x hx => List.mem_append_right _ (hsub x hx), ?_, hle2⟩
      · show ArmLow lay cenv lv top W L ov _ (garmT rest ⟨i, Nat.lt_of_succ_lt_succ hi'⟩) (lb + (i + 1)) k si bi si'
        rw [e]
        exact hbi
      · simp only at m1 m2 a1 ⊢
        omega

/-- The entry block of an arm is found and has no phis. -/
theorem armlow_kok (lay : Layout D) (cenv : List Reg) (lv : Lbl × Lbl) (top : Int) (W L : Nat) (ov : Opd)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (c : Option (Int × Int))
    (b : Gabbro.Grammatik.Block D V l (Gabbro.Grammatik.ArmCtx Γ c) Λ Λ') (lb k : Lbl) (s s' : St)
    (bi : List Block) (M : Modl) (fn : Nat) (hlow : ArmLow lay cenv lv top W L ov c b lb k s bi s')
    (hMi : InM M fn bi) : KOk M fn lb := by
  cases c with
  | none => exact kok_of_shape (lowerB_shape lay cenv lv b lb k s s' bi hlow) hMi
  | some p =>
      obtain ⟨lo, hi⟩ := p
      obtain ⟨cp, op, r1, cb, a, r2, bb, s1, hp, hb, hb1, rfl, hs'⟩ := hlow
      exact ⟨_, hMi _ (List.mem_cons_self ..), rfl⟩

/-- **The refinement of one arm.** The arm's entry block runs from the scrutinee's word (`ov` holds the
    word of the value `⟨i, nutz⟩`); the outcome is the source's, with the payload local gone out of scope. -/
theorem arm_ok (lay : Layout D) (hL : LayoutOk lay) (cenv : List Reg) (lv : Lbl × Lbl) (O : Orakel D)
    (passes : Nat) (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (top : Int) (W L : Nat) (ov : Opd)
    (c : Option (Int × Int)) (b : Gabbro.Grammatik.Block D V l (Gabbro.Grammatik.ArmCtx Γ c) Λ Λ')
    (nutz : Nutzlast c) (IHb : ArmBOk lay cenv lv O passes R c b)
    (lb k : Lbl) (s s' : St) (bi : List Block) (hlow : ArmLow lay cenv lv top W L ov c b lb k s bi s')
    (M : Modl) (S : Sees) (fn : Nat) (hMi : InM M fn bi) (hk : KOk M fn k) (hlv : LvOk M fn lv)
    (hFn : FnOk lay M) (hCall : CallRef lay M S R)
    (σ : World D) (ρ : Env D Γ) (m : Mem) (rs : Regs) (ks : List Frame) (dst : Option Reg)
    (hR : Rep lay σ m) (hE : EnvRep lay rs m cenv ρ) (hW : WfL lay m) (hc : ∀ x ∈ cenv, x < s.r)
    (i : Nat) (hiL : i < L)
    (hov : ov.ev rs = some (Val.ofInt W ((i : Int) + L * payOff c nutz))) (hlt : OpdLt ov s.r)
    (hTW : top < 2 ^ W) (hcode : (i : Int) + L * payOff c nutz < top) (hLt : (L : Int) ≤ top) :
    OutOk lay cenv lv M S fn lb k s.r s'.r m rs ks dst
      ((execBlock O passes R b σ (armEnv nutz ρ)).schrumpfArm c) := by
  cases c with
  | none =>
      exact IHb lb k s s' bi hlow M S fn hMi hk hlv hFn hCall σ ρ m rs ks dst hR hE hW hc
  | some p =>
      obtain ⟨lo, hi⟩ := p
      obtain ⟨cp, op, r1, cb, a, r2, bb, s1, hp, hb, hb1, rfl, hs'⟩ := hlow
      subst hs'
      have S1 := lowerB_shape lay (a :: cenv) lv b s.l k ⟨r2, s.l + 1⟩ s' bb hb1
      have hMhead := hMi _ (List.mem_cons_self ..)
      have hMbb : InM M fn bb := fun x hx => hMi x (List.mem_cons_of_mem _ hx)
      have hKb := kok_of_shape S1 hMbb
      have hnz : Zahl lo hi := nutz
      have F := payCode_frag top W L lo hi ov s.r m rs i (nutz : Zahl lo hi).n (payCode_fits hp) hiL
        (nutz : Zahl lo hi).lo_le (nutz : Zahl lo hi).le_hi hcode hTW hLt hov hlt (cp, op, r1) hp
      exact scope_ok (τ := .int lo hi) (l := l) (V := V) (lv := lv) (M := M) (S := S) (fn := fn) (k := k)
        (ks := ks) (dst := dst) ρ (nutz : Zahl lo hi) (lb1 := lb) (bd := s.l) (cv := cp) (cb := cb) (ov := op)
        (r0 := s.r) (r1 := r1) (r2 := r2) (a := a) (ri := r2) (r' := s'.r) m rs hR hE hW hc hMhead hKb F hb
        (Nat.le_refl _) _
        (fun m1 rs4 hRn hEn hWn hbound => IHb a s.l k ⟨r2, s.l + 1⟩ s' bb hb1 M S fn hMbb hk hlv hFn hCall σ
          (Env.cons (nutz : Zahl lo hi) ρ) m1 rs4 ks dst hRn hEn hWn hbound)

end Gabbro.Code.Lower
