/-
  File:      Grammatik/CFormenRZeuge2.lean
  Subject:   More witnesses of `CFormenR.lean` (rule 13): `narrow` and the
             check on `schreibe`'s `len` (the syscall's own `requires len
             <= 1024`, checked instead of assumed), forwarding a reason
             through a channel, and `locks` with a release.

  The shapes are the emitter's (emit.rs 8625ff.: `if (!(o <= hi)) { … }`
  -- the `>= 0` half is left out over an unsigned word; the forwarding
  `*_grund = e; return false;` of `beispiele/96`; `L_nimm(); { … }
  L_gib();`); the programs around them are fixtures on `d74` and `refD`.
-/
import Grammatik.CFormenRZeuge
import Grammatik.CFormenZeuge

namespace Gabbro.Grammatik

/-! ## 1. `narrow len to 0 .. 1024 else { return 0; } return len;` -/

def sonst74 : Endblock d74 V74s false Γ74 [] :=
  .ret (.wert (Expr.weiter (by decide) (by decide) (Expr.lit 0))) (List.Perm.refl _)

def narrowRest : Block d74 V74s false (.int 0 1024 :: Γ74) [] [] :=
  .cons (Stmt.ret (.wert (Expr.weiter (by decide) (by decide) (Expr.var .hier))) (List.Perm.refl _)) .nil

def narrowBlk : Block d74 V74s false Γ74 [] [] :=
  Block.narrow (Expr.var vLen) 0 1024 sonst74 narrowRest

/-- The emitted C: `if (!(len <= 1024)) { return 0; } return len;` --
    the narrowed value is `len`'s own C local 2. -/
def cNarrow : CS :=
  .seq (.ite (.lnot (.cmp .le CIT.u64 (.var 2) (.lit 1024))) (.ret (some (cU64, .lit 0))) .skip)
    (.seq (.ret (some (cU64, .var 2))) .skip)

theorem sonst74_corr : EndSemG xS74 0 false G0 k74 sonst74 (.ret (some (cU64, .lit 0))) := by
  have hE : ErgCorr xS74 k74 (Λ := []) (e := some u64T)
      (ErgExpr.wert (Expr.weiter (by decide) (by decide) (Expr.lit 0))) (some (cU64, .lit 0)) :=
    ⟨cU64, .lit 0, rfl, ecorr_weiter _ _ _ _ (ecorr_lit _ _ 0), rfl⟩
  have hR : EndCorrG xS74 0 false G0 k74 sonst74 ((CS.ret (some (cU64, .lit 0))).zs G0.gs) :=
    EndCorrG.ret rfl (List.Perm.refl _) hE
  exact cCorrG_end _ _ _ _ hR

theorem narrowRest_corr : BlockSemG xS74 0 G0 (k74.push (.int 0 1024) 2) narrowRest
    (.seq (.ret (some (cU64, .var 2))) .skip) := by
  have hE : ErgCorr xS74 (k74.push (.int 0 1024) 2) (Λ := []) (e := some u64T)
      (ErgExpr.wert (Expr.weiter (by decide) (by decide) (Expr.var .hier))) (some (cU64, .var 2)) :=
    ⟨cU64, .var 2, rfl, ecorr_weiter _ _ _ _ (ecorr_var _ _ .hier), rfl⟩
  exact cCorrG_block _ _ _ (BlockCorrG.cons
    (liftG xS74 0 G0 _ (scorr_ret xS74 0 _ (V := V74s) (l := false) (List.Perm.refl _) hE)
      (fun _ h => nomatch h) (fun κ hk => by simp [G0] at hk) (keeps_ret _ _ _ _ _)
      (fun h => absurd rfl h)) BlockCorrG.nil)

/-- R3 INSTANTIATED: the emitted narrow of `len` corresponds. -/
theorem narrow74_corr : BlockSemG xS74 0 G0 k74 narrowBlk cNarrow :=
  gsem_narrow xS74 0 G0 k74 2
    (narrowCond_le0 xS74 G0 k74 CIT.u64 (ecorr_var xS74 k74 vLen) 1024 (Int.le_refl 0)
      ⟨by decide, by decide⟩ ⟨by decide, by decide⟩)
    (narrow_bind_var xS74 G0 k74 vLen) sonst74_corr narrowRest_corr

/-- The C locals of `schreibe` with `len = c`. -/
def rhoC74 (a b c : Nat) : CLok :=
  lokUpd (lokUpd (lokUpd (fun _ => .undef) 2 (.int c)) 1 (.int b)) 0 (.int a)

theorem envRelG0_74 (a b c : Nat) (ha : a ≤ 18446744073709551615) (hb : b ≤ 18446744073709551615)
    (hc : c ≤ 18446744073709551615) :
    EnvRelG xS74 G0 k74 (rho74 a b c ha hb hc) (rhoC74 a b c) st74 :=
  ⟨envRel74 a b c ha hb hc, trivial, fun _ hq => (nomatch hq)⟩

/-- WITNESS, `narrow` both ways: with `len = 5` the C returns `len` (5),
    with `len = 2000` the `else` block returns 0 -- as the Gabbro block
    does. -/
theorem narrow_zeuge :
    (∃ st', Exec el74.lay orc74 2 xS74.CR xS74.XR cNarrow st74 (rhoC74 3 7 5)
      (.ret st' (some (.int 5)))) ∧
    (∃ st', Exec el74.lay orc74 2 xS74.CR xS74.XR cNarrow st74 (rhoC74 3 7 2000)
      (.ret st' (some (.int 0)))) := by
  constructor
  · obtain ⟨o, hx, hO⟩ := narrow74_corr w74 st74 (rho74 3 7 5) (rhoC74 3 7 5) (corr74 _ _)
      (envRelG0_74 3 7 5 (by decide) (by decide) (by decide)) rfl
    obtain ⟨st', cv, ho, -, c, hcv, hc⟩ := hO
    subst ho; subst hcv
    have : c = .int 5 := hc
    subst this
    exact ⟨st', hx⟩
  · obtain ⟨o, hx, hO⟩ := narrow74_corr w74 st74 (rho74 3 7 2000) (rhoC74 3 7 2000) (corr74 _ _)
      (envRelG0_74 3 7 2000 (by decide) (by decide) (by decide)) rfl
    obtain ⟨st', cv, ho, -, c, hcv, hc⟩ := hO
    subst ho; subst hcv
    have : c = .int 0 := hc
    subst this
    exact ⟨st', hx⟩

/-! ## 2. The check: `if (!(len <= 1024)) { return 0; }` -/

def pruefBlk : Block d74 V74s false Γ74 [] [] :=
  Block.pruefung (Expr.le (Expr.var vLen) (Expr.lit 1024)) sonst74 .nil

def cPruef : CS :=
  .seq (.ite (.lnot (.cmp .le CIT.u64 (.var 2) (.lit 1024))) (.ret (some (cU64, .lit 0))) .skip) .skip

/-- R4 INSTANTIATED. -/
theorem pruef74_corr : BlockSemG xS74 0 G0 k74 pruefBlk cPruef :=
  gsem_pruefung xS74 0 G0 k74
    (ecorr_le xS74 k74 CIT.u64 (ecorr_var xS74 k74 vLen) (ecorr_lit xS74 k74 1024)
      ⟨by decide, by decide⟩ ⟨by decide, by decide⟩)
    sonst74_corr (cCorrG_block _ _ _ BlockCorrG.nil)

/-- WITNESS, the check both ways: `len = 5` passes (the C ends normally),
    `len = 2000` fails (the C returns 0). -/
theorem pruef_zeuge :
    (∃ st' ρ', Exec el74.lay orc74 2 xS74.CR xS74.XR cPruef st74 (rhoC74 3 7 5) (.norm st' ρ')) ∧
    (∃ st', Exec el74.lay orc74 2 xS74.CR xS74.XR cPruef st74 (rhoC74 3 7 2000)
      (.ret st' (some (.int 0)))) := by
  constructor
  · obtain ⟨o, hx, hO⟩ := pruef74_corr w74 st74 (rho74 3 7 5) (rhoC74 3 7 5) (corr74 _ _)
      (envRelG0_74 3 7 5 (by decide) (by decide) (by decide)) rfl
    obtain ⟨st', ρ', ho, -⟩ := hO
    subst ho
    exact ⟨st', ρ', hx⟩
  · obtain ⟨o, hx, hO⟩ := pruef74_corr w74 st74 (rho74 3 7 2000) (rhoC74 3 7 2000) (corr74 _ _)
      (envRelG0_74 3 7 2000 (by decide) (by decide) (by decide)) rfl
    obtain ⟨st', cv, ho, -, c, hcv, hc⟩ := hO
    subst ho; subst hcv
    have : c = .int 0 := hc
    subst this
    exact ⟨st', hx⟩

/-! ## 3. Forwarding a reason: `*_grund = e; return false;` -/

/-- Every arm returns the reason it matched. -/
def armFwd (i : Nat) (h : i < 12) : Block d74 V74w false Γ74 [] [] :=
  .cons (Stmt.retGrund ⟨i, h⟩ (List.Perm.refl _)) .nil

def armsFwd : GrundArms d74 V74w false Γ74 [] [] 12 :=
  .cons (armFwd 0 (by decide)) (.cons (armFwd 1 (by decide)) (.cons (armFwd 2 (by decide))
    (.cons (armFwd 3 (by decide)) (.cons (armFwd 4 (by decide)) (.cons (armFwd 5 (by decide))
    (.cons (armFwd 6 (by decide)) (.cons (armFwd 7 (by decide)) (.cons (armFwd 8 (by decide))
    (.cons (armFwd 9 (by decide)) (.cons (armFwd 10 (by decide)) (.cons (armFwd 11 (by decide))
    .nil)))))))))))

theorem armsFwd_grund : ∀ (i : Fin 12) (σ : World d74) (ρ : Env d74 Γ74),
    execBlock o74 0 (rufAt p74 o74 0 0) (armsFwd.get i) σ ρ = .grund σ (id i) := by
  intro i σ ρ
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl
  | ⟨3, _⟩ => rfl
  | ⟨4, _⟩ => rfl
  | ⟨5, _⟩ => rfl
  | ⟨6, _⟩ => rfl
  | ⟨7, _⟩ => rfl
  | ⟨8, _⟩ => rfl
  | ⟨9, _⟩ => rfl
  | ⟨10, _⟩ => rfl
  | ⟨11, _⟩ => rfl

theorem fit74 : ∀ i : Fin 12, valFits cIo (.int ((i : Nat) : Int)) = true := by
  intro i
  have := i.isLt
  show decide (cLo true .w32 ≤ ((i : Nat) : Int) ∧ ((i : Nat) : Int) ≤ cHi true .w32) = true
  apply decide_eq_true
  have e1 : cLo true .w32 = -2147483648 := by decide
  have e2 : cHi true .w32 = 2147483647 := by decide
  rw [e1, e2]
  omega

/-- R2 INSTANTIATED, in `write`'s channel: `match BadFd { … }` whose
    every arm returns its reason, against `*_grund = 9; return false;`. -/
theorem fwd74_corr (wp gp : CPtr) {f x : Nat} (hg : gp.blk = .stk f x) :
    StmtCorrG xW74 0 ⟨[], some (κ74 wp gp)⟩ k74
      (Stmt.onGrund (Expr.grund 12 ⟨9, by decide⟩) armsFwd)
      (.seq (.store (.var 4) cIo (.lit 9)) (.ret (some (cBoolTy, .lit 0)))) :=
  kcorr_weiterleiten xW74 0 _ k74 (κ74 wp gp) rfl (ecorr_grundLit xW74 k74 12 ⟨9, by decide⟩) id
    armsFwd_grund (fun _ => rfl) fit74 hg

/-- A state of `write`'s frame with `e`'s cell of `schreibe` writable
    behind `_grund`. -/
def stFwd : CSt := { mem := fun _ _ => .undef, live := fun _ => true, obs := [] }

/-- WITNESS, forwarding: the C writes 9 into the caller's cell and returns
    `false`; the Gabbro statement returns reason 9. -/
theorem fwd_zeuge :
    ∃ st', Exec el74.lay orc74 1 xW74.CR xW74.XR
        (.seq (.store (.var 4) cIo (.lit 9)) (.ret (some (cBoolTy, .lit 0)))) stFwd
        (lokUpd (lokUpd (rhoC74 3 7 5) 3 (.ptr ⟨.stk 2 4, 0⟩)) 4 (.ptr ⟨.stk 2 5, 0⟩))
        (.ret st' (some (.int 0))) ∧ st'.mem (.stk 2 5) 0 = .int 9 := by
  have hrel : EnvRelG xW74 ⟨[], some (κ74 ⟨.stk 2 4, 0⟩ ⟨.stk 2 5, 0⟩)⟩ k74 (rho74 3 7 5 (by decide)
      (by decide) (by decide)) (lokUpd (lokUpd (rhoC74 3 7 5) 3 (.ptr ⟨.stk 2 4, 0⟩)) 4
        (.ptr ⟨.stk 2 5, 0⟩)) stFwd := by
    refine ⟨?_, ⟨rfl, rfl, by decide, by decide⟩, fun _ hq => (nomatch hq)⟩
    refine ⟨fun τ x => ?_, fun _ hq => (nomatch hq), fun _ hq => (nomatch hq)⟩
    cases x with
    | hier => rfl
    | dort y =>
        cases y with
        | hier => rfl
        | dort z =>
            cases z with
            | hier => rfl
            | dort w => exact nomatch w
  obtain ⟨o, hx, hO⟩ := fwd74_corr ⟨.stk 2 4, 0⟩ ⟨.stk 2 5, 0⟩ rfl w74 stFwd _ _ (corr74 _ _)
    hrel rfl
  obtain ⟨st', ho, -, hm⟩ := hO
  subst ho
  exact ⟨st', hx, hm⟩

/-! ## 4. `locks` and a release, on `refD` -/

/-- Foreign calls that return and change nothing: `L_nimm()` (5),
    `L_gib()` (6) -- the assumption at the runtime's lock functions. -/
def xrNoop : CCallR := fun _ st vs st' rv => vs = [] ∧ st' = st ∧ rv = none

theorem noop_ext (n : Nat) : ExtNoop xrNoop n :=
  fun st => ⟨st, ⟨rfl, rfl, rfl⟩, SameML.refl st⟩

/-- `einzahlen`'s frame with the lock runtime. -/
def xL : TVCtx refD :=
  ⟨refEL, tvOrc, 2, CallAt refEL.lay tvOrc xrNoop refCProg 1, xrNoop, refO, 0, rufAt refP refO 0 1⟩

/-- `konto[0] = 100;` under the lock. -/
def lockBody : Block refD (vertragVon refD refEin) false [.int 0 10] [Res.held (D := refD) ()]
    [Res.held (D := refD) ()] :=
  .cons (.assignSlot () () refIdxEin refHundert (refEin_schreibt ()) refDarf) .nil

theorem lockRang : ∀ M, Res.held (D := refD) M ∈ ([] : List (Res refD)) → refD.rang M < refD.rang () :=
  fun _ h => nomatch h

theorem lockBody_corr : BlockSemG xL 0 G0 kEin lockBody (.seq (.store cStand cU32 (.lit 100)) .skip) := by
  have hi : ExprCorr xL kEin (.var 1) refIdxEin :=
    ecorr_fest xL kEin kEin_ks refIdxEin (fun _ _ => rfl)
  have he : ExprCorr xL kEin (.lit 100) refHundert := ecorr_weiter xL kEin _ _ (ecorr_lit xL kEin 100)
  have hk : KeepsG xL G0 kEin (.store cStand cU32 (.lit 100)) :=
    fun _ _ _ _ _ _ _ _ => ⟨fun _ hq => (nomatch hq), fun κ hk => by simp [G0] at hk⟩
  exact cCorrG_block _ _ _ (BlockCorrG.cons
    (liftG xL 0 G0 kEin (scorr_assignSlotParam xL kEin 0 kEin_pp () rfl _ _ hi he)
      (fun _ h => nomatch h) (fun κ hk => by simp [G0] at hk) hk (fun h => absurd rfl h))
    BlockCorrG.nil)

/-- M8 WITH GHOSTS INSTANTIATED: `L_nimm(); { konto[0] = 100; } L_gib();`. -/
theorem locks_corr : StmtCorrG xL 0 G0 kEin
    (Stmt.locks (V := vertragVon refD refEin) (l := false) (Γ := [.int 0 10]) () lockRang lockBody)
    (.seq (.ext 5 [] none) (.seq (.seq (.store cStand cU32 (.lit 100)) .skip) (.ext 6 [] none))) :=
  gcorr_locks xL 0 G0 kEin () lockRang lockBody 5 6 (noop_ext 5) (noop_ext 6) lockBody_corr

/-- A release before a statement. -/
theorem extPre_corr : StmtCorrG xL 0 G0 kEin
    (Stmt.locks (V := vertragVon refD refEin) (l := false) (Γ := [.int 0 10]) () lockRang lockBody)
    (.seq (.ext 6 [] none)
      (.seq (.ext 5 [] none) (.seq (.seq (.store cStand cU32 (.lit 100)) .skip) (.ext 6 [] none)))) :=
  gcorr_extPre xL 0 G0 kEin 6 (noop_ext 6) locks_corr

/-- WITNESS, `locks`: from the zero state the C takes the lock, writes
    `100`, gives it back, and ends normally with the slot at `100`. -/
theorem locks_zeuge :
    ∃ st' ρ', Exec refEL.lay tvOrc 2 xL.CR xL.XR
        (.seq (.ext 5 [] none) (.seq (.seq (.store cStand cU32 (.lit 100)) .skip) (.ext 6 [] none)))
        refSt0 (lokUpd (lokUpd (lokUpd (fun _ => .undef) 2 (.int 7)) 1 (.int 0)) 0 (.ptr ⟨.tab 0, 0⟩))
        (.norm st' ρ') ∧ st'.mem (.tab 0) 0 = .int 100 := by
  obtain ⟨o, hx, hO⟩ := locks_corr refW0 refSt0 refRho7 _ refW0_corr
    ⟨ein_envRel, trivial, fun _ hq => (nomatch hq)⟩ rfl
  obtain ⟨st', ρ', ho, hc, -⟩ := hO
  subst ho
  refine ⟨st', ρ', hx, ?_⟩
  have := (hc.1 () rfl).2 0 () (by decide) (by decide)
  refine (this : st'.mem (.tab 0) 0 = _).trans ?_
  rfl

#print axioms narrow74_corr
#print axioms narrow_zeuge
#print axioms pruef74_corr
#print axioms pruef_zeuge
#print axioms fwd74_corr
#print axioms fwd_zeuge
#print axioms locks_corr
#print axioms extPre_corr
#print axioms locks_zeuge

end Gabbro.Grammatik
