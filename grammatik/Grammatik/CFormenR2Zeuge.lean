/-
  File:      Grammatik/CFormenR2Zeuge.lean
  Subject:   The witnesses of `CFormenR2.lean` (rule 13): a `forever`
             that leaves in its first round on `refD`, the signed
             saturation helper on three concrete calls (inside, clamped
             high, clamped low), and `<<%` on a concrete byte.
-/
import Grammatik.CFormenR2
import Grammatik.CFormenRZeuge2

namespace Gabbro.Grammatik

/-! ## 1. `forever` on `refD`: `forever { konto[0] = 100; leave; }` -/

/-- `einzahlen`'s frame, with two rounds of `forever` before the progress
    assumption. -/
def xF : TVCtx refD := { xEin with passes := 2 }

def foreverBody : Block refD (vertragVon refD refEin) true [.int 0 10] [Res.held (D := refD) ()]
    [Res.held (D := refD) ()] :=
  .cons (.assignSlot () () refIdxEin refHundert (refEin_schreibt ()) refDarf)
    (.cons (Stmt.leave rfl) .nil)

def cForeverBody : CS := .seq (.store cStand cU32 (.lit 100)) (.seq (.goto (.ende 7)) .skip)

theorem foreverBody_corr : BlockSem xF 7 kEin foreverBody cForeverBody := by
  have hi : ExprCorr xF kEin (.var 1) refIdxEin :=
    ecorr_fest xF kEin kEin_ks refIdxEin (fun _ _ => rfl)
  have he : ExprCorr xF kEin (.lit 100) refHundert := ecorr_weiter xF kEin _ _ (ecorr_lit xF kEin 100)
  exact cCorr_block xF 7 (BlockCorr.cons (scorr_assignSlotParam xF kEin 7 kEin_pp () rfl _ _ hi he)
    (BlockCorr.cons (scorr_leave xF kEin 7 rfl) BlockCorr.nil))

/-- F1 INSTANTIATED: `for (;;) { k->slots[i].stand = 100; goto m_ende; }`. -/
theorem forever_corr : StmtCorr xF 0 kEin
    (Stmt.forever (V := vertragVon refD refEin) (l := false) () Expr.wahr foreverBody)
    (CS.loop cForeverBody 7) :=
  scorr_forever xF 0 7 kEin () Expr.wahr foreverBody cForeverBody foreverBody_corr

/-- WITNESS, `forever`: from the zero state the loop runs one round and
    leaves it, the slot at `100` on both sides. -/
theorem forever_zeuge :
    ∃ st' ρ', Exec refEL.lay tvOrc 2 xF.CR xF.XR (CS.loop cForeverBody 7) refSt0
        (lokUpd (lokUpd (lokUpd (fun _ => .undef) 2 (.int 7)) 1 (.int 0)) 0 (.ptr ⟨.tab 0, 0⟩))
        (.norm st' ρ') ∧ st'.mem (.tab 0) 0 = .int 100 := by
  obtain ⟨o, hx, hO⟩ := forever_corr refW0 refSt0 refRho7 _ refW0_corr ein_envRel rfl
  obtain ⟨st', ρ', ho, hc, -⟩ := hO
  subst ho
  refine ⟨st', ρ', hx, ?_⟩
  have := (hc.1 () rfl).2 0 () (by decide) (by decide)
  refine (this : st'.mem (.tab 0) 0 = _).trans ?_
  rfl

/-! ## 2. `_gabbro_sat_i` on three calls -/

def rhoSat (a b lo hi : Int) : CLok :=
  lokUpd (lokUpd (lokUpd (lokUpd (fun _ => .undef) 3 (.int hi)) 2 (.int lo)) 1 (.int b)) 0 (.int a)

/-- WITNESS, the signed helper: `sat_i(5, -2, -3, 10) = 3` (inside),
    `sat_i(9, 8, -3, 10) = 10` (clamped high), `sat_i(-3, -2, -3, 10) = -3`
    (clamped low). -/
theorem satI_zeuge (L : CLayout) (orc : DevOrc) (st : CSt) :
    Exec L orc 1 tvXR tvXR satIBody st (rhoSat 5 (-2) (-3) 10) (.ret st (some (.int 3))) ∧
    Exec L orc 1 tvXR tvXR satIBody st (rhoSat 9 8 (-3) 10) (.ret st (some (.int 10))) ∧
    Exec L orc 1 tvXR tvXR satIBody st (rhoSat (-3) (-2) (-3) 10) (.ret st (some (.int (-3)))) := by
  refine ⟨?_, ?_, ?_⟩
  · have h := satI_run L orc 1 tvXR tvXR st (rhoSat 5 (-2) (-3) 10) 5 (-2) (-3) 10 (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl rfl rfl
    rwa [show max (-3 : Int) (min (5 + -2) 10) = 3 by decide] at h
  · have h := satI_run L orc 1 tvXR tvXR st (rhoSat 9 8 (-3) 10) 9 8 (-3) 10 (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl rfl rfl
    rwa [show max (-3 : Int) (min (9 + 8) 10) = 10 by decide] at h
  · have h := satI_run L orc 1 tvXR tvXR st (rhoSat (-3) (-2) (-3) 10) (-3) (-2) (-3) 10 (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl rfl rfl
    rwa [show max (-3 : Int) (min (-3 + -2) 10) = -3 by decide] at h

/-! ## 3. `<<%` on a byte: `200 <<% 3` in `u8` -/

def byte200 : Expr d74 Γ74 [] (.int 0 (2 ^ (7 + 1) - 1)) :=
  Expr.weiter (by decide) (by decide) (Expr.lit 200)

def drei : Expr d74 Γ74 [] (.int 0 ((7 : Nat) : Int)) :=
  Expr.weiter (by decide) (by decide) (Expr.lit 3)

/-- WITNESS, `<<%`: `(uint8_t)((uint32_t)(200) << (uint32_t)(3))` is `64`
    (`1600 mod 256`), `Zahl.shlW`'s value. -/
theorem shl_zeuge :
    ∃ st', ev el74.lay orc74 2 (wrapC .shl CIT.u32 CIT.u8 false (7 + 1) (.lit 200) (.lit 3)) st74
        (rhoC74 3 7 5) = some (.int 64, st') := by
  obtain ⟨st', h⟩ := wrapC_shl xS74 k74 7 CIT.u32 CIT.u8 rfl rfl (by decide) (by decide) false
    (fun _ => rfl) (a := byte200) (s := drei)
    (ecorr_weiter xS74 k74 _ _ (ecorr_lit xS74 k74 200)) (ecorr_weiter xS74 k74 _ _ (ecorr_lit xS74 k74 3))
    w74 st74 (rho74 3 7 5) (rhoC74 3 7 5) (corr74 _ _) (envRel74 3 7 5 (by decide) (by decide) (by decide))
  exact ⟨st', h⟩

#print axioms forever_corr
#print axioms forever_zeuge
#print axioms satI_zeuge
#print axioms shl_zeuge

end Gabbro.Grammatik
