module

public import Grammatik.Korpus.Referenz.ReferenzB.T1
public import Grammatik.Korpus.Referenz.ReferenzB.T2.Teil1

@[expose] public section

namespace Gabbro.Grammatik

/-- Step D (F): thread 1 returns from `lies` with value `100`, read from
    the post-write slot through the read world. Every premise is used:
    `hpop`/`hfg`/`hrho`/`hs0` select the head frame, `hΛ` the lock state,
    `hs1`/`hv`/`hneu` feed the constructor. -/
theorem refSchrittDF : RufSchrittF refP refO 0 refM3F 1 MB := by
  have hpop : (refM3F.faeden 1).stapel = [refCallerFF] := rfl
  have hhead : (refM3F.faeden 1).kopf.rest =
      ⟨false, refD.params refLies,
        Signatur.anfang refD (refD.signatur refLies),
        Env.nil, .ret refRetLies (by rfl)⟩ := by
    rw [refM3Frest]
    rfl
  have hfg : (refM3F.faeden 1).kopf.f = refLies := rfl
  have hrho : (refM3F.faeden 1).kopf.rho =
      (refLies_params ▸ Env.nil : Env refD (refD.params refLies)) := refM3Frho
  have hs0 : (refM3F.faeden 1).kopf.s0 = refM2F.weltVon 1 := rfl
  have hΛ : HeldGenau (Signatur.anfang refD (refD.signatur refLies))
      (offen (refM3F.faeden 1).spur) := by
    have e : offen (refM3F.faeden 1).spur =
        offen (refM1F.faeden 1).spur := rfl
    rw [e, refLies_start]
    exact refM1Fhaelt
  have hs1 : ((refM3F.weltVon 1).lese [Res.held (D := refD) ()] [Sum.inl (())]) =
      (refM3F.weltVon 1).lese (Signatur.anfang refD (refD.signatur refLies))
        (ErgExpr.orte refRetLies) := rfl
  have hv : refV100back =
      hfg ▸ evalErg ((refM3F.weltVon 1).lese [Res.held (D := refD) ()] [Sum.inl (())])
        refRetLies
        ((refM3F.weltVon 1).lese [Res.held (D := refD) ()] [Sum.inl (())])
        Env.nil := rfl
  have hneu : (((refM3F.weltVon 1).lese [Res.held (D := refD) ()] [Sum.inl (())])).spur =
      [Ereignis.zugriff () false [Res.held (D := refD) ()]
        (refM3F.weltVon 1).haelt] ++ (refM3F.faeden 1).spur := rfl
  exact RufSchrittF.rueck (P := refP) (O := refO) (passes := 0) refM3F 1
    _ [] hpop _ _ _ _ _ hhead _ hfg _ hrho _ hs0 hΛ _
    hs1 _ hv _ hneu

theorem refReachDF : RufErreichbarF refP refO 0 refM0F MB :=
  RufErreichbarF.schritt _ _ 1 refReachCF refSchrittDF

/-- `refM0F` IS the start machine. -/
theorem refM0F_start : refM0F = RufStartF refP refSp0 initB := by rfl

/-- The F witness run: lock, writing leaf, call, return -- reached from
    the start state. -/
theorem refB_erreicht :
    RufErreichbarF refP refO 0 (RufStartF refP refSp0 initB) MB := by
  rw [← refM0F_start]
  exact refReachDF

/-- The final memory carries the written cap at `konto[0]`. -/
theorem refMB_slot : MB.speicher.slots () 0 () = refV100 := by
  have hhit := storeSlot_hit (D := refD)
    ((refM1F.weltVon 1).lese [Res.held (D := refD) ()]
      (refIdxEin.orte ++ refHundert.orte)) () refK0 () refV100
  have k0 : refK0 = (0 : Int) := rfl
  have hmem : MB.speicher.slots () 0 () =
      ((((refM1F.weltVon 1).lese [Res.held (D := refD) ()]
        (refIdxEin.orte ++ refHundert.orte)).storeSlot ()
        refK0 () refV100).slots () 0 ()) := rfl
  rw [k0] at hhit
  rw [hmem, k0]
  exact hhit


end Gabbro.Grammatik
