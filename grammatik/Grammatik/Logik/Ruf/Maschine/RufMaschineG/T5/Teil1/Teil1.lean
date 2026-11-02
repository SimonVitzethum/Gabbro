module
public import Grammatik.Logik.Ruf.Maschine.RufMaschineG.T5.Teil1.Teil1Basis
import all Grammatik.Logik.Ruf.Maschine.RufMaschineG.T5.Teil1.Teil1Basis

public import Grammatik.Logik.Ruf.Maschine.RufMaschineG.T4

@[expose] public section



namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 7. Witness: an `if` whose taken branch writes a table

    The witness reuses the F declaration `rufDF` (one table, `Bool`
    functions, no locks): the callee `true` runs an `if` whose taken
    branch is the writing leaf, the caller `false` reuses the F caller
    body (a call to `true`). -/

/-- The condition: the literal `true`, so the taken branch fires. -/
def cG : Expr rufDF (rufDF.params rufIncF)
    (Signatur.anfang rufDF (rufDF.signatur rufIncF)) .bool :=
  .tru

/-- The taken branch: the writing leaf, then nothing. -/
def thenG : Block rufDF (vertragVon rufDF rufIncF) false
    (rufDF.params rufIncF)
    (Signatur.anfang rufDF (rufDF.signatur rufIncF))
    (Signatur.anfang rufDF (rufDF.signatur rufIncF)) :=
  .cons leafSF .nil

/-- The else branch: nothing. -/
def elseG : Block rufDF (vertragVon rufDF rufIncF) false
    (rufDF.params rufIncF)
    (Signatur.anfang rufDF (rufDF.signatur rufIncF))
    (Signatur.anfang rufDF (rufDF.signatur rufIncF)) :=
  .nil

/-- The `if` statement. -/
def iteG : Stmt rufDF (vertragVon rufDF rufIncF) false
    (rufDF.params rufIncF)
    (Signatur.anfang rufDF (rufDF.signatur rufIncF))
    (Signatur.anfang rufDF (rufDF.signatur rufIncF)) :=
  .ite cG thenG elseG

/-- The `if` unfolds. -/
theorem iteG_entf : GEntfaltbar iteG = true := by rfl

/-- The callee body: the `if`, then the parameter return `restF`. -/
def calleeG : Endblock rufDF (vertragVon rufDF rufIncF) false
    (rufDF.params rufIncF)
    (Signatur.anfang rufDF (rufDF.signatur rufIncF)) :=
  .cons iteG restF

/-- The program: trivial contracts, callee with the `if`, caller reused. -/
def gP : Programm rufDF where
  invariante := fun i => nomatch i
  requires := fun _ => .tru
  ensures := fun _ => .tru
  rumpf
    | true => calleeG
    | false => rufCallerRumpfF

/-- The callee body is what `gP` runs at `true`. -/
theorem gP_rumpf_true : gP.rumpf rufIncF = calleeG := by rfl

def M0G : RufMaschineG rufDF := RufStartG gP spF initF

/-- The start head is the caller body with the entry environment. -/
theorem M0G_kopf :
    (M0G.faeden 0).kopf.rest =
    ⟨false, rufDF.params rufCallerF,
     Signatur.anfang rufDF (rufDF.signatur rufCallerF),
     rhoCallerF, .ende rufCallerRumpfF⟩ := by
  have hstart : (RufStartG (D := rufDF) gP spF initF).faeden 0 =
      (match initF 0 with
      | ⟨g', rho'⟩ =>
        (⟨[], (⟨g', rho', spF.welt [],
          ⟨false, rufDF.params g', Signatur.anfang rufDF (rufDF.signatur g'),
           rho', .ende (gP.rumpf g')⟩⟩ : RufRahmenG rufDF),
       [], [RufEreignisF.eintritt g' rho' (spF.welt [])]⟩ :
          RufFadenG rufDF)) := rfl
  have hif : initF 0 = (⟨rufCallerF, rhoCallerF⟩ :
      Σ f : rufDF.Fn, Env rufDF (rufDF.params f)) := by
    simp only [initF]
  have hM : M0G.faeden 0 =
      (⟨[], (⟨rufCallerF, rhoCallerF, spF.welt [],
        ⟨false, rufDF.params rufCallerF,
         Signatur.anfang rufDF (rufDF.signatur rufCallerF),
         rhoCallerF, .ende (gP.rumpf rufCallerF)⟩⟩ : RufRahmenG rufDF),
       [], [RufEreignisF.eintritt rufCallerF rhoCallerF (spF.welt [])]⟩ :
        RufFadenG rufDF) := by
    simp only [M0G]
    rw [hstart, hif]
  have hrumpf : gP.rumpf rufCallerF = rufCallerRumpfF := rfl
  rw [hM, hrumpf]

/-- Reachability from `RufStartG`: `M0G` IS the start machine. -/
theorem M0G_start : M0G = RufStartG gP spF initF := by rfl

/-! ## 8. The witness run: call, unfold, branch, write, return -/

/-- The caller's residue AFTER the call: the parameter return. -/
def callerRestG : Endblock rufDF (vertragVon rufDF rufCallerF) false
    (rufDF.params rufCallerF) (nach rufDF rufIncF []) :=
  (rufDF_params rufCallerF).symm ▸
    ((.ret (.val ((.widen (by decide) (by decide) (.var .here) :
      Expr rufDF (rufDF.params rufIncF) [] (.int 0 6)))) (by decide)) :
      Endblock rufDF (vertragVon rufDF rufCallerF) false
        (rufDF.params rufIncF) (nach rufDF rufIncF []))

/-- The suspended caller frame: residue ADVANCED past the call. -/
def callerFrameG : RufRahmenG rufDF :=
  ⟨rufCallerF, rhoCallerF, spF.welt [],
   ⟨false, rufDF.params rufCallerF, nach rufDF rufIncF [], rhoCallerF,
    .ende callerRestG⟩⟩

/-- The machine after the `ruf` step: caller suspended past the call,
    callee installed with the `if` body. -/
def M1G : RufMaschineG rufDF :=
  ⟨M0G.speicher,
   rufUpdateG M0G.faeden 0
     ⟨callerFrameG :: (M0G.faeden 0).stapel,
      ⟨rufIncF, rufRhoF, M0G.weltVon 0,
       ⟨false, rufDF.params rufIncF,
        Signatur.anfang rufDF (rufDF.signatur rufIncF),
        rufRhoF, .ende (gP.rumpf rufIncF)⟩⟩,
      (M0G.weltVon 0).spur,
      (RufEreignisF.eintritt rufIncF rufRhoF (M0G.weltVon 0)) ::
        (M0G.faeden 0).log⟩,
   M0G.lauf ++ rufEigenG 0 [],
   M0G.start⟩

/-- Step 1 fires the `ruf` rule on the caller frame. Every premise feeds
    the constructor: `hhead`/`hΛ` fix the frame, `hs0`/`hrho`/`hneu` the
    entry data. -/
theorem schritt1G : RufSchrittG gP rufOF 0 M0G 0 M1G := by
  have hhead : (M0G.faeden 0).kopf.rest =
      ⟨false, rufDF.params rufCallerF, [],
       rhoCallerF,
       .ende (.cons (.call rufIncF rufArgsF rufHpF rfl)
         ((rufDF_params rufCallerF).symm ▸
           (.ret (.val ((.widen (by decide) (by decide) (.var .here) :
             Expr rufDF (rufDF.params rufIncF) [] (.int 0 6)))) (by decide)) :
           Endblock rufDF (vertragVon rufDF rufCallerF) false
             (rufDF.params rufIncF) (nach rufDF rufIncF [])))⟩ := by
    rw [M0G_kopf]
    rfl
  have hΛ : HeldIn ([] : List (Res rufDF)) (offen (M0G.faeden 0).spur) :=
    (heldLeerF _).heldIn
  have hs0 : M0G.weltVon 0 =
      (M0G.weltVon 0).lese [] (Args.orte rufArgsF) := by
    rw [argsOrteF]
    rfl
  have hrho : rufRhoF = evalArgs (M0G.weltVon 0) rufArgsF
      (M0G.weltVon 0) rhoCallerF := by
    have hw : M0G.weltVon 0 = spF.welt [] := rfl
    rw [hw]
    rfl
  have hneu : (M0G.weltVon 0).spur = [] ++ (M0G.faeden 0).spur := rfl
  exact RufSchrittG.ruf M0G 0 false (rufDF.params rufCallerF) [] rufIncF
    rufArgsF rufHpF rfl _ rhoCallerF hhead hΛ _ hs0 _ hrho _ hneu

/-- Step 1 as reachability. -/
theorem reach1G : RufErreichbarG gP rufOF 0 M0G M1G := by
  exact RufErreichbarG.schritt _ _ 0 RufErreichbarG.start schritt1G

/-- The callee head after the call is the `if` body with `rufRhoF`. -/
theorem M1G_kopf :
    (M1G.faeden 0).kopf.rest =
    ⟨false, rufDF.params rufIncF,
     Signatur.anfang rufDF (rufDF.signatur rufIncF), rufRhoF,
     .ende (.cons iteG restF)⟩ := by rfl

/-- The thread world is unchanged by the call (no new events). -/
theorem M1G_welt : M1G.weltVon 0 = spF.welt [] := by rfl

/-- The machine after the unfold: the `if` moved into `dann` position. -/
def M2G : RufMaschineG rufDF :=
  ⟨M1G.speicher,
   rufUpdateG M1G.faeden 0
     ⟨(M1G.faeden 0).stapel,
      ⟨(M1G.faeden 0).kopf.f, (M1G.faeden 0).kopf.rho, (M1G.faeden 0).kopf.s0,
       ⟨false, rufDF.params rufIncF,
        Signatur.anfang rufDF (rufDF.signatur rufIncF), rufRhoF,
        .dann (.cons iteG .nil) (.ende restF)⟩⟩,
      (M1G.faeden 0).spur, (M1G.faeden 0).log⟩,
   M1G.lauf, M1G.start⟩

/-- Step 2 fires `endeEntf`: the compound head moves into `dann`. -/
theorem schritt2G : RufSchrittG gP rufOF 0 M1G 0 M2G :=
  RufSchrittG.endeEntf M1G 0 false (rufDF.params rufIncF)
    (Signatur.anfang rufDF (rufDF.signatur rufIncF))
    (Signatur.anfang rufDF (rufDF.signatur rufIncF))
    iteG restF rufRhoF iteG_entf M1G_kopf

/-- Step 2 as reachability. -/
theorem reach2G : RufErreichbarG gP rufOF 0 M0G M2G := by
  exact RufErreichbarG.schritt _ _ 0 reach1G schritt2G

/-- The unfolded head. -/
theorem M2G_kopf :
    (M2G.faeden 0).kopf.rest =
    ⟨false, rufDF.params rufIncF,
     Signatur.anfang rufDF (rufDF.signatur rufIncF), rufRhoF,
     .dann (.cons iteG .nil) (.ende restF)⟩ := by rfl

/-- The thread world is unchanged by the unfold. -/
theorem M2G_welt : M2G.weltVon 0 = spF.welt [] := by rfl

theorem cG_orte : cG.orte = [] := by rfl

/-- The machine after the branch: the taken writing branch runs first,
    then the empty rest, then the return. The condition reads nothing,
    so the world is unchanged. -/
def M3G : RufMaschineG rufDF :=
  ⟨M2G.speicher,
   rufUpdateG M2G.faeden 0
     ⟨(M2G.faeden 0).stapel,
      ⟨(M2G.faeden 0).kopf.f, (M2G.faeden 0).kopf.rho, (M2G.faeden 0).kopf.s0,
       ⟨false, rufDF.params rufIncF,
        Signatur.anfang rufDF (rufDF.signatur rufIncF), rufRhoF,
        .dann (.cons leafSF .nil) (.dann .nil (.ende restF))⟩⟩,
      (M2G.weltVon 0).spur, (M2G.faeden 0).log⟩,
   M2G.lauf ++ rufEigenG 0 [],
   M2G.start⟩

/-- Held-exactly for `rufDF`: the declaration has no lock. -/
theorem heldGenau_rufDF (Λ : List (Res rufDF)) (spur : List (Ereignis rufDF)) :
    HeldIn Λ (offen spur) := fun L => nomatch L

end Gabbro.Grammatik
