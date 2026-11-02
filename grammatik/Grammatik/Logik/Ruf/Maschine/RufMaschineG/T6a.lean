module

public import Grammatik.Logik.Ruf.Maschine.RufMaschineG.T6

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}
/-- After `dannRetry`: one try with the overflow arm behind. -/
def H2H : RufMaschineG rufDF :=
  ⟨H1H.speicher,
   rufUpdateG H1H.faeden 0
     ⟨(H1H.faeden 0).stapel,
      ⟨(H1H.faeden 0).kopf.f, (H1H.faeden 0).kopf.rho, (H1H.faeden 0).kopf.s0,
       ⟨false, rufDF.params rufCallerF,
        Signatur.anfang rufDF (rufDF.signatur rufCallerF), rhoCallerF,
        .wieder 1 bisH bodyH .nil (.dann .nil (.ende driverRet))⟩⟩,
      (H1H.faeden 0).spur, (H1H.faeden 0).log⟩,
   H1H.lauf, H1H.start⟩

/-- Step 2 fires `dannRetry`. -/
theorem schritt2H : RufSchrittG hP rufOF 0 H1H 0 H2H :=
  RufSchrittG.dannRetry H1H 0 false (rufDF.params rufCallerF)
    (Signatur.anfang rufDF (rufDF.signatur rufCallerF))
    (nach rufDF rufIncF (Signatur.anfang rufDF (rufDF.signatur rufCallerF)))
    (Signatur.anfang rufDF (rufDF.signatur rufCallerF))
    1 bisH bodyH .nil .nil (.ende driverRet) rhoCallerF H1H_kopf

/-- Step 2 as reachability. -/
theorem reach2H : RufErreichbarG hP rufOF 0 M0H H2H := by
  exact RufErreichbarG.schritt _ _ 0 reach1H schritt2H

/-- The loop node, installed. -/
theorem H2H_kopf :
    (H2H.faeden 0).kopf.rest =
    ⟨false, rufDF.params rufCallerF,
     Signatur.anfang rufDF (rufDF.signatur rufCallerF), rhoCallerF,
     .wieder 1 bisH bodyH .nil (.dann .nil (.ende driverRet))⟩ := by rfl

/-- The thread world is unchanged by installing the loop. -/
theorem H2H_welt : H2H.weltVon 0 = spF.welt [] := by rfl

/-- After the condition check: the body runs under the loop shim. -/
def H3H : RufMaschineG rufDF :=
  ⟨H2H.speicher,
   rufUpdateG H2H.faeden 0
     ⟨(H2H.faeden 0).stapel,
      ⟨(H2H.faeden 0).kopf.f, (H2H.faeden 0).kopf.rho, (H2H.faeden 0).kopf.s0,
       ⟨true, rufDF.params rufCallerF,
        Signatur.anfang rufDF (rufDF.signatur rufCallerF), rhoCallerF,
        .dann bodyH
          (.wiederRest 0 bisH bodyH .nil
            (.dann .nil (.ende driverRet)))⟩⟩,
      (H2H.weltVon 0).spur, (H2H.faeden 0).log⟩,
   H2H.lauf ++ rufEigenG 0 [],
   H2H.start⟩

/-- Step 3 fires `wiederSchritt`: the condition is literal `false`. -/
theorem schritt3H : RufSchrittG hP rufOF 0 H2H 0 H3H := by
  have hs₁ : H2H.weltVon 0 =
      (H2H.weltVon 0).lese
        (Signatur.anfang rufDF (rufDF.signatur rufCallerF)) bisH.orte := by
    rw [bisH_orte]
    rfl
  have hw : wahr? (eval (H2H.weltVon 0) bisH (H2H.weltVon 0) rhoCallerF) =
      false :=
    rfl
  have hneu : (H2H.weltVon 0).spur = [] ++ (H2H.faeden 0).spur := rfl
  exact RufSchrittG.wiederSchritt H2H 0 false (rufDF.params rufCallerF)
    (Signatur.anfang rufDF (rufDF.signatur rufCallerF))
    0 bisH bodyH .nil (.dann .nil (.ende driverRet)) rhoCallerF H2H_kopf _
    hs₁ hw _ hneu (heldGenau_rufDF _ _)

/-- Step 3 as reachability. -/
theorem reach3H : RufErreichbarG hP rufOF 0 M0H H3H := by
  exact RufErreichbarG.schritt _ _ 0 reach2H schritt3H

/-- The body under the shim. -/
theorem H3H_kopf :
    (H3H.faeden 0).kopf.rest =
    ⟨true, rufDF.params rufCallerF,
     Signatur.anfang rufDF (rufDF.signatur rufCallerF), rhoCallerF,
     .dann bodyH
       (.wiederRest 0 bisH bodyH .nil
         (.dann .nil (.ende driverRet)))⟩ := by rfl

/-- The thread world is unchanged by the check (nothing read). -/
theorem H3H_welt : H3H.weltVon 0 = spF.welt [] := by rfl

/-- After the bind-call: caller suspended with `wartet`, writer installed. -/
def H4H : RufMaschineG rufDF :=
  ⟨H3H.speicher,
   rufUpdateG H3H.faeden 0
     ⟨⟨(H3H.faeden 0).kopf.f, (H3H.faeden 0).kopf.rho, (H3H.faeden 0).kopf.s0,
        ⟨true, rufDF.params rufCallerF,
         nach rufDF rufIncF
           (Signatur.anfang rufDF (rufDF.signatur rufCallerF)),
         rhoCallerF,
         .wartet restLeaveH
           (.wiederRest 0 bisH bodyH .nil
             (.dann .nil (.ende driverRet)))⟩⟩ ::
       (H3H.faeden 0).stapel,
      ⟨rufIncF, rufRhoF, H3H.weltVon 0,
       ⟨false, rufDF.params rufIncF,
        Signatur.anfang rufDF (rufDF.signatur rufIncF),
        rufRhoF, .ende (hP.rumpf rufIncF)⟩⟩,
      (H3H.weltVon 0).spur,
      (RufEreignisF.eintritt rufIncF rufRhoF (H3H.weltVon 0)) ::
        (H3H.faeden 0).log⟩,
   H3H.lauf ++ rufEigenG 0 [],
   H3H.start⟩

/-- Step 4 fires `dannBindCall`: the writer frame is pushed, the caller
    waits with `wartet`. Every premise feeds the constructor. -/
theorem schritt4H : RufSchrittG hP rufOF 0 H3H 0 H4H := by
  have hhead : (H3H.faeden 0).kopf.rest =
      ⟨true, rufDF.params rufCallerF,
       Signatur.anfang rufDF (rufDF.signatur rufCallerF), rhoCallerF,
       .dann (.bindCall rufIncF rufArgsF (rufDF_erg rufIncF) rufHpF rfl
         restLeaveH)
         (.wiederRest 0 bisH bodyH .nil
           (.dann .nil (.ende driverRet)))⟩ := H3H_kopf
  have hΛ : HeldIn ([] : List (Res rufDF)) (offen (H3H.faeden 0).spur) :=
    (heldLeerF _).heldIn
  have hs0 : H3H.weltVon 0 =
      (H3H.weltVon 0).lese
        (Signatur.anfang rufDF (rufDF.signatur rufCallerF))
        (Args.orte rufArgsF) := by
    rw [argsOrteF]
    rfl
  have hrho : rufRhoF = evalArgs (H3H.weltVon 0) rufArgsF
      (H3H.weltVon 0) rhoCallerF := by
    rw [H3H_welt]
    rfl
  have hneu : (H3H.weltVon 0).spur = [] ++ (H3H.faeden 0).spur := rfl
  exact RufSchrittG.dannBindCall H3H 0 true (rufDF.params rufCallerF)
    (Signatur.anfang rufDF (rufDF.signatur rufCallerF))
    (nach rufDF rufIncF (Signatur.anfang rufDF (rufDF.signatur rufCallerF)))
    (nach rufDF rufIncF (Signatur.anfang rufDF (rufDF.signatur rufCallerF)))
    (.int 0 6) rufIncF rufArgsF (rufDF_erg rufIncF) rufHpF rfl restLeaveH
    (.wiederRest 0 bisH bodyH .nil (.dann .nil (.ende driverRet)))
    rhoCallerF hhead hΛ _ hs0 _ hrho _ hneu

/-- Step 4 as reachability. -/
theorem reach4H : RufErreichbarG hP rufOF 0 M0H H4H := by
  exact RufErreichbarG.schritt _ _ 0 reach3H schritt4H

/-- The writer head after the push: leaf plus return. -/
theorem H4H_kopf :
    (H4H.faeden 0).kopf.rest =
    ⟨false, rufDF.params rufIncF,
     Signatur.anfang rufDF (rufDF.signatur rufIncF), rufRhoF,
     .ende (.cons leafSF restF)⟩ := by rfl

/-- The writer runs in the entry world (arguments read nothing). -/
theorem H4H_welt : H4H.weltVon 0 = spF.welt [] := by rfl

/-- After the writing leaf: memory moved to `outWF`. -/
def H5H : RufMaschineG rufDF :=
  ⟨outWF.speicher,
   rufUpdateG H4H.faeden 0
     ⟨(H4H.faeden 0).stapel,
      ⟨(H4H.faeden 0).kopf.f, (H4H.faeden 0).kopf.rho, (H4H.faeden 0).kopf.s0,
       ⟨false, rufDF.params rufIncF,
        Signatur.anfang rufDF (rufDF.signatur rufIncF), rufRhoF,
        .ende restF⟩⟩,
      outWF.spur, (H4H.faeden 0).log⟩,
   H4H.lauf ++ rufEigenG 0 outWF.spur,
   H4H.start⟩

/-- Step 5 fires `blatt` on the writing leaf -- the memory move. -/
theorem schritt5H : RufSchrittG hP rufOF 0 H4H 0 H5H := by
  have hhead : (H4H.faeden 0).kopf.rest =
      ⟨false, rufDF.params rufIncF,
       Signatur.anfang rufDF (rufDF.signatur rufIncF), rufRhoF,
       .ende (.cons leafSF restF)⟩ := H4H_kopf
  have hΛ : HeldIn (Signatur.anfang rufDF (rufDF.signatur rufIncF))
      (offen (H4H.faeden 0).spur) :=
    (heldLeerF _).heldIn
  have hstep : (execStmt rufOF 0 (R := keinRuf)
      (V := vertragVon rufDF (H4H.faeden 0).kopf.f)
      leafSF (H4H.weltVon 0) rufRhoF) =
      Ausgang.ok (D := rufDF) (V := vertragVon rufDF (H4H.faeden 0).kopf.f)
        outWF rufRhoF := by
    rw [H4H_welt]
    exact leafSF_ok
  have hneu : outWF.spur = outWF.spur ++ (H4H.faeden 0).spur := by
    have hspur : (H4H.faeden 0).spur = [] := rfl
    rw [hspur, List.append_nil]
  have hkein : ∀ (L : rufDF.Lock) (h : List rufDF.Lock),
      Ereignis.nimmt L h ∉ (outWF.spur : List (Ereignis rufDF)) := by
    intro L h hm
    exact nomatch L
  exact RufSchrittG.blatt H4H 0 false (rufDF.params rufIncF)
    (Signatur.anfang rufDF (rufDF.signatur rufIncF))
    (Signatur.anfang rufDF (rufDF.signatur rufIncF))
    leafSF restF rufRhoF leafSF_blatt hhead hΛ
    outWF rufRhoF outWF.spur hstep hneu hkein

/-- Step 5 as reachability. -/
theorem reach5H : RufErreichbarG hP rufOF 0 M0H H5H := by
  exact RufErreichbarG.schritt _ _ 0 reach4H schritt5H

/-- The writer residue after the leaf: the parameter return. -/
theorem H5H_kopf :
    (H5H.faeden 0).kopf.rest =
    ⟨false, rufDF.params rufIncF,
     Signatur.anfang rufDF (rufDF.signatur rufIncF), rufRhoF,
     .ende (.ret eF (by decide))⟩ := by rfl

/-- The suspended caller frame, named for the pop. -/
def callerH : RufRahmenG rufDF :=
  ⟨rufCallerF, rhoCallerF, H3H.weltVon 0,
   ⟨true, rufDF.params rufCallerF,
    nach rufDF rufIncF (Signatur.anfang rufDF (rufDF.signatur rufCallerF)),
    rhoCallerF,
    .wartet restLeaveH
      (.wiederRest 0 bisH bodyH .nil
        (.dann .nil (.ende driverRet)))⟩⟩

/-- The return world: the writer thread world read at the result places. -/
def s1H : World rufDF :=
  (H5H.weltVon 0).lese
    (Signatur.anfang rufDF (rufDF.signatur rufIncF)) (ErgExpr.orte eF)

/-- After `rueckBind`: caller restored, value bound, return logged. The
    head frame is written with projections, exactly as the rule builds it. -/
def H6H : RufMaschineG rufDF :=
  ⟨s1H.speicher,
   rufUpdateG H5H.faeden 0
     ⟨[], ⟨callerH.f, callerH.rho, callerH.s0,
        ⟨true, .int 0 6 :: rufDF.params rufCallerF,
         nach rufDF rufIncF (Signatur.anfang rufDF (rufDF.signatur rufCallerF)),
         .cons (ergWert (rufDF_erg rufIncF) vF) rhoCallerF,
         .dann restLeaveH
           (.schrumpf (.wiederRest 0 bisH bodyH .nil
             (.dann .nil (.ende driverRet))))⟩⟩,
      s1H.spur,
      (RufEreignisF.rueck rufIncF rufRhoF vF (H3H.weltVon 0) s1H) ::
        (H5H.faeden 0).log⟩,
   H5H.lauf ++ rufEigenG 0 [],
   H5H.start⟩


end Gabbro.Grammatik
