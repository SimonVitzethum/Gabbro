module

public import Grammatik.Logik.Ruf.Maschine.RufMaschineG.T4
public import Grammatik.Logik.Ruf.Maschine.RufMaschineG.T5.Teil1.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}

/-- Step 3 fires `dannIteWahr`: the condition is the literal `true`. -/
theorem schritt3G : RufSchrittG gP rufOF 0 M2G 0 M3G := by
  have hhead : (M2G.faeden 0).kopf.rest =
      ⟨false, rufDF.params rufIncF,
       Signatur.anfang rufDF (rufDF.signatur rufIncF), rufRhoF,
       .dann (.cons (.ite cG thenG elseG) .nil) (.ende restF)⟩ := M2G_kopf
  have hs₁ : M2G.weltVon 0 =
      (M2G.weltVon 0).lese
        (Signatur.anfang rufDF (rufDF.signatur rufIncF)) cG.orte := by
    rw [cG_orte]
    rfl
  have hw : wahr? (eval (M2G.weltVon 0) cG (M2G.weltVon 0) rufRhoF) = true :=
    rfl
  have hneu : (M2G.weltVon 0).spur = [] ++ (M2G.faeden 0).spur := rfl
  exact RufSchrittG.dannIteWahr M2G 0 false (rufDF.params rufIncF)
    (Signatur.anfang rufDF (rufDF.signatur rufIncF))
    (Signatur.anfang rufDF (rufDF.signatur rufIncF))
    (Signatur.anfang rufDF (rufDF.signatur rufIncF))
    cG thenG elseG .nil (.ende restF) rufRhoF hhead _ hs₁ hw _ hneu (heldGenau_rufDF _ _)

/-- Step 3 as reachability. -/
theorem reach3G : RufErreichbarG gP rufOF 0 M0G M3G := by
  exact RufErreichbarG.schritt _ _ 0 reach2G schritt3G

/-- The taken branch, unfolded. -/
theorem M3G_kopf :
    (M3G.faeden 0).kopf.rest =
    ⟨false, rufDF.params rufIncF,
     Signatur.anfang rufDF (rufDF.signatur rufIncF), rufRhoF,
     .dann (.cons leafSF .nil) (.dann .nil (.ende restF))⟩ := by rfl

/-- The thread world is unchanged by the branch choice. -/
theorem M3G_welt : M3G.weltVon 0 = spF.welt [] := by rfl

/-- The machine after the writing leaf: memory moved to `outWF`, the
    branch block is done. -/
def M4G : RufMaschineG rufDF :=
  ⟨outWF.speicher,
   rufUpdateG M3G.faeden 0
     ⟨(M3G.faeden 0).stapel,
      ⟨(M3G.faeden 0).kopf.f, (M3G.faeden 0).kopf.rho, (M3G.faeden 0).kopf.s0,
       ⟨false, rufDF.params rufIncF,
        Signatur.anfang rufDF (rufDF.signatur rufIncF), rufRhoF,
        .dann .nil (.dann .nil (.ende restF))⟩⟩,
      outWF.spur, (M3G.faeden 0).log⟩,
   M3G.lauf ++ rufEigenG 0 outWF.spur,
   M3G.start⟩

/-- Step 4 fires `dannBlatt` on the writing leaf -- the memory move. -/
theorem schritt4G : RufSchrittG gP rufOF 0 M3G 0 M4G := by
  have hhead : (M3G.faeden 0).kopf.rest =
      ⟨false, rufDF.params rufIncF,
       Signatur.anfang rufDF (rufDF.signatur rufIncF), rufRhoF,
       .dann (.cons leafSF .nil) (.dann .nil (.ende restF))⟩ := M3G_kopf
  have hΛ : HeldIn (Signatur.anfang rufDF (rufDF.signatur rufIncF))
      (offen (M3G.faeden 0).spur) :=
    (heldLeerF _).heldIn
  have hstep : (execStmt rufOF 0 (R := keinRuf)
      (V := vertragVon rufDF (M3G.faeden 0).kopf.f)
      leafSF (M3G.weltVon 0) rufRhoF) =
      Ausgang.ok (D := rufDF) (V := vertragVon rufDF (M3G.faeden 0).kopf.f)
        outWF rufRhoF := by
    rw [M3G_welt]
    exact leafSF_ok
  have hneu : outWF.spur = outWF.spur ++ (M3G.faeden 0).spur := by
    have hspur : (M3G.faeden 0).spur = [] := rfl
    rw [hspur, List.append_nil]
  have hkein : ∀ (L : rufDF.Lock) (h : List rufDF.Lock),
      Ereignis.nimmt L h ∉ (outWF.spur : List (Ereignis rufDF)) := by
    intro L h hm
    exact nomatch L
  exact RufSchrittG.dannBlatt M3G 0 false (rufDF.params rufIncF)
    (Signatur.anfang rufDF (rufDF.signatur rufIncF))
    (Signatur.anfang rufDF (rufDF.signatur rufIncF))
    (Signatur.anfang rufDF (rufDF.signatur rufIncF))
    leafSF .nil (.dann .nil (.ende restF)) rufRhoF leafSF_blatt hhead hΛ
    outWF rufRhoF outWF.spur hstep hneu hkein

/-- Step 4 as reachability. -/
theorem reach4G : RufErreichbarG gP rufOF 0 M0G M4G := by
  exact RufErreichbarG.schritt _ _ 0 reach3G schritt4G

/-- The finished branch, behind two empty blocks. -/
theorem M4G_kopf :
    (M4G.faeden 0).kopf.rest =
    ⟨false, rufDF.params rufIncF,
     Signatur.anfang rufDF (rufDF.signatur rufIncF), rufRhoF,
     .dann .nil (.dann .nil (.ende restF))⟩ := by rfl

/-- The machine after the first empty block completes. -/
def M5G : RufMaschineG rufDF :=
  ⟨M4G.speicher,
   rufUpdateG M4G.faeden 0
     ⟨(M4G.faeden 0).stapel,
      ⟨(M4G.faeden 0).kopf.f, (M4G.faeden 0).kopf.rho, (M4G.faeden 0).kopf.s0,
       ⟨false, rufDF.params rufIncF,
        Signatur.anfang rufDF (rufDF.signatur rufIncF), rufRhoF,
        .dann .nil (.ende restF)⟩⟩,
      (M4G.faeden 0).spur, (M4G.faeden 0).log⟩,
   M4G.lauf, M4G.start⟩

end Gabbro.Grammatik
