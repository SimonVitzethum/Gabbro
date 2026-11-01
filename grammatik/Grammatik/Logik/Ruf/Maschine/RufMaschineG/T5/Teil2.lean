module

public import Grammatik.Logik.Ruf.Maschine.RufMaschineG.T4
public import Grammatik.Logik.Ruf.Maschine.RufMaschineG.T5.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}

theorem schritt5G : RufSchrittG gP rufOF 0 M4G 0 M5G :=
  RufSchrittG.dannLeer M4G 0 false (rufDF.params rufIncF)
    (Signatur.anfang rufDF (rufDF.signatur rufIncF))
    (.dann .nil (.ende restF)) rufRhoF M4G_kopf

/-- Step 5 as reachability. -/
theorem reach5G : RufErreichbarG gP rufOF 0 M0G M5G := by
  exact RufErreichbarG.schritt _ _ 0 reach4G schritt5G

/-- The second empty block, done. -/
theorem M5G_kopf :
    (M5G.faeden 0).kopf.rest =
    ⟨false, rufDF.params rufIncF,
     Signatur.anfang rufDF (rufDF.signatur rufIncF), rufRhoF,
     .dann .nil (.ende restF)⟩ := by rfl

/-- The machine after the second empty block completes: the return. -/
def M6G : RufMaschineG rufDF :=
  ⟨M5G.speicher,
   rufUpdateG M5G.faeden 0
     ⟨(M5G.faeden 0).stapel,
      ⟨(M5G.faeden 0).kopf.f, (M5G.faeden 0).kopf.rho, (M5G.faeden 0).kopf.s0,
       ⟨false, rufDF.params rufIncF,
        Signatur.anfang rufDF (rufDF.signatur rufIncF), rufRhoF,
        .ende restF⟩⟩,
      (M5G.faeden 0).spur, (M5G.faeden 0).log⟩,
   M5G.lauf, M5G.start⟩

/-- Step 6 fires `dannLeer` again: the `if` scaffolding is gone. -/
theorem schritt6G : RufSchrittG gP rufOF 0 M5G 0 M6G :=
  RufSchrittG.dannLeer M5G 0 false (rufDF.params rufIncF)
    (Signatur.anfang rufDF (rufDF.signatur rufIncF))
    (.ende restF) rufRhoF M5G_kopf

/-- Step 6 as reachability. -/
theorem reach6G : RufErreichbarG gP rufOF 0 M0G M6G := by
  exact RufErreichbarG.schritt _ _ 0 reach5G schritt6G

/-- The return residue: the parameter return. -/
theorem M6G_kopf :
    (M6G.faeden 0).kopf.rest =
    ⟨false, rufDF.params rufIncF,
     Signatur.anfang rufDF (rufDF.signatur rufIncF), rufRhoF,
     .ende (.ret eF (by decide))⟩ := by rfl

/-- The return world: the callee thread world read at the (empty) result
    places. -/
def s1G : World rufDF :=
  (M6G.weltVon 0).lese
    (Signatur.anfang rufDF (rufDF.signatur rufIncF)) (ErgExpr.orte eF)

/-- The machine after the `rueck` step: caller restored, return logged. -/
def M7G : RufMaschineG rufDF :=
  ⟨(M6G.weltVon 0).speicher,
   rufUpdateG M6G.faeden 0
     ⟨[], callerFrameG, s1G.spur,
      [RufEreignisF.rueck rufIncF rufRhoF vF (M0G.weltVon 0) s1G] ++
        (M6G.faeden 0).log⟩,
   M6G.lauf ++ rufEigenG 0 [],
   M6G.start⟩


end Gabbro.Grammatik
