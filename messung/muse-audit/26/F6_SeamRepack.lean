/-
  Audit 26, finding F6 -- Geraet.lean: `SeamPublish` (line 768) carries a
  `sichtbar : DmaSichtbar t` field and `SeamAwait` (line 776) carries
  NOTHING but the take-back; `SeamPair.wache` (line 793) just repacks the
  three pieces into `GeraetWache`. Pattern (a): the "seam" layer is the
  window struct under another name -- `seam_pair_ordered` is `fenster_ende`
  and `seam_pair_race_free` is `geraet_ohne_wettlauf`, both via `.wache`.
  This demo shows the isomorphism is definitional in both directions on
  the field level.
-/
import Grammatik.Geraet

open Gabbro.Grammatik

/-- F6: every pair is a window (the filed bridge). -/
theorem audit26_seam_is_window {D : Deklaration} {gl : GLauf D}
    {W : D.Lock} {t : D.Tab} (p : SeamPair gl W t) :
    GeraetWache gl W t p.pub.k p.aw.m p.j :=
  p.wache

/-- F6: `seam_pair_ordered` is `fenster_ende` through the repacking. -/
theorem audit26_seam_ordered_is_fenster {D : Deklaration} {gl : GLauf D}
    {W : D.Lock} {t : D.Tab} (p : SeamPair gl W t) :
    GHB gl p.pub.k p.aw.m :=
  seam_pair_ordered p

/-- F6: every window splits back into publish/await/write triple. -/
def audit26_window_is_seam {D : Deklaration} {gl : GLauf D}
    {W : D.Lock} {t : D.Tab} {k m j : Nat}
    (hw : GeraetWache gl W t k m j) :
    SeamPair gl W t :=
  { pub := { k := k, gibt := hw.gibt, sichtbar := hw.sichtbar },
    aw := { m := m, nimmt := hw.nimmt },
    j := j, schreibt := hw.schreibt, vor := hw.vor, nach := hw.nach }

#print axioms audit26_seam_is_window
#print axioms audit26_seam_ordered_is_fenster
#print axioms audit26_window_is_seam

/-
CUTS:
  (C1) Whether the renaming buys readability is out of scope; the finding
       is only that no new proof burden is carried.
-/
