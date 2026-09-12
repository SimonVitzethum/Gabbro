/-
  Audit 26, finding F5 -- Geraet.lean: `tuerklingel_ohne_wettlauf`
  (line 690) takes premise `_hr : TuerklingelRueckgabe gl r' W d'` whose
  CONTENT is never used: the proof destructures only the index equation
  `hdm : d' = m` (rewriting `haussen`) and the window `h`. Any bell --
  readable register or not, any thread -- would do. Pattern (b): an unused
  premise (underscore-named by the author). Contrast with
  `tuerklingel_fenster_geordnet`, which DOES read `hr` (extracts `hm`).
  This demo shows the bell content is irrelevant: the same conclusion
  follows with the bell replaced by a bare index equation.
-/
import Grammatik.Geraet

open Gabbro.Grammatik

/-- F5: the return bell premise is unused -- only `d' = m` travels. -/
theorem audit26_tuerklingel_bell_unused {D : Deklaration} {gl : GLauf D}
    {r : D.Reg} {r' : D.Reg} {W : D.Lock} {t : D.Tab} {k m j d d' : Nat}
    (h : TuerklingelZuFenster gl r W t k m j d)
    (_hr : TuerklingelRueckgabe gl r' W d') (hdm : d' = m)
    (hz : CpuZugriff gl t)
    (haussen : GHB gl hz.idx d ∨ GHB gl d' hz.idx) :
    GHB gl hz.idx j ∨ GHB gl j hz.idx :=
  tuerklingel_ohne_wettlauf h _hr hdm hz haussen

/-- F5: without ANY bell, the same conclusion from the same index equation. -/
theorem audit26_tuerklingel_no_bell {D : Deklaration} {gl : GLauf D}
    {r : D.Reg} {W : D.Lock} {t : D.Tab} {k m j d d' : Nat}
    (h : TuerklingelZuFenster gl r W t k m j d) (hdm : d' = m)
    (hz : CpuZugriff gl t)
    (haussen : GHB gl hz.idx d ∨ GHB gl d' hz.idx) :
    GHB gl hz.idx j ∨ GHB gl j hz.idx := by
  obtain ⟨hw, _, hdk⟩ := h
  rw [hdk, hdm] at haussen
  exact geraet_ohne_wettlauf gl W t k m j hw hz haussen

#print axioms audit26_tuerklingel_bell_unused
#print axioms audit26_tuerklingel_no_bell

/-
CUTS:
  (C1) Whether the bell SHOULD constrain the proof (e.g. readability of
       `r'`) is a modelling question; this demo only shows it does not.
-/
