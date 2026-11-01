/-
  File:      Grammatik/ArenaDyn.lean
  Subject:   Dynamic arenas: virtual reservation, committed prefix, and the
             past-ceiling stop over a run's commit sequence
             (PLAN-DYNAMIC.md section 9, lane 241; reworked by fix lane F2
             after review G08 F4, 2026-09-21; the section-9 FORM -- `DynForm`,
             the four Block-form theorems and the simulation -- added by the
             server lane 2026-09-28, section `Form` at the end).

  A dynamic arena declares a static ceiling `M` (address reserved, never
  touched implicitly) and a committed prefix `c` (`hi <= c <= M`) grown
  explicitly by `grow`. Commit is monotone within a run; growth beyond `M`
  is a refusal, never a runtime surprise. Fault latency/cost arrives as a
  NAMED hardware assumption read as data (`faultKosten`), never justified
  here. The virtual region is the arena block's `Fin M` index set, the
  committed prefix the `Fin c` usable part.
-/
module

public import Grammatik.Bausteine.Arena.ArenaDyn.Teil1
public import Grammatik.Bausteine.Arena.ArenaDyn.Teil2
public import Grammatik.Bausteine.Arena.ArenaDyn.Teil3
