/-
  File:      Grammatik/Zielsatz/AtomarZertifikatZeuge.lean
  Subject:   THE FIRST CERTIFIED PROGRAM WITH A SHARED ATOMIC (Opus lane O25c, 2026-09-26).

  `beispiele/162-geteilte-flagge.gab`: `melde` stores the payload-free atomic `STAND` on one
  thread, `lies` loads it on another, no lock. The exporter carries it since lane O25c
  (`read_atomic`, `Stmt.publish` with the empty payload), and its certificate
  `Zertifikat/G162_geteilte_flagge.lean` decides `AkzeptiertX` in Lean (`gCheck`) and states
  `GabbroZiel` on it (`gP_gabbro_f`). Pinned here, in the build: the checker of BEFORE refuses
  the unit (so the certificate covers a program the statement of before did not), `STAND` is
  `atomic` in the exported declaration, and it IS an admitted shared atomic of the unit.
-/
import Grammatik.Zertifikat.G162_geteilte_flagge

namespace Gabbro.Grammatik.AtomarZertifikatZeuge

open Gabbro.Grammatik G162_geteilte_flagge_oblig

/-- The checker of before refuses the exported unit. -/
theorem g162_alt_abgelehnt : akzeptiert_pruefer.akzeptiert gE gFs gLs gCs = false := by decide

/-- The checker with the rely accepts it (the certificate's own premise). -/
theorem g162_neu_akzeptiert : Zielsatz.akzeptiertX_pruefer.akzeptiert gE gFs gLs gCs = true :=
  gCheck

/-- `STAND` travels as an `atomic` global. -/
theorem g162_atomar : G162_geteilte_flagge_oblig.gD.atomar G162_geteilte_flagge_oblig.GGlob.STAND = true := rfl

#print axioms g162_alt_abgelehnt
#print axioms g162_neu_akzeptiert

end Gabbro.Grammatik.AtomarZertifikatZeuge
