/-
  File:      Grammatik/Speichermodell/AtomarReplay.lean
  Subject:   THE REPLAY WITH THE ATOMIC RELY, part 2: the footprint property with shared
             atomics, the replay invariant `KopfSA` ... `ZielInvSA` (SperreBeweis.lean with one
             more record, `HX`, the atomic reads) and its generic steps. Opus lane O25b,
             2026-09-26, OFFEN O25. Standalone.

  `Tg` is the set of SHARED atomics of the run: carriers another thread may change with nothing
  in the program ordering it. What the footprint property `FussSX` demands of them: nothing at a
  body read (that is the exemption), and that they occur in NO contract (`VertragsFrei`:
  no `requires`, `ensures` or owed invariant reads them) -- a contract over a value that races
  would be a claim about a moment nobody can name. So every contract carrier stays STABLE, as
  in `ziel_ort_sperre`, and only body reads may see the rely.
-/

import Grammatik.Speichermodell.Atomar.AtomarReplay.T1
import Grammatik.Speichermodell.Atomar.AtomarReplay.T2
import Grammatik.Speichermodell.Atomar.AtomarReplay.T3
