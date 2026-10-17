/-
  File:      Grammatik/Speichermodell/AtomarAkteur.lean
  Subject:   THE REPLAY WITH THE ATOMIC RELY, part 3: the acting thread keeps its replay, every
             rule of G (`akteurSA`, the twin of `akteurS` in ZielOrtSperre.lean). Every rule
             that READS goes through `fadenSA_lese` (or records its read in `pushSA_gen`,
             `fadenSA_ax`, `popSA_ens`): the read is answered from the machine's presented
             memory at the shared atomics it touches. Opus lane O25b, 2026-09-26. Standalone.

  The step is a step of G from ANY machine `M` -- in particular from a machine whose memory at
  the shared atomics is what the weak memory presented (machine GA, Atomar.lean). Nothing here
  depends on how `M` was reached: the replay invariant `FadenSA` is the whole premise.
-/

import Grammatik.Speichermodell.Atomar.AtomarAkteur.T1
import Grammatik.Speichermodell.Atomar.AtomarAkteur.T2
