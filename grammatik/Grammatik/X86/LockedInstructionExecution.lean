/-
  File:      Grammatik/X86/LockedInstructionExecution.lean
  Subject:   Final-byte LOCK XADD / LOCK CMPXCHG (64-bit word forms) and
             MFENCE: canonical decode/encode plus fetched execution over
             the canonical register/TSO state, with a proved adapter to
             the accepted `LockedOps` vocabulary.

  Lane 662: producer API for the typed W/GX consumers and
  HardwareExecution660. Manual provenance (local snapshot
  `.tmp/HARDWARE-REFERENCES/`, Intel SDM 325462-093US Sep 2026):
  LOCK prefix Vol. 2A 3-565/3-566, XADD Vol. 2D 6-27/6-28,
  CMPXCHG Vol. 2A 3-193/3-194, MFENCE Vol. 2B 4-15.
  Reuses `Zustand`/`TSOZustand`, `effAddr`, `add64`/`sub64`,
  `lockSchritt`/`casSchritt`, `mfenceZulaessig` shape and the
  `decodeExt` dispatcher (tried first, never shadowed). No second
  evaluator for older forms, no source/checker/goal change.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Wort
import Grammatik.X86.Speicher
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.Codec
import Grammatik.X86.TSO
import Grammatik.X86.LockedOps
import Grammatik.X86.ExtendedExecution
import Grammatik.X86.FeatureProfile

namespace Gabbro.Grammatik.X86

/-- Essential locked word forms: LOCK XADD and LOCK CMPXCHG over one
    64-bit memory word (base register plus 32-bit displacement), and
    the MFENCE full fence. Narrower widths stay open (see CUTS). -/
inductive LockForm where
  | xadd64 (src base : Register) (disp : BitVec 32)
  | cmpxchg64 (src base : Register) (disp : BitVec 32)
  | mfence
  deriving DecidableEq, Repr

/- CUTS:
    - Skeleton only: forms declared, decode/execution follow.
-/

#print axioms breite_bytes

end Gabbro.Grammatik.X86
