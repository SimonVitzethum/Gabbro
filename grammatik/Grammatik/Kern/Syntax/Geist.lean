/-
  File:      Grammatik/Geist.lean
  Subject:   GHOST CARRIERS (syscall lane S3) -- spec-only tables and globals.

  A ghost carrier is ordinary memory for the semantics (every theorem stays
  valid) and absent for the emitter. Rule G001: executable code reads no
  ghost. Ghost tables may appear only in contracts (`requires`/`ensures`).
-/

import Grammatik.Kern.Syntax.Geist.T1
import Grammatik.Kern.Syntax.Geist.T2
