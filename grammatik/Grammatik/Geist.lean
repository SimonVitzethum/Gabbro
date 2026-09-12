/-
  File:      Grammatik/Geist.lean
  Subject:   GHOST CARRIERS (syscall lane S3) -- spec-only tables and globals.

  A ghost carrier is ordinary memory for the semantics (every theorem stays
  valid) and absent for the emitter. Rule G001: executable code reads no
  ghost. Ghost tables may appear only in contracts (`requires`/`ensures`).
-/
import Grammatik.Semantik

namespace Gabbro.Grammatik.Geist

open Gabbro.Grammatik

variable {D : Deklaration}

/-- A carrier is ghost if its declaration flag says so. -/
def istGeist : D.Tab ⊕ D.Glob → Bool
  | .inl t => D.geist t
  | .inr g => D.ggeist g

/-
CUTS: footprint checkers, G001 soundness, the omission theorem, and the
witness program are not proved yet.
-/

end Gabbro.Grammatik.Geist
