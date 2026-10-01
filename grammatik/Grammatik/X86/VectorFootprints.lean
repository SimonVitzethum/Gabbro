/-
  File:      Grammatik/X86/VectorFootprints.lean
  Subject:   Packed-vector byte footprints with checked extent and alias admission.

  Lane 426 (continuous Lean proof reserve): generic 16-byte footprints for
  the packed 128-bit words of `Vektor.lean` (two ordered canonical 8-byte
  chunks), over the canonical `Speicher.lean` byte vocabulary. Proves
  footprint membership/length, the Prop-to-Bool disjointness bridge the
  `OverlapRefusal.lean` checker consumes, vector-vector disjointness from
  checked Nat intervals, checked carrier extent (`fussEnthalten`) with a
  partial-tail refusal, and alias admission/refusal through the existing
  `klassifiziere`/`aliasZulassen` policy. No vector store atomicity is
  claimed (the torn intermediate state of `vecWrite_teilt` stands); full
  native vector lowering stays OPEN (see CUTS).
-/
import Grammatik.X86.Vektor
import Grammatik.X86.Regionen
import Grammatik.X86.OverlapRefusal

namespace Gabbro.Grammatik.X86

/-- The 16-byte footprint of a packed-vector access: the two ordered
    canonical 8-byte chunk footprints concatenated. Per-byte events, not
    one atomic occurrence. -/
def vecFuss (a : Adresse) : List Adresse :=
  Fuss a ++ Fuss (vecHiAddr a)

/-- A 16-byte vector carrier: a readable/writable, never-executable
    extent of exactly two words at `basis`. -/
def vecTraeger (basis : Nat) : Region :=
  { basis := basis, len := 16, lesbar := true,
    schreibbar := true, ausfuehrbar := false }

/-- A vector footprint is sixteen per-byte events. -/
theorem vecFuss_laenge (a : Adresse) : (vecFuss a).length = 16 := by
  simp [vecFuss, fuss_laenge]

/- CUTS:
    Skeleton only so far. Full native vector lowering (decoder/ABI/image,
    source correspondence, fault order, tearing correspondence, FP lanes,
    budget transfer, timing) is OPEN and stays refused by `simdFreigabe`.
-/

#print axioms vecFuss_laenge

end Gabbro.Grammatik.X86
