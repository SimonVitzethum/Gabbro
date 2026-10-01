/-
  File:      Grammatik/X86/SourceMemory.lean
  Subject:   Source world/table values to target byte representation (lane 570).

  The ONE small generic representation interface between real source
  `Deklaration`/`World` table carriers and accepted `TableLayout`/`Speicher`
  bytes, for the bounded integer fragment (one `.int lo hi` slot stored as
  one little-endian 8-byte word). Source writes reuse the actual
  `execStmt` table-write operation (`World.schreibSlot`, unfolded by
  `execStmt_assignSlot`); target writes reuse `write64`/`read64`; checked
  premises reuse `repOk` (range/width/region) and `layoutOk`/`regionDisjunkt`.
-/
import Grammatik.Syntax
import Grammatik.Semantik
import Grammatik.Parser.Uebersetze
import Grammatik.X86.Typen
import Grammatik.X86.Speicher
import Grammatik.X86.Regionen
import Grammatik.X86.TableLayout

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze

/-- A source integer value as a target word: the (nonnegative) number as
    64 bits. Faithful exactly when `0 <= v.n` and `v.n < 2 ^ 64`
    (`zahlWort_wortZahl`); outside that the mapping is lossy by
    construction (`Int.toNat` clips negatives, `BitVec.ofNat` wraps). -/
def zahlWort {lo hi : Int} (v : Zahl lo hi) : Wort :=
  BitVec.ofNat 64 v.n.toNat

/- CUTS:
    - Skeleton only: representation predicate, preservation theorems,
      refusals and the joint witness are still to come.
-/

#print axioms zahlWort

end Gabbro.Grammatik.X86
