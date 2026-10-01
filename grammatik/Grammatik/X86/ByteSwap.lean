/-
  File:      Grammatik/X86/ByteSwap.lean
  Subject:   Canonical 32/64-bit byte-swap helpers (lane 420).

  Pure byte-permutation value helpers over the canonical `Wort`
  (`Grammatik/X86/Typen.lean`), reusing `wortByte` from `Speicher.lean`.
  No `Befehl` constructor, no codec bytes, no `schritt` change, no
  source correspondence is claimed here; see CUTS.
-/
import Grammatik.X86.Speicher

namespace Gabbro.Grammatik.X86

/-- Canonical 64-bit byte reversal (future BSWAP r64 value shape). -/
def bswap64 (v : Wort) : Wort :=
  BitVec.ofNat 64 ((wortByte v 7).toNat + (wortByte v 6).toNat * 256 +
    (wortByte v 5).toNat * 65536 + (wortByte v 4).toNat * 16777216 +
    (wortByte v 3).toNat * 4294967296 +
    (wortByte v 2).toNat * 1099511627776 +
    (wortByte v 1).toNat * 281474976710656 +
    (wortByte v 0).toNat * 72057594037927936)

/- CUTS:
    Skeleton only: bswap32, involution, byte-order memory correspondence,
    width-extension, flag preservation, refusal of 16-bit shape, witnesses
    and the native-extension cut are open.
-/

#print axioms bswap64

end Gabbro.Grammatik.X86
