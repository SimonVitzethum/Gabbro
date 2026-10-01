/-
  Decoder/fetch coverage from the actual decoder (lane 435).

  The byte pilot (`Codec`) proves round trips per instruction and the fetch
  layer (`Byteschritt`) checks consumed-length consistency at runtime, but the
  general fact -- every successful `decode` of an ARBITRARY byte list consumes
  exactly its stated length within 1..15 -- is open in both files. This module
  closes it from the decoder side only (never from encoder round trips), adds
  the per-form exact-length classification, the suffix/window congruence, and
  the executable entry-byte relation over loaded images. No hardware, source,
  TSO or whole-image claim is made here.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Speicher
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.Codec
import Grammatik.X86.Byteschritt
import Grammatik.X86.Bild

namespace Gabbro.Grammatik.X86

/-- Executable entry window: the first `n` bytes of a loaded image at entry
    `e` under `bias`, read through the checked section mapping. -/
def eintrittFenster (bild : Bild) (bias e n : Nat) : List Byte :=
  (List.range n).map (fun i => ladenByte bild bias (e + i))

/-- Entry decode: the actual decoder over the entry window, capped at the
    15-byte maximum. Length comes from decoding only, never an annotation. -/
def eintrittDekodiert (bild : Bild) (bias e : Nat) :
    Option (Decodiert × List Byte) :=
  decode (eintrittFenster bild bias e fetchCap)

/- CUTS (skeleton):
    - The arbitrary-input length soundness, the per-form classification, the
      suffix/window congruence and the entry-byte bridge are not yet proved.
    - No hardware, source, TSO, concurrency or whole-image claim is made here.
-/

#print axioms eintrittFenster
#print axioms eintrittDekodiert

end Gabbro.Grammatik.X86
