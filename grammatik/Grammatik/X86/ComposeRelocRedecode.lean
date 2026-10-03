/-
  File:      Grammatik/X86/ComposeRelocRedecode.lean
  Subject:   Relocation-patching to re-decode closing step (lane 826).

  Producer/consumer interface closed here (nothing re-proved, no second
  decoder, loader, executor or ISA model):
  PRODUCERS (reused by name): `Relokation.patchAt`/`patchRel32`
  (finite byte patching with range/site/frame facts), `RelocatedExecution`
  (`RelocArt`/`relocBytes`/`relocBefehl`/`relocLen`, `relocBytes_decode`,
  `PatchSite`/`siteStart`/`siteNext`/`patchSiteOk`, `patchSite_ziel`,
  `ruf_schritt_zeuge`), `Codec.decode` (canonical decoder),
  `TableLayout.hinweisOk`/`layoutFuer`/`layoutOk` (re-decided layout
  admission over `zeugenU`), `Bild.schreibLese_zeuge` (memory vocabulary).
  CONSUMERS: `ValidatorSkeleton.valX86`/`bildDeckung` (decode coverage of
  patched executable sections) and `valLayout` (layout admission): the
  closing shows a successfully patched site window re-decodes through the
  canonical decoder to the site instruction, the executed target is the
  intended mapped target, and the layout hint is re-decided.
-/
import Grammatik.X86.Relokation
import Grammatik.X86.RelocatedExecution
import Grammatik.X86.Codec
import Grammatik.X86.TableLayout
import Grammatik.X86.Bild
import Grammatik.X86.Byteschritt

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg

/-- Patched-site window: the `len` bytes at file offset `off` of the
    patched image. Re-decode runs on this window, never on metadata. -/
def redecodeFenster (out : List Byte) (off len : Nat) : List Byte :=
  (out.drop off).take len

/- CUTS (skeleton):
   - `patchAt_segment`: patched window equals the canonical site bytes.
   - `ComposeRelocRedecode_verbindung` + `_zeuge`: the closing theorem.
   - Planted refusals: interior target, out-of-range, overlap.
   - `valX86_sound`, source correspondence, TSO/GX bridge, concurrency,
     cost/time: OPEN, with their owning lanes, never assumed here.
-/

#print axioms redecodeFenster

end Gabbro.Grammatik.X86
