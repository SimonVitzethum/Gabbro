/-
  Stack-to-ABI composition closing (lane 828).

  Producer/consumer interface closed here: the accepted `Stapel` frame-slot
  vocabulary (`Rahmen`, `Belegung`, `sichereWort`/`ladeWort`) meets the
  accepted `StackUnwind` push/pop restoration (`push_pop_wiederhergestellt`)
  at the shared stack slot `r.schlitzAddr (b.gerettetIdx i) =
  s.register rsp - 8`, under the accepted `CallAlign16` call-site alignment
  (`rufAlignOk`) and the per-frame red-zone rule below. No transition,
  decoder, memory model or source claim is created here; every execution
  fact reuses the accepted producer theorems by name.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Speicher
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.Stapel
import Grammatik.X86.StackUnwind
import Grammatik.X86.CallAlign16

namespace Gabbro.Grammatik.X86

/-- Red-zone rule per frame: the 128 bytes below `rsp` lie inside the frame
    extent, so a leaf routine's red zone never leaves the checked frame. -/
def rotZoneImRahmen (s : Zustand) (r : Rahmen) : Bool :=
  decide (r.basis + 128 ≤ (s.register Register.rsp).toNat ∧
    (s.register Register.rsp).toNat ≤ r.spitzeNat)

/- CUTS (skeleton; the composition theorem and its witness land next):
    - Proved here so far: the red-zone rule `rotZoneImRahmen` only.
    - The call/ret plus alignment leg stays with its producer
      `CallAlign16_verbindung`; the fetched nested leg stays with
      `geholt_verschachtelt_wiederhergestellt` (lane 569).
    - No TSO/store-buffer/GX bridge, no source correspondence, no
      loader/entry/relocation/cost/final-image claim is made here.
-/

#print axioms rotZoneImRahmen

end Gabbro.Grammatik.X86
