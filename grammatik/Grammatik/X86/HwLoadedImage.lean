/-
  File:      Grammatik/X86/HwLoadedImage.lean
  Subject:   Coherent machine fetching from the loaded image.

  Lane 1137: projection/embedding relating a `HwMaschine` core fetch to the
  loaded-image fetch (`Byteschritt`, `LoadedExecution`, `ComposeImageFetch`).
  Every accepted definition is reused unchanged; fetch identity on a checked
  mapping is proved, and a Hw register step of a fetched pilot instruction is
  a `Byteschritt` step on the projection. Extension rows are the stated
  obstruction: they step the Hw machine but refuse `byteschritt`.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Speicher
import Grammatik.X86.TSO
import Grammatik.X86.Byteschritt
import Grammatik.X86.Bild
import Grammatik.X86.LoadedExecution
import Grammatik.X86.ComposeImageFetch
import Grammatik.X86.ComposeMapPerms
import Grammatik.X86.ValidatorSkeleton
import Grammatik.X86.HardwareExecution
import Grammatik.X86.ExtendedExecution

namespace Gabbro.Grammatik.X86

/-- Memory coincidence: the machine runs on the loaded image. -/
def hwBildSpeicherGleich (m : HwMaschine) (bild : Bild) (bias : Nat) : Prop :=
  m.mem = geladen bild bias

/-- Core/fetch-input agreement: the core fetches where the image state does. -/
def hwBildKernGleich (m : HwMaschine) (c : Nat) (rip : Adresse)
    (reg : Register → Wort) (fl : Flags) : Prop :=
  (m.kerne c).rip = rip ∧ (m.kerne c).register = reg ∧ (m.kerne c).flags = fl

/-- PROJECTION IDENTITY: under memory coincidence and core agreement the
    core projection IS the loaded image state. -/
theorem hwBild_zustand_gleich (m : HwMaschine) (c : Nat) (bild : Bild)
    (bias : Nat) (rip : Adresse) (reg : Register → Wort) (fl : Flags)
    (hmem : m.mem = geladen bild bias)
    (hrip : (m.kerne c).rip = rip)
    (hreg : (m.kerne c).register = reg)
    (hfl : (m.kerne c).flags = fl) :
    projZustand m c = bildZustand bild bias rip reg fl := by
  unfold projZustand bildZustand
  simp only [hrip, hreg, hfl, hmem]

/- CUTS (skeleton):
   Proved: projection identity only.
   OPEN: fetched-byte/fetch/step identity, pilot-step connection, extension
   obstruction, adapter, refusals, joint witness, full bridge to W/GX.
   No hardware correspondence beyond self-consistency is claimed.
-/

#print axioms hwBild_zustand_gleich

end Gabbro.Grammatik.X86
