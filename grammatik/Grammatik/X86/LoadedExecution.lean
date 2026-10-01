/-
  Loaded image to actual instruction fetch (lane 560).

  Connects the checked `Bild` file/virtual mapping and its actual memory
  construction (`geladen`, `abteilFinden`, `ladenByte`) to the byte fetch
  (`Byteschritt.geholt`, `fetchDekodiert`, `byteschritt`). The checked map
  is a premise; fetched-byte equality and the loaded execution step are
  derived conclusions. No source refinement or hardware correspondence is
  claimed here; both stay explicitly open (see CUTS).
-/
import Grammatik.X86.Bild
import Grammatik.X86.Byteschritt

namespace Gabbro.Grammatik.X86

/-- Execution state over a canonically loaded image: registers, flags and
    `rip` are caller-chosen; memory is the checked `geladen` construction,
    never a second loader. -/
def bildZustand (bild : Bild) (bias : Nat) (rip : Adresse)
    (reg : Register → Wort) (fl : Flags) : Zustand :=
  { register := reg
    flags := fl
    rip := rip
    speicher := geladen bild bias }

/-- The loaded state carries the canonically loaded memory. -/
theorem bildZustand_speicher (bild : Bild) (bias : Nat) (rip : Adresse)
    (reg : Register → Wort) (fl : Flags) :
    (bildZustand bild bias rip reg fl).speicher = geladen bild bias := by
  rfl

/- CUTS:
   - Skeleton only: the fetch-interior equality, BSS, permission
     distinction, store execution and negative probes are not yet proved.
   - No source refinement claim and no hardware correspondence claim.
-/

#print axioms bildZustand_speicher

end Gabbro.Grammatik.X86
