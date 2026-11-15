module

public import Grammatik.Logik.Vertraege.Pruefer.Goal
public import Grammatik.Logik.Invarianten.VC.Witness

@[expose] public section

namespace Gabbro.Grammatik.Vertraege.Pruefer.LoopWitness

open Invarianten Invarianten.Frag Invarianten.Elim Invarianten.VC
open Invarianten.VC.Witness

/-- Each actual pass increments len while len < cap. The signature really
    writes len, so preserving len <= cap is a nonempty owed return duty. -/
def body (count : Nat) : Endblock declaration contract false [] [] :=
  .cons (.retry count (.not guard)
    (.cons (.assignGlob false (.eng (.add lengthValue (.lit 1)) 0 10 lengthValue)
      rfl (access false)) .nil) .nil)
    (.ret .empty (List.Perm.refl _))

def loopProgram (count : Nat) : Programm declaration :=
  { program with rumpf := fun _ => body count }

def hints : LoopHints declaration := fun _ => some invariant

/-- This proof exercises the new contract compiler, including the owed
    invariant, rather than only deciding a handwritten arithmetic formula. -/
theorem unrolling_accepted_zeuge :
    KontrakteGeprueftB (loopProgram 2) (SperrInv.leer declaration) [()]
      (fun _ => none) { expansion := 4 } = true := by
  decide

theorem checked_hint_accepted_zeuge :
    KontrakteGeprueftB (loopProgram 100) (SperrInv.leer declaration) [()]
      (fun _ => none) { expansion := 4 } hints = true := by
  decide

/-- The same large loop is refused when no hint is available. -/
theorem absent_hint_refused_zeuge :
    KontrakteGeprueftB (loopProgram 100) (SperrInv.leer declaration) [()]
      (fun _ => none) { expansion := 4 } = false := by
  decide

/-- A false hint fails its entry VC. -/
theorem false_hint_refused_zeuge :
    KontrakteGeprueftB (loopProgram 100) (SperrInv.leer declaration) [()]
      (fun _ => none) { expansion := 4 } (fun _ => some .fls) = false := by
  decide

end Gabbro.Grammatik.Vertraege.Pruefer.LoopWitness
