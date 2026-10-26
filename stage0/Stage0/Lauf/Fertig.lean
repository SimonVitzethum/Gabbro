/-
  File:      stage0/Stage0/Lauf/Fertig.lean
  Subject:   When a thread of the thread machine has ended: its last frame stands at its return.
-/
import Grammatik.Logik.Ruf.Maschine.RufMaschineG

namespace Gabbro.Stage0

open Gabbro.Grammatik

variable {D : Deklaration}

/-- A residue stands at its return. -/
def restFertig {g : D.Fn} :
    (Σ l : Bool, Σ Γ : Ctx, Σ Λ : List (Res D), Env D Γ × GRest D (vertragVon D g) l Γ Λ) → Bool
  | ⟨_, _, _, _, .ende (.ret ..)⟩ => true
  | _ => false

/-- A frame stands at its return. -/
def kopfFertig (r : RufRahmenG D) : Bool := restFertig r.rest

/-- Thread `f` has ended: its last frame stands at its return. -/
def fertig (M : RufMaschineG D) (f : Faden) : Bool :=
  (M.faeden f).stapel.isEmpty && kopfFertig (M.faeden f).kopf

end Gabbro.Stage0
