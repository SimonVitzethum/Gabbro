/- Gate-activation recognition for foreign-return witnesses. Actual check
   evidence is folded by Lauf/History from typed reporter arguments and the
   producer's normal return; no caller-supplied report is replayed here. -/
module

public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Herkunft

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration}

section GateActivation

variable [DecidableEq D.Fn]

/-- Match the selected gate activation's normal return, counting nested frames.
    An error return leaves the wrapper's Duty pending; a later unrelated normal
    return cannot turn that failed activation into successful completion. -/
def torAbschluss (g : D.Fn) : Nat → List (RufEreignisF D) → Bool
  | _, [] => false
  | depth, .eintritt _ _ _ :: rest => torAbschluss g (depth + 1) rest
  | 0, .rueck f _ _ _ _ :: _ => decide (f = g)
  | 0, .why _ _ _ _ _ :: _ => false
  | depth + 1, .rueck _ _ _ _ _ :: rest => torAbschluss g depth rest
  | depth + 1, .why _ _ _ _ _ :: rest => torAbschluss g depth rest

/-- A normal gate-wrapper return, independent of the explicit selected
    consumer's later physical retirement or reason-handling policy. -/
def torPush (g : D.Fn) : List (RufEreignisF D) → Bool
  | [] => false
  | .eintritt f _ _ :: rest =>
    (decide (f = g) && torAbschluss g 0 rest) || torPush g rest
  | _ :: rest => torPush g rest

/-- An error return does not complete this wrapper activation normally. -/
theorem torAbschluss_fehler (g : D.Fn) (rho : Env D (D.params g))
    (reason : Fin (D.gruende g)) (s0 s1 : World D)
    (rest : List (RufEreignisF D)) :
    torAbschluss g 0 (.why g rho reason s0 s1 :: rest) = false := rfl

end GateActivation

end Gabbro.Grammatik
