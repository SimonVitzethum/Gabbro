/-
  File:      stage0/Stage0/Schritt/Grund.lean
  Subject:   The executable step of the thread machine (`RufMaschineG`), part 1: the step record and the decidable
             side conditions.

  A `Zug P O passes M f` is a successor of `M` by thread `f` TOGETHER with the rule of `RufSchrittG` that takes it:
  every step stage 0 executes is a step of the machine by construction, no separate soundness theorem is needed.
  It also names the writes the step makes (`Schritt/Schreib.lean`), so the fast machine updates its arrays in place.
-/
import Stage0.Schritt.Schreib

namespace Gabbro.Stage0

open Gabbro.Grammatik

variable {D : Deklaration}

/-- **A step of thread `f` of `M`, with its rule and the writes it makes to the memory.** -/
structure Zug (P : Programm D) (O : Orakel D) (passes : Nat) (M : RufMaschineG D) (f : Faden) where
  M' : RufMaschineG D
  schritt : RufSchrittG P O passes M f M'
  w : List (Schreib D)
  hw : M'.speicher = schreibAuf w M.speicher

/-- `HeldIn` as a Boolean: every lock the static holdings name is held. -/
def heldInB (Λ : List (Res D)) (h : List D.Lock) : Bool :=
  Λ.all fun r => match r with
    | .held L => decide (L ∈ h)
    | .marke .. => true

theorem heldIn_of {Λ : List (Res D)} {h : List D.Lock} (hb : heldInB Λ h = true) : HeldIn Λ h := by
  intro L hL
  simp only [heldInB, List.all_eq_true] at hb
  simpa using hb _ hL

/-- The read events of `lese` extend the trace of the thread's world. -/
theorem lese_neu (M : RufMaschineG D) (f : Faden) (Λ : List (Res D)) (os : List (D.Tab ⊕ D.Glob)) :
    ((M.weltVon f).lese Λ os).spur = leseEv (M.weltVon f) Λ os ++ (M.faeden f).spur :=
  lese_spur _ _ _

end Gabbro.Stage0
