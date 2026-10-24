import Grammatik.Bausteine.Arena.Ownership.Body.Check.Sound
import Grammatik.Bausteine.Arena.Ownership.Body.Witness

/-! **The executable check of a whole program**: every body of the
enumeration passes the check from its parameter context. A passing program
is `Checked`, so every actual call keeps its ownership interface. -/

namespace Gabbro.Grammatik.ArenaOwnership.Body

open Source

variable {D : Deklaration}

/-- **The check of a program** against an interface table, over an enumeration of its functions. -/
def checkProgram (P : Programm D) (A : FreiForm D) (I : Interfaces A) (fs : List D.Fn) : Bool :=
  fs.all fun f => chkE A I fs (V := vertragVon D f) (I f).output (P.rumpf f) noLoop
    (Flow.parameterContext (I f).parameters)

theorem noLoop_bounded : (noLoop : Context).bounded :=
  ⟨fun _ _ => rfl, fun ref hm => by simp [noLoop, Context.empty] at hm⟩

/-- **A program that passes the check is `Checked`.** -/
theorem checkProgram_sound {P : Programm D} {A : FreiForm D} {I : Interfaces A} {fs : List D.Fn}
    (hvoll : ∀ f, f ∈ fs) (h : checkProgram P A I fs = true) : Checked P A I := by
  intro f
  exact chkE_sound hvoll (P.rumpf f) noLoop _ noLoop_bounded
    (Flow.parameterContext_bounded _) (List.all_eq_true.mp h f (hvoll f))

/-- **Every actual call of a program that passes the check keeps its ownership interface.** -/
theorem checkProgram_calls {P : Programm D} {A : FreiForm D} {I : Interfaces A} {fs : List D.Fn}
    (hvoll : ∀ f, f ∈ fs) (h : checkProgram P A I fs = true) {O : Orakel D} (hO : GutO O) (passes : Nat) :
    ∀ n, Respects A I.contracts (rufAt P O passes n) :=
  checked_calls (checkProgram_sound hvoll h) hO passes

/-- The witness program passes the executable check, decided by the kernel. -/
theorem witness_passes : checkProgram Witness.P Witness.A Witness.I [true, false] = true := by decide

theorem witness_checked : Checked Witness.P Witness.A Witness.I :=
  checkProgram_sound (fun f => by cases f <;> simp) witness_passes

#print axioms checkProgram_sound
#print axioms witness_checked

end Gabbro.Grammatik.ArenaOwnership.Body
