import Grammatik.Bausteine.Arena.Ownership.Body.Check.Sound
import Grammatik.Bausteine.Arena.Ownership.Body.Program

/-! **The executable check of a whole program**: every body of the
enumeration passes the check from its parameter context. A passing program
is `Checked`, so every actual call keeps its ownership interface. -/

namespace Gabbro.Grammatik.ArenaOwnership.Body

open Source

variable {D : Deklaration}

/-- An arena of the unit with the ownership interfaces of its functions. -/
structure ArenaIface (D : Deklaration) where
  A : FreiForm D
  I : Interfaces A

/-- **The check of a program** against an interface table, over an enumeration of its functions. -/
def checkProgram (P : Programm D) (A : FreiForm D) (I : Interfaces A) (fs : List D.Fn) : Bool :=
  fs.all fun f => chkE A I fs (V := vertragVon D f) (I f).output (P.rumpf f) noLoop
    (Flow.parameterContext (I f).parameters)

theorem noLoop_bounded : (noLoop : Context).bounded :=
  ⟨fun _ _ => rfl, fun ref hm => by simp only [noLoop, Context.empty, List.length_nil, List.replicate_zero, List.not_mem_nil] at hm⟩

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

#print axioms checkProgram_sound

end Gabbro.Grammatik.ArenaOwnership.Body
