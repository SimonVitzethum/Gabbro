module
public import Grammatik.Logik.Ruf.Ohne.RufOhneHardware.Teil2Basis
import all Grammatik.Logik.Ruf.Ohne.RufOhneHardware.Teil2Basis

public import Grammatik.Kern.Semantik.Semantik
public import Grammatik.Logik.Ruf.Ohne.RufOhneHardware.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}

/-! ## 4. The program-level check, and `rufAt` at every depth -/

/-- **The program carries no oracle form**: every body of the member list
    passes the check. A Boolean computation over the program text. -/
def programmHardwareFrei (P : Programm D) (fs : List D.Fn) : Bool :=
  fs.all fun f => (P.rumpf f).hardwareFrei

/-- **A CALL OF SUCH A PROGRAM NEVER ENDS IN A HARDWARE OUTCOME**, at any
    recursion depth, from any world, with any arguments, against any oracle.

    The induction is on the DEPTH, and it needs no premise about the oracle
    or about the user's logic: `rufAt`'s own error branches are all `logik`
    (`abstieg` at depth `0`, `vorbedingung`, `nachbedingung`, `invariante`),
    so the handler premise `OhneHardware` carries itself from one depth to
    the next, and the body contributes none by the check. -/
theorem rufAt_ohneHardware (P : Programm D) (O : Orakel D) (passes : Nat)
    (hP : ∀ f : D.Fn, (P.rumpf f).hardwareFrei = true) :
    ∀ n : Nat, OhneHardware (rufAt P O passes n) := by
  intro n
  induction n with
  | zero => intro g σ ρ e h; simp only [rufAt, reduceCtorEq] at h
  | succ m ih =>
      intro g σ ρ e h
      simp only [rufAt] at h
      split at h
      · cases h
      · split at h
        · split at h
          · cases h
          · split at h
            · cases h
            · cases h
        · cases h
        · rename_i hl _ _ _; exact absurd hl (by decide)
        · rename_i hl _ _ _; exact absurd hl (by decide)
        · cases h
        · rename_i heq
          cases h
          exact Endblock.hardwareFrei_ok O passes _ ih (P.rumpf g) (hP g) _ ρ _ heq

/-- **One `rufAt` unfolding, hardware half**: with the requires gate open and
    the body ending in a hardware outcome, the call does (the twin of
    `rufAt_ok_of_gates`, VertragOrtB.lean, for the other outcome). -/
theorem rufAt_hardware_von_rumpf (P : Programm D) (O : Orakel D) (passes m : Nat)
    (f : D.Fn) (σ : World D) (ρ : Env D (D.params f)) (e : Hardware D)
    (hreq : wahr? (eval (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte)
      (P.requires f) (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte) ρ) = true)
    (hb : execEnd (V := vertragVon D f) O passes (rufAt P O passes m) (P.rumpf f)
      (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte) ρ = .hardware e) :
    rufAt P O passes (m + 1) f σ ρ = .hardware e := by
  simp only [rufAt]
  rw [if_neg (by rw [hreq]; simp only [Bool.true_eq_false, not_false_eq_true]), hb]

/-- The program-level form, over a member list of the functions. -/
theorem rufAt_ohneHardware_fs (P : Programm D) (O : Orakel D) (passes : Nat)
    {fs : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs) (h : programmHardwareFrei P fs = true) :
    ∀ n : Nat, OhneHardware (rufAt P O passes n) :=
  rufAt_ohneHardware P O passes (fun f => (List.all_eq_true.mp h) f (hvoll f))

#print axioms Gabbro.Grammatik.Endblock.hardwareFrei_ok
#print axioms Gabbro.Grammatik.rufAt_hardware_von_rumpf
#print axioms Gabbro.Grammatik.rufAt_ohneHardware

end Gabbro.Grammatik
