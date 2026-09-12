/-
  Audit 46, probe F4: the strictness certificate shows the wrong witness (d).

  Claim (pattern d, filed as medium severity): `deckung_strikt_schwaecher`
  (KetteMehrfadenC.lean:909-936) is billed as "the deckung premise is strictly
  weaker than the hJw/hJsf equations (rule 4a certificate)" -- i.e. a joint run
  satisfying `KettenSpurDeckung` that breaks both equations. What it exhibits
  is the two-thread SEED `J₀` (`kette_zwei_start`: empty steps, start-machine
  worlds), which breaks both equations on a nonempty run (proved) but is never
  shown to satisfy the deckung: the file CUTS admit it ("a DIFFERENT chain
  discharges the deckung ... it does not exhibit one chain satisfying the
  deckung AND breaking the equations at the same machine"). A strictness
  certificate that shows equation-breaking in one witness and premise-holding
  in another proves neither `premise ∧ ¬equations` at one witness nor
  `equations → premise` -- the direction that matters.

  Demonstrated below as pure logic. First, the positive half: co-located facts
  (`Q` and `¬R` at ONE witness) do give the joint existential -- this is the
  shape the file does NOT supply for `J₀` (the missing `Q J₀`). Second, a
  concrete countermodel: split-shaped facts can both hold while the joint
  existential FAILS, so split witnesses entail nothing joint. Every binder is
  used; no `sorry/admit/axiom/native_decide/unsafe`.
-/

namespace Audit46

variable (W : Type) (Q R : W → Prop)

/-- Joint follows from co-located facts: `Q a` and `¬R a` at ONE witness. -/
theorem audit46_joint_needs_colocated
    (a : W) (hQa : Q a) (hNa : ¬ R a) :
    ∃ w : W, Q w ∧ ¬ R w :=
  ⟨a, hQa, hNa⟩

/-- Countermodel: with `W := Bool`, `Q w := (w = true)`, `R w := (w = true)`,
    the split shape holds (`¬R false`, `Q true`) yet no joint witness exists.
    So `¬R`-at-one plus `Q`-at-another proves nothing joint. -/
example : (¬ (false = true)) ∧ ((true = true)) ∧
    ¬ ∃ w : Bool, (w = true) ∧ ¬ (w = true) := by
  refine ⟨?_, ?_, ?_⟩
  · decide
  · rfl
  · rintro ⟨w, hw, hn⟩
    exact hn hw

end Audit46

/-
CUTS:
- The countermodel is the meta-argument, not a claim about chains: split
  hypotheses (`¬R` at `a`, `Q` at `b`) are compatible with joint failure.
- The missing file fact is `Q J₀` (deckung AT the seed): with it, the first
  theorem closes the joint existential at `J₀` itself.
- `deckung_strikt_schwaecher` itself is NOT challenged as a Lean theorem: it
  proves what it states (the seed breaks both equations). The finding is the
  docstring direction (d): "strictly weaker" is not established by it.
-/
#print axioms Audit46.audit46_joint_needs_colocated
