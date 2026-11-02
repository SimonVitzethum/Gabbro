module
public import Grammatik.Parser.Elab.UebersetzeAllg3.Measures.Fixtures
@[expose] public section

namespace Gabbro.Grammatik.Parser.Measures.Fixtures
open Uebersetze UebersetzeAllg UebersetzeAllg2

/-- The common call/continuation case in the witnesses. This is only an outcome case split;
    the program, measure gate and execution semantics remain the existing G definitions. -/
private theorem call_continuation {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx}
    (g : D.Fn) (hr : D.gruende g = 0) (out : RufAusgang g)
    (next : World D → EndAusgang V l Γ) (target : D.Fn)
    (safe : out ≠ .logik (.abstieg target))
    (rest : ∀ state, next state ≠ .logik (.abstieg target)) :
    (match out with
      | .ok state _ => next state
      | .why _ reason => keinGrund hr reason
      | .logik error => .logik error
      | .hardware error => .hardware error) ≠ EndAusgang.logik (.abstieg target) := by
  cases out with
  | ok state value => exact rest state
  | why state reason => exact (Nat.not_lt_zero _ (hr ▸ reason.isLt)).elim
  | logik error => intro bad; apply safe; cases bad; rfl
  | hardware error => intro bad; cases bad

/-- The countdown's exported `n` is its actual nonnegative entry argument. -/
theorem countdown_value_zeuge (state : World (declOf countdown)) (n : Zahl 0 1) :
    countM.mass.wert 0 state (.cons n .nil) = [n.n.toNat] := by rfl

/-- The finite countdown satisfies the real measure duty, for all pass grants and handlers. -/
theorem countdown_duty_zeuge (passes : Nat) (Q : AxEns (declOf countdown))
    (S : SperrInv (declOf countdown)) (T : (declOf countdown).Tab ⊕ (declOf countdown).Glob → Prop) :
    MassPflicht countP passes Q S T countM.mass (zykS countP [0]) 0 := by
  intro O _ _ _ U _ A _ R _ noDescent _ state env _ target _
  cases env with
  | cons n tail =>
    cases tail
    rcases n with ⟨n, lower, upper⟩
    have casesN : n = 0 ∨ n = 1 := by omega
    rcases casesN with zero | one
    · subst n
      intro bad
      cases bad
    · subst n
      change (match R 0 (A [] (A [] state)) (.cons (⟨0, by decide, by decide⟩ : Zahl 0 1) .nil) with
        | .ok state' _ => .zurueck (A [] state') ()
        | .why _ reason => keinGrund (by rfl) reason
        | .logik error => .logik error
        | .hardware error => .hardware error) ≠ EndAusgang.logik (.abstieg target)
      exact call_continuation 0 rfl _ _ target (noDescent _ _ _ target) (fun _ bad => by cases bad)

/-- Both functions of the mutual cycle carry the same singleton tuple. -/
theorem mutual_lengths_zeuge :
    ∀ f g, zykS mutualP [0, 1] f g = true → (mutualM.mass f).length = (mutualM.mass g).length :=
  cycleLengths_sound mutual mutualP mutualM.mass cycleLengths_sound_zeuge

/-- Every function of the mutual cycle discharges the duty; both positive-entry calls pass `0`. -/
theorem mutual_duty_zeuge (passes : Nat) (Q : AxEns (declOf mutual))
    (S : SperrInv (declOf mutual)) (T : (declOf mutual).Tab ⊕ (declOf mutual).Glob → Prop)
    (f : (declOf mutual).Fn) :
    MassPflicht mutualP passes Q S T mutualM.mass (zykS mutualP [0, 1]) f := by
  rcases f with ⟨index, bound⟩
  have casesF : index = 0 ∨ index = 1 := by change index < 2 at bound; omega
  rcases casesF with first | second <;> subst index
  all_goals
    intro O _ _ _ U _ A _ R _ noDescent _ state env _ target _
    cases env with
    | cons n tail =>
      cases tail
      rcases n with ⟨n, lower, upper⟩
      have casesN : n = 0 ∨ n = 1 := by omega
      rcases casesN with zero | one
      · subst n
        intro bad
        cases bad
      · subst n
        first
        | change (match R 1 (A [] (A [] state)) (.cons (⟨0, by decide, by decide⟩ : Zahl 0 1) .nil) with
            | .ok state' _ => .zurueck (A [] state') ()
            | .why _ reason => keinGrund (by rfl) reason
            | .logik error => .logik error
            | .hardware error => .hardware error) ≠ EndAusgang.logik (.abstieg target)
          exact call_continuation 1 rfl _ _ target (noDescent _ _ _ target) (fun _ bad => by cases bad)
        | change (match R 0 (A [] (A [] state)) (.cons (⟨0, by decide, by decide⟩ : Zahl 0 1) .nil) with
            | .ok state' _ => .zurueck (A [] state') ()
            | .why _ reason => keinGrund (by rfl) reason
            | .logik error => .logik error
            | .hardware error => .hardware error) ≠ EndAusgang.logik (.abstieg target)
          exact call_continuation 0 rfl _ _ target (noDescent _ _ _ target) (fun _ bad => by cases bad)

/-- The first call of this cycle is not in tail position; both calls really decrease the measure. -/
theorem nonTail_duty_zeuge (passes : Nat) (Q : AxEns (declOf nonTail))
    (S : SperrInv (declOf nonTail)) (T : (declOf nonTail).Tab ⊕ (declOf nonTail).Glob → Prop) :
    MassPflicht nonTailP passes Q S T nonTailM.mass (zykS nonTailP [0]) 0 := by
  intro O _ _ _ U _ A _ R _ noDescent _ state env _ target _
  cases env with
  | cons n tail =>
    cases tail
    rcases n with ⟨n, lower, upper⟩
    have casesN : n = 0 ∨ n = 1 := by omega
    rcases casesN with zero | one
    · subst n
      intro bad
      cases bad
    · subst n
      change (match R 0 (A [] (A [] state)) (.cons (⟨0, by decide, by decide⟩ : Zahl 0 1) .nil) with
        | .ok state' _ =>
          match R 0 (A [] state') (.cons (⟨0, by decide, by decide⟩ : Zahl 0 1) .nil) with
          | .ok state'' _ => .zurueck (A [] state'') ()
          | .why _ reason => keinGrund (by rfl) reason
          | .logik error => .logik error
          | .hardware error => .hardware error
        | .why _ reason => keinGrund (by rfl) reason
        | .logik error => .logik error
        | .hardware error => .hardware error) ≠ EndAusgang.logik (.abstieg target)
      apply call_continuation 0 rfl _ _ target (noDescent _ _ _ target)
      intro state'
      exact call_continuation 0 rfl _ _ target (noDescent _ _ _ target) (fun _ bad => by cases bad)

/-- Acyclic source functions reuse the existing vacuous-cycle theorem, with their real exported measure. -/
theorem acyclic_duty_zeuge (passes : Nat) (Q : AxEns (declOf acyclic))
    (S : SperrInv (declOf acyclic)) (T : (declOf acyclic).Tab ⊕ (declOf acyclic).Glob → Prop) :
    MassPflicht acyclicP passes Q S T acyclicM.mass (zykS acyclicP [0]) 0 :=
  massPflicht_ohne_zyklus acyclicP [0] passes Q S T acyclicM.mass 0 (by
    intro g
    have hg : g = 0 := Fin.ext (by have := g.isLt; change g.val < 1 at this; omega)
    subst g
    decide +kernel)

end Gabbro.Grammatik.Parser.Measures.Fixtures
