module

public import Grammatik.Logik.Invarianten.VC.Domain
public import Grammatik.Logik.Invarianten.Frag.Witness

@[expose] public section

namespace Gabbro.Grammatik.Invarianten.Frag.IntervalWitness

open Elim Elim.Korrekt VC

/-- A u32 observation, with both endpoints included and no value enumeration. -/
def u32Post : QF Bool := lower (.le (.var false) (.konst 4294967295))

theorem universalInterval_denote_zeuge (values : Assignment Bool) :
    (universalInterval false 0 4294967295 u32Post).denote values := by
  apply (universalInterval_denote _ _ _ _ _).mpr
  intro value _ upper
  rw [u32Post, lower_denote]
  change (values.bind false value) false ≤ 4294967295
  rw [bind_same]
  exact upper

theorem u32_decided_zeuge :
    decideB (close (universalInterval false 0 4294967295 u32Post))
      (close_closed _) = true :=
  (close_decide_true_iff _).mpr universalInterval_denote_zeuge

private abbrev declaration : Deklaration := Witness.declaration

private def program : Programm declaration where
  invariante := fun _ => .tru
  requires := fun f => nomatch f
  ensures := fun f => nomatch f
  rumpf := fun f => nomatch f

private def wideConstant : Expr declaration [] [] (.int 0 4294967295) :=
  .widen (by decide) (by decide) (.lit 7)

private def constantTarget (value : Wert declaration (.int 0 4294967295))
    (_ : Runtime program (fun _ => []) (SperrInv.leer declaration)) (_ : World declaration) : Prop :=
  value.n = 7

private def checkConstant (value : Wert declaration (.int 0 4294967295)) :
    Except Refusal (Condition (constantTarget value)) :=
  .ok {
    formula := lower (.eq (.konst value.n) (.konst 7))
    sound := fun _ world valid => (lower_denote _ (assignment world)).mp valid }

/-- The production selection entry point checks a u32 binding even with an
    enumeration allowance of zero. The real continuation is still checked. -/
theorem wide_local_selected_zeuge :
    (localSelect 0 wideConstant .nil constantTarget checkConstant).toOption.isSome = true := by
  rfl

private def productConstant : Expr declaration [] [] (.prod 5 [.int 7 7, .bool]) :=
  .prod 5 (.cons (.lit 7) (.cons .tru .nil))

theorem constantValue_zeuge : (constantValue productConstant .nil).isSome = true := by
  rfl

private def square : Expr declaration [] [] (.int 0 100) :=
  .mul (.glob false (Witness.globalAccess false)) (.glob true (Witness.globalAccess true))

private def boundedPost : QF (Observation declaration) :=
  lower (.le (.var (.glob false)) (.konst 100))

private theorem square_interval_valid :
    decideB (close (universalInterval (.glob false) 0 100 boundedPost))
      (close_closed _) = true := by
  apply (close_decide_true_iff _).mpr
  intro values
  apply (universalInterval_denote _ _ _ _ _).mpr
  intro value _ upper
  rw [boundedPost, lower_denote]
  change (values.bind (.glob false) value) (.glob false) ≤ 100
  rw [bind_same]
  exact upper

/-- A product of two memory variables is proved through the result interval;
    no exact linear encoding of multiplication is claimed. -/
theorem intervalWP_zeuge : (intervalWP square .nil (.glob false) boundedPost).toOption.isSome = true := by
  simp only [intervalWP, square_interval_valid, ↓reduceDIte, Except.toOption, Option.isSome]

private theorem impossible_interval :
    decideB (close (universalInterval (.glob false : Observation declaration) 0 100 .fls))
      (close_closed _) = false := by
  apply (close_decide_false_iff _).mpr
  refine ⟨fun _ => 0, fun valid => ?_⟩
  exact (universalInterval_denote _ _ _ _ _).mp valid 0 (by decide) (by decide)

/-- Failed abstraction is refused before the concrete counterexample printer.
    It cannot report the independent interval variable as a real product. -/
theorem intervalWP_refused_zeuge :
    (intervalWP square .nil (.glob false) .fls).toOption.isSome = false := by
  simp only [intervalWP, impossible_interval, Bool.false_eq_true, ↓reduceDIte,
    Except.toOption, Option.isSome]

#print axioms u32_decided_zeuge
#print axioms intervalWP_zeuge

#eval decideB (close (universalInterval false 0 4294967295 u32Post)) (close_closed _)

end Gabbro.Grammatik.Invarianten.Frag.IntervalWitness
