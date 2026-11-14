module

public import Grammatik.Logik.Invarianten.Modell.Trace
public import Grammatik.Logik.Invarianten.Korrekt.Support

public section

namespace Gabbro.Grammatik.Invarianten.Modell

open Frag Elim Elim.Korrekt

/-- Closing exactly the computed support leaves no caller-supplied coverage duty. -/
theorem universalClosure_closedUnderB [DecidableEq α] (names : List α)
    (formula : LProp α) (bound : List α)
    (supported : closedUnderB (names ++ bound) formula = true) :
    closedUnderB bound (universalClosure names formula) = true := by
  induction names generalizing bound with
  | nil => exact supported
  | cons name names ih =>
      change closedUnderB (name :: bound) (universalClosure names formula) = true
      apply ih (name :: bound)
      apply (closedUnderB_iff _ formula).mpr
      intro key member
      have covered := (closedUnderB_iff _ formula).mp supported key member
      rcases List.mem_append.mp covered with first | later
      · rcases List.mem_cons.mp first with same | rest
        · exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl same)))
        · exact List.mem_append.mpr (Or.inl rest)
      · exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr later)))

theorem universalClosure_closed [DecidableEq α] (formula : LProp α) :
    closedUnderB [] (universalClosure formula.keys formula) = true := by
  apply universalClosure_closedUnderB
  simpa only [List.append_nil] using formula.keys_supported

/-- A universal formula specializes to any full assignment, including repeated
    names. Setting a name to its current value leaves that assignment unchanged. -/
theorem universalClosure_specialize [DecidableEq α] (names : List α)
    (formula : LProp α) (values : Assignment α)
    (holds : (universalClosure names formula).denote values) : formula.denote values := by
  induction names generalizing values with
  | nil => exact holds
  | cons name names ih =>
      have identity : values.bind name (values name) = values := by
        funext other
        by_cases same : other = name <;> simp [Assignment.bind, same]
      have inner := holds (values name)
      rw [identity] at inner
      exact ih values inner

end Gabbro.Grammatik.Invarianten.Modell
