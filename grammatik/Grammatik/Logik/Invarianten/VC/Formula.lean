module

public import Grammatik.Logik.Invarianten.Modell.World

@[expose] public section

namespace Gabbro.Grammatik.Invarianten.VC

open Frag Elim Elim.Korrekt Modell

/-- Re-embed the existing quantifier-free result. Substitution always happens
    AFTER elimination, so a call's havoc binder cannot capture a stored value. -/
def quoteQF : QF α → LProp α
  | .tru => .tru
  | .fls => .fls
  | .atom .lt term => .lt term (.konst 0)
  | .atom (.dvd k) term => .dvd (k + 1 : Nat) term
  | .atom (.ndvd k) term => .not (.dvd (k + 1 : Nat) term)
  | .conj left right => .and (quoteQF left) (quoteQF right)
  | .disj left right => .or (quoteQF left) (quoteQF right)

theorem quoteQF_denote [DecidableEq α] (body : QF α) (values : Assignment α) :
    (quoteQF body).denote values ↔ body.denote values := by
  induction body with
  | tru => rfl
  | fls => rfl
  | atom relation term => cases relation <;> rfl
  | conj left right ihLeft ihRight => exact and_congr ihLeft ihRight
  | disj left right ihLeft ihRight => exact or_congr ihLeft ihRight

def lower [DecidableEq α] (body : LProp α) : QF α := (elimination body).1

theorem lower_denote [DecidableEq α] (body : LProp α) (values : Assignment α) :
    (lower body).denote values ↔ body.denote values := elimination_denote body values

def termKeys : LTerm α → List α
  | .var name => [name]
  | .konst _ => []
  | .add left right | .sub left right => termKeys left ++ termKeys right
  | .scale _ term => termKeys term

def qfKeys : QF α → List α
  | .tru | .fls => []
  | .atom _ term => termKeys term
  | .conj left right | .disj left right => qfKeys left ++ qfKeys right

theorem termKeys_congr (term : LTerm α) (values other : Assignment α)
    (agree : ∀ name ∈ termKeys term, values name = other name) :
    term.denote values = term.denote other := by
  induction term with
  | var name => exact agree name (by simp [termKeys])
  | konst _ => rfl
  | add left right ihLeft ihRight =>
      change left.denote values + right.denote values = left.denote other + right.denote other
      rw [ihLeft (fun name h => agree name (List.mem_append_left _ h)),
        ihRight (fun name h => agree name (List.mem_append_right _ h))]
  | sub left right ihLeft ihRight =>
      change left.denote values - right.denote values = left.denote other - right.denote other
      rw [ihLeft (fun name h => agree name (List.mem_append_left _ h)),
        ihRight (fun name h => agree name (List.mem_append_right _ h))]
  | scale k term ih => exact congrArg (k * ·) (ih agree)

theorem qfKeys_congr (body : QF α) (values other : Assignment α)
    (agree : ∀ name ∈ qfKeys body, values name = other name) :
    body.denote values ↔ body.denote other := by
  induction body with
  | tru => rfl
  | fls => rfl
  | atom relation term =>
      simp only [QF.denote, termKeys_congr term values other agree]
  | conj left right ihLeft ihRight =>
      exact and_congr
        (ihLeft (fun name h => agree name (List.mem_append_left _ h)))
        (ihRight (fun name h => agree name (List.mem_append_right _ h)))
  | disj left right ihLeft ihRight =>
      exact or_congr
        (ihLeft (fun name h => agree name (List.mem_append_left _ h)))
        (ihRight (fun name h => agree name (List.mem_append_right _ h)))

/-- Quantify exactly the observations a callee may change. Unobserved cells
    require no variables; other observations retain their entry values. -/
def havoc [DecidableEq α] (written : α → Bool) (body : QF α) : QF α :=
  lower (universalClosure ((qfKeys body).filter written).eraseDups (quoteQF body))

private theorem closure_transfer [DecidableEq α] (names : List α) (body : QF α)
    (values other : Assignment α)
    (valid : (universalClosure names (quoteQF body)).denote values)
    (agree : ∀ name ∈ qfKeys body, name ∉ names → values name = other name) :
    body.denote other := by
  induction names generalizing values with
  | nil =>
      exact (qfKeys_congr body values other (fun name h => agree name h (by simp))).mp
        ((quoteQF_denote body values).mp valid)
  | cons name names ih =>
      apply ih (values.bind name (other name)) (valid (other name))
      intro key member absent
      by_cases same : key = name
      · subst key
        exact bind_same values name (other name)
      · simpa only [Assignment.bind, same, ↓reduceIte] using
          agree key member (by simp only [List.mem_cons, not_or]; exact ⟨same, absent⟩)

private theorem closure_characterization [DecidableEq α] (names : List α) (body : QF α)
    (values : Assignment α) :
    (universalClosure names (quoteQF body)).denote values ↔
      ∀ other, (∀ key ∈ qfKeys body, key ∉ names → values key = other key) →
        body.denote other := by
  constructor
  · exact fun valid other agree => closure_transfer names body values other valid agree
  · intro valid
    induction names generalizing values with
    | nil => exact (quoteQF_denote _ _).mpr (valid values (fun _ _ _ => rfl))
    | cons name names ih =>
        intro value
        apply ih (values.bind name value)
        intro other agree
        apply valid other
        intro key member absent
        have different : key ≠ name := fun same =>
          absent (List.mem_cons.mpr (Or.inl same))
        have absentTail : key ∉ names := fun inside =>
          absent (List.mem_cons_of_mem name inside)
        simpa only [Assignment.bind, different, ↓reduceIte] using agree key member absentTail

/-- Repeated observations add only shadowed universal binders. Removing them
    preserves the whole formula, including every unquantified observation. -/
theorem closure_eraseDups [DecidableEq α] (names : List α) (body : QF α)
    (values : Assignment α) :
    (universalClosure names.eraseDups (quoteQF body)).denote values ↔
      (universalClosure names (quoteQF body)).denote values := by
  simp only [closure_characterization, List.mem_eraseDups]

theorem havoc_sound [DecidableEq α] (written : α → Bool) (body : QF α)
    (values other : Assignment α) (valid : (havoc written body).denote values)
    (frame : ∀ key ∈ qfKeys body, written key = false → values key = other key) :
    body.denote other := by
  apply closure_transfer ((qfKeys body).filter written).eraseDups body values other
    ((lower_denote _ values).mp valid)
  intro key member absent
  apply frame key member
  cases h : written key with
  | false => rfl
  | true => exact False.elim (absent (List.mem_eraseDups.mpr (List.mem_filter.mpr ⟨member, h⟩)))

theorem havoc_of_valid [DecidableEq α] (written : α → Bool) (body : QF α)
    (valid : ∀ values, body.denote values) (values : Assignment α) :
    (havoc written body).denote values := by
  apply (lower_denote _ _).mpr
  apply (closure_characterization _ _ _).mpr
  exact fun other _ => valid other

/-- The list is the complete free support, with no external enumeration duty. -/
theorem termKeys_closed [DecidableEq α] (term : LTerm α) (names : List α)
    (included : ∀ name ∈ termKeys term, name ∈ names) : termClosedB names term = true := by
  induction term with
  | var name => simpa only [termClosedB, decide_eq_true_eq] using included name (by simp [termKeys])
  | konst _ => rfl
  | add left right ihLeft ihRight | sub left right ihLeft ihRight =>
      exact Bool.and_eq_true_iff.mpr
        ⟨ihLeft (fun name h => included name (List.mem_append_left _ h)),
         ihRight (fun name h => included name (List.mem_append_right _ h))⟩
  | scale _ term ih => exact ih included

theorem quoteQF_closed [DecidableEq α] (body : QF α) (names : List α)
    (included : ∀ name ∈ qfKeys body, name ∈ names) :
    closedUnderB names (quoteQF body) = true := by
  induction body with
  | tru => rfl
  | fls => rfl
  | atom relation term =>
      have ht := termKeys_closed term names included
      cases relation <;> simp only [quoteQF, closedUnderB, termClosedB, ht, Bool.and_self]
  | conj left right ihLeft ihRight | disj left right ihLeft ihRight =>
      exact Bool.and_eq_true_iff.mpr
        ⟨ihLeft (fun name h => included name (List.mem_append_left _ h)),
         ihRight (fun name h => included name (List.mem_append_right _ h))⟩

theorem termClosed_mono [DecidableEq α] (term : LTerm α) (names more : List α)
    (included : ∀ name ∈ names, name ∈ more) (closed : termClosedB names term = true) :
    termClosedB more term = true := by
  induction term with
  | var name =>
      apply decide_eq_true (included name (of_decide_eq_true closed))
  | konst _ => rfl
  | add left right ihLeft ihRight | sub left right ihLeft ihRight =>
      obtain ⟨hl, hr⟩ := Bool.and_eq_true_iff.mp closed
      exact Bool.and_eq_true_iff.mpr ⟨ihLeft hl, ihRight hr⟩
  | scale _ term ih => exact ih closed

theorem formulaClosed_mono [DecidableEq α] (body : LProp α) (names more : List α)
    (included : ∀ name ∈ names, name ∈ more) (closed : closedUnderB names body = true) :
    closedUnderB more body = true := by
  induction body generalizing names more with
  | tru => rfl
  | fls => rfl
  | le left right | lt left right | eq left right =>
      obtain ⟨hl, hr⟩ := Bool.and_eq_true_iff.mp closed
      exact Bool.and_eq_true_iff.mpr
        ⟨termClosed_mono left names more included hl,
         termClosed_mono right names more included hr⟩
  | dvd _ term => exact termClosed_mono term names more included closed
  | not body ih => exact ih names more included closed
  | and left right ihLeft ihRight | or left right ihLeft ihRight | imp left right ihLeft ihRight =>
      obtain ⟨hl, hr⟩ := Bool.and_eq_true_iff.mp closed
      exact Bool.and_eq_true_iff.mpr ⟨ihLeft names more included hl, ihRight names more included hr⟩
  | ex name body ih | all name body ih =>
      apply ih (name :: names) (name :: more) _ closed
      intro key member
      rcases List.mem_cons.mp member with same | member
      · exact List.mem_cons.mpr (Or.inl same)
      · exact List.mem_cons.mpr (Or.inr (included key member))

theorem closure_closed [DecidableEq α] (names bound : List α) (body : LProp α)
    (closed : closedUnderB (names ++ bound) body = true) :
    closedUnderB bound (universalClosure names body) = true := by
  induction names generalizing bound with
  | nil => exact closed
  | cons name names ih =>
      apply ih (name :: bound)
      apply formulaClosed_mono body (name :: names ++ bound) (names ++ name :: bound) _ closed
      intro key member
      simpa only [List.mem_cons, List.mem_append, or_assoc, or_left_comm] using member

/-- The closed formula passed to P15/P16. Free variables are never evaluated
    at zero accidentally; they are universally bound by construction. -/
def close [DecidableEq α] (body : QF α) : LProp α :=
  universalClosure (qfKeys body).eraseDups (quoteQF body)

theorem close_closed [DecidableEq α] (body : QF α) : closedUnderB [] (close body) = true :=
  closure_closed (qfKeys body).eraseDups [] (quoteQF body)
    (quoteQF_closed body _ (fun _ h => by simpa only [List.append_nil, List.mem_eraseDups] using h))

theorem close_sound [DecidableEq α] (body : QF α) (accepted : decideB (close body) = true)
    (values : Assignment α) : body.denote values := by
  apply closure_transfer (qfKeys body).eraseDups body values values
    (decideB_sound (close body) (close_closed body) accepted values)
  exact fun _ _ _ => rfl

/-- Decision completeness lets witnesses prove validity symbolically without
    reducing Cooper elimination again inside the kernel. -/
theorem close_decide_true_iff [DecidableEq α] (body : QF α) :
    decideB (close body) = true ↔ ∀ values, body.denote values := by
  constructor
  · exact close_sound body
  · intro valid
    apply decideB_of_valid (close body) (close_closed body) (fun _ => 0)
    apply (closure_characterization _ _ _).mpr
    exact fun values _ => valid values

theorem close_decide_false_iff [DecidableEq α] (body : QF α) :
    decideB (close body) = false ↔ ∃ values, ¬ body.denote values := by
  classical
  constructor
  · intro rejected
    apply Classical.byContradiction
    intro absent
    have valid : ∀ values, body.denote values := by
      intro values
      apply Classical.byContradiction
      intro invalid
      exact absent ⟨values, invalid⟩
    have accepted := (close_decide_true_iff body).mpr valid
    exact Bool.noConfusion (rejected.symm.trans accepted)
  · rintro ⟨values, invalid⟩
    exact Bool.eq_false_iff.mpr (fun accepted => invalid (close_sound body accepted values))

end Gabbro.Grammatik.Invarianten.VC
