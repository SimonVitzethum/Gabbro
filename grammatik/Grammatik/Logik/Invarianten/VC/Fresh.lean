module

public import Grammatik.Logik.Invarianten.VC.Control

@[expose] public section

namespace Gabbro.Grammatik.Invarianten.VC

open Frag Elim Elim.Korrekt Modell

variable {D : Deklaration}

/-- `none` is fresh by construction: memory observations are all `some key`.
    Elimination immediately removes the local binder from the public matrix. -/
def liftLocalTerm : LTerm α → LTerm (Option α)
  | .var key => .var (some key)
  | .konst value => .konst value
  | .add a b => .add (liftLocalTerm a) (liftLocalTerm b)
  | .sub a b => .sub (liftLocalTerm a) (liftLocalTerm b)
  | .scale k a => .scale k (liftLocalTerm a)

def dropLocalTerm : LTerm (Option α) → LTerm α
  | .var none => .konst 0
  | .var (some key) => .var key
  | .konst value => .konst value
  | .add a b => .add (dropLocalTerm a) (dropLocalTerm b)
  | .sub a b => .sub (dropLocalTerm a) (dropLocalTerm b)
  | .scale k a => .scale k (dropLocalTerm a)

def liftLocalQF : QF α → QF (Option α)
  | .tru => .tru
  | .fls => .fls
  | .atom relation term => .atom relation (liftLocalTerm term)
  | .conj a b => .conj (liftLocalQF a) (liftLocalQF b)
  | .disj a b => .disj (liftLocalQF a) (liftLocalQF b)

def dropLocalQF : QF (Option α) → QF α
  | .tru => .tru
  | .fls => .fls
  | .atom relation term => .atom relation (dropLocalTerm term)
  | .conj a b => .conj (dropLocalQF a) (dropLocalQF b)
  | .disj a b => .disj (dropLocalQF a) (dropLocalQF b)

theorem liftLocalTerm_denote (term : LTerm α) (values : Assignment (Option α)) :
    (liftLocalTerm term).denote values = term.denote (fun key => values (some key)) := by
  induction term <;> simp_all [liftLocalTerm, LTerm.denote]

/-- The assignment of the lifted variables: the fresh local reads 0, the rest reads `values`. -/
def dropBase (values : Assignment α) : Assignment (Option α)
  | none => 0
  | some name => values name

theorem dropLocalTerm_denote (term : LTerm (Option α)) (values : Assignment α) :
    (dropLocalTerm term).denote values = term.denote (dropBase values) := by
  induction term with
  | var key => cases key <;> rfl
  | konst _ => rfl
  | add a b ha hb | sub a b ha hb => simp_all [dropLocalTerm, LTerm.denote]
  | scale k a ha => simp_all [dropLocalTerm, LTerm.denote]

theorem liftLocalQF_denote (body : QF α) (values : Assignment (Option α)) :
    (liftLocalQF body).denote values ↔ body.denote (fun key => values (some key)) := by
  induction body <;> simp_all [liftLocalQF, QF.denote, liftLocalTerm_denote]

theorem dropLocalQF_denote (body : QF (Option α)) (values : Assignment α) :
    (dropLocalQF body).denote values ↔ body.denote (dropBase values) := by
  induction body <;> simp_all [dropLocalQF, QF.denote, dropLocalTerm_denote]

def localCode : (τ : Ty) → Wert D τ → Int
  | .int _ _, value => value.n
  | .bool, value => if wahr? value = true then 1 else 0
  | _, _ => 0

def localRange (τ : Ty) : LProp (Option (Observation D)) :=
  match τ with
  | .int lo hi => .and (.le (.konst lo) (.var none)) (.le (.var none) (.konst hi))
  | .bool => .and (.le (.konst 0) (.var none)) (.le (.var none) (.konst 1))
  | _ => .tru

theorem localRange_sound (τ : Ty) (value : Wert D τ) (values : Assignment (Observation D)) :
    (localRange τ).denote (Assignment.bind (dropBase values) none (localCode τ value)) := by
  cases τ with
  | int lo hi =>
      simpa [localRange, LProp.denote, LTerm.denote, Assignment.bind, localCode] using
        (⟨value.lo_le, value.le_hi⟩ : lo ≤ value.n ∧ value.n ≤ hi)
  | bool =>
      by_cases h : wahr? value = true <;>
        simp [localRange, LProp.denote, LTerm.denote, Assignment.bind, localCode, h]
  | _ => trivial

/-- A decoded local is universally quantified with its type range and snapshot
    equality. Finite type specialization keeps the concrete Expr translator;
    the fresh variable cannot alias any world observation. -/
def freshImplication (τ : Ty) (value : Wert D τ)
    (guard : LProp (Observation D)) (post : QF (Observation D)) : QF (Observation D) :=
  dropLocalQF (lower (.all none (.imp
    (.and (localRange τ) (.eq (.var none) (.konst (localCode τ value))))
    (.imp (quoteQF (liftLocalQF (lower guard))) (quoteQF (liftLocalQF post))))))

theorem freshImplication_sound (τ : Ty) (value : Wert D τ)
    (guard : LProp (Observation D)) (post : QF (Observation D))
    (values : Assignment (Observation D))
    (valid : (freshImplication τ value guard post).denote values)
    (selected : guard.denote values) : post.denote values := by
  have universal := (lower_denote _ _).mp ((dropLocalQF_denote _ values).mp valid)
  let extended : Assignment (Option (Observation D)) :=
    Assignment.bind (dropBase values) none (localCode τ value)
  have projection : (fun key => extended (some key)) = values := by
    funext key
    simp [extended, Assignment.bind]
    rfl
  have ready := universal (localCode τ value)
    ⟨localRange_sound τ value values, by simp [LProp.denote, LTerm.denote, Assignment.bind]⟩
  have present : (quoteQF (liftLocalQF (lower guard))).denote extended := by
    rw [quoteQF_denote, liftLocalQF_denote, projection, lower_denote]
    exact selected
  have result := (liftLocalQF_denote post extended).mp ((quoteQF_denote _ _).mp (ready present))
  simpa only [projection] using result

end Gabbro.Grammatik.Invarianten.VC
